// Quelvra integration: shared helpers.
//
//   canon(u)               simplify with a fresh, bounded context (never the shared default budget)
//   evalD(u, env)          independent double evaluator (real domain) that also knows the special
//                          functions the integrator may produce: erf, erfi, Si, Ci, Shi, Chi, Ei, li,
//                          FresnelS, FresnelC. Returns NaN where the expression is undefined.
//   checkAntiderivative(F, f, x, opts)
//                          independent numeric check that F' == f on the real domain of f, and that
//                          F is defined wherever f is (catches ln(x) for 1/x on x < 0). Used on
//                          every candidate before it can leave the integrator.
//   linearCoeffs(u, x)     [a, b] with u == a x + b (a, b free of x) or null
//   polyCoeffs(u, x)       coefficient trees (low degree first) or null

import * as X from "../expr.js";
import * as N from "../num.js";
import { simplify, expand, makeCtx } from "../simplify.js";
import { coefficients } from "../poly.js";

export const SPECIAL = new Set(["erf", "erfi", "Si", "Ci", "Shi", "Chi", "Ei", "li", "FresnelS", "FresnelC"]);

export function budgetErr(what = "integration") {
  const e = new Error(`Quelvra: operation budget exhausted (${what})`);
  e.code = "BUDGET";
  return e;
}

let CANON_OPS = 400000;
// simplify.js can overflow the stack on some inputs (e.g. sin(-x - 2): its parity rule recurses without
// end); that is reported upstream and turned into an honest UNSUPPORTED here
function guardSimp(fn) {
  try { return fn(); } catch (e) {
    if (e instanceof RangeError && /call stack/i.test(e.message)) throw Object.assign(new Error("Quelvra: the simplifier could not handle an intermediate expression"), { code: "UNSUPPORTED" });
    throw e;
  }
}
export function canon(u, ops = CANON_OPS) {
  try { return simplify(u, makeCtx({ budget: { ops } })); } catch (e) {
    if (!(e instanceof RangeError)) throw e;
  }
  // retry with the parity of sin/cos/atan/... of an all-negative sum applied beforehand (the case that
  // makes simplify.js recurse without end)
  return guardSimp(() => simplify(fixParity(u, ops), makeCtx({ budget: { ops } })));
}
const ODD = new Set(["sin", "tan", "cot", "csc", "atan", "asin", "acot", "sinh", "tanh", "coth", "csch", "asinh", "atanh", "erf", "erfi", "Si", "Shi", "FresnelS", "FresnelC", "cbrt"]);
const EVEN = new Set(["cos", "sec", "cosh", "sech", "abs"]);
const negTerm = (t) => (t.k === "num" && t.v.n < 0n) || (t.k === "mul" && t.args[0].k === "num" && t.args[0].v.n < 0n);
function fixParity(u, ops) {
  if (!u.args.length) return u;
  const args = u.args.map((a) => fixParity(a, ops));
  if (u.k !== "fn" || args.length !== 1 || (!ODD.has(u.name) && !EVEN.has(u.name) && u.name !== "acos")) return X.withArgs ? X.withArgs(u, args) : u;
  let a = args[0];
  try { a = simplify(a, makeCtx({ budget: { ops } })); } catch (e) { if (!(e instanceof RangeError)) throw e; }
  if (a.k === "add" && a.args.every(negTerm)) {
    const p = simplify(X.add(...a.args.map((t) => simplify(X.mul(X.NEG_ONE, t), makeCtx({ budget: { ops } })))), makeCtx({ budget: { ops } }));
    if (ODD.has(u.name)) return X.neg(X.fn(u.name, p));
    if (EVEN.has(u.name)) return X.fn(u.name, p);
    return X.sub(X.PI, X.fn("acos", p));
  }
  return X.fn(u.name, a);
}
export function expandC(u) { return guardSimp(() => expand(u, makeCtx({ budget: { ops: 400000 } }))); }

// simplifying builders on a fresh context
export const B = {
  add: (...a) => canon(X.add(...a)),
  sub: (a, b) => canon(X.sub(a, b)),
  mul: (...a) => canon(X.mul(...a)),
  div: (a, b) => canon(X.div(a, b)),
  pow: (a, b) => canon(X.pow(a, b)),
  neg: (a) => canon(X.neg(a)),
  sqrt: (a) => canon(X.sqrt(a)),
  fn: (n, ...a) => canon(X.fn(n, ...a)),
  num: (n, d) => X.num(n, d),
  ln: (a) => canon(X.fn("ln", a)),
  lnAbs: (a) => canon(X.fn("ln", X.fn("abs", a))),
};

export const isFreeOf = (u, x) => X.freeOf(u, x);

// [a, b] with u == a*x + b, a != 0, a and b free of x; null otherwise.
export function linearCoeffs(u, x) {
  if (X.freeOf(u, x)) return null;
  let c;
  try { c = coefficients(u, x); } catch (_) { return null; }
  if (!c || c.length !== 2) return null;
  if (!X.freeOf(c[0], x) || !X.freeOf(c[1], x)) return null;
  return [c[1], c[0]];
}
export function polyCoeffs(u, x) {
  try { const c = coefficients(u, x); if (!c) return null; if (c.some((t) => !X.freeOf(t, x))) return null; return c; } catch (e) { if (e && e.code === "BUDGET") return null; return null; }
}

// ---------------------------------------------------------------- special functions (double)
const EULER_GAMMA = 0.57721566490153286061;
const GL_X = [-0.9739065285171717, -0.8650633666889845, -0.6794095682990244, -0.4333953941292472, -0.1488743389816312,
  0.1488743389816312, 0.4333953941292472, 0.6794095682990244, 0.8650633666889845, 0.9739065285171717];
const GL_W = [0.0666713443086881, 0.1494513491505806, 0.2190863625159820, 0.2692667193099963, 0.2955242247147529,
  0.2955242247147529, 0.2692667193099963, 0.2190863625159820, 0.1494513491505806, 0.0666713443086881];
// composite 10-point Gauss-Legendre on [0, x]
function glInt(g, x, panels) {
  if (x === 0) return 0;
  const n = Math.max(1, Math.min(4000, panels));
  const h = x / n;
  let s = 0;
  for (let i = 0; i < n; i++) {
    const a = i * h, m = a + h / 2;
    for (let k = 0; k < 10; k++) s += GL_W[k] * g(m + (h / 2) * GL_X[k]);
  }
  return (s * h) / 2;
}
export function erfD(x) {
  const ax = Math.abs(x);
  if (ax < 3) {
    let sum = x, term = x, n = 0;
    while (Math.abs(term) > 1e-17 * Math.abs(sum) && n < 300) { n++; term *= -x * x / n; sum += term / (2 * n + 1); }
    return (2 / Math.sqrt(Math.PI)) * sum;
  }
  if (ax > 6) return x > 0 ? 1 : -1;
  // continued fraction for erfc (Lentz)
  const t = erfcCF(ax);
  return x > 0 ? 1 - t : t - 1;
}
function erfcCF(x) {
  // erfc(x) = exp(-x^2)/sqrt(pi) * 1/(x + 1/2/(x + 1/(x + 3/2/(x + ...))))
  let f = x, C = x, D = 0;
  for (let n = 1; n < 300; n++) {
    const an = n / 2;
    D = x + an * D; D = D === 0 ? 1e-300 : 1 / D;
    C = x + an / C; if (C === 0) C = 1e-300;
    const del = C * D; f *= del;
    if (Math.abs(del - 1) < 1e-16) break;
  }
  return Math.exp(-x * x) / Math.sqrt(Math.PI) / f;
}
export function erfiD(x) {
  const ax = Math.abs(x);
  if (ax > 26) return x > 0 ? Infinity : -Infinity;
  // series with positive terms: no cancellation
  let term = x, sum = x;
  for (let n = 1; n < 2000; n++) {
    term *= x * x / n;
    const t = term / (2 * n + 1);
    sum += t;
    if (Math.abs(t) < 1e-17 * Math.abs(sum)) break;
  }
  return (2 / Math.sqrt(Math.PI)) * sum;
}
const sinc = (t) => (t === 0 ? 1 : Math.sin(t) / t);
export function SiD(x) {
  const ax = Math.abs(x);
  if (ax > 1e6) return (x > 0 ? 1 : -1) * Math.PI / 2;
  if (ax <= 40) return glInt(sinc, x, Math.ceil(ax * 2) + 2);
  // auxiliary asymptotics
  const { f, g } = auxFG(ax);
  const v = Math.PI / 2 - f * Math.cos(ax) - g * Math.sin(ax);
  return x > 0 ? v : -v;
}
function auxFG(x) {
  let f = 0, g = 0, t = 1 / x;
  // f ~ 1/x (1 - 2!/x^2 + 4!/x^4 ...), g ~ 1/x^2 (1 - 3!/x^2 + ...)
  let tf = 1 / x, tg = 1 / (x * x);
  for (let k = 0; k < 20; k++) {
    f += tf; g += tg;
    const nf = -tf * (2 * k + 1) * (2 * k + 2) / (x * x), ng = -tg * (2 * k + 2) * (2 * k + 3) / (x * x);
    if (Math.abs(nf) > Math.abs(tf)) break;
    tf = nf; tg = ng;
  }
  void t;
  return { f, g };
}
export function CiD(x) {
  if (!(x > 0)) return NaN;
  if (x <= 40) return EULER_GAMMA + Math.log(x) + glInt((t) => (t === 0 ? 0 : (Math.cos(t) - 1) / t), x, Math.ceil(x * 2) + 2);
  const { f, g } = auxFG(x);
  return f * Math.sin(x) - g * Math.cos(x);
}
export function ShiD(x) {
  if (Math.abs(x) > 700) return x > 0 ? Infinity : -Infinity;
  return glInt((t) => (t === 0 ? 1 : Math.sinh(t) / t), x, Math.ceil(Math.abs(x) * 2) + 2);
}
export function ChiD(x) {
  if (!(x > 0)) return NaN;
  if (x > 700) return Infinity;
  return EULER_GAMMA + Math.log(x) + glInt((t) => (t === 0 ? 0 : (Math.cosh(t) - 1) / t), x, Math.ceil(x * 2) + 2);
}
export function EiD(x) {
  if (x === 0) return NaN;
  if (x > 700) return Infinity;
  if (x < -40) {
    // Ei(x) = -E1(-x), continued fraction for E1
    const z = -x;
    let b = z + 1, c = 1e300, d = 1 / b, h = d;
    for (let i = 1; i < 500; i++) {
      const an = -i * i; b += 2;
      d = 1 / (an * d + b); c = b + an / c;
      const del = c * d; h *= del;
      if (Math.abs(del - 1) < 1e-16) break;
    }
    return -h * Math.exp(-z);
  }
  return EULER_GAMMA + Math.log(Math.abs(x)) + glInt((t) => (t === 0 ? 1 : Math.expm1(t) / t), x, Math.ceil(Math.abs(x) * 2) + 2);
}
export const liD = (x) => (x > 0 && x !== 1 ? EiD(Math.log(x)) : x === 0 ? 0 : NaN);
export function FresnelSD(x) {
  const ax = Math.abs(x);
  if (ax > 200) return (x > 0 ? 1 : -1) * 0.5;
  return glInt((t) => Math.sin(Math.PI * t * t / 2), x, Math.ceil(ax * (ax + 1) * 1.5) + 2);
}
export function FresnelCD(x) {
  const ax = Math.abs(x);
  if (ax > 200) return (x > 0 ? 1 : -1) * 0.5;
  return glInt((t) => Math.cos(Math.PI * t * t / 2), x, Math.ceil(ax * (ax + 1) * 1.5) + 2);
}
function gammaD(x) {
  if (Number.isInteger(x) && x <= 0) return NaN;
  if (x < 0.5) return Math.PI / (Math.sin(Math.PI * x) * gammaD(1 - x));
  const c = [0.99999999999980993, 676.5203681218851, -1259.1392167224028, 771.32342877765313, -176.61502916214059,
    12.507343278686905, -0.13857109526572012, 9.9843695780195716e-6, 1.5056327351493116e-7];
  x -= 1;
  let a = c[0];
  const t = x + 7.5;
  for (let i = 1; i < 9; i++) a += c[i] / (x + i);
  return Math.sqrt(2 * Math.PI) * Math.pow(t, x + 0.5) * Math.exp(-t) * a;
}
const FN = {
  sin: Math.sin, cos: Math.cos,
  tan: (t) => { const c = Math.cos(t); return Math.abs(c) < 1e-300 ? NaN : Math.sin(t) / c; },
  cot: (t) => { const s = Math.sin(t); return s === 0 ? NaN : Math.cos(t) / s; },
  sec: (t) => { const c = Math.cos(t); return c === 0 ? NaN : 1 / c; },
  csc: (t) => { const s = Math.sin(t); return s === 0 ? NaN : 1 / s; },
  asin: (t) => (Math.abs(t) > 1 ? NaN : Math.asin(t)), acos: (t) => (Math.abs(t) > 1 ? NaN : Math.acos(t)),
  atan: Math.atan, acot: (t) => (t === 0 ? Math.PI / 2 : Math.atan(1 / t)),
  asec: (t) => (Math.abs(t) < 1 ? NaN : Math.acos(1 / t)), acsc: (t) => (Math.abs(t) < 1 ? NaN : Math.asin(1 / t)),
  sinh: Math.sinh, cosh: Math.cosh, tanh: Math.tanh,
  coth: (t) => (t === 0 ? NaN : 1 / Math.tanh(t)), sech: (t) => 1 / Math.cosh(t), csch: (t) => (t === 0 ? NaN : 1 / Math.sinh(t)),
  asinh: Math.asinh, acosh: (t) => (t < 1 ? NaN : Math.acosh(t)), atanh: (t) => (Math.abs(t) >= 1 ? NaN : Math.atanh(t)),
  ln: (t) => (t > 0 ? Math.log(t) : NaN), exp: Math.exp, abs: Math.abs, sign: Math.sign,
  sqrt: (t) => (t < 0 ? NaN : Math.sqrt(t)), cbrt: Math.cbrt,
  erf: erfD, erfi: erfiD, Si: SiD, Ci: CiD, Shi: ShiD, Chi: ChiD, Ei: EiD, li: liD, FresnelS: FresnelSD, FresnelC: FresnelCD,
  gamma: gammaD,
};
export const hasEvaluator = (name) => !!FN[name];

// Real-domain double evaluator. env: object name -> number.
export function evalD(u, env = {}) {
  const ev = (w) => {
    switch (w.k) {
      case "num": return Number(w.v.n) / Number(w.v.d);
      case "sym": { const v = env[w.name]; return v === undefined ? NaN : v; }
      case "const": return w.name === "pi" ? Math.PI : w.name === "e" ? Math.E : w.name === "oo" ? Infinity : NaN;
      case "add": { let s = 0; for (const a of w.args) s += ev(a); return s; }
      case "mul": { let s = 1; for (const a of w.args) s *= ev(a); return s; }
      case "pow": {
        const b = ev(w.args[0]);
        const e = w.args[1];
        if (e.k === "num") {
          const { n, d } = e.v;
          if (b === 0 && n < 0n) return NaN;
          if (d === 1n) return Math.pow(b, Number(n));
          if (b < 0) {
            if (d % 2n === 0n) return NaN;
            const v = Math.pow(-b, Number(n) / Number(d));
            return n % 2n === 0n ? v : -v;
          }
          return Math.pow(b, Number(n) / Number(d));
        }
        const ee = ev(e);
        if (b === 0) return ee > 0 ? 0 : NaN;
        if (b < 0) return Number.isInteger(ee) ? Math.pow(b, ee) : NaN;
        return Math.pow(b, ee);
      }
      case "fn": {
        if (w.name === "log") {
          if (w.args.length === 1) return FN.ln(ev(w.args[0])) / Math.LN10;
          return FN.ln(ev(w.args[1])) / FN.ln(ev(w.args[0]));
        }
        const f = FN[w.name];
        if (!f || w.args.length !== 1) return NaN;
        const a = ev(w.args[0]);
        if (Number.isNaN(a)) return NaN;
        return f(a);
      }
      default: return NaN;
    }
  };
  try { const v = ev(u); return typeof v === "number" ? v : NaN; } catch (_) { return NaN; }
}

// ---------------------------------------------------------------- independent antiderivative check
function mulberry(seed) {
  let a = seed >>> 0;
  return () => {
    a = (a + 0x6d2b79f5) >>> 0;
    let t = a;
    t = Math.imul(t ^ (t >>> 15), t | 1);
    t ^= t + Math.imul(t ^ (t >>> 7), t | 61);
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
  };
}
const fin = (v) => Number.isFinite(v);

// Numeric derivative of F at x0 (Richardson on central differences), or NaN.
function numDeriv(F, xn, env, x0, h) {
  const at = (t) => evalD(F, { ...env, [xn]: t });
  const fp = at(x0 + h), fm = at(x0 - h), fp2 = at(x0 + h / 2), fm2 = at(x0 - h / 2);
  if (![fp, fm, fp2, fm2].every(fin)) return NaN;
  const d1 = (fp - fm) / (2 * h), d2 = (fp2 - fm2) / h;
  return (4 * d2 - d1) / 3;
}

// Check d/dx F == f. Returns { ok, good, detail }.
// Probes cover several ranges; other symbols (parameters) get random values of BOTH signs, so an
// answer that is only valid for a > 0 is rejected unless opts.assume says so.
const GL5 = [[-0.906179845938664, 0.236926885056189], [-0.538469310105683, 0.478628670499366], [0, 0.568888888888889], [0.538469310105683, 0.478628670499366], [0.906179845938664, 0.236926885056189]];
function glTree(f, xn, env, a, b, M) {
  const hh = (b - a) / M;
  let I = 0, IA = 0;
  for (let k = 0; k < M; k++) {
    const c = a + (k + 0.5) * hh;
    for (const [t, wt] of GL5) {
      const v = evalD(f, { ...env, [xn]: c + (t * hh) / 2 });
      if (!fin(v)) return null;
      I += (wt * v * hh) / 2; IA += (wt * Math.abs(v) * hh) / 2;
    }
  }
  return [I, IA];
}
// true: F(b) - F(a) matches the integral of f near x0; false: a resolved mismatch; null: cannot tell
function localFTC(F, f, xn, env, x0, Fx) {
  let resolved = false;
  for (const w of [1e-4, 1e-5, 1e-6, 1e-7]) {
    const delta = w * Math.max(1, Math.abs(x0));
    const a = x0 - delta, b = x0 + delta;
    const Fa = evalD(F, { ...env, [xn]: a }), Fb = evalD(F, { ...env, [xn]: b });
    if (!fin(Fa) || !fin(Fb)) return null;
    const r1 = glTree(f, xn, env, a, b, 32), r2 = glTree(f, xn, env, a, b, 64);
    if (!r1 || !r2) return null;
    const [I, IA] = r2;
    const tol = 1e-6 * IA + 8e-15 * (Math.abs(Fx) + Math.abs(Fa) + Math.abs(Fb));
    if (Math.abs(r1[0] - I) > 0.1 * tol) continue; // quadrature not resolved at this width
    resolved = true;
    if (Math.abs(Fb - Fa - I) <= tol) return true;
  }
  return resolved ? false : null;
}

export function checkAntiderivative(F, f, x, opts = {}) {
  const xn = typeof x === "string" ? x : x.name;
  const params = [...new Set([...X.freeSymbols(F), ...X.freeSymbols(f)])].filter((v) => v !== xn);
  const positive = new Set(opts.positive || []);
  const rnd = mulberry(opts.seed || 20260925);
  const ranges = opts.ranges || [[-3, 3], [0.02, 3], [-12, 12], [2, 40], [-40, -2], [-1.2, 1.2]];
  let good = 0, domainBad = 0, tried = 0;
  const perRange = opts.points || 14;
  const paramSets = params.length ? 3 : 1;
  for (let ps = 0; ps < paramSets; ps++) {
    const env = {};
    for (const p of params) {
      let v = 0.4 + 2.6 * rnd();
      if (!positive.has(p) && ps === 1) v = -v;
      if (!positive.has(p) && ps === 2 && rnd() < 0.5) v = -v;
      env[p] = v;
    }
    for (const [lo, hi] of ranges) {
      for (let i = 0; i < perRange; i++) {
        const x0 = lo + (hi - lo) * rnd();
        const fx = evalD(f, { ...env, [xn]: x0 });
        if (!fin(fx)) continue;
        if (Math.abs(fx) > 1e9) continue;
        // ill-conditioned point (e.g. sin(e^x) for large x): a relative change of 1e-10 in x changes f a lot
        const fx2 = evalD(f, { ...env, [xn]: x0 * (1 + 1e-10) + 1e-12 });
        if (!fin(fx2) || Math.abs(fx2 - fx) > 1e-4 * Math.max(1, Math.abs(fx))) continue;
        tried++;
        const Fx = evalD(F, { ...env, [xn]: x0 });
        if (!fin(Fx)) {
          // f is defined here but F is not: the antiderivative misses part of the domain
          // (allow isolated points: F must be defined close by on both sides)
          const l = evalD(F, { ...env, [xn]: x0 - 1e-3 }), r = evalD(F, { ...env, [xn]: x0 + 1e-3 });
          if (fin(l) && fin(r)) continue;
          domainBad++;
          if (domainBad > 0) return { ok: false, good, detail: `the antiderivative is undefined at ${xn} = ${+x0.toPrecision(6)} where the integrand is defined${params.length ? " (parameters " + JSON.stringify(env) + ")" : ""}` };
          continue;
        }
        if (Math.abs(Fx) > 1e12) continue;
        let passed = false, lastD = NaN;
        for (const hs of [1e-3, 1e-4, 1e-5, 1e-2]) {
          const h = hs * Math.max(1, Math.abs(x0));
          const d = numDeriv(F, xn, env, x0, h);
          if (!fin(d)) continue;
          lastD = d;
          const tol = 2e-6 * Math.max(1, Math.abs(fx)) + 1e-10 * Math.max(1, Math.abs(Fx)) / h;
          if (Math.abs(d - fx) <= tol) { passed = true; break; }
        }
        if (!passed && fin(lastD)) {
          // fast oscillation or large curvature defeats finite differences: compare F(b) - F(a) with a
          // fine Gauss-Legendre integral of f over a short interval around x0 instead (local FTC)
          const r = localFTC(F, f, xn, env, x0, Fx);
          if (r === true) passed = true;
          else if (r === null) continue;
        }
        if (!passed) {
          if (!fin(lastD)) {
            // F defined at x0 but not in a neighbourhood: skip only if f is also undefined nearby
            const fl = evalD(f, { ...env, [xn]: x0 - 1e-3 }), fr = evalD(f, { ...env, [xn]: x0 + 1e-3 });
            if (!fin(fl) || !fin(fr)) continue;
            return { ok: false, good, detail: `the antiderivative is not differentiable near ${xn} = ${+x0.toPrecision(6)}` };
          }
          return { ok: false, good, detail: `F'(${+x0.toPrecision(6)}) = ${+lastD.toPrecision(8)} but f = ${+fx.toPrecision(8)}` };
        }
        good++;
      }
    }
  }
  if (good < 6) return { ok: null, good, detail: `too few points where the integrand is defined (${good} of ${tried})` };
  return { ok: true, good, detail: `F' matches f at ${good} points` };
}

// Does the tree use any function unknown to the verifier in verify.js?
export function usesSpecial(u) {
  if (u.k === "fn" && SPECIAL.has(u.name) && u.name !== "erf") return true;
  return u.args.some(usesSpecial);
}

// The integration variable is x; everything else free in u is a parameter.
export function params(u, x) { return [...X.freeSymbols(u)].filter((n) => n !== x.name); }

export function isRationalNum(u) { return u.k === "num"; }
export const Q = N.Q;

// Rational normal form: returns [numerator, denominator] (expanded trees) for u, treating any
// non-rational subterm (functions, fractional powers) as an atom. Nested fractions are cleared.
export function togetherND(u) {
  const rec = (w) => {
    if (w.k === "add") {
      let n = X.ZERO, d = X.ONE;
      for (const a of w.args) {
        const [n2, d2] = rec(a);
        if (d2 === d) n = X.add(n, n2);
        else { n = X.add(X.mul(n, d2), X.mul(n2, d)); d = X.mul(d, d2); }
      }
      return [n, d];
    }
    if (w.k === "mul") {
      let n = X.ONE, d = X.ONE;
      for (const a of w.args) { const [n2, d2] = rec(a); n = X.mul(n, n2); d = X.mul(d, d2); }
      return [n, d];
    }
    if (w.k === "pow" && X.isInt(w.args[1])) {
      const k = w.args[1].v.n;
      const [n, d] = rec(w.args[0]);
      if (k >= 0n) return [X.pow(n, w.args[1]), X.pow(d, w.args[1])];
      const e = X.num(N.Q(-k));
      return [X.pow(d, e), X.pow(n, e)];
    }
    if (w.k === "num" && w.v.d !== 1n) return [X.num(N.Q(w.v.n)), X.num(N.Q(w.v.d))];
    return [w, X.ONE];
  };
  const [n, d] = rec(u);
  return [expandC(n), expandC(d)];
}
