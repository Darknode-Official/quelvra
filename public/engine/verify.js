// Quelvra verifier: independent checks that never reuse the solving method.
//
// The verifier has its own evaluator (double precision, complex aware) so that a bug in the
// symbolic simplifier cannot silently confirm its own wrong answer. Exact checks go through
// the canonicalizer; numeric checks go through evalC below. A result is reported as:
//   "verified-exact"    : substitution simplifies to a true statement exactly
//   "verified-numeric"  : exact check inconclusive, numeric residual below tolerance at every probe
//   "failed"            : a probe shows the claim is false (with the counterexample)
//   "inconclusive"      : could not be evaluated either way
//   "rejected-domain"   : the candidate makes the ORIGINAL problem undefined (extraneous)

import * as X from "./expr.js";
import * as N from "./num.js";
import { simplify, makeCtx } from "./simplify.js";
import { toText } from "./print.js";
import { SPECIAL_REAL } from "./specfun.js";
import { DISCRETE_FLOAT } from "./verify-discrete.js";

// ---------- complex double evaluator ----------
const C = (re, im = 0) => ({ re, im });
const cadd = (a, b) => C(a.re + b.re, a.im + b.im);
const cmul = (a, b) => C(a.re * b.re - a.im * b.im, a.re * b.im + a.im * b.re);
const cdiv = (a, b) => {
  const d = b.re * b.re + b.im * b.im;
  if (d === 0) return C(NaN, NaN);
  return C((a.re * b.re + a.im * b.im) / d, (a.im * b.re - a.re * b.im) / d);
};
const cabs = (a) => Math.hypot(a.re, a.im);
const cexp = (a) => { const m = Math.exp(a.re); return C(m * Math.cos(a.im), m * Math.sin(a.im)); };
const clog = (a) => C(Math.log(cabs(a)), Math.atan2(a.im, a.re));
const isRealC = (a, tol = 1e-12) => Math.abs(a.im) <= tol * Math.max(1, Math.abs(a.re));
const bad = (a) => !Number.isFinite(a.re) || !Number.isFinite(a.im);
const NaNC = C(NaN, NaN);

function cpow(a, b, realMode) {
  if (b.im === 0 && Number.isInteger(b.re) && Math.abs(b.re) <= 64) {
    let n = Math.abs(b.re), r = C(1), p = a;
    while (n) { if (n & 1) r = cmul(r, p); p = cmul(p, p); n >>= 1; }
    return b.re < 0 ? cdiv(C(1), r) : r;
  }
  if (a.re === 0 && a.im === 0) return b.re > 0 ? C(0) : NaNC;
  if (realMode && a.im === 0 && b.im === 0) {
    if (a.re > 0) return C(Math.pow(a.re, b.re));
    // real odd roots of negatives: b = p/q with q odd
    const q = oddDenominator(b.re);
    if (q) { const v = Math.pow(-a.re, b.re); return C(Math.round(b.re * q) % 2 === 0 ? v : -v); }
    return NaNC; // even root of a negative is not real
  }
  return cexp(cmul(b, clog(a)));
}
function oddDenominator(x) {
  for (let q = 1; q <= 99; q += 2) { const p = x * q; if (Math.abs(p - Math.round(p)) < 1e-12) return q; }
  return 0;
}
const REAL_FN = {
  ...SPECIAL_REAL,
  sin: Math.sin, cos: Math.cos, tan: (x) => (Math.abs(Math.cos(x)) < 1e-15 ? NaN : Math.tan(x)),
  cot: (x) => 1 / Math.tan(x), sec: (x) => 1 / Math.cos(x), csc: (x) => 1 / Math.sin(x),
  asin: (x) => (Math.abs(x) > 1 + 1e-15 ? NaN : Math.asin(Math.max(-1, Math.min(1, x)))),
  acos: (x) => (Math.abs(x) > 1 + 1e-15 ? NaN : Math.acos(Math.max(-1, Math.min(1, x)))),
  atan: Math.atan, acot: (x) => (x === 0 ? Math.PI / 2 : Math.atan(1 / x)), asec: (x) => Math.acos(1 / x), acsc: (x) => Math.asin(1 / x),
  sinh: Math.sinh, cosh: Math.cosh, tanh: Math.tanh, coth: (x) => 1 / Math.tanh(x), sech: (x) => 1 / Math.cosh(x), csch: (x) => 1 / Math.sinh(x),
  asinh: Math.asinh, acosh: (x) => (x < 1 ? NaN : Math.acosh(x)), atanh: (x) => (Math.abs(x) >= 1 ? NaN : Math.atanh(x)),
  ln: (x) => (x <= 0 ? NaN : Math.log(x)), exp: Math.exp, abs: Math.abs, sign: Math.sign,
  floor: Math.floor, ceil: Math.ceil, round: (x) => (x < 0 ? -Math.round(-x) : Math.round(x)), erf: erf, gamma: gamma, factorial: (x) => gamma(x + 1),
  sqrt: (x) => (x < 0 ? NaN : Math.sqrt(x)), cbrt: Math.cbrt,
};
function erf(x) {
  // Abramowitz-Stegun 7.1.26 is too coarse for verification; use series / continued fraction.
  const ax = Math.abs(x);
  if (ax < 3) {
    let sum = x, term = x, n = 0;
    while (Math.abs(term) > 1e-17 * Math.abs(sum) && n < 200) { n++; term *= -x * x / n; sum += term / (2 * n + 1); }
    return (2 / Math.sqrt(Math.PI)) * sum;
  }
  // asymptotic complement
  let t = 1, s = 1;
  for (let n = 1; n < 30; n++) { t *= -(2 * n - 1) / (2 * x * x); if (Math.abs(t) < 1e-17) break; s += t; }
  const r = 1 - Math.exp(-x * x) / (ax * Math.sqrt(Math.PI)) * s;
  return x < 0 ? -r : r;
}
function gamma(x) {
  if (Number.isInteger(x) && x <= 0) return NaN;
  if (x < 0.5) return Math.PI / (Math.sin(Math.PI * x) * gamma(1 - x));
  const g = 7, c = [0.99999999999980993, 676.5203681218851, -1259.1392167224028, 771.32342877765313, -176.61502916214059,
    12.507343278686905, -0.13857109526572012, 9.9843695780195716e-6, 1.5056327351493116e-7];
  x -= 1;
  let a = c[0];
  const t = x + g + 0.5;
  for (let i = 1; i < 9; i++) a += c[i] / (x + i);
  return Math.sqrt(2 * Math.PI) * Math.pow(t, x + 0.5) * Math.exp(-t) * a;
}
const COMPLEX_FN = {
  exp: cexp, ln: (a) => (a.re === 0 && a.im === 0 ? NaNC : clog(a)),
  sin: (a) => C(Math.sin(a.re) * Math.cosh(a.im), Math.cos(a.re) * Math.sinh(a.im)),
  cos: (a) => C(Math.cos(a.re) * Math.cosh(a.im), -Math.sin(a.re) * Math.sinh(a.im)),
  sqrt: (a) => cpow(a, C(0.5), false), abs: (a) => C(cabs(a)), re: (a) => C(a.re), im: (a) => C(a.im), conj: (a) => C(a.re, -a.im),
  arg: (a) => C(Math.atan2(a.im, a.re)),
};
COMPLEX_FN.tan = (a) => cdiv(COMPLEX_FN.sin(a), COMPLEX_FN.cos(a));

// Evaluate a tree at env (Map or object name -> number | {re,im}). Returns {re, im}; NaN parts mean undefined.
// mode "real": real-domain semantics (even roots / logs of negatives are undefined).
export function evalC(u, env = {}, mode = "real") {
  const get = (n) => (env instanceof Map ? env.get(n) : env[n]);
  const realMode = mode === "real";
  const ev = (w) => {
    switch (w.k) {
      case "num": return C(Number(w.v.n) / Number(w.v.d));
      case "sym": { const v = get(w.name); if (v === undefined) return NaNC; return typeof v === "number" ? C(v) : v; }
      case "const":
        if (w.name === "pi") return C(Math.PI);
        if (w.name === "e") return C(Math.E);
        if (w.name === "I") return C(0, 1);
        if (w.name === "oo") return C(Infinity);
        return NaNC;
      case "add": return w.args.reduce((s, a) => cadd(s, ev(a)), C(0));
      case "mul": return w.args.reduce((s, a) => cmul(s, ev(a)), C(1));
      case "pow": {
        const b = ev(w.args[0]), e = ev(w.args[1]);
        if (bad(b) || bad(e)) return NaNC;
        if (realMode && X.isNum(w.args[1]) && b.im === 0) {
          const r = w.args[1].v;
          if (b.re < 0 && r.d !== 1n) {
            if (r.d % 2n === 0n) return NaNC;
            const v = Math.pow(-b.re, Number(r.n) / Number(r.d));
            return C(r.n % 2n === 0n ? v : -v);
          }
          if (b.re === 0 && r.n < 0n) return NaNC;
        }
        return cpow(b, e, realMode && b.im === 0 && e.im === 0);
      }
      case "fn": {
        const args = w.args.map(ev);
        // normalcdf(-oo, b): an infinite bound is allowed (the only function here that takes one)
        // (-1) * oo in complex arithmetic leaves a NaN imaginary part: an infinite real bound is still real
        const realArg = (a) => (a.im === 0 || (!Number.isFinite(a.re) && !Number.isNaN(a.re) && Number.isNaN(a.im))) && !Number.isNaN(a.re);
        if (w.name === "normalcdf" && args.every(realArg)) {
          const v = DISCRETE_FLOAT.normalcdf(args.map((a) => a.re));
          return Number.isFinite(v) ? C(v) : NaNC;
        }
        if (args.some(bad)) return NaNC;
        const n = w.name;
        if (n === "log") {
          if (args.length === 1) return cdiv(ev(X.fn("ln", w.args[0])), C(Math.LN10));
          return cdiv(ev(X.fn("ln", w.args[1])), ev(X.fn("ln", w.args[0])));
        }
        if (args.length === 1 && args[0].im === 0 && REAL_FN[n]) {
          const v = REAL_FN[n](args[0].re);
          if (Number.isNaN(v) && !realMode && COMPLEX_FN[n]) return COMPLEX_FN[n](args[0]);
          return C(v);
        }
        if (args.length === 1 && !realMode && COMPLEX_FN[n]) return COMPLEX_FN[n](args[0]);
        if (args.every((a) => a.im === 0)) {
          const xs = args.map((a) => a.re);
          if (n === "max") return C(Math.max(...xs));
          if (n === "min") return C(Math.min(...xs));
          if (n === "mod" && xs.length === 2) return xs[1] === 0 ? NaNC : C(xs[0] - xs[1] * Math.floor(xs[0] / xs[1]));
          if (n === "binomial" || n === "nCr") return C(gamma(xs[0] + 1) / (gamma(xs[1] + 1) * gamma(xs[0] - xs[1] + 1)));
          if (n === "nPr") return C(gamma(xs[0] + 1) / gamma(xs[0] - xs[1] + 1));
          if (n === "root" && xs.length === 2) return ev(X.pow(w.args[0], X.recip(w.args[1])));
          if (DISCRETE_FLOAT[n]) { const v = DISCRETE_FLOAT[n](xs); return Number.isFinite(v) ? C(v) : NaNC; }
        }
        return NaNC;
      }
      case "piecewise": {
        for (let i = 0; i < w.args.length; i += 2) {
          const val = w.args[i], cond = w.args[i + 1];
          if (!cond || cond === X.TRUE) return ev(val);
          const t = truth(cond, env, mode);
          if (t === true) return ev(val);
          if (t === null) return NaNC;
        }
        return NaNC;
      }
      default: return NaNC;
    }
  };
  try { return ev(u); } catch (_) { return NaNC; }
}
export const evalReal = (u, env) => { const v = evalC(u, env, "real"); return !bad(v) && isRealC(v, 1e-9) ? v.re : NaN; };

// Truth of a relation at a point: true / false / null (undefined or too close to call).
export function truth(r, env, mode = "real", tol = 1e-9) {
  if (r.k === "bool") return r.v;
  if (r.k === "and") { let res = true; for (const a of r.args) { const t = truth(a, env, mode, tol); if (t === false) return false; if (t === null) res = null; } return res; }
  if (r.k === "or") { let res = false; for (const a of r.args) { const t = truth(a, env, mode, tol); if (t === true) return true; if (t === null) res = null; } return res; }
  if (r.k === "not") { const t = truth(r.args[0], env, mode, tol); return t === null ? null : !t; }
  if (r.k !== "eq" && r.k !== "rel") return null;
  const a = evalC(r.args[0], env, mode), b = evalC(r.args[1], env, mode);
  if (bad(a) || bad(b)) return null;
  const scale = Math.max(1, cabs(a), cabs(b));
  const d = C(a.re - b.re, a.im - b.im);
  const op = r.k === "eq" ? "=" : r.op;
  if (op === "=") return cabs(d) <= tol * scale;
  if (op === "!=") return cabs(d) > tol * scale;
  if (!isRealC(a) || !isRealC(b)) return null;
  const x = d.re, z = Math.abs(x) <= tol * scale;
  switch (op) {
    case "<": return z ? false : x < 0;
    case "<=": return z ? true : x < 0;
    case ">": return z ? false : x > 0;
    case ">=": return z ? true : x > 0;
  }
  return null;
}

// ---------- exact check ----------
function exactTrue(rel, ctx) {
  try {
    const s = simplify(rel, ctx || makeCtx({ budget: 20000 }));
    if (s === X.TRUE) return true;
    if (s === X.FALSE) return false;
    if (rel.k === "eq") {
      const d = simplify(X.sub(rel.args[0], rel.args[1]), ctx || makeCtx({ budget: 20000 }));
      if (d === X.ZERO) return true;
      if (X.isNum(d)) return false;
    }
  } catch (_) { /* budget exceeded: fall through to numeric */ }
  return null;
}

// Does every subexpression of the ORIGINAL problem stay defined at env? (catches extraneous roots,
// division by zero, logs of non-positive numbers, even roots of negatives in the real domain)
export function definedAt(u, env, mode = "real") {
  let ok = true;
  const walk = (w) => {
    if (!ok) return;
    if (w.k === "eq" || w.k === "rel" || w.k === "and" || w.k === "or" || w.k === "system" || w.k === "not") { w.args.forEach(walk); return; }
    const v = evalC(w, env, mode);
    if (bad(v) || (mode === "real" && !isRealC(v, 1e-9))) { ok = false; return; }
    if (w.args && w.k !== "num") w.args.forEach(walk);
  };
  walk(u);
  return ok;
}

// ---------- public checks ----------

// Verify that `values` (Map name -> tree) satisfies the ORIGINAL problem (equation, inequality or system).
export function verifySolution(original, values, { domain = "real" } = {}) {
  const checks = [];
  const env = new Map(), envC = {};
  for (const [k, v] of values) {
    env.set(k, v);
    const c = evalC(v, {}, "complex");
    envC[k] = c;
  }
  // domain check first (extraneous candidates)
  const numEnv = {};
  for (const [k, c] of Object.entries(envC)) numEnv[k] = c;
  if (domain === "real" && Object.values(envC).some((c) => !isRealC(c, 1e-9))) {
    return { status: "rejected-domain", checks: [{ kind: "domain", ok: false, detail: "the value is not a real number" }] };
  }
  if (!definedAt(original, numEnv, domain === "real" ? "real" : "complex")) {
    return { status: "rejected-domain", checks: [{ kind: "domain", ok: false, detail: "the original problem is undefined at this value" }] };
  }
  checks.push({ kind: "domain", ok: true, detail: "every part of the original problem is defined here" });
  const rels = original.k === "system" ? original.args : [original];
  let allExact = true;
  for (const rel of rels) {
    const substituted = X.subs(rel, env);
    const ex = exactTrue(substituted);
    if (ex === true) { checks.push({ kind: "substitution-exact", ok: true, detail: `${toText(substituted)} simplifies to true`, on: rel }); continue; }
    allExact = false;
    const t = truth(rel, numEnv, domain === "real" ? "real" : "complex", 1e-9);
    if (t === true) checks.push({ kind: "substitution-numeric", ok: true, detail: `residual below 1e-9 at ${fmtEnv(numEnv)}`, on: rel });
    else if (t === false) {
      if (ex === false) return { status: "failed", checks: [...checks, { kind: "substitution-exact", ok: false, detail: `${toText(substituted)} is false`, on: rel }] };
      return { status: "failed", checks: [...checks, { kind: "substitution-numeric", ok: false, detail: `the relation is false at ${fmtEnv(numEnv)}`, on: rel }] };
    } else return { status: "inconclusive", checks: [...checks, { kind: "substitution-numeric", ok: null, detail: "could not evaluate", on: rel }] };
  }
  return { status: allExact ? "verified-exact" : "verified-numeric", checks };
}
function fmtEnv(env) {
  return Object.entries(env).map(([k, c]) => `${k} = ${fmtC(c)}`).join(", ");
}
export function fmtC(c) {
  const r = (x) => +x.toPrecision(12);
  if (isRealC(c)) return String(r(c.re));
  return `${r(c.re)} ${c.im < 0 ? "-" : "+"} ${r(Math.abs(c.im))}i`;
}

// Random probe points avoiding special values.
function probes(vars, count, seed = 12345, range = [-3, 3]) {
  let s = seed >>> 0;
  const rnd = () => { s = (s + 0x6d2b79f5) >>> 0; let t = s; t = Math.imul(t ^ (t >>> 15), t | 1); t ^= t + Math.imul(t ^ (t >>> 7), t | 61); return ((t ^ (t >>> 14)) >>> 0) / 4294967296; };
  const pts = [];
  for (let i = 0; i < count; i++) {
    const p = {};
    for (const v of vars) p[v] = range[0] + (range[1] - range[0]) * rnd() + 1e-3 * (i + 1);
    pts.push(p);
  }
  return pts;
}

// Are a and b equal as functions (on the common real domain)? Exact first, then random probes.
// Returns { status: "equivalent-exact" | "equivalent-numeric" | "different" | "inconclusive", counterexample? }
export function equivalent(a, b, { vars, points = 24, domain = "real", ctx } = {}) {
  try {
    const d = simplify(X.sub(a, b), ctx || makeCtx({ budget: 20000 }));
    if (d === X.ZERO) return { status: "equivalent-exact" };
  } catch (_) { /* fall through */ }
  const vs = vars || [...new Set([...X.freeSymbols(a), ...X.freeSymbols(b)])];
  let tested = 0;
  const mode = domain === "real" ? "real" : "complex";
  for (const range of [[-3, 3], [0.1, 4], [-10, 10]]) {
    for (const p of probes(vs, points, 777 + tested, range)) {
      const va = evalC(a, p, mode), vb = evalC(b, p, mode);
      const aBad = bad(va), bBad = bad(vb);
      if (aBad && bBad) continue;
      if (aBad !== bBad) continue; // differing domains are reported separately by callers
      const scale = Math.max(1, cabs(va), cabs(vb));
      if (cabs(C(va.re - vb.re, va.im - vb.im)) > 1e-7 * scale) return { status: "different", counterexample: p, values: [va, vb] };
      tested++;
    }
    if (tested >= points) break;
  }
  if (tested < 4) return { status: "inconclusive", tested };
  return { status: "equivalent-numeric", tested };
}

// d/dx F == f ? checked with the verifier's own central differences (independent of the integrator).
export function verifyAntiderivative(F, f, x, { diffFn } = {}) {
  const xn = typeof x === "string" ? x : x.name;
  if (diffFn) {
    try {
      const dF = diffFn(F, X.sym(xn));
      const r = equivalent(dF, f, { vars: [...new Set([xn, ...X.freeSymbols(F), ...X.freeSymbols(f)])] });
      if (r.status === "equivalent-exact") return { status: "verified-exact", checks: [{ kind: "differentiate-back", ok: true, detail: "d/dx of the result simplifies to the integrand" }] };
      if (r.status === "different") return { status: "failed", checks: [{ kind: "differentiate-back", ok: false, detail: "d/dx of the result differs from the integrand", counterexample: r.counterexample }] };
    } catch (_) { /* numeric below */ }
  }
  const others = [...new Set([...X.freeSymbols(F), ...X.freeSymbols(f)])].filter((v) => v !== xn);
  let good = 0;
  for (const p of probes([xn, ...others], 30, 99, [-2.5, 2.5])) {
    const h = 1e-4 * Math.max(1, Math.abs(p[xn]));
    const fp = evalReal(F, { ...p, [xn]: p[xn] + h }), fm = evalReal(F, { ...p, [xn]: p[xn] - h });
    const fx = evalReal(f, p);
    if (![fp, fm, fx].every(Number.isFinite)) continue;
    // Richardson-extrapolated central difference
    const fp2 = evalReal(F, { ...p, [xn]: p[xn] + h / 2 }), fm2 = evalReal(F, { ...p, [xn]: p[xn] - h / 2 });
    if (![fp2, fm2].every(Number.isFinite)) continue;
    const d1 = (fp - fm) / (2 * h), d2 = (fp2 - fm2) / h;
    const d = (4 * d2 - d1) / 3;
    if (Math.abs(d - fx) > 1e-5 * Math.max(1, Math.abs(fx))) return { status: "failed", checks: [{ kind: "numeric-derivative", ok: false, detail: `F'(${+p[xn].toPrecision(6)}) = ${+d.toPrecision(8)} but f = ${+fx.toPrecision(8)}` }] };
    good++;
  }
  if (good < 5) return { status: "inconclusive", checks: [{ kind: "numeric-derivative", ok: null, detail: "too few points where both are defined" }] };
  return { status: "verified-numeric", checks: [{ kind: "numeric-derivative", ok: true, detail: `F' matches f at ${good} random points` }] };
}

// Derivative check: compare a claimed derivative with central differences of the original.
export function verifyDerivative(u, du, x) {
  const xn = typeof x === "string" ? x : x.name;
  return verifyAntiderivative(u, du, xn);
}

// Inequality solution check: for a claimed solution set in one variable, probe points inside and
// outside the set and compare against the ORIGINAL inequality.
// setTest(xValue) -> boolean says whether the claimed answer contains x.
export function verifySolutionSet(original, x, setTest, { boundaries = [], span = 20 } = {}) {
  const xn = typeof x === "string" ? x : x.name;
  const pts = new Set();
  const bs = boundaries.filter(Number.isFinite).sort((a, b) => a - b);
  for (const b of bs) for (const e of [-1e-4, 1e-4, -0.37, 0.41]) pts.add(b + e);
  for (let i = 0; i < bs.length - 1; i++) pts.add((bs[i] + bs[i + 1]) / 2);
  for (let i = 0; i <= 80; i++) pts.add(-span + (2 * span * i) / 80 + 0.0137);
  let checked = 0;
  for (const p of pts) {
    const t = truth(original, { [xn]: p }, "real", 1e-12);
    if (t === null) { if (setTest(p)) return { status: "failed", checks: [{ kind: "probe", ok: false, detail: `the answer contains ${xn} = ${+p.toPrecision(6)} where the original is undefined` }] }; continue; }
    if (t !== setTest(p)) return { status: "failed", checks: [{ kind: "probe", ok: false, detail: `at ${xn} = ${+p.toPrecision(6)} the original is ${t} but the answer says ${!t}` }] };
    checked++;
  }
  return { status: "verified-numeric", checks: [{ kind: "probe", ok: true, detail: `answer agrees with the original inequality at ${checked} test points, including both sides of every boundary` }] };
}

export { isRealC, bad as isBadC };
