// Quelvra differential / property fuzzing: generators, printers and oracle-free checks.
//
// Used by tools/fuzz.mjs (large runs, optional sympy/mpmath oracle through python3) and by
// test/fuzz.test.js (fixed seed, small, oracle-free). Nothing here is shipped: the engine
// under public/quelvra/engine never imports it.
//
// A generated case is { cat, input, group, variant, truth? , task? }:
//   input   the text given to Quelvra
//   group   metamorphic group id: every case of one group is the same problem written differently,
//           so their verified answer sets must agree
//   truth   answer known by construction (oracle-free checks), e.g. { roots: [numbers], exact: true }
//   task    the problem in the oracle's syntax (python sympy), filled by the generator

import { solve } from "../public/engine/quelvra.js";
import { parse } from "../public/engine/parse.js";
import { toText } from "../public/engine/print.js";

// ---------------------------------------------------------------- random
export function rng(seed = 1) {
  let a = seed >>> 0;
  const next = () => {
    a = (a + 0x6d2b79f5) >>> 0;
    let t = a;
    t = Math.imul(t ^ (t >>> 15), t | 1);
    t ^= t + Math.imul(t ^ (t >>> 7), t | 61);
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
  };
  const int = (lo, hi) => lo + Math.floor(next() * (hi - lo + 1));
  return {
    next, int,
    pick: (arr) => arr[Math.floor(next() * arr.length)],
    chance: (p) => next() < p,
    nz: (lo, hi) => { let v = 0; while (v === 0) v = int(lo, hi); return v; },
    shuffle: (arr) => { const b = arr.slice(); for (let i = b.length - 1; i > 0; i--) { const j = Math.floor(next() * (i + 1)); [b[i], b[j]] = [b[j], b[i]]; } return b; },
  };
}

// ---------------------------------------------------------------- tiny AST (generator side)
const bg = (a, b) => { while (b) [a, b] = [b, a % b]; return a || 1n; };
const gcd = (a, b) => { a = Math.abs(a); b = Math.abs(b); while (b) [a, b] = [b, a % b]; return a || 1; };
export const N = (n, d = 1) => { if (d < 0) { n = -n; d = -d; } const g = gcd(n, d); return { t: "num", n: n / g, d: d / g }; };
export const V = (name) => ({ t: "sym", name });
export const K = (name) => ({ t: "const", name });
export const Add = (...a) => (a.length === 1 ? a[0] : { t: "add", a });
export const Mul = (...a) => (a.length === 1 ? a[0] : { t: "mul", a });
export const Neg = (a) => ({ t: "neg", a: [a] });
export const Div = (a, b) => ({ t: "div", a: [a, b] });
export const Pow = (a, b) => ({ t: "pow", a: [a, typeof b === "number" ? N(b) : b] });
export const F = (name, ...a) => ({ t: "fn", name, a });
export const Sub = (a, b) => Add(a, Neg(b));

const PREC = { add: 1, neg: 2, mul: 2, div: 2, pow: 4, fn: 5, sym: 6, const: 6, num: 6 };
const numPrec = (u) => (u.d !== 1 ? 2 : u.n < 0 ? 2 : 6);
const prec = (u) => (u.t === "num" ? numPrec(u) : PREC[u.t]);

// Quelvra-syntax printer. style: { implicit, fnpow, spaces, bareFn, negExp }
export function toQ(u, style = {}) {
  const sp = style.spaces === false ? "" : " ";
  const wrap = (v, p) => (prec(v) < p ? `(${toQ(v, style)})` : toQ(v, style));
  switch (u.t) {
    case "num": return u.d === 1 ? String(u.n) : `${u.n}/${u.d}`;
    case "sym": return u.name;
    case "const": return u.name;
    case "add": {
      let s = "";
      u.a.forEach((v, i) => {
        if (i === 0) { s += v.t === "neg" ? `-${wrap(v.a[0], 3)}` : wrap(v, 1); return; }
        if (v.t === "neg") s += `${sp}-${sp}${wrap(v.a[0], 3)}`;
        else if (v.t === "num" && v.n < 0) s += `${sp}-${sp}${toQ(N(-v.n, v.d), style)}`;
        else { const piece = wrap(v, 1); s += piece.startsWith("-") ? `${sp}-${sp}${piece.slice(1)}` : `${sp}+${sp}${piece}`; }
      });
      return s;
    }
    case "neg": return `-${wrap(u.a[0], 3)}`;
    case "mul": {
      let s = "";
      u.a.forEach((v, i) => {
        let piece = wrap(v, 3);
        if (i === 0) {
          // a leading negative number keeps its sign: -3x
          if (v.t === "num" && v.d === 1) piece = String(v.n);
          else if (v.t === "num") piece = `(${toQ(v, style)})`;
          s = piece; return;
        }
        if (v.t === "num") piece = `(${toQ(v, style)})`;
        const prevNum = i === 1 && u.a[0].t === "num" && u.a[0].d === 1;
        const safeImplicit = style.implicit && ((prevNum && (v.t === "sym" || v.t === "fn" || piece.startsWith("(") || v.t === "pow" && v.a[0].t === "sym")) || (piece.startsWith("(") && s.endsWith(")")));
        s += safeImplicit ? piece : `${style.spaces === false ? "" : ""}*${piece}`;
      });
      return s;
    }
    case "div": return `${wrap(u.a[0], 2)}/${wrap(u.a[1], 4)}`;
    case "pow": {
      const [b, e] = u.a;
      // sin^2(x) function power notation
      if (style.fnpow && b.t === "fn" && b.a.length === 1 && e.t === "num" && e.d === 1 && e.n >= 2 && e.n <= 4 && ["sin", "cos", "tan"].includes(b.name)) return `${b.name}^${e.n}(${toQ(b.a[0], style)})`;
      let es = e.t === "num" && e.d === 1 && e.n >= 0 ? String(e.n) : e.t === "sym" || e.t === "const" ? e.name : `(${toQ(e, style)})`;
      if (style.negExp && e.t === "num" && e.d === 1 && e.n < 0) es = String(e.n);
      const bs = b.t === "num" && (b.n < 0 || b.d !== 1) ? `(${toQ(b, style)})` : b.t === "fn" ? `(${toQ(b, style)})` : wrap(b, 5);
      return `${bs}^${es}`;
    }
    case "fn": {
      if (u.name === "abs") return `|${toQ(u.a[0], style)}|`;
      if (u.name === "log" && u.a.length === 2) return `log(${toQ(u.a[0], style)}, ${toQ(u.a[1], style)})`;
      return `${u.name}(${u.a.map((v) => toQ(v, style)).join(", ")})`;
    }
  }
  throw new Error("toQ: " + u.t);
}

// sympy-syntax printer (real semantics are applied by the oracle's own evaluator)
export function toPy(u) {
  const w = (v) => `(${toPy(v)})`;
  switch (u.t) {
    case "num": return u.d === 1 ? `Integer(${u.n})` : `Rational(${u.n},${u.d})`;
    case "sym": return `_s_${u.name}`;
    case "const": return u.name === "pi" ? "pi" : u.name === "e" ? "E" : u.name === "oo" ? "oo" : (() => { throw new Error("const " + u.name); })();
    case "add": return u.a.map(w).join(" + ");
    case "neg": return `-${w(u.a[0])}`;
    case "mul": return u.a.map(w).join("*");
    case "div": return `${w(u.a[0])}/${w(u.a[1])}`;
    case "pow": return `${w(u.a[0])}**${w(u.a[1])}`;
    case "fn": {
      const m = { ln: "log", abs: "Abs", ceil: "ceiling", sqrt: "sqrt", cbrt: "_cbrt" }[u.name] || u.name;
      if (u.name === "log") return u.a.length === 2 ? `log(${toPy(u.a[1])}, ${toPy(u.a[0])})` : `log(${toPy(u.a[0])}, 10)`;
      return `${m}(${u.a.map(toPy).join(", ")})`;
    }
  }
  throw new Error("toPy: " + u.t);
}

// independent double evaluation of the generator AST (real semantics like Quelvra's real domain)
export function evalG(u, env) {
  switch (u.t) {
    case "num": return u.n / u.d;
    case "sym": return env[u.name];
    case "const": return u.name === "pi" ? Math.PI : u.name === "e" ? Math.E : NaN;
    case "add": return u.a.reduce((s, v) => s + evalG(v, env), 0);
    case "neg": return -evalG(u.a[0], env);
    case "mul": return u.a.reduce((s, v) => s * evalG(v, env), 1);
    case "div": { const d = evalG(u.a[1], env); return d === 0 ? NaN : evalG(u.a[0], env) / d; }
    case "pow": return realPow(evalG(u.a[0], env), u.a[1].t === "num" ? [u.a[1].n, u.a[1].d] : evalG(u.a[1], env));
    case "fn": return realFn(u.name, u.a.map((v) => evalG(v, env)));
  }
  return NaN;
}
function realPow(b, e) {
  if (Array.isArray(e)) {
    const [p, q] = e;
    if (b === 0 && p < 0) return NaN;
    if (b < 0 && q !== 1) {
      if (q % 2 === 0) return NaN;
      const v = Math.pow(-b, p / q);
      return p % 2 === 0 ? v : -v;
    }
    return Math.pow(b, p / q);
  }
  if (b < 0 && !Number.isInteger(e)) return NaN;
  if (b === 0 && e < 0) return NaN;
  return Math.pow(b, e);
}
function realFn(n, xs) {
  const x = xs[0];
  switch (n) {
    case "sin": return Math.sin(x); case "cos": return Math.cos(x);
    case "tan": return Math.abs(Math.cos(x)) < 1e-15 ? NaN : Math.tan(x);
    case "sec": return 1 / Math.cos(x); case "csc": return 1 / Math.sin(x); case "cot": return 1 / Math.tan(x);
    case "asin": return Math.abs(x) > 1 ? NaN : Math.asin(x); case "acos": return Math.abs(x) > 1 ? NaN : Math.acos(x);
    case "atan": return Math.atan(x);
    case "sinh": return Math.sinh(x); case "cosh": return Math.cosh(x); case "tanh": return Math.tanh(x);
    case "exp": return Math.exp(x); case "ln": return x > 0 ? Math.log(x) : NaN;
    case "log": return xs.length === 2 ? (xs[0] > 0 && xs[0] !== 1 && xs[1] > 0 ? Math.log(xs[1]) / Math.log(xs[0]) : NaN) : x > 0 ? Math.log10(x) : NaN;
    case "sqrt": return x >= 0 ? Math.sqrt(x) : NaN; case "cbrt": return Math.cbrt(x);
    case "abs": return Math.abs(x); case "sign": return Math.sign(x);
    case "floor": return Math.floor(x); case "ceil": return Math.ceil(x);
    case "atanh": return Math.abs(x) < 1 ? Math.atanh(x) : NaN;
    case "asinh": return Math.asinh(x); case "acosh": return x >= 1 ? Math.acosh(x) : NaN;
  }
  return NaN;
}

// ---------------------------------------------------------------- engine trees (X nodes)
// Independent evaluator of Quelvra's own trees (does NOT use engine/verify.js), real mode.
export function evalX(u, env = {}) {
  switch (u.k) {
    case "num": return Number(u.v.n) / Number(u.v.d);
    case "sym": { const v = env[u.name]; return v === undefined ? NaN : v; }
    case "const": return u.name === "pi" ? Math.PI : u.name === "e" ? Math.E : u.name === "oo" ? Infinity : NaN;
    case "add": return u.args.reduce((s, v) => s + evalX(v, env), 0);
    case "mul": { let s = 1; for (const v of u.args) { const x = evalX(v, env); s *= x; } return s; }
    case "pow": {
      const b = evalX(u.args[0], env);
      const r = ratX(u.args[1]);
      if (r) return realPow(b, r);
      if (u.args[0].k === "const" && u.args[0].name === "e") return Math.exp(evalX(u.args[1], env));
      return realPow(b, evalX(u.args[1], env));
    }
    case "fn": return realFn(u.name, u.args.map((v) => evalX(v, env)));
  }
  return NaN;
}

// exact small rational value [p, q] of a constant tree built from numbers with + * and integer powers
function ratX(u, depth = 0) {
  if (depth > 10) return null;
  if (u.k === "num") return [Number(u.v.n), Number(u.v.d)];
  const norm = ([p, q]) => { const g = gcd(p, q); return q < 0 ? [-p / g, -q / g] : [p / g, q / g]; };
  if (u.k === "add" || u.k === "mul") {
    let acc = u.k === "add" ? [0, 1] : [1, 1];
    for (const a of u.args) { const r = ratX(a, depth + 1); if (!r) return null; acc = norm(u.k === "add" ? [acc[0] * r[1] + r[0] * acc[1], acc[1] * r[1]] : [acc[0] * r[0], acc[1] * r[1]]); }
    return Number.isSafeInteger(acc[0]) && Number.isSafeInteger(acc[1]) ? acc : null;
  }
  if (u.k === "pow" && u.args[1].k === "num" && u.args[1].v.d === 1n && Math.abs(Number(u.args[1].v.n)) <= 6) {
    const b = ratX(u.args[0], depth + 1), n = Number(u.args[1].v.n);
    if (!b || (b[0] === 0 && n < 0)) return null;
    const r = norm(n >= 0 ? [b[0] ** n, b[1] ** n] : [b[1] ** -n, b[0] ** -n]);
    return Number.isSafeInteger(r[0]) && Number.isSafeInteger(r[1]) ? r : null;
  }
  return null;
}

// Quelvra tree -> sympy syntax (throws on anything the oracle cannot represent)
const PYFN = { ln: "log", abs: "Abs", ceil: "ceiling", sign: "sign", floor: "floor", exp: "exp", sqrt: "sqrt", cbrt: "_cbrt",
  sin: "sin", cos: "cos", tan: "tan", cot: "cot", sec: "sec", csc: "csc", asin: "asin", acos: "acos", atan: "atan", acot: "_acot", asec: "_asec", acsc: "_acsc",
  sinh: "sinh", cosh: "cosh", tanh: "tanh", coth: "coth", sech: "sech", csch: "csch", asinh: "asinh", acosh: "acosh", atanh: "atanh",
  erf: "erf", erfi: "erfi", erfc: "erfc", gamma: "gamma", factorial: "factorial", Si: "Si", Ci: "Ci", Ei: "Ei", li: "li", Shi: "Shi", Chi: "Chi",
  binomial: "binomial", zeta: "zeta", lambertw: "LambertW", LambertW: "LambertW", FresnelS: "fresnels", FresnelC: "fresnelc", re: "re", im: "im", arg: "arg", conj: "conjugate", max: "Max", min: "Min" };
export function xToPy(u) {
  const w = (v) => `(${xToPy(v)})`;
  switch (u.k) {
    case "num": return u.v.d === 1n ? `Integer(${u.v.n})` : `Rational(${u.v.n},${u.v.d})`;
    case "sym": if (!/^[A-Za-z][A-Za-z0-9_]*$/.test(u.name)) throw new Error("symbol " + u.name); return `_s_${u.name}`;
    case "const": {
      const m = { pi: "pi", e: "E", I: "I", oo: "oo", undef: "nan" }[u.name];
      if (!m) throw new Error("const " + u.name);
      return m;
    }
    case "add": return u.args.map(w).join(" + ");
    case "mul": return u.args.map(w).join("*");
    case "pow": return `${w(u.args[0])}**${w(u.args[1])}`;
    case "fn": {
      if (u.name === "log") return u.args.length === 2 ? `log(${xToPy(u.args[1])}, ${xToPy(u.args[0])})` : `log(${xToPy(u.args[0])}, 10)`;
      if (u.name === "root" && u.args.length === 2) return `(${xToPy(u.args[0])})**(1/(${xToPy(u.args[1])}))`;
      const m = PYFN[u.name];
      if (!m) throw new Error("fn " + u.name);
      return `${m}(${u.args.map(xToPy).join(", ")})`;
    }
    case "bool": return u.v ? "true" : "false";
    case "eq": return `Eq(${xToPy(u.args[0])}, ${xToPy(u.args[1])})`;
    case "rel": return `${{ "<": "Lt", "<=": "Le", ">": "Gt", ">=": "Ge", "!=": "Ne" }[u.op]}(${xToPy(u.args[0])}, ${xToPy(u.args[1])})`;
    case "and": return `And(${u.args.map(xToPy).join(", ")})`;
    case "or": return `Or(${u.args.map(xToPy).join(", ")})`;
    case "not": return `Not(${xToPy(u.args[0])})`;
    case "matrix": return `Matrix([${u.args.map((r) => `[${r.args.map(xToPy).join(", ")}]`).join(", ")}])`;
    case "tuple": case "vector": return `[${u.args.map(xToPy).join(", ")}]`;
    case "piecewise": {
      const pairs = [];
      for (let i = 0; i < u.args.length; i += 2) pairs.push(`(${xToPy(u.args[i])}, ${u.args[i + 1] ? xToPy(u.args[i + 1]) : "true"})`);
      return `Piecewise(${pairs.join(", ")})`;
    }
  }
  throw new Error("kind " + u.k);
}

// ---------------------------------------------------------------- running the engine
export const verified = (r) => !!(r && r.ok && r.verification && r.verification.status === "passed");

// Extract what Quelvra claims, in a JSON-able form the oracle understands.
export function claimOf(r) {
  const c = { verified: verified(r), status: r && r.solutionStatus, noSolution: !!(r && (r.noSolution || (r.extra && r.extra.noSolution))), answers: [], ms: r && r.ms, text: "" };
  if (!r) return c;
  const texts = [];
  for (const a of r.answers || []) {
    const o = { kind: a.kind, label: a.label || null };
    try {
      if (a.tree) { o.text = toText(a.tree); o.py = xToPy(a.tree); }
      if (a.values) { o.values = a.values.map(([k, v]) => [k, xToPy(v)]); o.text = a.values.map(([k, v]) => `${k} = ${toText(v)}`).join(", "); }
    } catch (e) { o.unconvertible = String(e.message); if (a.tree) o.text = toText(a.tree); }
    if (a.approx && a.approx.value != null) o.approx = String(a.approx.value);
    if (a.param) o.param = a.param;
    if (a.params) o.params = a.params;
    if (a.constant) o.constant = true;
    if (a.interval) o.interval = true;
    texts.push(o.text || o.approx || o.label || o.kind);
    c.answers.push(o);
  }
  c.text = texts.join("; ");
  if (r.error) c.error = r.error.message;
  return c;
}

export function runCase(input, timeLimit = 8000) {
  const t = performance.now();
  let r, crash = null;
  try { r = solve(input, { timeLimit }); } catch (e) { crash = String(e && e.stack || e); }
  const ms = performance.now() - t;
  const c = claimOf(r);
  c.ms = ms;
  if (crash) c.crash = crash.split("\n").slice(0, 4).join(" | ");
  c.tree = r;
  return c;
}

// ---------------------------------------------------------------- generators
const VARS = ["x", "t", "z", "u", "w"];
const smallQ = (R) => (R.chance(0.75) ? N(R.nz(-6, 6)) : N(R.nz(-9, 9), R.pick([2, 3, 4, 5])));

// polynomial helpers on number arrays (coefficients low -> high, rationals as [n, d] avoided: integers only)
const polyMul = (a, b) => { const r = new Array(a.length + b.length - 1).fill(0); a.forEach((x, i) => b.forEach((y, j) => { r[i + j] += x * y; })); return r; };
export function polyAst(coeffs, x) {
  // highest degree first, integer coefficients
  const terms = [];
  for (let i = coeffs.length - 1; i >= 0; i--) {
    const c = coeffs[i];
    if (!c) continue;
    const mono = i === 0 ? null : i === 1 ? V(x) : Pow(V(x), i);
    if (!mono) terms.push(N(c));
    else if (c === 1) terms.push(mono);
    else if (c === -1) terms.push(Neg(mono));
    else if (c < 0) terms.push(Neg(Mul(N(-c), mono)));
    else terms.push(Mul(N(c), mono));
  }
  return terms.length ? Add(...terms) : N(0);
}
const lin = (a, b, x) => polyAst([b, a], x); // a x + b

// Build a polynomial equation from factors with known real roots.
function genPolyEq(R, x) {
  const factors = []; // integer coefficient arrays (low->high)
  const roots = [];
  let deg = 0;
  const target = R.int(1, 6);
  while (deg < target) {
    const kind = R.next();
    if (kind < 0.45 || target - deg < 2) { // rational root q x - p
      const p = R.int(-7, 7), q = R.chance(0.7) ? 1 : R.pick([2, 3, 5]);
      factors.push([-p, q]); roots.push(p / q); deg += 1;
      if (R.chance(0.15) && deg < target) { factors.push([-p, q]); deg += 1; } // repeated root
    } else if (kind < 0.7) { // x^2 - m with m not a square (irrational pair) or negative (no real root)
      const m = R.pick([2, 3, 5, 6, 7, -1, -2, -4, 10, 12]);
      const s = R.int(-3, 3); // (x - s)^2 - m
      factors.push([s * s - m, -2 * s, 1]);
      if (m > 0) { roots.push(s + Math.sqrt(m), s - Math.sqrt(m)); }
      deg += 2;
    } else if (kind < 0.85) { // x^2 + b x + c random
      const b = R.int(-6, 6), c = R.int(-9, 9);
      factors.push([c, b, 1]);
      const D = b * b - 4 * c;
      if (D > 0) roots.push((-b + Math.sqrt(D)) / 2, (-b - Math.sqrt(D)) / 2);
      else if (D === 0) roots.push(-b / 2);
      deg += 2;
    } else { // x^3 - m (one real root)
      if (target - deg < 3) continue;
      const m = R.pick([2, 3, 4, 5, -2, 9]);
      factors.push([-m, 0, 0, 1]); roots.push(Math.cbrt(m)); deg += 3;
    }
  }
  let coeffs = [1];
  for (const f of factors) coeffs = polyMul(coeffs, f);
  const lead = R.chance(0.3) ? R.nz(-3, 3) : 1;
  coeffs = coeffs.map((c) => c * lead);
  const uniq = [...new Set(roots.map((r) => +r.toPrecision(12)))].sort((a, b) => a - b);
  const factored = Mul(...(lead !== 1 ? [N(lead)] : []), ...factors.map((f) => polyAst(f, x)));
  return { expanded: polyAst(coeffs, x), factored, coeffs, roots: uniq, factorCount: factors.length };
}

// random expression over x (for simplify / diff / integrals / parse)
export function genExpr(R, x, depth = 3, opts = {}) {
  const fns = opts.fns || ["sin", "cos", "exp", "ln", "sqrt", "tan", "atan", "abs"];
  const atom = () => {
    const k = R.next();
    if (k < 0.55) return V(x);
    if (k < 0.9) return N(R.nz(-5, 7));
    if (k < 0.95 && !opts.noConst) return K("pi");
    return N(R.nz(-5, 5), R.pick([2, 3]));
  };
  const go = (d) => {
    if (d <= 0 || R.chance(0.25)) return atom();
    const k = R.next();
    if (k < 0.25) return Add(go(d - 1), go(d - 1));
    if (k < 0.45) return Mul(R.chance(0.5) ? N(R.nz(-4, 5)) : go(d - 1), go(d - 1));
    if (k < 0.55) return Sub(go(d - 1), go(d - 1));
    if (k < 0.65 && !opts.noDiv) return Div(go(d - 1), go(d - 1));
    if (k < 0.78) return Pow(go(d - 1), R.pick(opts.intPow ? [2, 3] : [2, 3, 2, -1, N(1, 2)]));
    if (k < 0.97) return F(R.pick(fns), go(d - 1));
    return Neg(go(d - 1));
  };
  return go(depth);
}

// ---------------------------------------------------------------- category generators
// Each returns an array of cases (the variants of one problem). `id` is the group id.
const eqStyle = (R) => ({ implicit: R.chance(0.6), fnpow: R.chance(0.3), spaces: R.chance(0.8), negExp: R.chance(0.3) });

function eqCases(cat, id, R, lhs, rhs, x, extra = {}) {
  // lhs = rhs; variants: as is, swapped, moved to one side, scaled, renamed variable
  const variants = [];
  const st = eqStyle(R);
  variants.push(["orig", `${toQ(lhs, st)} = ${toQ(rhs, st)}`, lhs, rhs, x]);
  variants.push(["swap", `${toQ(rhs, st)} = ${toQ(lhs, st)}`, rhs, lhs, x]);
  const c = R.pick([N(2), N(-3), N(1, 2), N(5)]);
  if (extra.scale !== false) variants.push(["scale", `${toQ(Mul(c, lhs.t === "add" ? lhs : lhs), st)} = ${toQ(Mul(c, rhs), st)}`, Mul(c, lhs), Mul(c, rhs), x]);
  const y = R.pick(VARS.filter((v) => v !== x));
  const ren = (u) => (u.t === "sym" && u.name === x ? V(y) : u.a ? { ...u, a: u.a.map(ren) } : u);
  variants.push(["rename", `${toQ(ren(lhs), st)} = ${toQ(ren(rhs), st)}`, ren(lhs), ren(rhs), y]);
  if (extra.alt) for (const [name, l, r2] of extra.alt) variants.push([name, `${toQ(l, st)} = ${toQ(r2, st)}`, l, r2, x]);
  const pick = extra.all ? variants : [variants[0], ...R.shuffle(variants.slice(1)).slice(0, extra.nVariants || 2)];
  return pick.map(([variant, input, l, r2, v]) => ({
    cat, group: id, variant, input, x: v,
    task: { kind: "eq", lhs: toPy(l), rhs: toPy(r2), x: v, R: extra.range || 40 },
    truth: extra.truth ? { ...extra.truth, x: v } : null,
    gl: l, gr: r2,
  }));
}

export const GENERATORS = {
  // parse / print round trip: oracle-free, compares Quelvra's parse with the generator's own AST
  parse(R, id) {
    const x = R.pick(VARS);
    if (R.chance(0.35)) {
      // hand-written notations with one conventional reading
      const a = R.int(2, 5), b = R.int(1, 4);
      const X_ = V(x);
      const T = [
        [`sin ${x} + ${b}`, Add(F("sin", X_), N(b))],
        [`-${x}^2`, Neg(Pow(X_, 2))],
        [`${a}^-${x}`, Pow(N(a), Neg(X_))],
        [`sin^2 ${x}`, Pow(F("sin", X_), 2)],
        [`cos^2(${x}) + sin^2(${x})`, Add(Pow(F("cos", X_), 2), Pow(F("sin", X_), 2))],
        [`sin ${a}${x}`, F("sin", Mul(N(a), X_))],
        [`${x} e^${x}`, Mul(X_, F("exp", X_))],
        [`e^-${x}`, F("exp", Neg(X_))],
        [`e^${x}^2`, F("exp", Pow(X_, 2))],
        [`${a}^${x}^2`, Pow(N(a), Pow(X_, 2))],
        [`${a}pi ${x}`, Mul(N(a), K("pi"), X_)],
        [`${a}${x}^2`, Mul(N(a), Pow(X_, 2))],
        [`-${a}^2 + ${x}`, Add(Neg(Pow(N(a), 2)), X_)],
        [`sqrt ${x} + ${b}`, Add(F("sqrt", X_), N(b))],
        [`${a}|${x} - ${b}|`, Mul(N(a), F("abs", Sub(X_, N(b))))],
        [`${x}(${x} + ${b})`, Mul(X_, Add(X_, N(b)))],
        [`(${x} + ${a})(${x} - ${b})`, Mul(Add(X_, N(a)), Sub(X_, N(b)))],
        [`${x}/${a}${x}`, Mul(Div(X_, N(a)), X_)],
        [`e ${x}`, Mul(K("e"), X_)],
        [`${a}e^${x}`, Mul(N(a), F("exp", X_))],
        [`ln(${x})^2`, Pow(F("ln", X_), 2)],
        [`ln ${x} + ${b}`, Add(F("ln", X_), N(b))],
        [`${x}^-1 + ${x}^-2`, Add(Pow(X_, -1), Pow(X_, -2))],
        [`${x}^(1/${a})`, Pow(X_, N(1, a))],
        [`-${x}^-2`, Neg(Pow(X_, -2))],
        [`${a} - -${x}`, Sub(N(a), Neg(X_))],
        [`cos ${x} sin ${x}`, Mul(F("cos", X_), F("sin", X_))],
        [`tan^-1 ${x}`, F("atan", X_)],
        [`sin^-1(${x}/${a + 3})`, F("asin", Div(X_, N(a + 3)))],
        [`log_${a}(${x})`, F("log", N(a), X_)],
        [`log_${a} ${x}`, F("log", N(a), X_)],
        [`${a}sqrt(${x})${x}`, Mul(N(a), F("sqrt", X_), X_)],
        [`${x}²+${b}`, Add(Pow(X_, 2), N(b))],
        [`${a}·${x}`, Mul(N(a), X_)],
        [`${x}−${b}`, Sub(X_, N(b))],
      ];
      const [src, g] = R.pick(T);
      return [{ cat: "parse", group: id, variant: "notation", input: src, x, gexpr: g, task: null }];
    }
    const g = genExpr(R, x, R.int(1, 4), { fns: ["sin", "cos", "tan", "exp", "ln", "sqrt", "abs", "atan", "log"] });
    const st = { implicit: R.chance(0.6), fnpow: R.chance(0.5), spaces: R.chance(0.5), negExp: R.chance(0.4) };
    return [{ cat: "parse", group: id, variant: "orig", input: toQ(g, st), x, gexpr: g, task: null }];
  },
  simp(R, id) {
    const x = R.pick(VARS);
    const g = genExpr(R, x, R.int(2, 3), { fns: ["sin", "cos", "exp", "ln", "sqrt", "abs"] });
    const st = eqStyle(R);
    return [{ cat: "simp", group: id, variant: "orig", input: `simplify ${toQ(g, st)}`, x, gexpr: g, task: { kind: "simp", expr: toPy(g), x } }];
  },
  arith(R, id) {
    // constant expressions: exact value vs high-precision oracle
    const g = genExpr(R, "x", R.int(2, 4), { fns: ["sin", "cos", "tan", "exp", "ln", "sqrt", "atan", "abs", "asin", "acos"] });
    const sub = (u) => (u.t === "sym" ? R.pick([N(R.nz(-4, 4)), N(1, R.pick([2, 3, 4, 6])), Mul(N(R.int(1, 5)), Div(K("pi"), N(R.pick([2, 3, 4, 6, 12]))))]) : u.a ? { ...u, a: u.a.map(sub) } : u);
    const c = sub(g);
    return [{ cat: "arith", group: id, variant: "orig", input: toQ(c, eqStyle(R)), gexpr: c, task: { kind: "value", expr: toPy(c) } }];
  },
  "eq-poly"(R, id) {
    const x = R.pick(["x", "x", "t", "z"]);
    const p = genPolyEq(R, x);
    const alt = [["factored", p.factored, N(0)], ["zero-left", N(0), p.expanded]];
    // move a term to the right-hand side
    if (p.expanded.t === "add" && p.expanded.a.length > 1) {
      const last = p.expanded.a[p.expanded.a.length - 1];
      alt.push(["moved", Add(...p.expanded.a.slice(0, -1)), last.t === "neg" ? last.a[0] : Neg(last)]);
    }
    return eqCases("eq-poly", id, R, p.expanded, N(0), x, { alt, truth: { roots: p.roots }, nVariants: 3 });
  },
  // floating-point edges: close roots, tiny / huge scales, decimal coefficients (exact by construction)
  "eq-edge"(R, id) {
    const x = "x";
    const k = R.next();
    const rootsQ = []; // [n, d] BigInt
    const pow10 = (e) => 10n ** BigInt(e);
    if (k < 0.35) { // two roots 10^-e apart
      const r = BigInt(R.int(-5, 5)), e = R.int(3, 9);
      rootsQ.push([r * pow10(e), pow10(e)], [r * pow10(e) + 1n, pow10(e)]);
      if (R.chance(0.4)) rootsQ.push([BigInt(R.int(-9, 9)), 1n]);
    } else if (k < 0.6) { // tiny roots
      const e = R.int(3, 8);
      rootsQ.push([BigInt(R.nz(-9, 9)), pow10(e)], [BigInt(R.nz(-9, 9)), pow10(e)]);
    } else if (k < 0.8) { // huge roots
      const e = R.int(4, 9);
      rootsQ.push([BigInt(R.nz(-9, 9)) * pow10(e), 1n], [BigInt(R.int(-9, 9)), 1n]);
    } else { // decimal roots with a double root
      const r = [BigInt(R.int(-999, 999)), 100n];
      rootsQ.push(r, r, [BigInt(R.int(-99, 99)), 10n]);
    }
    // expand prod (x - r) exactly with BigInt rationals
    const qn = ([n, d]) => { const g = bg(n < 0n ? -n : n, d); return [n / g, d / g]; };
    const qadd = (a, b) => qn([a[0] * b[1] + b[0] * a[1], a[1] * b[1]]);
    const qmul = (a, b) => qn([a[0] * b[0], a[1] * b[1]]);
    let poly = [[1n, 1n]];
    for (const r of rootsQ) {
      const next = new Array(poly.length + 1).fill(null).map(() => [0n, 1n]);
      poly.forEach((c, i) => { next[i + 1] = qadd(next[i + 1], c); next[i] = qadd(next[i], qmul(c, [-r[0], r[1]])); });
      poly = next;
    }
    const qtext = ([n, d]) => {
      if (d === 1n) return n.toString();
      // a power-of-ten denominator prints as a decimal
      let dd = d, e = 0; while (dd % 10n === 0n) { dd /= 10n; e++; }
      if (dd === 1n) { const neg = n < 0n; let s = (neg ? -n : n).toString().padStart(e + 1, "0"); s = s.slice(0, -e) + "." + s.slice(-e); return (neg ? "-" : "") + s; }
      return `${n}/${d}`;
    };
    const terms = [];
    for (let i = poly.length - 1; i >= 0; i--) {
      const c = poly[i];
      if (c[0] === 0n) continue;
      const neg = c[0] < 0n, a = qtext([neg ? -c[0] : c[0], c[1]]);
      const mono = i === 0 ? "" : i === 1 ? x : `${x}^${i}`;
      const body = mono ? (a === "1" ? mono : `${a}${/[./]/.test(a) ? "*" : ""}${mono}`) : a;
      terms.push(terms.length ? `${neg ? " - " : " + "}${body}` : `${neg ? "-" : ""}${body}`);
    }
    const expanded = terms.join("");
    const factored = rootsQ.map((r) => `(${x} ${r[0] < 0n ? "+" : "-"} ${qtext([r[0] < 0n ? -r[0] : r[0], r[1]])})`).join("");
    const uniq = [];
    for (const r of rootsQ) { const v = Number(r[0]) / Number(r[1]); if (!uniq.includes(v)) uniq.push(v); }
    const task = { kind: "eq", lhs: rootsQ.map((r) => `(_s_${x} - Rational(${r[0]}, ${r[1]}))`).join("*"), rhs: "Integer(0)", x, R: 40 };
    const mk = (variant, input) => ({ cat: "eq-edge", group: id, variant, input, x, task: { ...task, src: input }, truth: { roots: uniq.sort((a, b) => a - b) } });
    return [mk("expanded", `${expanded} = 0`), mk("factored", `${factored} = 0`)];
  },
  "eq-rational"(R, id) {
    const x = "x";
    const a = R.nz(-5, 5), b = R.int(-6, 6), c = R.nz(-4, 4), d = R.int(-6, 6);
    const k = R.next();
    let lhs, rhs;
    if (k < 0.3) { lhs = Div(lin(1, a, x), lin(1, b, x)); rhs = N(c); }                        // (x+a)/(x+b) = c
    else if (k < 0.55) { lhs = Add(Div(N(1), lin(1, a, x)), Div(N(1), lin(1, b, x))); rhs = N(c, R.pick([1, 2, 3])); } // 1/(x+a) + 1/(x+b) = c
    else if (k < 0.75) { lhs = Div(polyAst([a * b, a + b, 1], x), lin(1, a, x)); rhs = N(d); } // removable: (x+a)(x+b)/(x+a) = d  (x = -a extraneous)
    else if (k < 0.9) { lhs = Div(Pow(V(x), 2), lin(1, a, x)); rhs = Div(N(a * a), lin(1, a, x)); } // x^2/(x+a) = a^2/(x+a): x = -a extraneous
    else { lhs = Add(V(x), Div(N(c), V(x))); rhs = N(d); }                                     // x + c/x = d
    return eqCases("eq-rational", id, R, lhs, rhs, x, { nVariants: 2 });
  },
  "eq-radical"(R, id) {
    const x = "x";
    const a = R.int(-6, 6), b = R.int(-5, 5), c = R.int(0, 6), m = R.nz(-3, 3);
    const k = R.next();
    let lhs, rhs;
    if (k < 0.3) { lhs = F("sqrt", lin(1, a, x)); rhs = lin(1, b, x); }               // sqrt(x+a) = x+b
    else if (k < 0.45) { lhs = F("sqrt", lin(m, a, x)); rhs = N(c); }                  // sqrt(mx+a) = c
    else if (k < 0.6) { lhs = Sub(F("sqrt", lin(1, a + 6, x)), F("sqrt", lin(1, b + 6, x))); rhs = N(R.int(-2, 2)); } // sqrt(x+p) - sqrt(x+q) = c
    else if (k < 0.72) { lhs = F("cbrt", lin(1, a, x)); rhs = N(R.int(-3, 3)); }       // cbrt(x+a) = c
    else if (k < 0.84) { lhs = Pow(lin(1, a, x), N(1, 3)); rhs = N(R.int(-3, 3)); }    // (x+a)^(1/3) = c   (real cube root)
    else { lhs = Add(V(x), F("sqrt", lin(1, a, x))); rhs = N(b + 6); }                  // x + sqrt(x+a) = c
    return eqCases("eq-radical", id, R, lhs, rhs, x, { nVariants: 2, scale: R.chance(0.5) });
  },
  "eq-exp"(R, id) {
    const x = "x";
    const bse = R.pick([N(2), N(3), K("e"), N(5), N(1, 2), N(10)]);
    const a = R.nz(-3, 3), b = R.int(-3, 3), c = R.pick([N(1), N(2), N(8), N(1, 4), N(27), N(5), N(-1), N(0), N(7)]);
    const k = R.next();
    let lhs, rhs;
    if (k < 0.35) { lhs = Pow(bse, lin(a, b, x)); rhs = c; }                                    // b^(ax+b) = c
    else if (k < 0.55) { const B = R.pick([2, 3]); lhs = Add(Pow(N(B * B), V(x)), Mul(N(R.int(-6, 6)), Pow(N(B), V(x))), N(R.int(-8, 8))); rhs = N(0); } // quadratic in B^x
    else if (k < 0.7) { lhs = Pow(N(2), V(x)); rhs = Pow(N(3), lin(1, R.int(-2, 2), x)); }      // 2^x = 3^(x+k)
    else if (k < 0.85) { lhs = Add(Pow(K("e"), V(x)), Pow(K("e"), Neg(V(x)))); rhs = N(R.int(1, 5)); } // e^x + e^-x = c
    else { lhs = Mul(N(R.nz(-3, 3)), Pow(bse, V(x))); rhs = N(R.int(-4, 12)); }
    return eqCases("eq-exp", id, R, lhs, rhs, x, { nVariants: 2 });
  },
  "eq-log"(R, id) {
    const x = "x";
    const a = R.int(-4, 4), b = R.int(-4, 4), c = R.int(-2, 3);
    const k = R.next();
    let lhs, rhs;
    if (k < 0.25) { lhs = F("ln", lin(1, a, x)); rhs = N(c); }
    else if (k < 0.45) { lhs = Add(F("log", N(2), V(x)), F("log", N(2), lin(1, a, x))); rhs = N(R.int(0, 4)); }   // log_2 x + log_2(x+a) = c
    else if (k < 0.6) { lhs = Add(F("ln", V(x)), F("ln", lin(1, a, x))); rhs = F("ln", N(R.int(1, 12))); }
    else if (k < 0.72) { lhs = F("ln", Pow(V(x), 2)); rhs = N(R.int(0, 3)); }                          // ln(x^2) = c (two roots)
    else if (k < 0.84) { lhs = Mul(N(2), F("ln", V(x))); rhs = F("ln", lin(1, R.int(0, 6), x)); }     // 2 ln x = ln(x + a)
    else { lhs = F("log", lin(1, a, x)); rhs = N(R.int(0, 2)); }                                         // log10
    return eqCases("eq-log", id, R, lhs, rhs, x, { nVariants: 2, range: 60 });
  },
  "eq-trig"(R, id) {
    const x = "x";
    const k = R.next();
    const f = R.pick(["sin", "cos", "tan"]);
    const vals = f === "tan" ? [N(1), N(-1), N(0), Pow(N(3), N(1, 2)), N(2)] : [N(1, 2), N(-1, 2), N(0), N(1), N(-1), Div(Pow(N(2), N(1, 2)), N(2)), N(2), N(1, 3)];
    let lhs, rhs;
    if (k < 0.35) { lhs = F(f, lin(R.pick([1, 2, 3]), 0, x)); rhs = R.pick(vals); }
    else if (k < 0.5) { lhs = F(f, Add(V(x), Div(K("pi"), N(R.pick([3, 4, 6]))))); rhs = R.pick(vals); }
    else if (k < 0.65) { lhs = Add(Mul(N(2), Pow(F("sin", V(x)), 2)), Neg(F("sin", V(x))), N(-1)); rhs = N(0); }  // quadratic in sin
    else if (k < 0.78) { lhs = F("sin", V(x)); rhs = F("cos", V(x)); }
    else if (k < 0.9) { lhs = Pow(F(f === "tan" ? "sin" : f, V(x)), 2); rhs = R.pick([N(1, 4), N(1, 2), N(3, 4), N(1), N(0)]); }
    else { lhs = Add(F("sin", V(x)), F("cos", V(x))); rhs = R.pick([N(1), N(0), Pow(N(2), N(1, 2)), N(2)]); }
    return eqCases("eq-trig", id, R, lhs, rhs, x, { nVariants: 2, range: 20 });
  },
  "eq-abs"(R, id) {
    const x = "x";
    const a = R.int(-5, 5), b = R.int(-5, 5), c = R.int(-3, 7), m = R.nz(-3, 3);
    const k = R.next();
    let lhs, rhs;
    if (k < 0.35) { lhs = F("abs", lin(m, a, x)); rhs = N(c); }
    else if (k < 0.55) { lhs = F("abs", lin(1, a, x)); rhs = lin(R.nz(-2, 2), b, x); }
    else if (k < 0.7) { lhs = F("abs", lin(1, a, x)); rhs = F("abs", lin(R.nz(-3, 3), b, x)); }
    else if (k < 0.85) { lhs = Add(F("abs", lin(1, a, x)), F("abs", lin(1, b, x))); rhs = N(Math.abs(c) + 2); }
    else { lhs = F("abs", polyAst([a, 0, 1], x)); rhs = N(Math.abs(c)); }        // |x^2 + a| = c
    return eqCases("eq-abs", id, R, lhs, rhs, x, { nVariants: 2 });
  },
  ineq(R, id) {
    const x = R.pick(["x", "x", "t"]);
    const k = R.next();
    const ops = ["<", "<=", ">", ">="];
    const op = R.pick(ops);
    let lhs, rhs;
    if (k < 0.3) { const p = genPolyEq(R, x); lhs = p.expanded; rhs = N(0); if (p.coeffs.length > 5) { const q = genPolyEq(R, x); lhs = q.factored; } }
    else if (k < 0.5) { const a = R.int(-5, 5), b = R.int(-5, 5); lhs = Div(lin(1, a, x), lin(1, b, x)); rhs = N(R.int(-2, 2)); }
    else if (k < 0.65) { lhs = F("abs", lin(R.nz(-3, 3), R.int(-5, 5), x)); rhs = N(R.int(-1, 6)); }
    else if (k < 0.75) { lhs = Pow(R.pick([N(2), K("e"), N(1, 3)]), V(x)); rhs = N(R.pick([1, 2, 5, 9, -1])); }
    else if (k < 0.85) { lhs = F("ln", lin(1, R.int(-3, 3), x)); rhs = N(R.int(-1, 2)); }
    else if (k < 0.93) { lhs = F("sqrt", lin(1, R.int(-4, 4), x)); rhs = lin(1, R.int(-3, 3), x); }
    else { lhs = Div(N(1), V(x)); rhs = N(R.nz(-3, 3)); }
    const st = eqStyle(R);
    const flip = { "<": ">", "<=": ">=", ">": "<", ">=": "<=" };
    const mk = (variant, l, o, r2, v = x) => ({ cat: "ineq", group: id, variant, input: `${toQ(l, st)} ${o} ${toQ(r2, st)}`, x: v, task: { kind: "ineq", lhs: toPy(l), op: o, rhs: toPy(r2), x: v } });
    const out = [mk("orig", lhs, op, rhs), mk("swap", rhs, flip[op], lhs)];
    const c = R.pick([2, -2, 3, -1]);
    out.push(mk("scale", Mul(N(c), lhs), c < 0 ? flip[op] : op, Mul(N(c), rhs)));
    return out;
  },
  "sys-linear"(R, id) {
    const n = R.chance(0.6) ? 2 : 3;
    const vars = n === 2 ? ["x", "y"] : ["x", "y", "z"];
    const sol = vars.map(() => (R.chance(0.8) ? R.int(-5, 5) : R.int(-9, 9) / R.pick([2, 3])));
    const rows = [];
    for (let i = 0; i < n; i++) rows.push(vars.map(() => R.int(-4, 4)));
    const kind = R.next();
    if (kind < 0.12) rows[n - 1] = rows[0].map((v) => 2 * v); // dependent (or inconsistent below)
    const rhs = rows.map((r) => r.reduce((s, a, j) => s + a * sol[j], 0));
    if (kind < 0.06) rhs[n - 1] += 1; // inconsistent
    const eqs = rows.map((r, i) => {
      const terms = r.map((a, j) => (a ? Mul(N(a), V(vars[j])) : null)).filter(Boolean);
      return [terms.length ? Add(...terms) : N(0), N(Math.round(rhs[i] * 6)).n % 6 === 0 ? N(Math.round(rhs[i])) : N(Math.round(rhs[i] * 6), 6)];
    });
    const st = eqStyle(R);
    const text = (E) => E.map(([l, r2]) => `${toQ(l, st)} = ${toQ(r2, st)}`).join(", ");
    const task = { kind: "sys", eqs: eqs.map(([l, r2]) => [toPy(l), toPy(r2)]), vars };
    return [
      { cat: "sys-linear", group: id, variant: "orig", input: text(eqs), task },
      { cat: "sys-linear", group: id, variant: "reorder", input: text(R.shuffle(eqs)), task },
    ];
  },
  "sys-nonlinear"(R, id) {
    const k = R.next();
    let eqs;
    const X_ = V("x"), Y_ = V("y");
    if (k < 0.35) { const r2 = R.pick([1, 2, 4, 5, 9, 10, 13, 25]); eqs = [[Add(Pow(X_, 2), Pow(Y_, 2)), N(r2)], [Y_, lin(R.int(-2, 2), R.int(-3, 3), "x")]]; }
    else if (k < 0.6) { eqs = [[Mul(X_, Y_), N(R.nz(-6, 6))], [Add(X_, Y_), N(R.int(-5, 5))]]; }
    else if (k < 0.8) { eqs = [[Y_, polyAst([R.int(-3, 3), R.int(-2, 2), 1], "x")], [Y_, lin(R.int(-2, 2), R.int(-3, 3), "x")]]; }
    else { eqs = [[Add(Pow(X_, 2), Pow(Y_, 2)), N(R.pick([5, 10, 13, 25]))], [Sub(Pow(X_, 2), Pow(Y_, 2)), N(R.int(-5, 5))]]; }
    const st = eqStyle(R);
    const text = (E) => E.map(([l, r2]) => `${toQ(l, st)} = ${toQ(r2, st)}`).join(", ");
    const task = { kind: "sys", eqs: eqs.map(([l, r2]) => [toPy(l), toPy(r2)]), vars: ["x", "y"] };
    return [
      { cat: "sys-nonlinear", group: id, variant: "orig", input: text(eqs), task },
      { cat: "sys-nonlinear", group: id, variant: "reorder", input: text(eqs.slice().reverse()), task },
    ];
  },
  diff(R, id) {
    const x = R.pick(["x", "x", "t"]);
    const g = genExpr(R, x, R.int(1, 3), { fns: ["sin", "cos", "tan", "exp", "ln", "sqrt", "atan", "asin"] });
    const st = eqStyle(R);
    return [
      { cat: "diff", group: id, variant: "orig", input: `d/d${x} ${toQ(g, st).includes(" ") ? `(${toQ(g, st)})` : toQ(g, st)}`, x, task: { kind: "diff", expr: toPy(g), x }, gexpr: g },
      { cat: "diff", group: id, variant: "words", input: `derivative of ${toQ(g, st)}${x !== "x" ? ` with respect to ${x}` : ""}`, x, task: { kind: "diff", expr: toPy(g), x }, gexpr: g },
    ];
  },
  anti(R, id) {
    const x = "x";
    // integrands with elementary antiderivatives most of the time: build F, differentiate? No: pick
    // common textbook shapes plus random products
    const a = R.nz(-4, 4), b = R.int(-3, 3), n = R.int(0, 4);
    const shapes = [
      () => Mul(Pow(V(x), n), F("exp", lin(a, b, x))),
      () => Mul(Pow(V(x), n), F(R.pick(["sin", "cos"]), lin(a, 0, x))),
      () => Div(N(1), polyAst([R.int(-6, 6), R.int(-4, 4), 1], x)),
      () => Div(lin(R.int(-3, 3), R.int(-3, 3), x), polyAst([R.int(-6, 6), R.int(-4, 4), 1], x)),
      () => Mul(Pow(V(x), n), F("ln", V(x))),
      () => Pow(F(R.pick(["sin", "cos"]), V(x)), R.int(2, 4)),
      () => Mul(F("sin", lin(a, 0, x)), F("cos", lin(R.nz(-3, 3), 0, x))),
      () => Div(N(1), F("sqrt", polyAst([R.int(1, 9), 0, -1], x))),
      () => Mul(V(x), F("sqrt", lin(1, R.int(0, 4), x))),
      () => Div(N(1), Mul(V(x), lin(1, R.nz(-4, 4), x))),
      () => Mul(F("exp", V(x)), F(R.pick(["sin", "cos"]), V(x))),
      () => Div(F("exp", V(x)), Add(N(1), F("exp", V(x)))),
      () => polyAst([R.int(-5, 5), R.int(-5, 5), R.int(-5, 5), R.int(-3, 3)], x),
      () => Div(Pow(F("ln", V(x)), R.int(1, 3)), V(x)),
      () => Mul(V(x), F("atan", V(x))),
      () => F(R.pick(["tan", "atan", "asin", "sec"]), V(x)),
      () => genExpr(R, x, 2, { fns: ["sin", "cos", "exp", "sqrt"], noDiv: true }),
    ];
    const g = R.pick(shapes)();
    const st = eqStyle(R);
    return [{ cat: "anti", group: id, variant: "orig", input: `int ${toQ(g, st)} dx`, x, task: { kind: "anti", expr: toPy(g), x }, gexpr: g },
      { cat: "anti", group: id, variant: "words", input: `integrate ${toQ(g, st)}`, x, task: { kind: "anti", expr: toPy(g), x }, gexpr: g }];
  },
  defint(R, id) {
    const x = "x";
    const g = R.chance(0.5) ? genExpr(R, x, 2, { fns: ["sin", "cos", "exp", "sqrt", "ln", "atan", "abs"] }) : GENERATORS.anti(R, id)[0].gexpr;
    const lo = R.pick([N(0), N(1), N(-1), N(2), N(-2), N(1, 2)]);
    let hi = R.pick([N(1), N(2), N(3), K("pi"), N(1, 2), N(4), K("oo")]);
    if (hi.t === "num" && lo.t === "num" && hi.n / hi.d <= lo.n / lo.d) hi = N(lo.n / lo.d >= 2 ? 5 : 3);
    const st = eqStyle(R);
    const L = toQ(lo, st), H = toQ(hi, st);
    const wrapB = (s) => (/^[\w.]+$/.test(s) ? s : `(${s})`);
    return [
      { cat: "defint", group: id, variant: "orig", input: `int_${wrapB(L)}^${wrapB(H)} ${toQ(g, st)} dx`, x, task: { kind: "defint", expr: toPy(g), x, lo: toPy(lo), hi: toPy(hi) } },
      { cat: "defint", group: id, variant: "words", input: `integral of ${toQ(g, st)} from ${L} to ${H}`, x, task: { kind: "defint", expr: toPy(g), x, lo: toPy(lo), hi: toPy(hi) } },
    ];
  },
  limit(R, id) {
    const x = "x";
    const k = R.next();
    let g, pt;
    const a = R.int(-3, 3);
    if (k < 0.3) { const p = R.int(-3, 3); g = Div(polyAst([p * a, -(p + a), 1], x), lin(1, -a, x)); pt = N(a); }   // removable
    else if (k < 0.5) { g = Div(F(R.pick(["sin", "tan", "atan"]), lin(R.nz(-3, 3), 0, x)), lin(R.nz(-3, 3), 0, x)); pt = N(0); }
    else if (k < 0.65) { g = Div(polyAst([R.int(-5, 5), R.int(-5, 5), R.nz(-4, 4)], x), polyAst([R.int(-5, 5), R.nz(-4, 4), R.int(-2, 2)], x)); pt = K("oo"); }
    else if (k < 0.75) { g = Div(Sub(F("exp", lin(R.nz(-3, 3), 0, x)), N(1)), V(x)); pt = N(0); }
    else if (k < 0.85) { g = Pow(Add(N(1), Div(N(R.nz(-3, 3)), V(x))), V(x)); pt = K("oo"); }
    else if (k < 0.93) { g = Div(Sub(N(1), F("cos", lin(R.nz(-3, 3), 0, x))), Pow(V(x), 2)); pt = N(0); }
    else { g = genExpr(R, x, 2, { fns: ["sin", "cos", "exp", "atan"], noDiv: true }); pt = N(R.int(-2, 2)); }
    const st = eqStyle(R);
    const P = toQ(pt, st);
    return [{ cat: "limit", group: id, variant: "orig", input: `lim ${x}->${P} ${toQ(g, st)}`, x, task: { kind: "limit", expr: toPy(g), x, pt: toPy(pt) } },
      { cat: "limit", group: id, variant: "words", input: `limit of ${toQ(g, st)} as ${x} -> ${P}`, x, task: { kind: "limit", expr: toPy(g), x, pt: toPy(pt) } }];
  },
  sum(R, id) {
    const n = "k";
    const k = R.next();
    let g, lo = N(R.int(0, 2)), hi;
    if (k < 0.3) { g = polyAst([R.int(-3, 3), R.int(-3, 3), R.int(0, 2), R.int(0, 1)], n); hi = N(R.int(3, 40)); }
    else if (k < 0.5) { g = Pow(N(R.pick([1, 2, -1, 3]), R.pick([2, 3, 5])), V(n)); hi = K("oo"); }
    else if (k < 0.65) { g = Div(N(1), Pow(V(n), R.int(2, 4))); lo = N(1); hi = K("oo"); }
    else if (k < 0.75) { const a = R.int(1, 3); g = Div(N(1), Mul(V(n), lin(1, a, n))); lo = N(1); hi = K("oo"); }
    else if (k < 0.85) { g = polyAst([R.int(-3, 3), R.int(-3, 3), R.int(0, 2), R.int(0, 1)], n); hi = V("n"); lo = N(1); }
    else if (k < 0.93) { g = Div(Pow(N(-1), V(n)), lin(1, 1, n)); lo = N(0); hi = K("oo"); }
    else { g = Div(Pow(N(R.int(1, 3)), V(n)), F("factorial", V(n))); lo = N(0); hi = K("oo"); }
    const st = eqStyle(R);
    const H = toQ(hi, st), L = toQ(lo, st);
    return [{ cat: "sum", group: id, variant: "orig", input: `sum_(${n}=${L})^(${H}) ${/[+-]/.test(toQ(g, st).slice(1)) ? `(${toQ(g, st)})` : toQ(g, st)}`, task: { kind: "sum", expr: toPy(g), n, lo: toPy(lo), hi: toPy(hi) } },
      { cat: "sum", group: id, variant: "call", input: `sum(${toQ(g, st)}, ${n}, ${L}, ${H})`, task: { kind: "sum", expr: toPy(g), n, lo: toPy(lo), hi: toPy(hi) } }];
  },
  ode(R, id) {
    const k = R.next();
    let text, ode, ics = [];
    const a = R.nz(-3, 3), b = R.int(-4, 4), c = R.int(-4, 4);
    // ode is sympy residual in terms of _y (function of x): string using Y0, Y1, Y2 for y, y', y''
    if (k < 0.25) { text = `y' = ${a}y`; ode = `Y1 - (${a})*Y0`; }
    else if (k < 0.45) { text = `y'' ${b < 0 ? "-" : "+"} ${Math.abs(b)}y' ${c < 0 ? "-" : "+"} ${Math.abs(c)}y = 0`; ode = `Y2 + (${b})*Y1 + (${c})*Y0`; }
    else if (k < 0.6) { text = `y' + ${Math.abs(a)}y = x`; ode = `Y1 + ${Math.abs(a)}*Y0 - X`; }
    else if (k < 0.72) { text = `dy/dx = ${a}x*y`; ode = `Y1 - (${a})*X*Y0`; }
    else if (k < 0.82) { text = `y'' + ${Math.abs(c) + 1}y = 0`; ode = `Y2 + ${Math.abs(c) + 1}*Y0`; }
    else { text = `y' = ${R.pick(["x^2", "sin(x)", "e^x", "2x + 1", "cos(2x)"])}`; ode = `Y1 - (${text.slice(5).replace(/\^/g, "**").replace(/(\d)x/g, "$1*x").replace(/e\*\*x/, "exp(x)").replace(/x/g, "X").replace(/eXp/, "exp")})`; }
    const order = /Y2/.test(ode) ? 2 : 1;
    if (R.chance(0.5)) {
      const y0 = R.int(-3, 3);
      ics.push([0, 0, y0]);
      if (order === 2) ics.push([1, 0, R.int(-3, 3)]);
    }
    const input = text + ics.map(([d, x0, v]) => `, y${"'".repeat(d)}(${x0}) = ${v}`).join("");
    return [{ cat: "ode", group: id, variant: "orig", input, task: { kind: "ode", ode, order, ics } }];
  },
  matrix(R, id) {
    const n = R.int(2, 4);
    const M = []; for (let i = 0; i < n; i++) { const row = []; for (let j = 0; j < n; j++) row.push(R.int(-5, 5)); M.push(row); }
    if (R.chance(0.15)) M[n - 1] = M[0].map((v, j) => v + M[1][j]); // singular
    const op = R.pick(["det", "inv", "rank", "transpose", "trace", "square"]);
    const ms = `[${M.map((r) => `[${r.join(",")}]`).join(",")}]`;
    const input = op === "square" ? `${ms}*${ms}` : `${op}(${ms})`;
    return [{ cat: "matrix", group: id, variant: "orig", input, task: { kind: "matrix", op, M } }];
  },
};

export const CATEGORY_WEIGHTS = {
  parse: 3000, "eq-edge": 800, simp: 1200, arith: 1500, "eq-poly": 2600, "eq-rational": 1000, "eq-radical": 1000, "eq-exp": 900, "eq-log": 900,
  "eq-trig": 1000, "eq-abs": 900, ineq: 1500, "sys-linear": 800, "sys-nonlinear": 600, diff: 1200, anti: 1200, defint: 1000,
  limit: 800, sum: 600, ode: 500, matrix: 800,
};

// Generate about `count` cases for a category (whole metamorphic groups).
export function generate(cat, count, seed) {
  const R = rng(seed);
  const out = [];
  let g = 0;
  while (out.length < count) {
    const cs = GENERATORS[cat](R, `${cat}:${seed}:${g++}`);
    for (const c of cs) out.push(c);
  }
  return out;
}

// ---------------------------------------------------------------- oracle-free checks
// Return a list of { type, detail } problems found without the oracle.
const closeRel = (a, b, tol = 1e-7) => Math.abs(a - b) <= tol * Math.max(1, Math.abs(a), Math.abs(b));

export function checkParse(c) {
  const probs = [];
  let node;
  try { node = parse(c.input); } catch (e) { return [{ type: "refusal", detail: "parse error: " + e.message }]; }
  let text, node2;
  try { text = toText(node); node2 = parse(text); } catch (e) { return [{ type: "wrong", detail: `toText gives unparseable "${text}": ${e.message}` }]; }
  const pts = [0.37, 1.61, -0.83, 2.3, -1.9, 0.05];
  let n = 0;
  for (const p of pts) {
    const want = evalG(c.gexpr, { [c.x]: p });
    const got = evalX(node, { [c.x]: p });
    const got2 = evalX(node2, { [c.x]: p });
    if (!Number.isFinite(want)) { if (Number.isFinite(got) && Math.abs(got) < 1e12) probs.push({ type: "wrong", detail: `parse defined at ${c.x}=${p} (${got}) but the intended expression is not` }); continue; }
    if (Math.abs(want) > 1e12) continue;
    if (!Number.isFinite(got) || !closeRel(got, want, 1e-9)) { probs.push({ type: "wrong", detail: `parse(${c.input}) = ${toText(node)} differs at ${c.x}=${p}: ${got} vs intended ${want}` }); break; }
    if (!Number.isFinite(got2) || !closeRel(got2, got, 1e-9)) { probs.push({ type: "wrong", detail: `round trip "${text}" differs at ${c.x}=${p}: ${got2} vs ${got}` }); break; }
    n++;
  }
  return probs;
}

// equations with truth known by construction (polynomials): the verified real root set must match
export function checkEqTruth(c, r) {
  if (!verified(r) || !c.truth || !c.truth.roots) return [];
  if ((r.answers || []).some((a) => a.kind === "general" || a.kind === "all" || a.kind === "set")) return [{ type: "wrong", detail: "a polynomial answered with a family or set" }];
  const vals = pointValues(r);
  const want = c.truth.roots;
  const uniq = [];
  // purely relative tolerance: roots 1e-8 apart or of size 1e-8 must still be told apart
  const near = (a, b) => Math.abs(a - b) <= 1e-10 * Math.max(Math.abs(a), Math.abs(b), 1e-300);
  for (const v of vals) if (!uniq.some((u) => near(u, v))) uniq.push(v);
  if (uniq.length !== vals.length || uniq.length !== want.length || !want.every((w) => uniq.some((g) => near(g, w)))) {
    return [{ type: "wrong", detail: `roots ${JSON.stringify(vals.map((v) => +v.toPrecision(10)))} but expected ${JSON.stringify(want)}` }];
  }
  return [];
}

// numeric values of an equation's point answers (exact tree or approx)
export function pointValues(r) {
  const vals = [];
  for (const a of (r && r.answers) || []) {
    if (a.kind === "exact" && a.tree) vals.push(evalX(a.tree, {}));
    else if (a.kind === "approx" && a.approx) vals.push(parseFloat(a.approx.value));
  }
  return vals;
}

// Substitute each verified point answer back into the ORIGINAL (generator) equation, independently.
export function checkSubstitution(c, r) {
  if (!verified(r) || !c.gl) return [];
  const probs = [];
  for (const a of r.answers || []) {
    let v = NaN;
    if (a.kind === "exact" && a.tree) v = evalX(a.tree, {});
    else if (a.kind === "approx" && a.approx) v = parseFloat(a.approx.value);
    else continue;
    if (!Number.isFinite(v)) { probs.push({ type: "wrong", detail: `answer ${a.tree ? toText(a.tree) : a.approx.value} is not a real number` }); continue; }
    const L = evalG(c.gl, { [c.x]: v }), Rr = evalG(c.gr, { [c.x]: v });
    if (!Number.isFinite(L) || !Number.isFinite(Rr)) { probs.push({ type: "wrong", detail: `answer ${c.x} = ${v} is outside the domain of the original` }); continue; }
    // residual scaled by the size of the terms involved (double precision evaluation)
    const scale = Math.max(1, Math.abs(L), Math.abs(Rr));
    if (Math.abs(L - Rr) > 1e-6 * scale) probs.push({ type: "wrong", detail: `substituting ${c.x} = ${v}: ${L} != ${Rr}` });
  }
  return probs;
}

// Compare verified answer sets across a metamorphic group: point answers plus every member of a
// periodic family inside a window, as one sorted set of numbers (so different ways of writing a
// family compare equal).
export function answerKey(r) {
  if (!verified(r)) return null;
  const nums = [], tags = [];
  const addNum = (v) => { if (!nums.some((u) => Math.abs(u - v) <= 1e-7 * Math.max(1, Math.abs(v)))) nums.push(v); };
  for (const a of r.answers || []) {
    if ((a.kind === "exact" || a.kind === "approx") && (a.tree || a.approx)) {
      const v = a.tree ? evalX(a.tree, {}) : parseFloat(a.approx.value);
      if (Number.isFinite(v)) addNum(v); else tags.push("T:" + (a.tree ? toText(a.tree) : a.approx.value));
    } else if (a.kind === "general" && a.tree) {
      const k = a.param || "k";
      for (let i = -40; i <= 40; i++) { const v = evalX(a.tree, { [k]: i }); if (Number.isFinite(v) && Math.abs(v) < 12) addNum(v); }
      tags.push("general");
    } else tags.push(a.kind === "none" ? "none" : a.kind);
  }
  const inWin = tags.includes("general") ? nums.filter((v) => Math.abs(v) < 11.5) : nums;
  return [...new Set(tags)].sort().join(",") + "#" + inWin.sort((a, b) => a - b).map((v) => v.toPrecision(8)).join("|");
}
