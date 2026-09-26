// Quelvra numerical engine.
//
// Honest numerics: every approximate answer is an Approx record
//   { value: string, digits: number, requested: number, errorBound: string|null,
//     method: string, iterations: number, converged: boolean, warnings?: string[] }
// where `digits` is the number of significant digits we believe are correct (never more
// than `requested`), `errorBound` bounds |value - true| (as a 1-significant-digit decimal
// string, rounded up) and is `null` when no estimate exists. Whether the bound is certified
// or heuristic is stated in `method` / `warnings`.
//
// Evaluation is done by compiling a math tree (expr.js) into closures over an "algebra"
// (double, BigFloat, interval, or dual numbers over any of these for forward-mode automatic
// differentiation). There is no eval / new Function.
//
// All loops are bounded; exhausting a budget throws an Error with code "BUDGET" or
// "TIMEOUT" unless a partial, clearly flagged result can be returned instead.

import * as Nq from "./num.js";
import * as X from "./expr.js";
import * as B from "./bigfloat.js";
import * as IV from "./interval.js";

const { BigFloat, Complex } = B;

// ---------------------------------------------------------------------------------------
// errors, markers, formatting
// ---------------------------------------------------------------------------------------
function qerr(code, msg) {
  const e = new Error("Quelvra: " + msg);
  e.code = code;
  return e;
}
const undefErr = (msg) => qerr("UNDEFINED", msg);
const unsupported = (msg) => qerr("UNSUPPORTED", msg);
const isUndefCode = (e) => e && (e.code === "UNDEFINED" || e.code === "DOMAIN");

// Explicit marker for "the expression is undefined at this point". Never NaN.
export const UNDEFINED = Object.freeze({ kind: "undefined", reason: "undefined" });
export const makeUndefined = (reason) => Object.freeze({ kind: "undefined", reason: reason || "undefined" });
export const isUndefined = (v) => !!v && v.kind === "undefined";

const now = () => (typeof performance !== "undefined" ? performance.now() : Date.now());
function deadline(ms) {
  const t0 = now();
  return { expired: () => now() - t0 > ms, elapsed: () => now() - t0 };
}

// Error bound as a 1-significant-digit string rounded UP ("3e-21"); accepts BigFloat or number.
export function fmtErr(x) {
  if (x === null || x === undefined) return null;
  if (typeof x === "number") {
    if (!Number.isFinite(x)) return x > 0 ? "Infinity" : null;
    x = B.fromNumber(Math.abs(x));
  }
  x = B.abs(x);
  if (x.m === 0n) return "0";
  const { ds, k } = B.toDigits(x, 3);
  let lead = Number(ds[0]) + (ds.slice(1) !== "00" ? 1 : 0);
  let kk = k;
  if (lead === 10) { lead = 1; kk++; }
  return `${lead}e${kk}`;
}
export function fmtNum(x, digits = 17) {
  if (typeof x === "number") {
    if (Number.isNaN(x)) return "undefined";
    if (!Number.isFinite(x)) return x > 0 ? "oo" : "-oo";
    x = B.fromNumber(x);
  }
  return B.toString(x, Math.max(1, Math.min(digits, 1000)));
}
export function record(o) {
  const r = {
    value: o.value,
    digits: Math.max(0, Math.floor(o.digits ?? 0)),
    requested: o.requested,
    errorBound: o.errorBound ?? null,
    method: o.method,
    iterations: o.iterations ?? 0,
    converged: !!o.converged,
  };
  if (o.warnings && o.warnings.length) r.warnings = o.warnings.slice();
  return r;
}
// decimal exponent floor(log10 |x|) of a BigFloat (x != 0)
const decExp = (x) => B.toDigits(x, 2).k;
const pow10 = (k, prec) => (k >= 0 ? B.fromBigInt(10n ** BigInt(k)) : B.div(B.ONE, B.fromBigInt(10n ** BigInt(-k)), prec));
// Correct digits implied by an absolute error bound on |x|.
function digitsFrom(x, errBF, requested) {
  if (errBF.m === 0n) return requested;
  if (x.m === 0n) return 0;
  const rel = B.toNumber(B.div(errBF, B.abs(x), 64));
  if (!(rel > 0)) return requested;
  return Math.max(0, Math.min(requested, Math.floor(-Math.log10(rel))));
}
const EPS = Number.EPSILON;

// ---------------------------------------------------------------------------------------
// double-precision special functions
// ---------------------------------------------------------------------------------------
const LANCZOS = [0.99999999999980993, 676.5203681218851, -1259.1392167224028, 771.32342877765313,
  -176.61502916214059, 12.507343278686905, -0.13857109526572012, 9.9843695780195716e-6, 1.5056327351493116e-7];
export function gammaD(x) {
  if (Number.isNaN(x)) return NaN;
  if (Number.isInteger(x)) {
    if (x <= 0) return NaN;
    if (x <= 171) { let r = 1; for (let i = 2; i < x; i++) r *= i; return r; }
    return Infinity;
  }
  if (x < 0.5) {
    const fr = x - Math.round(x);
    const s = Math.sin(Math.PI * fr) * (Math.round(x) % 2 === 0 ? 1 : -1);
    return Math.PI / (s * gammaD(1 - x));
  }
  x -= 1;
  let a = LANCZOS[0];
  const t = x + 7.5;
  for (let i = 1; i < 9; i++) a += LANCZOS[i] / (x + i);
  return Math.sqrt(2 * Math.PI) * Math.pow(t, x + 0.5) * Math.exp(-t) * a;
}
export function digammaD(x) {
  if (Number.isNaN(x) || (x <= 0 && Number.isInteger(x))) return NaN;
  if (x < 0.5) return digammaD(1 - x) - Math.PI / Math.tan(Math.PI * (x - Math.round(x)));
  let r = 0;
  while (x < 8) { r -= 1 / x; x += 1; }
  const x2 = 1 / (x * x);
  return r + Math.log(x) - 0.5 / x - x2 * (1 / 12 - x2 * (1 / 120 - x2 * (1 / 252 - x2 * (1 / 240 - x2 / 132))));
}
export function erfD(x) {
  if (Number.isNaN(x)) return NaN;
  if (x < 0) return -erfD(-x);
  if (x === 0) return 0;
  if (x > 6) return 1;
  if (x < 2.5) {
    // erf x = 2/sqrt(pi) e^{-x^2} sum 2^n x^{2n+1} / (1*3*...*(2n+1)) (all terms positive)
    let term = x, sum = x;
    for (let n = 1; n < 200; n++) {
      term *= (2 * x * x) / (2 * n + 1);
      sum += term;
      if (term < sum * 1e-17) break;
    }
    return (2 / Math.sqrt(Math.PI)) * Math.exp(-x * x) * sum;
  }
  // erfc continued fraction (modified Lentz)
  let f = x, C = x, D = 0;
  for (let n = 1; n < 300; n++) {
    const an = n / 2;
    D = x + an * D; D = D === 0 ? 1e-300 : 1 / D;
    C = x + an / C; if (C === 0) C = 1e-300;
    const delta = C * D;
    f *= delta;
    if (Math.abs(delta - 1) < 1e-16) break;
  }
  return 1 - Math.exp(-x * x) / (f * Math.sqrt(Math.PI));
}

// ---------------------------------------------------------------------------------------
// algebras
// ---------------------------------------------------------------------------------------
const nz = (x) => (x === 0 ? NaN : x);
const DFN = {
  sin: Math.sin, cos: Math.cos, tan: Math.tan,
  cot: (x) => 1 / nz(Math.tan(x)), sec: (x) => 1 / Math.cos(x), csc: (x) => 1 / nz(Math.sin(x)),
  asin: (x) => (Math.abs(x) <= 1 ? Math.asin(x) : NaN), acos: (x) => (Math.abs(x) <= 1 ? Math.acos(x) : NaN),
  atan: Math.atan, acot: (x) => Math.PI / 2 - Math.atan(x),
  asec: (x) => (Math.abs(x) >= 1 ? Math.acos(1 / x) : NaN), acsc: (x) => (Math.abs(x) >= 1 ? Math.asin(1 / x) : NaN),
  sinh: Math.sinh, cosh: Math.cosh, tanh: Math.tanh,
  coth: (x) => 1 / nz(Math.tanh(x)), sech: (x) => 1 / Math.cosh(x), csch: (x) => 1 / nz(Math.sinh(x)),
  asinh: Math.asinh, acosh: (x) => (x >= 1 ? Math.acosh(x) : NaN), atanh: (x) => (Math.abs(x) < 1 ? Math.atanh(x) : NaN),
  ln: (x) => (x > 0 ? Math.log(x) : NaN), exp: Math.exp, abs: Math.abs,
  sqrt: (x) => (x >= 0 ? Math.sqrt(x) : NaN), cbrt: Math.cbrt,
  floor: Math.floor, ceil: Math.ceil, round: (x) => Math.sign(x) * Math.round(Math.abs(x)), sign: Math.sign,
  gamma: gammaD, factorial: (x) => gammaD(x + 1), erf: erfD, digamma: digammaD,
};
function powRatD(a, p, q) {
  if (a === 0) return p > 0 ? 0 : NaN;
  if (a < 0) {
    if (q % 2 === 0) return NaN;
    const r = Math.pow(-a, p / q);
    return p % 2 === 0 ? r : -r;
  }
  if (q === 3 && p === 1) return Math.cbrt(a);
  return Math.pow(a, p / q);
}
export const DOUBLE = {
  kind: "double", stamp: 0, zero: 0, one: 1,
  fromInt: (n) => Number(n),
  num: (q) => Nq.toFloat(q),
  konst(name) {
    if (name === "pi") return Math.PI;
    if (name === "e") return Math.E;
    if (name === "undef") return NaN;
    throw unsupported(`constant ${name} in real double evaluation`);
  },
  undef: () => NaN,
  add: (a, b) => a + b, sub: (a, b) => a - b, mul: (a, b) => a * b, neg: (a) => -a,
  div: (a, b) => (b === 0 ? NaN : a / b),
  powInt(a, n) {
    n = Number(n);
    if (a === 0 && n <= 0) return NaN;
    return Math.pow(a, n);
  },
  powRat: (a, p, q) => powRatD(a, Number(p), Number(q)),
  pow(a, b) {
    if (a === 0) return b > 0 ? 0 : NaN;
    if (a < 0 && !Number.isInteger(b)) return NaN;
    return Math.pow(a, b);
  },
  fn(name, args) {
    const f = DFN[name];
    if (!f) throw unsupported(`function ${name} in double evaluation`);
    return f(args[0]);
  },
  isZero: (a) => a === 0,
  toNumber: (a) => a,
};

// BigFloat (and complex) algebra; `wp` is the working precision in bits and may be changed
// between calls (compiled constants are re-evaluated when it changes).
const B_REAL = {
  sin: B.sin, cos: B.cos, tan: B.tan,
  cot: (x, p) => { const [s, c] = B.sincos(x, p + 16); return B.div(c, s, p); },
  sec: (x, p) => B.div(B.ONE, B.cos(x, p + 16), p),
  csc: (x, p) => B.div(B.ONE, B.sin(x, p + 16), p),
  asin: B.asin, acos: B.acos, atan: B.atan,
  acot: (x, p) => B.sub(B.mulPow2(B.pi(p + 8), -1), B.atan(x, p + 8), p),
  asec: (x, p) => B.acos(B.div(B.ONE, x, p + 16), p),
  acsc: (x, p) => B.asin(B.div(B.ONE, x, p + 16), p),
  sinh: B.sinh, cosh: B.cosh, tanh: B.tanh,
  coth: (x, p) => B.div(B.ONE, B.tanh(x, p + 16), p),
  sech: (x, p) => B.div(B.ONE, B.cosh(x, p + 16), p),
  csch: (x, p) => B.div(B.ONE, B.sinh(x, p + 16), p),
  asinh: B.asinh, acosh: B.acosh, atanh: B.atanh,
  ln: B.ln, exp: B.exp, abs: (x) => B.abs(x), sqrt: B.sqrt, cbrt: (x, p) => B.nthRoot(x, 3, p),
  floor: (x) => B.floor(x), ceil: (x) => B.ceil(x), round: (x) => B.roundInt(x), sign: (x) => B.fromInt(B.sign(x)),
  gamma: B.gamma, factorial: B.factorial, erf: B.erf, digamma: B.digamma,
};
const B_COMPLEX = {
  sin: B.csin, cos: B.ccos, exp: B.cexp, ln: B.cln, sqrt: B.csqrt,
  tan: (z, p) => B.cdiv(B.csin(z, p + 16), B.ccos(z, p + 16), p),
  abs: (z, p) => B.cabs(z, p),
};
export class BFAlgebra {
  constructor(wp = 128, mode = "real") {
    this.kind = "bigfloat";
    this.wp = wp;
    this.mode = mode;
    this.zero = B.ZERO;
    this.one = B.ONE;
    this.sumDigits = null;
  }
  get stamp() { return this.wp; }
  fromInt(n) { return B.fromInt(n); }
  num(q) { return B.fromRational(q, this.wp); }
  konst(name) {
    if (name === "pi") return B.pi(this.wp);
    if (name === "e") return B.e(this.wp);
    if (name === "I") return B.CI;
    if (name === "undef") throw undefErr("the expression contains 'undefined'");
    throw unsupported(`constant ${name} in numeric evaluation`);
  }
  undef() { throw undefErr("undefined"); }
  add(a, b) { return a instanceof Complex || b instanceof Complex ? B.cadd(a, b, this.wp) : B.add(a, b, this.wp); }
  sub(a, b) { return a instanceof Complex || b instanceof Complex ? B.csub(a, b, this.wp) : B.sub(a, b, this.wp); }
  mul(a, b) { return a instanceof Complex || b instanceof Complex ? B.cmul(a, b, this.wp) : B.mul(a, b, this.wp); }
  neg(a) { return a instanceof Complex ? B.cneg(a) : B.neg(a); }
  div(a, b) {
    if (a instanceof Complex || b instanceof Complex) return B.cdiv(a, b, this.wp);
    if (b.m === 0n) throw undefErr("division by zero");
    return B.div(a, b, this.wp);
  }
  powInt(a, n) {
    if (a instanceof Complex) return B.cpow(a, B.fromBigInt(BigInt(n)), this.wp);
    return B.powInt(a, BigInt(n), this.wp);
  }
  powRat(a, p, q) {
    const cx = a instanceof Complex || (this.mode === "complex" && a.m < 0n && BigInt(q) % 2n === 0n);
    if (cx && BigInt(q) === 2n) return B.cpow(B.csqrt(a, this.wp + 16), B.fromBigInt(BigInt(p)), this.wp);
    if (cx) {
      return B.cpow(a, B.div(B.fromBigInt(BigInt(p)), B.fromBigInt(BigInt(q)), this.wp + 16), this.wp);
    }
    return B.powRat(a, p, q, this.wp);
  }
  pow(a, b) {
    if (a instanceof Complex || b instanceof Complex) return B.cpow(a, b, this.wp);
    if (a.m < 0n && !B.isInteger(b) && this.mode === "complex") return B.cpow(a, b, this.wp);
    return B.pow(a, b, this.wp);
  }
  fn(name, args) {
    const x = args[0];
    if (x instanceof Complex) {
      if (x.im.m === 0n && B_REAL[name] && this.mode !== "complex") return this.fn(name, [x.re]);
      const f = B_COMPLEX[name];
      if (!f) throw unsupported(`function ${name} of a complex argument`);
      return f(x, this.wp);
    }
    if (this.mode === "complex" && x.m < 0n && (name === "ln" || name === "sqrt")) return B_COMPLEX[name](x, this.wp);
    const f = B_REAL[name];
    if (!f) throw unsupported(`function ${name} in BigFloat evaluation`);
    return f(x, this.wp);
  }
  isZero(a) { return a instanceof Complex ? a.re.m === 0n && a.im.m === 0n : a.m === 0n; }
  toNumber(a) {
    if (a instanceof Complex) return a.im.m === 0n ? B.toNumber(a.re) : NaN;
    return B.toNumber(a);
  }
  sumInfinite(term, n0, isProduct) {
    if (isProduct) throw unsupported("infinite products");
    const digits = this.sumDigits ?? Math.max(10, B.bitsToDigits(this.wp) - 6);
    const saved = this.wp;
    // Levin transforms amplify rounding errors: evaluate the terms at twice the precision
    this.wp = 2 * B.digitsToBits(digits) + 64;
    let r;
    try { r = levinSum(term, BigInt(n0), { digits, wp: this.wp }); } finally { this.wp = saved; }
    if (!r.converged) throw qerr("NOCONVERGE", "infinite sum did not converge numerically" + (r.warning ? ": " + r.warning : ""));
    return B.round(r.valueBF, this.wp);
  }
}

// Interval algebra (doubles, outward rounded)
const IFN = {
  sin: IV.sin, cos: IV.cos, tan: IV.tan,
  cot: (a) => IV.div(IV.cos(a), IV.sin(a)), sec: (a) => IV.div(IV.I(1), IV.cos(a)), csc: (a) => IV.div(IV.I(1), IV.sin(a)),
  asin: IV.asin, acos: IV.acos, atan: IV.atan, acot: (a) => IV.sub(IV.I(IV.nextDown(Math.PI / 2), IV.nextUp(Math.PI / 2)), IV.atan(a)),
  asec: (a) => IV.acos(IV.div(IV.I(1), a)), acsc: (a) => IV.asin(IV.div(IV.I(1), a)),
  sinh: IV.sinh, cosh: IV.cosh, tanh: IV.tanh,
  coth: (a) => IV.div(IV.I(1), IV.tanh(a)), sech: (a) => IV.div(IV.I(1), IV.cosh(a)), csch: (a) => IV.div(IV.I(1), IV.sinh(a)),
  asinh: IV.asinh, acosh: IV.acosh, atanh: IV.atanh,
  ln: IV.ln, exp: IV.exp, abs: IV.abs, sqrt: IV.sqrt, cbrt: (a) => IV.root(a, 3),
  floor: IV.floor, ceil: IV.ceil, round: IV.round, sign: IV.sign,
  erf: IV.erfMono(erfD), gamma: IV.gammaWith(gammaD), factorial: (a) => IV.gammaWith(gammaD)(IV.add(a, IV.I(1))),
  digamma: (a) => {
    if (IV.isEmpty(a)) return IV.EMPTY;
    if (a.lo <= 0) return IV.entire(false, false);
    const lo = digammaD(a.lo), hi = digammaD(a.hi);
    return IV.I(lo - 1e-13 * (1 + Math.abs(lo)), hi + 1e-13 * (1 + Math.abs(hi)), a.def, a.cont);
  },
};
export const INTERVAL = {
  kind: "interval", stamp: 0, zero: IV.I(0), one: IV.I(1),
  fromInt: (n) => IV.I(Number(n)),
  num: (q) => IV.fromRational(q),
  konst(name) {
    if (name === "pi") return IV.I(IV.nextDown(Math.PI), IV.nextUp(Math.PI));
    if (name === "e") return IV.I(IV.nextDown(Math.E), IV.nextUp(Math.E));
    if (name === "undef") return IV.EMPTY;
    throw unsupported(`constant ${name} in interval evaluation`);
  },
  undef: () => IV.EMPTY,
  add: IV.add, sub: IV.sub, mul: IV.mul, neg: IV.neg, div: IV.div,
  powInt: (a, n) => IV.powInt(a, Number(n)),
  powRat: (a, p, q) => IV.powRat(a, Number(p), Number(q)),
  pow: IV.pow,
  fn(name, args) {
    const f = IFN[name];
    if (!f) return IV.entire(false, false);
    return f(args[0]);
  },
  isZero: (a) => a.lo === 0 && a.hi === 0,
  toNumber: (a) => (a.lo === a.hi ? a.lo : NaN),
};

// Forward-mode automatic differentiation: dual numbers { v, d } over any base algebra.
export function makeDual(Bs) {
  const c = (v) => ({ v, d: Bs.zero });
  const Z = Bs.zero;
  const zeroD = (a) => Bs.isZero(a.d);
  const A = {
    kind: `dual(${Bs.kind})`, base: Bs,
    get stamp() { return Bs.stamp; },
    zero: c(Bs.zero), one: c(Bs.one),
    fromInt: (n) => c(Bs.fromInt(n)),
    num: (q) => c(Bs.num(q)),
    konst: (name) => c(Bs.konst(name)),
    undef: () => c(Bs.undef()),
    add: (a, b) => ({ v: Bs.add(a.v, b.v), d: Bs.add(a.d, b.d) }),
    sub: (a, b) => ({ v: Bs.sub(a.v, b.v), d: Bs.sub(a.d, b.d) }),
    neg: (a) => ({ v: Bs.neg(a.v), d: Bs.neg(a.d) }),
    mul(a, b) {
      const v = Bs.mul(a.v, b.v);
      if (zeroD(a) && zeroD(b)) return { v, d: Z };
      if (zeroD(a)) return { v, d: Bs.mul(a.v, b.d) };
      if (zeroD(b)) return { v, d: Bs.mul(a.d, b.v) };
      return { v, d: Bs.add(Bs.mul(a.d, b.v), Bs.mul(a.v, b.d)) };
    },
    div(a, b) {
      const v = Bs.div(a.v, b.v);
      if (zeroD(a) && zeroD(b)) return { v, d: Z };
      return { v, d: Bs.div(Bs.sub(a.d, Bs.mul(v, b.d)), b.v) };
    },
    powInt(a, n) {
      n = BigInt(n);
      const v = Bs.powInt(a.v, n);
      if (n === 0n || zeroD(a)) return { v, d: Z };
      if (n === 1n) return { v, d: a.d };
      return { v, d: Bs.mul(Bs.mul(Bs.fromInt(n), Bs.powInt(a.v, n - 1n)), a.d) };
    },
    powRat(a, p, q) {
      p = BigInt(p); q = BigInt(q);
      const v = Bs.powRat(a.v, p, q);
      if (zeroD(a)) return { v, d: Z };
      const k = Bs.div(Bs.fromInt(p), Bs.fromInt(q));
      return { v, d: Bs.mul(Bs.mul(k, Bs.powRat(a.v, p - q, q)), a.d) };
    },
    pow(a, b) {
      const v = Bs.pow(a.v, b.v);
      if (zeroD(b)) {
        if (zeroD(a)) return { v, d: Z };
        return { v, d: Bs.mul(Bs.mul(b.v, Bs.pow(a.v, Bs.sub(b.v, Bs.one))), a.d) };
      }
      const t = Bs.mul(b.d, Bs.fn("ln", [a.v]));
      const u = zeroD(a) ? t : Bs.add(t, Bs.div(Bs.mul(b.v, a.d), a.v));
      return { v, d: Bs.mul(v, u) };
    },
    fn(name, args) {
      const a = args[0];
      const v = Bs.fn(name, [a.v]);
      if (zeroD(a)) return { v, d: Z };
      const x = a.v, one = Bs.one;
      const sq = (t) => Bs.mul(t, t);
      let g;
      switch (name) {
        case "sin": g = Bs.fn("cos", [x]); break;
        case "cos": g = Bs.neg(Bs.fn("sin", [x])); break;
        case "tan": g = Bs.add(one, sq(v)); break;
        case "cot": g = Bs.neg(Bs.add(one, sq(v))); break;
        case "sec": g = Bs.mul(v, Bs.fn("tan", [x])); break;
        case "csc": g = Bs.neg(Bs.mul(v, Bs.fn("cot", [x]))); break;
        case "asin": g = Bs.div(one, Bs.fn("sqrt", [Bs.sub(one, sq(x))])); break;
        case "acos": g = Bs.neg(Bs.div(one, Bs.fn("sqrt", [Bs.sub(one, sq(x))]))); break;
        case "atan": g = Bs.div(one, Bs.add(one, sq(x))); break;
        case "acot": g = Bs.neg(Bs.div(one, Bs.add(one, sq(x)))); break;
        case "sinh": g = Bs.fn("cosh", [x]); break;
        case "cosh": g = Bs.fn("sinh", [x]); break;
        case "tanh": g = Bs.sub(one, sq(v)); break;
        case "asinh": g = Bs.div(one, Bs.fn("sqrt", [Bs.add(sq(x), one)])); break;
        case "acosh": g = Bs.div(one, Bs.fn("sqrt", [Bs.sub(sq(x), one)])); break;
        case "atanh": g = Bs.div(one, Bs.sub(one, sq(x))); break;
        case "ln": g = Bs.div(one, x); break;
        case "exp": g = v; break;
        case "abs": g = Bs.fn("sign", [x]); break;
        case "sqrt": g = Bs.div(one, Bs.mul(Bs.fromInt(2), v)); break;
        case "cbrt": g = Bs.div(one, Bs.mul(Bs.fromInt(3), sq(v))); break;
        case "floor": case "ceil": case "round": case "sign": return { v, d: Z };
        case "gamma": g = Bs.mul(v, Bs.fn("digamma", [x])); break;
        case "factorial": g = Bs.mul(v, Bs.fn("digamma", [Bs.add(x, one)])); break;
        case "erf": g = Bs.mul(Bs.div(Bs.fromInt(2), Bs.fn("sqrt", [Bs.konst("pi")])), Bs.fn("exp", [Bs.neg(sq(x))])); break;
        default: throw unsupported(`derivative of ${name}`);
      }
      return { v, d: Bs.mul(g, a.d) };
    },
    isZero: (a) => Bs.isZero(a.v) && Bs.isZero(a.d),
    toNumber: (a) => Bs.toNumber(a.v),
  };
  return A;
}
// Tower of nested duals: level 0 = base, level k = dual^k(base).
function tower(base, k) {
  const t = [base];
  for (let i = 1; i <= k; i++) t.push(makeDual(t[i - 1]));
  return t;
}
function seed(T, level, x) {
  if (level === 0) return x;
  return { v: seed(T, level - 1, x), d: T[level - 1].one };
}
// k-th derivative component of a level-L tower value
function pick(r, k, L) {
  for (let i = 0; i < k; i++) r = r.d;
  for (let i = k; i < L; i++) r = r.v;
  return r;
}

// ---------------------------------------------------------------------------------------
// compiler: tree -> closures over an algebra
// ---------------------------------------------------------------------------------------
const MAX_SUM_TERMS = 1_000_000;
// Exact value of a constant tree built from rationals with +, * and small integer powers, else null.
function ratConst(u, depth = 0) {
  if (depth > 12) return null;
  if (u.k === "num") return u.v;
  if (u.k === "add" || u.k === "mul") {
    let acc = u.k === "add" ? Nq.ZERO : Nq.ONE;
    for (const a of u.args) { const r = ratConst(a, depth + 1); if (!r) return null; acc = u.k === "add" ? Nq.add(acc, r) : Nq.mul(acc, r); }
    return acc;
  }
  if (u.k === "pow" && u.args[1].k === "num" && u.args[1].v.d === 1n && u.args[1].v.n >= -8n && u.args[1].v.n <= 8n) {
    const b = ratConst(u.args[0], depth + 1);
    if (!b || (Nq.isZero(b) && u.args[1].v.n < 0n)) return null;
    return Nq.pow(b, u.args[1].v.n);
  }
  return null;
}

function compile(node, vars, A) {
  const slots = new Map(vars.map((v, i) => [v, i]));
  let nslots = vars.length;
  const memoConst = (make) => {
    let st, cv, have = false;
    return () => {
      if (!have || st !== A.stamp) { cv = make(); st = A.stamp; have = true; }
      return cv;
    };
  };
  const foldMul = (fs) => (env) => {
    let r = fs[0](env);
    for (let i = 1; i < fs.length; i++) r = A.mul(r, fs[i](env));
    return r;
  };
  function c(u) {
    switch (u.k) {
      case "num": { const q = u.v; return memoConst(() => A.num(q)); }
      case "const": {
        const name = u.name;
        if (name === "undef") return () => A.undef();
        if (name === "oo") throw unsupported("infinity inside an expression to evaluate");
        return memoConst(() => A.konst(name));
      }
      case "sym": {
        if (!slots.has(u.name)) throw qerr("UNBOUND", `no value for symbol ${u.name}`);
        const i = slots.get(u.name);
        return (env) => env[i];
      }
      case "add": {
        const pos = [], negs = [];
        for (const t of u.args) {
          if (t.k === "mul" && t.args[0].k === "num" && t.args[0].v.n === -1n && t.args[0].v.d === 1n) {
            const rest = t.args.slice(1);
            negs.push(c(rest.length === 1 ? rest[0] : X.mul(...rest)));
          } else pos.push(c(t));
        }
        return (env) => {
          let s = pos.length ? pos[0](env) : A.neg(negs[0](env));
          for (let i = 1; i < pos.length; i++) s = A.add(s, pos[i](env));
          for (let i = pos.length ? 0 : 1; i < negs.length; i++) s = A.sub(s, negs[i](env));
          return s;
        };
      }
      case "mul": {
        let negate = false;
        const numF = [], denF = [];
        for (const f of u.args) {
          if (f.k === "num" && f.v.n === -1n && f.v.d === 1n) { negate = !negate; continue; }
          if (f.k === "num" && f.v.n === 1n && f.v.d === 1n) continue;
          if (f.k === "pow" && f.args[1].k === "num" && f.args[1].v.n < 0n) {
            const e = f.args[1].v;
            denF.push(c(e.n === -1n && e.d === 1n ? f.args[0] : X.pow(f.args[0], X.num(Nq.neg(e)))));
          } else numF.push(c(f));
        }
        const nf = numF.length ? foldMul(numF) : () => A.one;
        const df = denF.length ? foldMul(denF) : null;
        const core = df ? (env) => A.div(nf(env), df(env)) : nf;
        return negate ? (env) => A.neg(core(env)) : core;
      }
      case "pow": {
        const [b, e0] = u.args;
        if (b.k === "const" && b.name === "e") { const ce = c(e0); return (env) => A.fn("exp", [ce(env)]); }
        const cb = c(b);
        // an unsimplified rational exponent ((x+6)^(1/3) parses as 1 * 3^-1) is still a rational, so
        // the real odd root applies, not the complex principal value
        const er = e0.k === "num" ? null : ratConst(e0);
        const e = er ? X.num(er) : e0;
        if (e.k === "num") {
          const { n, d } = e.v;
          if (d === 1n) return (env) => A.powInt(cb(env), n);
          if (d <= 1000n) return (env) => A.powRat(cb(env), n, d);
        }
        const ce = c(e);
        return (env) => A.pow(cb(env), ce(env));
      }
      case "fn": {
        const name = u.name;
        const args = u.args.map(c);
        if (name === "log") {
          if (args.length === 1) {
            const ten = memoConst(() => A.fn("ln", [A.fromInt(10)]));
            return (env) => A.div(A.fn("ln", [args[0](env)]), ten());
          }
          return (env) => A.div(A.fn("ln", [args[1](env)]), A.fn("ln", [args[0](env)]));
        }
        if (name === "root") {
          const n = u.args[1];
          if (n.k === "num" && n.v.d === 1n && n.v.n > 0n) return (env) => A.powRat(args[0](env), 1n, n.v.n);
          return (env) => A.pow(args[0](env), A.div(A.one, args[1](env)));
        }
        if (name === "cbrt") return (env) => A.powRat(args[0](env), 1n, 3n);
        if (args.length !== 1) throw unsupported(`function ${name} with ${args.length} arguments`);
        const a0 = args[0];
        return (env) => A.fn(name, [a0(env)]);
      }
      case "sum": case "product": {
        const [body, v, lo, hi] = u.args;
        const isProd = u.k === "product";
        const clo = c(lo);
        const infinite = hi.k === "const" && hi.name === "oo";
        const chi = infinite ? null : c(hi);
        const prev = slots.get(v.name);
        const slot = nslots++;
        slots.set(v.name, slot);
        const cb = c(body);
        if (prev === undefined) slots.delete(v.name); else slots.set(v.name, prev);
        return (env) => {
          const a = A.toNumber(clo(env));
          if (!Number.isInteger(a)) throw unsupported("sum/product bounds must be integers");
          if (infinite) {
            if (!A.sumInfinite) throw unsupported(`infinite ${u.k} in ${A.kind} evaluation`);
            return A.sumInfinite((k) => { env[slot] = A.fromInt(k); return cb(env); }, a, isProd);
          }
          const b = A.toNumber(chi(env));
          if (!Number.isInteger(b)) throw unsupported("sum/product bounds must be integers");
          if (b - a + 1 > MAX_SUM_TERMS) throw qerr("BUDGET", "finite sum has too many terms");
          let acc = isProd ? A.one : A.zero;
          for (let k = a; k <= b; k++) {
            env[slot] = A.fromInt(k);
            acc = isProd ? A.mul(acc, cb(env)) : A.add(acc, cb(env));
          }
          return acc;
        };
      }
      case "eq": throw unsupported("an equation is not an expression to evaluate (use lhs - rhs)");
      default: throw unsupported(`cannot evaluate a ${u.k} node numerically`);
    }
  }
  const f = c(node);
  const n = () => nslots;
  return (args) => {
    const env = new Array(n());
    for (let i = 0; i < args.length; i++) env[i] = args[i];
    return f(env);
  };
}
const COMPILED = new WeakMap();
function compileCached(node, vars, A, key) {
  let m = COMPILED.get(node);
  if (!m) { m = new Map(); COMPILED.set(node, m); }
  const k = key + "|" + vars.join(",");
  let f = m.get(k);
  if (!f) { f = compile(node, vars, A); m.set(k, f); }
  return f;
}
const eqToExpr = (node) => (node.k === "eq" ? X.sub(node.args[0], node.args[1]) : node);
const varName = (x) => (typeof x === "string" ? x : x && x.k === "sym" ? x.name : String(x));

// Fast double evaluator. Returns NaN exactly at undefined points (division by zero, log of
// a non-positive number, even root of a negative, 0^0, outside asin/acos domains ...).
export function compileDouble(node, vars = []) {
  node = eqToExpr(node);
  const names = vars.map(varName);
  const f = compile(node, names, DOUBLE);
  return (...args) => {
    const r = f(args);
    return typeof r === "number" ? r : NaN;
  };
}
// Double dual evaluator: (x) => [f(x), f'(x)] for one variable.
export function compileDual(node, x) {
  node = eqToExpr(node);
  const T = tower(DOUBLE, 1);
  const f = compile(node, [varName(x)], T[1]);
  return (xv) => { const r = f([seed(T, 1, xv)]); return [r.v, r.d]; };
}
function toBFValue(v, wp) {
  if (v instanceof BigFloat || v instanceof Complex) return v;
  if (typeof v === "object" && v && v.k === "num") return B.fromRational(v.v, wp);
  return B.from(v, wp);
}
// BigFloat / complex evaluation. env: Map or object name -> number | string | Rational |
// BigFloat | Complex. Returns BigFloat | Complex, or an UNDEFINED marker (never NaN).
export function evalTree(node, env = {}, opts = {}) {
  node = eqToExpr(node);
  const digits = opts.digits ?? 30;
  const wp = opts.bits ?? B.digitsToBits(digits) + 24;
  const m = env instanceof Map ? env : new Map(Object.entries(env));
  const names = [...X.freeSymbols(node)];
  for (const n of names) if (!m.has(n)) throw qerr("UNBOUND", `no value for symbol ${n}`);
  const A = new BFAlgebra(wp, opts.mode || "real");
  try {
    const f = compile(node, names, A);
    return f(names.map((n) => toBFValue(m.get(n), wp)));
  } catch (e) {
    if (isUndefCode(e)) return makeUndefined(e.message.replace(/^Quelvra: /, ""));
    throw e;
  }
}
export function evalDouble(node, env = {}) {
  const m = env instanceof Map ? env : new Map(Object.entries(env));
  const names = [...X.freeSymbols(eqToExpr(node))];
  return compileDouble(node, names)(...names.map((n) => Number(m.get(n))));
}
// Interval evaluation; env values are numbers, [lo, hi] pairs or interval objects.
export function evalInterval(node, env = {}) {
  node = eqToExpr(node);
  const m = env instanceof Map ? env : new Map(Object.entries(env));
  const names = [...X.freeSymbols(node)];
  const toI = (v) => (Array.isArray(v) ? IV.I(v[0], v[1]) : typeof v === "number" ? IV.I(v) : v);
  const f = compile(node, names, INTERVAL);
  return f(names.map((n) => {
    if (!m.has(n)) throw qerr("UNBOUND", `no value for symbol ${n}`);
    return toI(m.get(n));
  }));
}

// ---------------------------------------------------------------------------------------
// N(): constant expression to requested digits with precision doubling
// ---------------------------------------------------------------------------------------
const cabsBF = (v, wp) => (v instanceof Complex ? B.cabs(v, wp) : B.abs(v));
const diffBF = (a, b, wp) => (a instanceof Complex || b instanceof Complex ? B.cabs(B.csub(a, b, wp), wp) : B.abs(B.sub(a, b, wp)));
function formatValue(v, digits, errBF, warnings) {
  if (!(v instanceof Complex)) return B.toString(v, digits);
  const re = v.re, im = v.im;
  const parts = [];
  const mag = B.cabs(v, 64);
  const kMag = decExp(mag);
  const show = (x) => {
    if (x.m === 0n) return null;
    if (errBF && B.cmp(B.abs(x), errBF) <= 0) return null;
    const d = digits - (kMag - decExp(x));
    return d >= 1 ? B.toString(x, d) : null;
  };
  const rs = show(re), is = show(B.abs(im));
  if (!is && im.m !== 0n) warnings.push("The imaginary part is below the error bound and is not shown.");
  if (!rs && re.m !== 0n && is) warnings.push("The real part is below the error bound and is not shown.");
  if (rs) parts.push(rs);
  if (is) {
    const t = (is === "1" ? "" : is) + "i";
    if (!parts.length) parts.push((im.m < 0n ? "-" : "") + t);
    else parts.push((im.m < 0n ? " - " : " + ") + t);
  }
  return parts.length ? parts.join("") : "0";
}
export function N(node, digits = 15, opts = {}) {
  node = eqToExpr(node);
  const requested = Math.max(1, Math.floor(digits));
  const fs = X.freeSymbols(node);
  if (fs.size) throw qerr("NOT_CONSTANT", `N() needs a constant expression; free symbols: ${[...fs].join(", ")}`);
  const base = B.digitsToBits(requested) + 24;
  const maxBits = opts.maxBits ?? Math.max(4 * base, base + 1024);
  const dl = deadline(opts.timeLimitMs ?? 5000);
  const A = new BFAlgebra(base, opts.mode || "real");
  let f;
  try { f = compile(node, [], A); } catch (e) {
    if (isUndefCode(e)) return undefinedRecord(requested, e.message, 0);
    throw e;
  }
  const warnings = [];
  let bits = base, prev = null, prevBits = 0, iterations = 0;
  const run = () => {
    try { return f([]); } catch (e) {
      if (isUndefCode(e)) return makeUndefined(e.message.replace(/^Quelvra: /, ""));
      if (e.code === "NOCONVERGE") return { kind: "noconverge", reason: e.message };
      if (e.code === "UNDERFLOW") return { kind: "noconverge", reason: e.message + "; the value is 0 to within that bound but its digits cannot be computed" };
      throw e;
    }
  };
  for (;;) {
    iterations++;
    A.wp = bits;
    A.sumDigits = B.bitsToDigits(bits) - 8;
    const v = run();
    if (v && v.kind === "noconverge") {
      return record({ value: "", digits: 0, requested, errorBound: null, method: "evaluation", iterations, converged: false, warnings: [v.reason.replace(/^Quelvra: /, "")] });
    }
    if (isUndefined(v)) {
      if (prev && isUndefined(prev)) return undefinedRecord(requested, v.reason, iterations);
      if (prev) warnings.push("The expression was defined at one precision and undefined at another; the value is not reliable.");
    } else if (prev && !isUndefined(prev)) {
      const wp = bits + 16;
      const diff = diffBF(v, prev, wp);
      const mag = cabsBF(v, wp);
      const pmag = cabsBF(prev, wp);
      const tinyNow = mag.m === 0n || B.top(mag) < -(bits - 32);
      const tinyPrev = pmag.m === 0n || B.top(pmag) < -(prevBits - 32);
      if (mag.m === 0n && pmag.m === 0n) {
        return record({ value: "0", digits: requested, requested, errorBound: "0", method: "multiprecision evaluation", iterations, converged: true, warnings });
      }
      if (tinyNow && tinyPrev) {
        const eb = B.mulPow2(B.max(mag, pmag), 1);
        warnings.push("The value is 0 to within errorBound (absolute); relative precision cannot be certified numerically (the exact value may be 0).");
        return record({ value: "0", digits: 0, requested, errorBound: fmtErr(eb), method: "multiprecision evaluation", iterations, converged: false, warnings });
      }
      if (mag.m !== 0n) {
        const k = decExp(mag);
        const ulp = pow10(k - requested + 1, wp);
        // agreement: difference below 1/10 of the last displayed digit
        if (B.cmp(B.mul(diff, B.fromInt(10), wp), ulp) <= 0) {
          const eb = B.add(diff, B.mulPow2(ulp, -1), wp);
          return record({
            value: formatValue(v, requested, diff, warnings), digits: requested, requested, errorBound: fmtErr(eb),
            method: "multiprecision evaluation (precision doubling)", iterations, converged: true, warnings,
          });
        }
      }
    }
    if (bits >= maxBits || dl.expired()) {
      if (isUndefined(v)) return undefinedRecord(requested, v.reason, iterations);
      if (!prev || isUndefined(prev)) {
        warnings.push("Only one evaluation completed; no error estimate.");
        return record({ value: formatValue(v, Math.min(requested, 6), null, warnings), digits: 0, requested, errorBound: null, method: "multiprecision evaluation", iterations, converged: false, warnings });
      }
      const wp = bits + 16;
      const diff = diffBF(v, prev, wp);
      const mag = cabsBF(v, wp);
      const got = digitsFrom(mag, diff, requested);
      warnings.push(dl.expired() ? "Time limit reached before the requested precision was confirmed." : "Evaluations at increasing precision did not agree to the requested digits (possible cancellation, discontinuity or exact zero).");
      return record({
        value: formatValue(v, Math.max(1, got), diff, warnings), digits: got, requested, errorBound: fmtErr(diff),
        method: "multiprecision evaluation (precision doubling)", iterations, converged: false, warnings,
      });
    }
    prev = v;
    prevBits = bits;
    bits = Math.min(maxBits, bits * 2);
  }
}
function undefinedRecord(requested, reason, iterations) {
  return record({
    value: "undefined", digits: 0, requested, errorBound: null, method: "multiprecision evaluation", iterations,
    converged: true, warnings: [`The expression is undefined: ${String(reason).replace(/^Quelvra: /, "")}`],
  });
}

// ---------------------------------------------------------------------------------------
// scalar root finders (double precision)
// ---------------------------------------------------------------------------------------
function asFn(f, opts = {}) {
  if (typeof f === "function") return { f, df: opts.df || null };
  const node = eqToExpr(f);
  let name = opts.x ? varName(opts.x) : null;
  if (!name) {
    const fs = [...X.freeSymbols(node)];
    if (fs.length !== 1) throw qerr("UNBOUND", "specify the variable with opts.x");
    name = fs[0];
  }
  const fd = compileDual(node, name);
  return { f: compileDouble(node, [name]), df: (x) => fd(x)[1], node, name };
}
function rootRecord(x, errAbs, requested, method, iterations, converged, warnings, extra = {}) {
  const req = Math.min(requested, 17);
  let digits = 0;
  if (Number.isFinite(x) && Number.isFinite(errAbs)) {
    if (x === 0) digits = errAbs === 0 ? req : 0;
    else digits = errAbs === 0 ? req : Math.max(0, Math.min(req, Math.floor(-Math.log10(errAbs / Math.abs(x)))));
  }
  const r = record({
    value: Number.isFinite(x) ? fmtNum(x, Math.max(1, digits || 1)) : "undefined", digits, requested,
    errorBound: Number.isFinite(errAbs) ? fmtErr(errAbs + (x !== 0 ? Math.abs(x) * 10 ** -Math.max(1, digits) / 2 : 0)) : null,
    method, iterations, converged, warnings,
  });
  return Object.assign(r, extra);
}
export function bisection(f, a, b, opts = {}) {
  ({ f } = asFn(f, opts));
  const maxIter = opts.maxIter ?? 200;
  let fa = f(a), fb = f(b);
  const warnings = [];
  if (!(fa * fb <= 0)) {
    return rootRecord(NaN, NaN, opts.digits ?? 15, "bisection", 0, false, ["f(a) and f(b) do not have opposite signs"], { x: NaN });
  }
  if (fa === 0) return rootRecord(a, 0, opts.digits ?? 15, "bisection", 0, true, [], { x: a, fx: 0 });
  if (fb === 0) return rootRecord(b, 0, opts.digits ?? 15, "bisection", 0, true, [], { x: b, fx: 0 });
  let it = 0;
  for (; it < maxIter; it++) {
    const m = a + (b - a) / 2;
    if (m === a || m === b) break;
    const fm = f(m);
    if (Number.isNaN(fm)) { warnings.push("function undefined inside the bracket"); break; }
    if (fm === 0) { a = b = m; break; }
    if ((fm < 0) === (fa < 0)) { a = m; fa = fm; } else { b = m; fb = fm; }
  }
  const x = a + (b - a) / 2;
  const w = Math.abs(b - a) / 2;
  return rootRecord(x, w, opts.digits ?? 15, "bisection", it, it < maxIter && !warnings.length, warnings, { x, fx: f(x), bracket: [a, b] });
}
export function brent(f, a, b, opts = {}) {
  ({ f } = asFn(f, opts));
  const maxIter = opts.maxIter ?? 200;
  const tol = opts.tol ?? 2 * EPS;
  let fa = f(a), fb = f(b);
  if (!(fa * fb <= 0)) {
    return rootRecord(NaN, NaN, opts.digits ?? 15, "brent", 0, false, ["f(a) and f(b) do not have opposite signs"], { x: NaN });
  }
  if (fa === 0) return rootRecord(a, 0, opts.digits ?? 15, "brent", 0, true, [], { x: a, fx: 0, bracket: [a, a], fa: 0, fb: 0 });
  if (fb === 0) return rootRecord(b, 0, opts.digits ?? 15, "brent", 0, true, [], { x: b, fx: 0, bracket: [b, b], fa: 0, fb: 0 });
  let c = a, fc = fa, d = b - a, e = d;
  let it = 0, converged = false;
  const warnings = [];
  for (; it < maxIter; it++) {
    if ((fb > 0 && fc > 0) || (fb < 0 && fc < 0)) { c = a; fc = fa; d = b - a; e = d; }
    if (Math.abs(fc) < Math.abs(fb)) { a = b; b = c; c = a; fa = fb; fb = fc; fc = fa; }
    const tol1 = 2 * EPS * Math.abs(b) + 0.5 * tol * Math.max(Math.abs(b), 1e-300);
    const xm = 0.5 * (c - b);
    if (Math.abs(xm) <= tol1 || fb === 0) { converged = true; break; }
    if (Math.abs(e) >= tol1 && Math.abs(fa) > Math.abs(fb)) {
      const s = fb / fa;
      let p, q;
      if (a === c) { p = 2 * xm * s; q = 1 - s; } else {
        const qq = fa / fc, r = fb / fc;
        p = s * (2 * xm * qq * (qq - r) - (b - a) * (r - 1));
        q = (qq - 1) * (r - 1) * (s - 1);
      }
      if (p > 0) q = -q;
      p = Math.abs(p);
      if (2 * p < Math.min(3 * xm * q - Math.abs(tol1 * q), Math.abs(e * q))) { e = d; d = p / q; } else { d = xm; e = d; }
    } else { d = xm; e = d; }
    a = b; fa = fb;
    b += Math.abs(d) > tol1 ? d : xm > 0 ? tol1 : -tol1;
    fb = f(b);
    if (Number.isNaN(fb)) { warnings.push("function undefined inside the bracket"); break; }
  }
  const lo = Math.min(b, c), hi = Math.max(b, c);
  return rootRecord(b, Math.abs(c - b), opts.digits ?? 15, "brent", it, converged, warnings,
    { x: b, fx: fb, bracket: [lo, hi], fa: b <= c ? fb : fc, fb: b <= c ? fc : fb });
}
export function secant(f, x0, x1, opts = {}) {
  ({ f } = asFn(f, opts));
  const maxIter = opts.maxIter ?? 100, tol = opts.tol ?? 4 * EPS;
  let f0 = f(x0), f1 = f(x1), it = 0, converged = false, step = Infinity;
  const warnings = [];
  for (; it < maxIter; it++) {
    if (f1 === 0) { converged = true; step = 0; break; }
    if (f1 === f0) { warnings.push("secant slope vanished"); break; }
    step = (f1 * (x1 - x0)) / (f1 - f0);
    x0 = x1; f0 = f1; x1 -= step; f1 = f(x1);
    if (!Number.isFinite(f1)) { warnings.push("iteration left the domain of f"); break; }
    if (Math.abs(step) <= tol * Math.max(1, Math.abs(x1))) { converged = true; break; }
  }
  if (!converged && !warnings.length) warnings.push("iteration limit reached");
  return rootRecord(x1, Math.abs(step), opts.digits ?? 15, "secant", it + 1, converged, warnings, { x: x1, fx: f1 });
}
function numDeriv(f, x) {
  const h = Math.cbrt(EPS) * Math.max(1, Math.abs(x));
  return (f(x + h) - f(x - h)) / (2 * h);
}
export function newton(f, x0, opts = {}) {
  const F = asFn(f, opts);
  const df = F.df || ((x) => numDeriv(F.f, x));
  const maxIter = opts.maxIter ?? 100, tol = opts.tol ?? 4 * EPS;
  let x = x0, it = 0, converged = false, step = Infinity;
  const warnings = [];
  for (; it < maxIter; it++) {
    const fx = F.f(x), d = df(x);
    if (fx === 0) { converged = true; step = 0; break; }
    if (!Number.isFinite(fx) || !Number.isFinite(d)) { warnings.push("iteration left the domain of f"); break; }
    if (d === 0) { warnings.push("zero derivative"); break; }
    step = fx / d;
    x -= step;
    if (Math.abs(step) <= tol * Math.max(1, Math.abs(x))) { converged = true; break; }
  }
  if (!converged && !warnings.length) warnings.push("iteration limit reached");
  return rootRecord(x, Math.abs(step), opts.digits ?? 15, F.df ? "newton (automatic differentiation)" : "newton (numerical derivative)", it + 1, converged, warnings, { x, fx: F.f(x) });
}
// Newton's method kept inside a sign-change bracket, falling back to bisection (rtsafe).
export function safeguardedNewton(f, a, b, opts = {}) {
  const F = asFn(f, opts);
  const df = F.df || ((x) => numDeriv(F.f, x));
  const maxIter = opts.maxIter ?? 200;
  let fa = F.f(a), fb = F.f(b);
  if (!(fa * fb <= 0)) return rootRecord(NaN, NaN, opts.digits ?? 15, "safeguarded newton", 0, false, ["f(a) and f(b) do not have opposite signs"], { x: NaN });
  if (fa === 0) return rootRecord(a, 0, opts.digits ?? 15, "safeguarded newton", 0, true, [], { x: a, fx: 0 });
  if (fb === 0) return rootRecord(b, 0, opts.digits ?? 15, "safeguarded newton", 0, true, [], { x: b, fx: 0 });
  let lo = fa < 0 ? a : b, hi = fa < 0 ? b : a;
  let x = 0.5 * (a + b), dxold = Math.abs(b - a), dx = dxold;
  let fx = F.f(x), d = df(x), it = 0, converged = false;
  const warnings = [];
  for (; it < maxIter; it++) {
    if (!Number.isFinite(fx)) { warnings.push("function undefined inside the bracket"); break; }
    const newtonOut = ((x - hi) * d - fx) * ((x - lo) * d - fx) > 0 || !Number.isFinite(d);
    if (newtonOut || Math.abs(2 * fx) > Math.abs(dxold * d)) {
      dxold = dx; dx = 0.5 * (hi - lo); x = lo + dx;
    } else {
      dxold = dx; dx = fx / d; x -= dx;
    }
    if (Math.abs(dx) <= 2 * EPS * Math.max(1, Math.abs(x))) { converged = true; break; }
    fx = F.f(x); d = df(x);
    if (fx === 0) { converged = true; dx = 0; break; }
    if (fx < 0) lo = x; else hi = x;
  }
  return rootRecord(x, Math.abs(dx), opts.digits ?? 15, "safeguarded newton", it + 1, converged, warnings, { x, fx: F.f(x) });
}

// ---------------------------------------------------------------------------------------
// function objects for the root finder: f^(order) in double, dual, interval and BigFloat
// ---------------------------------------------------------------------------------------
export function makeFuncs(node, x, order = 0, mode = "real") {
  node = eqToExpr(node);
  const name = varName(x);
  const vars = [name];
  const TD = tower(DOUBLE, order + 1);
  const d0 = compile(node, vars, TD[order]);
  const d1 = compile(node, vars, TD[order + 1]);
  let TI = null, i0 = null;
  try { TI = tower(INTERVAL, order); i0 = compile(node, vars, TI[order]); } catch (_) { i0 = null; }
  const BA = new BFAlgebra(128, mode);
  const TB = tower(BA, order + 2);
  const b0 = compile(node, vars, TB[order]);
  const b1 = compile(node, vars, TB[order + 1]);
  const num = (r) => (typeof r === "number" ? r : NaN);
  const safeD = (fn) => { try { return fn(); } catch (e) { if (isUndefCode(e)) return NaN; throw e; } };
  return {
    order, name,
    f: (xv) => safeD(() => num(pick(d0([seed(TD, order, xv)]), order, order))),
    fd: (xv) => safeD(() => { const r = d1([seed(TD, order + 1, xv)]); return [num(pick(r, order, order + 1)), num(pick(r, order + 1, order + 1))]; }),
    fi(lo, hi) {
      if (!i0) return IV.entire(false, false);
      try {
        const r = i0([seed(TI, order, IV.I(Math.min(lo, hi), Math.max(lo, hi)))]);
        return pick(r, order, order);
      } catch (e) { return IV.entire(false, false); }
    },
    bf(xb, wp) { BA.wp = wp; return pick(b0([seed(TB, order, xb)]), order, order); },
    bfd(xb, wp) { BA.wp = wp; const r = b1([seed(TB, order + 1, xb)]); return [pick(r, order, order + 1), pick(r, order + 1, order + 1)]; },
    // k-th derivative of f^(order) in BigFloat (lazily compiled nested duals)
    bfk(xb, wp, k) {
      const L = order + k;
      if (!this._bk) this._bk = new Map();
      let e = this._bk.get(L);
      if (!e) { const T = tower(BA, L); e = { T, f: compile(node, vars, T[L]) }; this._bk.set(L, e); }
      BA.wp = wp;
      return pick(e.f([seed(e.T, L, xb)]), L, L);
    },
  };
}
const safeBF = (fn) => { try { return fn(); } catch (e) { if (isUndefCode(e)) return null; throw e; } };

// ---------------------------------------------------------------------------------------
// findRoots: all real roots on [lo, hi]
// ---------------------------------------------------------------------------------------
const sgn = (v) => (v > 0 ? 1 : v < 0 ? -1 : 0);
export function findRoots(node, x, opts = {}) {
  const F = makeFuncs(node, x, 0, "real");
  return findRootsF(F, opts);
}
function findRootsF(F, opts = {}) {
  const lo = Number(opts.lo ?? -10), hi = Number(opts.hi ?? 10);
  if (!(Number.isFinite(lo) && Number.isFinite(hi) && lo < hi)) throw qerr("BAD_INPUT", "findRoots needs a finite window lo < hi");
  const digits = Math.max(1, Math.floor(opts.digits ?? 15));
  const maxRoots = opts.maxRoots ?? 100;
  const n = Math.max(8, Math.floor(opts.samples ?? 400));
  const maxDepth = opts.maxDepth ?? 4;
  const maxEvals = opts.maxEvals ?? 150000;
  const dl = deadline(opts.timeLimitMs ?? 20000);
  const warnings = [];
  let evals = 0, budgetHit = false;
  const f = (t) => { evals++; return F.f(t); };

  // 1. adaptive sampling, pruned by interval arithmetic
  const L = hi - lo;
  const grid = [lo];
  for (let i = 1; i < n; i++) grid.push(lo + (L * (i + 0.0137)) / n);
  grid.push(hi);
  const pts = [{ x: lo, y: f(lo) }];
  const rootFree = []; // certified root-free cells (kept for reporting)
  function cell(a, fa, b, fb, depth) {
    const sc = Number.isFinite(fa) && Number.isFinite(fb) && (fa * fb < 0 || fa === 0 || fb === 0);
    if (!sc) {
      const enc = F.fi(a, b);
      if (enc.def && enc.cont && !IV.containsZero(enc) && !IV.isEmpty(enc)) { rootFree.push([a, b]); pts.push({ x: b, y: fb }); return; }
      if (depth < maxDepth && evals < maxEvals) {
        const xs = [a + (b - a) * 0.25, a + (b - a) * 0.5, a + (b - a) * 0.75, b];
        const ys = [f(xs[0]), f(xs[1]), f(xs[2]), fb];
        let pa = a, pf = fa;
        for (let i = 0; i < 4; i++) { cell(pa, pf, xs[i], ys[i], depth + 1); pa = xs[i]; pf = ys[i]; }
        return;
      }
      if (evals >= maxEvals) budgetHit = true;
      else if (!enc.cont) suspects.push([a, fa, b, fb]);
    }
    pts.push({ x: b, y: fb });
  }
  const suspects = [];
  for (let i = 1; i < grid.length; i++) {
    const b = grid[i];
    cell(pts[pts.length - 1].x, pts[pts.length - 1].y, b, f(b), 0);
    if (dl.expired()) { warnings.push("Time limit reached during sampling; the search is incomplete."); break; }
  }
  if (budgetHit) warnings.push("Sampling budget exhausted; narrow features may have been missed.");

  // 2. scan for brackets, exact zeros, domain boundaries and |f| minima
  const brackets = [], candidates = [], disc = [], evenCands = [];
  const fin = Number.isFinite;
  for (let i = 0; i < pts.length; i++) {
    const p = pts[i];
    if (p.y === 0) candidates.push({ x: p.x, a: p.x, b: p.x, kind: "exact", cont: true });
    if (i + 1 < pts.length) {
      const q = pts[i + 1];
      if (fin(p.y) && fin(q.y) && p.y * q.y < 0) brackets.push([p.x, q.x, p.y, q.y]);
      else if (fin(p.y) !== fin(q.y)) {
        // domain boundary: bisect on definedness
        let a = p.x, b = q.x;
        const aDef = fin(p.y);
        for (let k = 0; k < 80 && b - a > 0; k++) {
          const m = a + (b - a) / 2;
          if (m === a || m === b) break;
          if (fin(f(m)) === aDef) a = m; else b = m;
        }
        const edge = aDef ? a : b;
        const fe = f(edge);
        disc.push({ at: fmtNum(edge, 12), kind: "domain-boundary", x: edge });
        const ref = aDef ? p.y : q.y;
        if (fin(fe) && Math.abs(fe) <= 1e-7 * Math.max(1, Math.abs(ref))) {
          candidates.push({ x: edge, a: edge, b: edge, kind: "boundary", cont: false, width: b - a });
        }
      }
    }
    if (i > 0 && i + 1 < pts.length) {
      const pa = pts[i - 1], pb = pts[i + 1];
      if (fin(pa.y) && fin(p.y) && fin(pb.y) && p.y !== 0 && sgn(pa.y) === sgn(p.y) && sgn(pb.y) === sgn(p.y) &&
          Math.abs(p.y) < Math.abs(pa.y) && Math.abs(p.y) <= Math.abs(pb.y)) {
        evenCands.push([pa.x, p.x, pb.x, pa.y, p.y, pb.y]);
      }
    }
  }

  // 3. brackets -> Brent, classified as root / pole / jump
  const processBracket = (a, b, fa0, fb0) => {
    const r = brent(f, a, b, { maxIter: 300 });
    if (!Number.isFinite(r.x)) return;
    const [ba, bb] = r.bracket;
    const enc = F.fi(ba, bb);
    const endMax = Math.max(Math.abs(r.fa ?? 0), Math.abs(r.fb ?? 0), Math.abs(r.fx));
    const startMax = Math.max(Math.abs(fa0), Math.abs(fb0));
    if (enc.def && enc.cont && IV.containsZero(enc)) {
      candidates.push({ x: r.x, a, b, kind: "bracket", cont: true, iters: r.iterations });
    } else if (!(endMax < Infinity) || endMax > 10 * startMax) {
      disc.push({ at: fmtNum(r.x, 12), kind: "pole", x: r.x });
    } else if (endMax <= 1e-6 * startMax) {
      candidates.push({ x: r.x, a, b, kind: "bracket", cont: false, iters: r.iterations });
    } else {
      disc.push({ at: fmtNum(r.x, 12), kind: "jump", x: r.x });
    }
  };
  for (const [a, b, fa, fb] of brackets) {
    if (dl.expired()) { warnings.push("Time limit reached while bracketing; the search is incomplete."); break; }
    processBracket(a, b, fa, fb);
  }

  // 3b. discontinuities flagged by interval arithmetic without a sign change (1/x^2, jumps)
  for (const [a0, fa0, b0, fb0] of suspects) {
    if (dl.expired()) break;
    let a = a0, b = b0, found = true;
    for (let k = 0; k < 60 && b - a > 4 * EPS * Math.max(1, Math.abs(a)); k++) {
      const m = a + (b - a) / 2;
      const l = F.fi(a, m), r = F.fi(m, b);
      if (!l.cont || !l.def) b = m;
      else if (!r.cont || !r.def) a = m;
      else { found = false; break; }
    }
    if (!found) continue;
    const xm = a + (b - a) / 2;
    if (disc.some((d) => Math.abs(d.x - xm) <= 1e-9 * Math.max(1, Math.abs(xm)))) continue;
    const ya = f(a), yb = f(b);
    const ref = Math.max(Math.abs(fa0), Math.abs(fb0));
    if (!fin(ya) || !fin(yb) || Math.max(Math.abs(ya), Math.abs(yb)) > 1e6 * Math.max(ref, 1e-300)) disc.push({ at: fmtNum(xm, 12), kind: "pole", x: xm });
    else if (Math.abs(ya - yb) > 1e-6 * Math.max(ref, Math.abs(ya), Math.abs(yb))) disc.push({ at: fmtNum(xm, 12), kind: "jump", x: xm });
  }

  // 4. local minima of |f| without sign change: close pairs or even-multiplicity roots
  const F1 = { f: (t) => F.fd(t)[1] };
  for (const [xa, xm, xb, ya, ym, yb] of evenCands) {
    if (dl.expired()) break;
    let c = xm;
    const da = F1.f(xa), db = F1.f(xb);
    if (Number.isFinite(da) && Number.isFinite(db) && da * db < 0) {
      const r = brent(F1.f, xa, xb, { maxIter: 200 });
      if (Number.isFinite(r.x)) c = r.x;
    } else {
      const r = brentMin((t) => Math.abs(f(t)), xa, xb, { tol: 1e-12 });
      c = r.x;
    }
    const fc = f(c);
    if (!Number.isFinite(fc)) continue;
    if (fc === 0) { candidates.push({ x: c, a: xa, b: xb, kind: "even", cont: true }); continue; }
    if (sgn(fc) !== sgn(ym)) {
      processBracket(xa, c, ya, fc);
      processBracket(c, xb, fc, yb);
      continue;
    }
    const enc = F.fi(c, c);
    if (IV.containsZero(enc) || Math.abs(fc) <= 1e-12 * Math.max(Math.abs(ya), Math.abs(yb))) {
      candidates.push({ x: c, a: xa, b: xb, kind: "even", cont: true });
    }
  }

  // 5. deduplicate double-level candidates, then refine each in BigFloat
  candidates.sort((p, q) => p.x - q.x);
  const uniq = [];
  for (const c of candidates) {
    const last = uniq[uniq.length - 1];
    if (last && Math.abs(c.x - last.x) <= 1e-12 * Math.max(1, Math.abs(c.x))) {
      if (last.kind === "exact" || c.kind === "bracket") Object.assign(last, { ...c, kind: last.kind === "exact" ? "exact" : c.kind });
      continue;
    }
    uniq.push({ ...c });
  }
  const roots = [];
  for (const c of uniq) {
    if (roots.length >= maxRoots) { warnings.push(`Stopped after maxRoots = ${maxRoots} roots.`); break; }
    if (dl.expired()) { warnings.push("Time limit reached during high-precision refinement; some roots are unrefined."); break; }
    roots.push(refineRoot(F, c, digits, lo, hi));
  }
  // final dedupe on refined values
  const out = [];
  for (const r of roots) {
    const prev = out[out.length - 1];
    if (prev) {
      const d = Math.abs(r._x - prev._x);
      const tol = 10 * Math.max(Number(prev.errorBound) || 0, Number(r.errorBound) || 0) + 1e-14 * Math.max(1, Math.abs(r._x));
      if (d <= tol) { if (!prev.converged && r.converged) out[out.length - 1] = r; continue; }
    }
    out.push(r);
  }
  for (const r of out) delete r._x;
  disc.sort((p, q) => p.x - q.x);
  const res0 = 1e-13 * Math.max(Math.abs(lo), Math.abs(hi));
  const discontinuities = [];
  for (const d of disc) {
    const at = Math.abs(d.x) < res0 ? "0" : d.at;
    const last = discontinuities[discontinuities.length - 1];
    if (last && last.kind === d.kind && Math.abs(last._x - d.x) <= 1e-9 * Math.max(1, Math.abs(d.x))) continue;
    discontinuities.push({ at, kind: d.kind, _x: d.x });
  }
  for (const d of discontinuities) delete d._x;
  return {
    roots: out,
    discontinuities,
    window: { lo, hi },
    complete: false,
    caveat: `Roots outside [${fmtNum(lo, 12)}, ${fmtNum(hi, 12)}] were not searched. Inside the window, roots closer together than the sampling resolution or tangential roots of odd multiplicity may be missed unless interval arithmetic excluded them.`,
    samples: pts.length,
    evaluations: evals,
    warnings,
  };
}

// High-precision refinement of one root candidate with multiplicity detection and
// sign-change certification.
function refineRoot(F, c, digits, wlo, whi) {
  const warnings = [];
  const target = B.digitsToBits(digits) + 16;
  const method = c.kind === "even" ? "critical point + modified newton (AD, multiprecision)" :
    c.kind === "boundary" ? "domain-boundary bisection" : "brent + newton (AD, multiprecision)";
  if (c.kind === "boundary") {
    // try the nearest "nice" points: 0 and the 12-digit rounding of the edge
    const wpx = target + 32;
    const eb0 = Math.max(c.width || 0, EPS * Math.max(1, Math.abs(c.x)));
    for (const cand of [0, Number(c.x.toPrecision(12))]) {
      if (Math.abs(cand - c.x) > 4 * eb0 + 1e-300) continue;
      const cb = B.fromString(String(cand), wpx);
      const fv = safeBF(() => F.bf(cb, wpx));
      if (fv && fv.m === 0n) {
        return Object.assign(record({ value: cand === 0 ? "0" : B.toString(cb, digits, { trim: false }), digits, requested: digits,
          errorBound: fmtErr(cand === 0 ? 0 : Math.abs(cand) * 10 ** -digits / 2), method, iterations: 80, converged: true,
          warnings: ["Root at the edge of the domain of f: f evaluates to exactly 0 at this point in multiprecision arithmetic."] }),
          { residual: "0", multiplicityHint: null, certified: false, _x: cand });
      }
    }
    warnings.push("Root at the edge of the domain of f, located by bisection on definedness in double precision; high-precision refinement is not available.");
    const eb = Math.max(c.width || 0, EPS * Math.max(1, Math.abs(c.x)));
    const dg = Math.max(0, Math.min(digits, Math.floor(-Math.log10(eb / Math.max(Math.abs(c.x), 1e-300)))));
    return Object.assign(record({ value: fmtNum(c.x, Math.max(1, dg)), digits: dg, requested: digits, errorBound: fmtErr(eb), method, iterations: 80, converged: false, warnings }),
      { residual: fmtErr(Math.abs(F.f(c.x))), multiplicityHint: null, certified: false, _x: c.x });
  }
  const aB = B.fromNumber(Math.min(c.a, c.b) - (c.a === c.b ? 1e-6 * (1 + Math.abs(c.x)) : 0));
  const bB = B.fromNumber(Math.max(c.a, c.b) + (c.a === c.b ? 1e-6 * (1 + Math.abs(c.x)) : 0));
  let xB = B.fromNumber(c.x);
  let iters = c.iters || 0;
  // phase A: plain Newton at moderate precision to detect the multiplicity from the
  // convergence rate (quadratic -> simple root; linear with ratio r -> m = 1/(1-r)).
  let m = 1;
  const pA = Math.max(160, Math.min(target, 400));
  const steps = [];
  let zeroHit = false;
  for (let k = 0; k < 12; k++) {
    const r = safeBF(() => F.bfd(xB, pA));
    if (!r) break;
    const [fv, dv] = r;
    if (fv.m === 0n) { zeroHit = true; break; }
    if (dv.m === 0n) break;
    const st = B.div(fv, dv, pA);
    xB = B.sub(xB, st, pA);
    iters++;
    steps.push(Math.abs(B.toNumber(st)));
    if (steps.length >= 3) {
      const s = steps.slice(-3);
      if (s[2] === 0 || s[1] === 0) break;
      const r1 = s[1] / s[0], r2 = s[2] / s[1];
      if (r2 < 0.1 && r2 < r1 * 0.5) break; // accelerating: simple root
      if (Math.abs(r1 - r2) < 0.03 && r2 > 0.4 && r2 < 0.97) { m = Math.max(1, Math.round(1 / (1 - r2))); break; }
    }
    if (steps[steps.length - 1] <= 2 ** -(pA - 8) * Math.max(1e-300, Math.abs(B.toNumber(xB)))) break;
  }
  if (zeroHit) {
    // exact zero in BigFloat: the multiplicity is the order of the first nonvanishing derivative
    for (let k = 1; k <= 6; k++) {
      const dk = safeBF(() => F.bfk(xB, pA, k));
      if (!dk) break;
      if (dk.m !== 0n) { m = k; break; }
      m = k + 1;
    }
  }
  if (c.kind === "even" && m === 1) m = 2;
  if (m > 1) warnings.push(`Convergence rate indicates a root of multiplicity about ${m}; modified Newton used.`);
  // phase B: modified Newton with precision doubling up to m * target bits
  const wpFinal = target * m + 32;
  const mB = B.fromInt(m);
  let p = pA, converged = zeroHit, lastStep = null;
  const absTol = B.mulPow2(B.ONE, -2 * target);
  if (!zeroHit) {
    for (let k = 0; k < 200; k++) {
      p = Math.min(wpFinal, p * 2);
      const r = safeBF(() => F.bfd(xB, p));
      if (!r) { warnings.push("f or f' undefined during refinement"); break; }
      const [fv, dv] = r;
      if (fv.m === 0n) { converged = true; lastStep = B.ZERO; break; }
      if (dv.m === 0n) { warnings.push("derivative vanished during refinement"); break; }
      const st = B.div(B.mul(mB, fv, p), dv, p);
      let xn = B.sub(xB, st, p);
      if (B.cmp(xn, aB) < 0 || B.cmp(xn, bB) > 0) xn = B.mulPow2(B.add(xB, B.cmp(xn, aB) < 0 ? aB : bB, p), -1);
      xB = xn;
      iters++;
      lastStep = B.abs(st);
      const rel = B.max(B.mulPow2(B.abs(xB), -(target + 4)), absTol);
      if (p === wpFinal && B.cmp(lastStep, rel) <= 0) { converged = true; break; }
    }
  }
  // snap to exact zero when x is within the absolute tolerance and f(0) = 0 exactly
  if (B.cmp(B.abs(xB), B.mulPow2(B.ONE, -target)) < 0) {
    const f0 = safeBF(() => F.bf(B.ZERO, wpFinal));
    if (f0 && f0.m === 0n) { xB = B.ZERO; converged = true; }
  }
  // certification by a sign change of f at x +- delta (in BigFloat)
  const wpc = wpFinal + 16;
  const k10 = xB.m === 0n ? -digits - 1 : decExp(xB);
  const ulp = pow10(k10 - digits + 1, wpc);
  let certified = false, eb = null;
  if (m % 2 === 1) {
    let delta = B.max(B.div(ulp, B.fromInt(100), wpc), B.mulPow2(B.ONE, -2 * target));
    for (let t = 0; t < 4 && !certified; t++) {
      const fl = safeBF(() => F.bf(B.sub(xB, delta, wpc), wpFinal));
      const fr = safeBF(() => F.bf(B.add(xB, delta, wpc), wpFinal));
      if (fl && fr && B.sign(fl) * B.sign(fr) < 0) { certified = true; eb = delta; break; }
      if (xB.m === 0n && fl && fr && (fl.m === 0n || fr.m === 0n)) break;
      delta = B.mul(delta, B.fromInt(10), wpc);
    }
    if (certified && !c.cont) warnings.push("Sign change verified in high precision, but continuity on the bracket was not proven by interval arithmetic.");
  }
  if (!certified) {
    eb = lastStep ? B.max(B.mul(lastStep, B.fromInt(16), 64), B.div(ulp, B.fromInt(100), 64)) : B.div(ulp, B.fromInt(10), 64);
    if (m % 2 === 0) warnings.push("Even-multiplicity root: f does not change sign, so existence is not certified by a sign change; |f| is below the residual at this point (a tiny positive/negative minimum cannot be excluded at this precision).");
    else if (converged) warnings.push("Could not certify the root by a sign change at the reported precision; errorBound is a Newton-step estimate.");
  }
  const resid = safeBF(() => F.bf(xB, wpFinal));
  const residual = resid ? fmtErr(B.abs(resid)) : null;
  const totalErr = B.add(eb, B.mulPow2(ulp, -1), 64);
  let dg = converged ? digits : digitsFrom(xB, eb, digits);
  if (B.cmp(eb, ulp) > 0) dg = Math.min(dg, digitsFrom(xB, eb, digits));
  if (!converged) warnings.push("Refinement did not converge to the requested precision.");
  const value = xB.m === 0n ? "0" : B.toString(xB, Math.max(1, dg));
  return Object.assign(
    record({ value, digits: dg, requested: digits, errorBound: fmtErr(totalErr), method, iterations: iters, converged, warnings }),
    { residual, multiplicityHint: m, certified, _x: B.toNumber(xB) },
  );
}

// ---------------------------------------------------------------------------------------
// numerical differentiation
// ---------------------------------------------------------------------------------------
// Ridders / Richardson extrapolation of central differences, with error estimate.
export function diffRichardson(f, x0, opts = {}) {
  ({ f } = asFn(f, opts));
  const h0 = opts.h ?? 0.1 * Math.max(1, Math.abs(x0));
  const CON = 1.4, CON2 = CON * CON, NTAB = 12, SAFE = 2;
  const a = Array.from({ length: NTAB }, () => new Array(NTAB).fill(0));
  let hh = h0, err = Infinity, ans = NaN, it = 0;
  a[0][0] = (f(x0 + hh) - f(x0 - hh)) / (2 * hh);
  for (let i = 1; i < NTAB; i++) {
    it = i;
    hh /= CON;
    a[0][i] = (f(x0 + hh) - f(x0 - hh)) / (2 * hh);
    let fac = CON2;
    for (let j = 1; j <= i; j++) {
      a[j][i] = (a[j - 1][i] * fac - a[j - 1][i - 1]) / (fac - 1);
      fac *= CON2;
      const errt = Math.max(Math.abs(a[j][i] - a[j - 1][i]), Math.abs(a[j][i] - a[j - 1][i - 1]));
      if (errt <= err) { err = errt; ans = a[j][i]; }
    }
    if (Math.abs(a[i][i] - a[i - 1][i - 1]) >= SAFE * err) break;
  }
  const requested = Math.min(opts.digits ?? 12, 15);
  const ok = Number.isFinite(ans) && Number.isFinite(err);
  const dg = ok ? (ans === 0 ? (err === 0 ? requested : 0) : Math.max(0, Math.min(requested, Math.floor(-Math.log10(Math.max(err, EPS * Math.abs(ans)) / Math.abs(ans)))))) : 0;
  return Object.assign(record({
    value: ok ? fmtNum(ans, Math.max(1, dg)) : "undefined", digits: dg, requested,
    errorBound: ok ? fmtErr(err + EPS * Math.abs(ans)) : null, method: "richardson extrapolation (ridders)",
    iterations: it, converged: ok && dg >= requested,
    warnings: ok ? (dg < requested ? ["Extrapolation error estimate did not reach the requested digits."] : []) : ["f undefined near x0"],
  }), { x: ans });
}
// Exact-to-precision derivative value by forward-mode AD in BigFloat (order >= 1),
// confirmed by evaluation at two precisions.
export function derivative(node, x, x0, opts = {}) {
  const order = opts.order ?? 1;
  const digits = opts.digits ?? 15;
  const F = makeFuncs(node, x, order, "real");
  const x0r = typeof x0 === "object" && x0 && x0.k ? x0 : null;
  let bits = B.digitsToBits(digits) + 24, prev = null;
  const warnings = [];
  for (let it = 1; it <= 4; it++) {
    const xb = x0r ? evalTree(x0r, {}, { bits: bits + 16 }) : toBFValue(x0, bits + 16);
    if (isUndefined(xb)) break;
    const v = safeBF(() => F.bf(xb, bits));
    if (!v) return record({ value: "undefined", digits: 0, requested: digits, errorBound: null, method: "automatic differentiation (multiprecision)", iterations: it, converged: true, warnings: ["The derivative is undefined at this point."] });
    if (prev) {
      const diff = B.abs(B.sub(v, prev, bits));
      if (v.m === 0n && prev.m === 0n) return record({ value: "0", digits, requested: digits, errorBound: "0", method: "automatic differentiation (multiprecision)", iterations: it, converged: true });
      if (v.m !== 0n) {
        const ulp = pow10(decExp(v) - digits + 1, bits);
        if (B.cmp(B.mul(diff, B.fromInt(10), bits), ulp) <= 0) {
          return record({ value: B.toString(v, digits), digits, requested: digits, errorBound: fmtErr(B.add(diff, B.mulPow2(ulp, -1), bits)), method: "automatic differentiation (multiprecision)", iterations: it, converged: true });
        }
      }
    }
    prev = v;
    bits *= 2;
  }
  warnings.push("Derivative values at increasing precision did not agree.");
  return record({ value: prev ? B.toString(prev, 6) : "undefined", digits: 0, requested: digits, errorBound: null, method: "automatic differentiation (multiprecision)", iterations: 4, converged: false, warnings });
}

// ---------------------------------------------------------------------------------------
// integration
// ---------------------------------------------------------------------------------------
const XGK = [0.991455371120812639206854697526329, 0.949107912342758524526189684047851, 0.864864423359769072789712788640926,
  0.741531185599394439863864773280788, 0.586087235467691130294144845693013, 0.405845151377397166906606412076961,
  0.207784955007898467600689403773245, 0];
const WGK = [0.022935322010529224963732008058970, 0.063092092629978553290700663189204, 0.104790010322250183839876322541518,
  0.140653259715525918745189590510238, 0.169004726639267902826583426598550, 0.190350578064785409913256402421014,
  0.204432940075298892414161999234649, 0.209482141084727828012999174891714];
const WG = [0.129484966168869693270611432679082, 0.279705391489276667901467771423780, 0.381830050505118944950369775488975,
  0.417959183673469387755102040816327];
function gk15(f, a, b) {
  const c = 0.5 * (a + b), h = 0.5 * (b - a);
  const fc = f(c);
  let rk = fc * WGK[7], rg = fc * WG[3], ok = Number.isFinite(fc);
  for (let j = 0; j < 7; j++) {
    const dx = h * XGK[j];
    const f1 = f(c - dx), f2 = f(c + dx);
    if (!Number.isFinite(f1) || !Number.isFinite(f2)) ok = false;
    rk += WGK[j] * (f1 + f2);
    if (j % 2 === 1) rg += WG[(j - 1) / 2] * (f1 + f2);
  }
  const val = rk * h;
  return { a, b, val, err: Math.abs((rk - rg) * h) + 50 * EPS * Math.abs(val), ok };
}
// Adaptive Gauss-Kronrod G7-K15 (global subdivision of the worst segment).
export function gaussKronrod(f, a, b, opts = {}) {
  const tolRel = opts.tolRel ?? 1e-12, tolAbs = opts.tolAbs ?? 1e-300;
  const limit = opts.maxSubdiv ?? 500;
  let segs = [gk15(f, a, b)];
  let evals = 15, it = 0;
  for (; ; it++) {
    let tot = 0, err = 0, ok = true;
    for (const s of segs) { tot += s.val; err += s.err; ok = ok && s.ok; }
    if (!ok) return { value: tot, err: Infinity, evals, subdivisions: it, ok: false, converged: false };
    if (err <= Math.max(tolAbs, tolRel * Math.abs(tot))) return { value: tot, err, evals, subdivisions: it, ok: true, converged: true, segs };
    if (segs.length >= limit) return { value: tot, err, evals, subdivisions: it, ok: true, converged: false, segs };
    let wi = 0;
    for (let i = 1; i < segs.length; i++) if (segs[i].err > segs[wi].err) wi = i;
    const s = segs[wi];
    const m = 0.5 * (s.a + s.b);
    if (m <= s.a || m >= s.b) return { value: tot, err, evals, subdivisions: it, ok: true, converged: false, segs };
    segs.splice(wi, 1, gk15(f, s.a, m), gk15(f, m, s.b));
    evals += 30;
  }
}
// Double-precision tanh-sinh on [a, b]; g(x, dLeft, dRight) gets accurate endpoint distances.
export function tanhSinh(g, a, b, opts = {}) {
  const tolRel = opts.tolRel ?? 1e-12, maxLevel = opts.maxLevel ?? 9;
  const hw = 0.5 * (b - a);
  const HP = Math.PI / 2;
  let S = 0, h = 1, prev = NaN, err = Infinity, evals = 0, level = 0, ok = true;
  const term = (t) => {
    const ch = Math.cosh(t), sh = Math.sinh(t);
    const y = HP * sh;
    const q = Math.exp(-2 * y);
    const d = (b - a) * q / (1 + q); // distance to the nearest endpoint
    const w = HP * ch * 4 * q / ((1 + q) * (1 + q));
    let s = 0;
    const xl = a + d, xr = b - d;
    if (xl > a && xl < b) { const v = g(xl, d, b - xl); evals++; if (Number.isFinite(v)) s += w * v; else ok = false; }
    if (xr < b && xr > a && t !== 0) { const v = g(xr, xr - a, d); evals++; if (Number.isFinite(v)) s += w * v; else ok = false; }
    return { s, w };
  };
  const errs = [];
  for (level = 0; level <= maxLevel; level++) {
    let add = 0;
    const step = level === 0 ? 1 : 2;
    const start = level === 0 ? 0 : 1;
    for (let j = start; j < 100000; j += step) {
      const t = j * h;
      const { s, w } = term(t);
      add += s;
      if (w < 1e-300 || (t > 1 && Math.abs(s) < 1e-18 * Math.abs(S + add) && w < 1e-18)) break;
      if (t > 6.5) break;
    }
    S = level === 0 ? add : S + add;
    const I = hw * h * S;
    if (level > 0) {
      err = Math.abs(I - prev);
      errs.push(err);
      if (level >= 3 && err <= tolRel * Math.abs(I) && errs.length >= 2) { prev = I; break; }
    }
    prev = I;
    h /= 2;
  }
  return { value: prev, err: err + 10 * EPS * Math.abs(prev), evals, levels: level, ok, converged: ok && err <= Math.max(tolRel * Math.abs(prev), 1e-300) };
}
function boundValue(v) {
  if (typeof v === "number") return v;
  if (typeof v === "string") {
    const s = v.trim().toLowerCase();
    if (["oo", "inf", "infinity", "+oo", "+inf"].includes(s)) return Infinity;
    if (["-oo", "-inf", "-infinity"].includes(s)) return -Infinity;
    return Number(s);
  }
  if (v && v.k) {
    if (v.k === "const" && v.name === "oo") return Infinity;
    if (v.k === "mul" && v.args.length === 2 && v.args[1].k === "const" && v.args[1].name === "oo" && v.args[0].k === "num") return v.args[0].v.n < 0n ? -Infinity : Infinity;
    const r = evalTree(v, {}, { digits: 20 });
    if (isUndefined(r) || r instanceof Complex) return NaN;
    return B.toNumber(r);
  }
  if (v instanceof BigFloat) return B.toNumber(v);
  return NaN;
}
function boundBF(v, wp) {
  if (v && v.k) {
    const r = evalTree(v, {}, { bits: wp });
    return isUndefined(r) || r instanceof Complex ? null : r;
  }
  if (typeof v === "string" && !/^[-+]?(oo|inf)/i.test(v.trim())) return B.fromString(v, wp);
  if (typeof v === "number") return B.fromNumber(v);
  if (v instanceof BigFloat) return v;
  return null;
}
// integrate(node, x, a, b, {digits, maxSubdiv, timeLimitMs}): definite integral with
// error estimate. digits <= 14: adaptive Gauss-Kronrod with tanh-sinh fallback in double;
// digits > 14: tanh-sinh in BigFloat.
export function integrate(node, x, a, b, opts = {}) {
  const requested = Math.max(1, Math.floor(opts.digits ?? 12));
  const name = varName(x);
  let A = boundValue(a), Bv = boundValue(b);
  if (Number.isNaN(A) || Number.isNaN(Bv)) throw qerr("BAD_INPUT", "integration bounds must be real numbers or +-oo");
  if (A === Bv) return record({ value: "0", digits: requested, requested, errorBound: "0", method: "empty interval", iterations: 0, converged: true });
  if (A > Bv) {
    const r = integrate(node, x, b, a, opts);
    if (r.value && r.value !== "undefined" && r.value !== "0") r.value = r.value.startsWith("-") ? r.value.slice(1) : "-" + r.value;
    return r;
  }
  if (requested > 14) return integrateHP(node, name, a, b, A, Bv, requested, opts);
  const f0 = compileDouble(node, [name]);
  // infinite ranges -> finite by x = a + t/(1-t) etc.
  let g, lo = A, hi = Bv, method = "";
  if (A === -Infinity && Bv === Infinity) {
    g = (t) => { const u = 1 - t * t; return f0(t / u) * (1 + t * t) / (u * u); };
    lo = -1; hi = 1; method = " (x = t/(1-t^2))";
  } else if (Bv === Infinity) {
    g = (t) => { const u = 1 - t; return f0(A + t / u) / (u * u); };
    lo = 0; hi = 1; method = " (x = a + t/(1-t))";
  } else if (A === -Infinity) {
    g = (t) => { const u = 1 - t; return f0(Bv - t / u) / (u * u); };
    lo = 0; hi = 1; method = " (x = b - t/(1-t))";
  } else g = f0;
  // isolated undefined points (e.g. sin(x)/x at 0) are removable when both sides agree
  const gRaw = g;
  let patched = 0;
  const badSpots = [];
  g = (t) => {
    const v = gRaw(t);
    if (Number.isFinite(v)) return v;
    if (badSpots.length < 8) badSpots.push(t);
    const d = 1e-9 * Math.max(1, Math.abs(t));
    const l = gRaw(t - d), r = gRaw(t + d);
    if (Number.isFinite(l) && Number.isFinite(r) && Math.abs(l - r) <= 1e-6 * Math.max(1, Math.abs(l), Math.abs(r))) {
      // bounded nearby? (a symmetric pole also has equal one-sided values)
      const l2 = gRaw(t - 1e3 * d), r2 = gRaw(t + 1e3 * d);
      if (Number.isFinite(l2) && Number.isFinite(r2) && Math.abs(l) <= 2 * Math.max(Math.abs(l2), Math.abs(r2)) + 1e-12) { patched++; return 0.5 * (l + r); }
    }
    return v;
  };
  const tol = Math.max(10 ** -requested, 4 * EPS);
  const warnings = [];
  const gk = gaussKronrod(g, lo, hi, { tolRel: tol / 10, maxSubdiv: opts.maxSubdiv ?? 400 });
  let best = { value: gk.value, err: gk.err, method: "adaptive gauss-kronrod G7-K15" + method, iters: gk.evals, converged: gk.converged && gk.ok };
  if (!best.converged) {
    const ginf = (t, dl, dr) => {
      if (hi === 1 && lo === 0 && (A === -Infinity || Bv === Infinity)) {
        const u = dr; const xx = Bv === Infinity ? A + t / u : Bv - t / u;
        return f0(xx) / (u * u);
      }
      return g(t);
    };
    const ts = tanhSinh(ginf, lo, hi, { tolRel: tol / 10 });
    if (ts.ok && (ts.converged || ts.err < best.err || !gk.ok)) {
      if (!gk.ok) warnings.push("Gauss-Kronrod hit an undefined or infinite integrand value; switched to tanh-sinh (endpoint singularity handling).");
      best = { value: ts.value, err: ts.err, method: "tanh-sinh (double exponential)" + method, iters: ts.evals + gk.evals, converged: ts.converged };
    }
  }
  if (patched) warnings.push("The integrand is undefined at isolated point(s) with equal one-sided values; they were treated as removable.");
  if (!best.converged) {
    // divergence diagnosis at the worst segment / endpoints: |g| ~ C d^-p with p >= 1
    const spots = [];
    if (gk.segs && gk.segs.length) {
      const w = gk.segs.reduce((p, q) => (q.err > p.err ? q : p));
      spots.push(w.a, w.b);
    }
    spots.push(lo, hi, ...badSpots);
    for (const s0 of spots) {
      for (const side of [1, -1]) {
        const ds = [1e-4, 1e-7, 1e-10].map((d) => d * Math.max(1, hi - lo));
        const vs = ds.map((d) => Math.abs(gRaw(s0 + side * d)));
        if (vs.every((v) => Number.isFinite(v) && v > 0) && s0 + side * ds[0] > lo && s0 + side * ds[0] < hi) {
          const p1 = Math.log(vs[1] / vs[0]) / Math.log(ds[0] / ds[1]), p2 = Math.log(vs[2] / vs[1]) / Math.log(ds[1] / ds[2]);
          if (p1 >= 0.97 && p2 >= 0.97) {
            return record({ value: "undefined", digits: 0, requested, errorBound: null, method: best.method, iterations: best.iters, converged: false,
              warnings: [...warnings, `The integral appears to diverge: the integrand grows like |x - c|^-${p2.toFixed(2)} near x = ${fmtNum(s0, 8)}.`] });
          }
        }
      }
    }
    warnings.push("The quadrature did not converge; the error estimate may be unreliable.");
  }
  if (!Number.isFinite(best.value)) {
    return record({ value: "undefined", digits: 0, requested, errorBound: null, method: best.method, iterations: best.iters, converged: false, warnings: ["The integrand is not integrable numerically on this interval (singular or divergent)."] });
  }
  const errAbs = best.err;
  const dg = best.value === 0 ? (errAbs === 0 ? requested : 0) : Math.max(0, Math.min(requested, Math.floor(-Math.log10(Math.max(errAbs, 1e-300) / Math.abs(best.value)))));
  const shown = Math.max(1, Math.min(dg, 16));
  const valBF = B.fromNumber(best.value);
  const ulpHalf = best.value === 0 ? 0 : 0.5 * 10 ** (decExp(valBF) - shown + 1);
  return record({ value: fmtNum(best.value, shown), digits: Math.min(dg, 16), requested, errorBound: fmtErr(errAbs + ulpHalf), method: best.method, iterations: best.iters, converged: best.converged && dg >= requested, warnings });
}
// High-precision tanh-sinh quadrature in BigFloat.
function integrateHP(node, name, a, b, A, Bv, requested, opts) {
  const warnings = [];
  const target = B.digitsToBits(requested) + 16;
  const wp = target + 32;
  const dl = deadline(opts.timeLimitMs ?? 20000);
  const BA = new BFAlgebra(wp, "real");
  const f = compile(eqToExpr(node), [name], BA);
  const aB = Number.isFinite(A) ? boundBF(a, wp + 64) : null;
  const bB = Number.isFinite(Bv) ? boundBF(b, wp + 64) : null;
  if ((Number.isFinite(A) && !aB) || (Number.isFinite(Bv) && !bB)) throw qerr("BAD_INPUT", "bad integration bound");
  const mode = Number.isFinite(A) && Number.isFinite(Bv) ? "finite" : Number.isFinite(A) ? "right-inf" : Number.isFinite(Bv) ? "left-inf" : "both-inf";
  // integrand on the finite parameter interval [lo, hi] with endpoint distances dl/dr
  let underflows = 0;
  const F = (t, dL, dR) => {
    try { return F0(t, dL, dR); } catch (e) {
      if (e.code === "UNDERFLOW") { underflows++; return B.ZERO; }
      throw e;
    }
  };
  const F0 = (t, dL, dR) => {
    const xv = mode === "finite" ? t
      : mode === "right-inf" ? B.add(aB, B.sub(B.div(B.ONE, dR, wp), B.ONE, wp), wp) // a + t/(1-t), 1-t = dR
      : mode === "left-inf" ? B.sub(bB, B.sub(B.div(B.ONE, dR, wp), B.ONE, wp), wp)
      : null;
    if (mode === "both-inf") {
      // x = t / (1 - t^2) on (-1, 1): 1 - t^2 = (1-t)(1+t) = dR * dL
      const u = B.mul(dR, dL, wp);
      const xx = B.div(t, u, wp);
      const jac = B.div(B.add(B.ONE, B.mul(t, t, wp), wp), B.mul(u, u, wp), wp);
      return B.mul(f([xx]), jac, wp);
    }
    const v = f([xv]);
    if (mode === "finite") return v;
    return B.div(v, B.mul(dR, dR, wp), wp);
  };
  const [lo, hi] = mode === "finite" ? [aB, bB] : mode === "both-inf" ? [B.fromInt(-1), B.ONE] : [B.ZERO, B.ONE];
  const len = B.sub(hi, lo, wp);
  const halfPi = B.mulPow2(B.pi(wp), -1);
  let S = B.ZERO, h = B.ONE, prevI = null, errBF = null, evals = 0, level = 0, converged = false;
  const tiny = -(wp + 20);
  const errs = [];
  const maxLevel = opts.maxLevel ?? 12;
  try {
    for (level = 0; level <= maxLevel; level++) {
      const step = level === 0 ? 1 : 2, start = level === 0 ? 0 : 1;
      let add = B.ZERO, small = 0;
      for (let j = start; j < 20000; j += step) {
        if (dl.expired()) throw qerr("TIMEOUT", "time limit");
        const t = B.mul(B.fromInt(j), h, wp);
        const et = B.exp(t, wp), eti = B.div(B.ONE, et, wp);
        const sh = B.mulPow2(B.sub(et, eti, wp), -1), ch = B.mulPow2(B.add(et, eti, wp), -1);
        const y = B.mul(halfPi, sh, wp);
        if (B.toNumber(y) > wp * 0.35 * 4) break; // q < 2^-(4 wp)
        const q = B.exp(B.neg(B.mulPow2(y, 1)), wp);
        const opq = B.add(B.ONE, q, wp);
        const d = B.div(B.mul(len, q, wp), opq, wp); // distance of the node to the nearest endpoint
        const w = B.div(B.mulPow2(B.mul(halfPi, B.mul(ch, q, wp), wp), 2), B.mul(opq, opq, wp), wp);
        const extra = Math.max(0, -B.top(d)) + 8;
        const xl = B.add(lo, d, wp + extra), xr = B.sub(hi, d, wp + extra);
        let s = B.mul(w, F(xl, d, B.sub(len, d, wp + extra)), wp);
        evals++;
        if (j !== 0) { s = B.add(s, B.mul(w, F(xr, B.sub(len, d, wp + extra), d), wp), wp); evals++; }
        add = B.add(add, s, wp);
        const ref = B.add(S, add, wp);
        if (j > 0 && (s.m === 0n || B.top(s) < B.top(ref) + tiny)) { if (++small >= 2) break; } else small = 0;
      }
      S = level === 0 ? add : B.add(S, add, wp);
      const I = B.mul(B.mul(B.mulPow2(len, -1), h, wp), S, wp);
      if (prevI) {
        errBF = B.abs(B.sub(I, prevI, wp));
        errs.push(errBF);
        const need = I.m === 0n ? B.mulPow2(B.ONE, -target) : B.mul(B.abs(I), pow10(-requested - 1, wp), wp);
        if (level >= 3 && B.cmp(errBF, need) <= 0) { prevI = I; converged = true; break; }
      }
      prevI = I;
      h = B.mulPow2(h, -1);
    }
  } catch (e) {
    if (e.code === "TIMEOUT") warnings.push("Time limit reached; result is from the last completed level.");
    else if (isUndefCode(e)) {
      return record({ value: "undefined", digits: 0, requested, errorBound: null, method: "tanh-sinh (multiprecision)", iterations: evals, converged: false, warnings: ["The integrand is undefined at a quadrature node inside the interval: " + e.message.replace(/^Quelvra: /, "")] });
    } else throw e;
  }
  if (underflows) warnings.push("The integrand underflowed (|f| < 2^(-2^59)) at extreme quadrature nodes; those contributions were taken as 0.");
  if (!prevI) return record({ value: "undefined", digits: 0, requested, errorBound: null, method: "tanh-sinh (multiprecision)", iterations: evals, converged: false, warnings });
  let I = prevI;
  if (A > Bv) I = B.neg(I);
  const eb = errBF ?? B.abs(I);
  const dg = converged ? requested : digitsFrom(I, eb, requested);
  if (!converged) warnings.push("Successive tanh-sinh levels did not agree to the requested digits.");
  const ulpHalf = I.m === 0n ? B.ZERO : B.mulPow2(pow10(decExp(I) - Math.max(1, dg) + 1, 64), -1);
  return record({
    value: I.m === 0n ? "0" : B.toString(I, Math.max(1, dg)), digits: dg, requested, errorBound: fmtErr(B.add(eb, ulpHalf, 64)),
    method: "tanh-sinh (double exponential, multiprecision)" + (mode === "finite" ? "" : " with x = t/(1-t) map"), iterations: evals, converged, warnings,
  });
}

// ---------------------------------------------------------------------------------------
// optimization
// ---------------------------------------------------------------------------------------
const CGOLD = 0.3819660112501051;
export function goldenSection(f, a, b, opts = {}) {
  ({ f } = asFn(f, opts));
  const F = (t) => { const v = f(t); return Number.isNaN(v) ? Infinity : v; };
  const tol = opts.tol ?? 1e-10, maxIter = opts.maxIter ?? 300;
  let x1 = a + CGOLD * (b - a), x2 = b - CGOLD * (b - a), f1 = F(x1), f2 = F(x2), it = 0;
  for (; it < maxIter && Math.abs(b - a) > tol * (Math.abs(x1) + Math.abs(x2) + 1e-10); it++) {
    if (f1 < f2) { b = x2; x2 = x1; f2 = f1; x1 = a + CGOLD * (b - a); f1 = F(x1); }
    else { a = x1; x1 = x2; f1 = f2; x2 = b - CGOLD * (b - a); f2 = F(x2); }
  }
  const x = f1 < f2 ? x1 : x2;
  return rootRecord(x, Math.abs(b - a) / 2, opts.digits ?? 8, "golden-section search", it, it < maxIter, [], { x, fx: f(x) });
}
export function brentMin(f, a, b, opts = {}) {
  ({ f } = asFn(f, opts));
  const F = (t) => { const v = f(t); return Number.isNaN(v) ? Infinity : v; };
  const tol = opts.tol ?? Math.sqrt(EPS), maxIter = opts.maxIter ?? 300;
  let x, w, v, fx, fw, fv, d = 0, e = 0, it = 0, converged = false;
  x = w = v = a + CGOLD * (b - a);
  fx = fw = fv = F(x);
  for (; it < maxIter; it++) {
    const xm = 0.5 * (a + b);
    const tol1 = tol * Math.abs(x) + 1e-12, tol2 = 2 * tol1;
    if (Math.abs(x - xm) <= tol2 - 0.5 * (b - a)) { converged = true; break; }
    if (Math.abs(e) > tol1) {
      const r = (x - w) * (fx - fv);
      let q = (x - v) * (fx - fw);
      let p = (x - v) * q - (x - w) * r;
      q = 2 * (q - r);
      if (q > 0) p = -p;
      q = Math.abs(q);
      const et = e;
      e = d;
      if (Math.abs(p) >= Math.abs(0.5 * q * et) || p <= q * (a - x) || p >= q * (b - x)) { e = x >= xm ? a - x : b - x; d = CGOLD * e; }
      else { d = p / q; const u = x + d; if (u - a < tol2 || b - u < tol2) d = xm - x >= 0 ? tol1 : -tol1; }
    } else { e = x >= xm ? a - x : b - x; d = CGOLD * e; }
    const u = Math.abs(d) >= tol1 ? x + d : x + (d >= 0 ? tol1 : -tol1);
    const fu = F(u);
    if (fu <= fx) { if (u >= x) a = x; else b = x; v = w; w = x; x = u; fv = fw; fw = fx; fx = fu; }
    else {
      if (u < x) a = u; else b = u;
      if (fu <= fw || w === x) { v = w; w = u; fv = fw; fw = fu; } else if (fu <= fv || v === x || v === w) { v = u; fv = fu; }
    }
  }
  return rootRecord(x, Math.abs(b - a) / 2, opts.digits ?? 8, "brent minimization", it, converged, [], { x, fx });
}
// minimize(node|f, a, b, opts): Brent minimization; for trees the minimiser is polished to
// opts.digits by Newton on f' (AD) in BigFloat.
export function minimize(f, a, b, opts = {}) {
  const r = brentMin(f, a, b, opts);
  if (typeof f === "function" || !Number.isFinite(r.x)) return r;
  const name = opts.x ? varName(opts.x) : [...X.freeSymbols(eqToExpr(f))][0];
  const digits = opts.digits ?? 15;
  const F1 = makeFuncs(f, name, 1);
  const d1 = F1.f(r.x);
  if (!Number.isFinite(d1)) return r;
  const w = Math.max(Math.abs(b - a) * 1e-3, 1e-6);
  const c = { x: r.x, a: Math.max(a, r.x - w), b: Math.min(b, r.x + w), kind: "bracket", cont: true, iters: r.iterations };
  if (r.x - a < 1e-9 * (1 + Math.abs(a)) || b - r.x < 1e-9 * (1 + Math.abs(b))) {
    return Object.assign(r, { warnings: [...(r.warnings || []), "The minimum is at (or next to) an endpoint of the interval."] });
  }
  const rr = refineRoot(F1, c, digits, a, b);
  const F0 = makeFuncs(f, name, 0);
  const xB = B.fromString(rr.value === "0" ? "0" : rr.value, B.digitsToBits(digits) + 32);
  const fv = safeBF(() => F0.bf(xB, B.digitsToBits(digits) + 32));
  delete rr._x;
  return Object.assign(rr, { method: "brent minimization + newton on f' (AD, multiprecision)", x: B.toNumber(xB), fx: fv ? B.toNumber(fv) : NaN, fValue: fv ? B.toString(fv, digits) : "undefined" });
}
export function nelderMead(f, x0, opts = {}) {
  let fn = f;
  if (typeof f !== "function") {
    const vars = (opts.vars || [...X.freeSymbols(eqToExpr(f))].sort()).map(varName);
    const g = compileDouble(f, vars);
    fn = (p) => g(...p);
  }
  const F = (p) => { const v = fn(p); return Number.isNaN(v) ? Infinity : v; };
  const n = x0.length;
  const maxIter = opts.maxIter ?? 2000 * n, tol = opts.tol ?? 1e-12;
  const step = opts.step ?? 0.1;
  let simplex = [x0.slice()];
  for (let i = 0; i < n; i++) { const p = x0.slice(); p[i] += step * Math.max(1, Math.abs(p[i])); simplex.push(p); }
  let vals = simplex.map(F);
  let it = 0, converged = false;
  for (; it < maxIter; it++) {
    const idx = vals.map((v, i) => i).sort((i, j) => vals[i] - vals[j]);
    simplex = idx.map((i) => simplex[i]); vals = idx.map((i) => vals[i]);
    const spread = Math.abs(vals[n] - vals[0]);
    let size = 0;
    for (let i = 1; i <= n; i++) for (let k = 0; k < n; k++) size = Math.max(size, Math.abs(simplex[i][k] - simplex[0][k]));
    if (spread <= tol * (Math.abs(vals[0]) + 1e-20) && size <= Math.sqrt(tol) * (1 + Math.max(...simplex[0].map(Math.abs)))) { converged = true; break; }
    const cen = new Array(n).fill(0);
    for (let i = 0; i < n; i++) for (let k = 0; k < n; k++) cen[k] += simplex[i][k] / n;
    const lin = (t) => cen.map((c, k) => c + t * (simplex[n][k] - c));
    const xr = lin(-1), fr = F(xr);
    if (fr < vals[0]) {
      const xe = lin(-2), fe = F(xe);
      if (fe < fr) { simplex[n] = xe; vals[n] = fe; } else { simplex[n] = xr; vals[n] = fr; }
    } else if (fr < vals[n - 1]) { simplex[n] = xr; vals[n] = fr; }
    else {
      const xc = fr < vals[n] ? lin(-0.5) : lin(0.5), fc = F(xc);
      if (fc < Math.min(fr, vals[n])) { simplex[n] = xc; vals[n] = fc; }
      else {
        for (let i = 1; i <= n; i++) { simplex[i] = simplex[i].map((v, k) => simplex[0][k] + 0.5 * (v - simplex[0][k])); vals[i] = F(simplex[i]); }
      }
    }
  }
  let size = 0;
  for (let i = 1; i <= n; i++) for (let k = 0; k < n; k++) size = Math.max(size, Math.abs(simplex[i][k] - simplex[0][k]));
  const pt = simplex[0];
  const warnings = converged ? ["Nelder-Mead finds a local minimum; the error bound is the final simplex size (heuristic)."] : ["Iteration limit reached before the simplex collapsed."];
  const dg = Math.max(0, Math.min(8, Math.floor(-Math.log10(Math.max(size, 1e-16) / Math.max(1e-300, ...pt.map(Math.abs))))));
  return Object.assign(record({
    value: "(" + pt.map((v) => fmtNum(v, Math.max(1, dg))).join(", ") + ")", digits: dg, requested: opts.digits ?? 8,
    errorBound: fmtErr(size), method: "nelder-mead", iterations: it, converged, warnings,
  }), { point: pt, fx: vals[0] });
}
// Local extrema on [lo, hi] as roots of the AD derivative, classified with f''.
export function localExtrema(node, x, opts = {}) {
  const name = varName(x);
  const F1 = makeFuncs(node, name, 1);
  const res = findRootsF(F1, opts);
  const F0 = makeFuncs(node, name, 0);
  const digits = opts.digits ?? 15;
  const extrema = [];
  for (const r of res.roots) {
    const xv = Number(r.value);
    const d2 = F1.fd(xv)[1];
    let kind;
    if (Number.isFinite(d2) && Math.abs(d2) > 1e-9) kind = d2 > 0 ? "min" : "max";
    else {
      const h = 1e-4 * (1 + Math.abs(xv));
      const l = F1.f(xv - h), rr = F1.f(xv + h);
      kind = l < 0 && rr > 0 ? "min" : l > 0 && rr < 0 ? "max" : "stationary";
    }
    const xB = B.fromString(r.value, B.digitsToBits(digits) + 32);
    const fv = safeBF(() => F0.bf(xB, B.digitsToBits(digits) + 32));
    extrema.push({ kind, x: r, fx: fv ? B.toString(fv, digits) : "undefined" });
  }
  return { extrema, discontinuities: res.discontinuities, window: res.window, complete: false,
    caveat: res.caveat.replace("Roots", "Critical points") + " Endpoint extrema of the window are not reported.", warnings: res.warnings };
}

// ---------------------------------------------------------------------------------------
// ODE: Dormand-Prince 5(4) with adaptive steps and Hermite dense output
// ---------------------------------------------------------------------------------------
const DP = {
  c: [0, 1 / 5, 3 / 10, 4 / 5, 8 / 9, 1, 1],
  a: [[], [1 / 5], [3 / 40, 9 / 40], [44 / 45, -56 / 15, 32 / 9], [19372 / 6561, -25360 / 2187, 64448 / 6561, -212 / 729],
    [9017 / 3168, -355 / 33, 46732 / 5247, 49 / 176, -5103 / 18656], [35 / 384, 0, 500 / 1113, 125 / 192, -2187 / 6784, 11 / 84]],
  e: [71 / 57600, 0, -71 / 16695, 71 / 1920, -17253 / 339200, 22 / 525, -1 / 40],
};
// solveODE(rhs, t, ys, t0, y0, t1, opts): y' = rhs(t, y). rhs is an array of trees (one per
// component, in variables t and ys) or a JS function (t, y[]) -> y'[].
export function solveODE(rhs, t, ys, t0, y0, t1, opts = {}) {
  let fn;
  if (typeof rhs === "function") fn = rhs;
  else {
    const list = Array.isArray(rhs) ? rhs : [rhs];
    const vars = [varName(t), ...(Array.isArray(ys) ? ys : [ys]).map(varName)];
    const cs = list.map((r) => compileDouble(r, vars));
    fn = (tt, y) => cs.map((c) => c(tt, ...y));
  }
  y0 = Array.isArray(y0) ? y0.slice() : [y0];
  const n = y0.length;
  const rtol = opts.rtol ?? 1e-10, atol = opts.atol ?? 1e-12;
  const maxSteps = opts.maxSteps ?? 100000;
  const nSamples = opts.samples ?? 101;
  const dir = t1 >= t0 ? 1 : -1;
  const warnings = [];
  let tt = t0, y = y0.slice(), k1 = fn(tt, y);
  let h = opts.h0 ?? dir * Math.min(Math.abs(t1 - t0) / 100, 0.1 * Math.max(1e-6, Math.abs(t1 - t0)));
  const T = [tt], Y = [y.slice()], FY = [k1.slice()];
  let steps = 0, rejected = 0, evals = 1, errSum = new Array(n).fill(0), converged = false;
  const dl = deadline(opts.timeLimitMs ?? 10000);
  if (k1.some((v) => !Number.isFinite(v))) warnings.push("The right-hand side is undefined at the initial point.");
  else {
    while (steps < maxSteps) {
      if (dir * (tt - t1) >= 0) { converged = true; break; }
      if (dl.expired()) { warnings.push("Time limit reached."); break; }
      if (dir * (tt + h - t1) > 0) h = t1 - tt;
      const K = [k1];
      let bad = false;
      for (let s = 1; s < 7; s++) {
        const yi = y.map((v, i) => { let acc = v; for (let j = 0; j < s; j++) acc += h * DP.a[s][j] * K[j][i]; return acc; });
        const ks = fn(tt + DP.c[s] * h, yi);
        evals++;
        if (ks.some((v) => !Number.isFinite(v))) { bad = true; break; }
        K.push(ks);
      }
      let err = 0, ynew = null, e = null;
      if (!bad) {
        ynew = y.map((v, i) => { let acc = v; for (let j = 0; j < 6; j++) acc += h * DP.a[6][j] * K[j][i]; return acc; });
        e = y.map((v, i) => { let acc = 0; for (let j = 0; j < 7; j++) acc += h * DP.e[j] * K[j][i]; return acc; });
        for (let i = 0; i < n; i++) { const sc = atol + rtol * Math.max(Math.abs(y[i]), Math.abs(ynew[i])); err += (e[i] / sc) ** 2; }
        err = Math.sqrt(err / n);
      }
      if (bad || !Number.isFinite(err)) { h *= 0.25; rejected++; }
      else if (err <= 1) {
        tt += h; y = ynew; k1 = K[6]; steps++;
        for (let i = 0; i < n; i++) errSum[i] += Math.abs(e[i]);
        T.push(tt); Y.push(y.slice()); FY.push(k1.slice());
        h *= Math.min(5, Math.max(0.2, 0.9 * err ** -0.2));
      } else { h *= Math.max(0.2, 0.9 * err ** -0.2); rejected++; }
      if (Math.abs(h) < 1e-14 * Math.max(1, Math.abs(tt))) { warnings.push(`Step size underflow at t = ${fmtNum(tt, 8)} (singularity or stiffness).`); break; }
    }
    if (steps >= maxSteps) warnings.push("Maximum number of steps reached.");
  }
  // dense output by cubic Hermite interpolation between accepted steps
  const ts = [], yOut = [];
  let seg = 0;
  const tEnd = T[T.length - 1];
  for (let s = 0; s < nSamples; s++) {
    const tsv = nSamples === 1 ? t0 : t0 + ((t1 - t0) * s) / (nSamples - 1);
    if (dir * (tsv - tEnd) > 1e-12 * Math.max(1, Math.abs(tEnd))) break;
    while (seg < T.length - 2 && dir * (tsv - T[seg + 1]) > 0) seg++;
    if (T.length === 1) { ts.push(tsv); yOut.push(Y[0].slice()); continue; }
    const ta = T[seg], tb = T[seg + 1], hh = tb - ta;
    const th = hh === 0 ? 0 : (tsv - ta) / hh;
    const h00 = 2 * th ** 3 - 3 * th ** 2 + 1, h10 = th ** 3 - 2 * th ** 2 + th, h01 = -2 * th ** 3 + 3 * th ** 2, h11 = th ** 3 - th ** 2;
    ts.push(tsv);
    yOut.push(Y[seg].map((ya, i) => h00 * ya + h10 * hh * FY[seg][i] + h01 * Y[seg + 1][i] + h11 * hh * FY[seg + 1][i]));
  }
  const yEnd = Y[Y.length - 1];
  const final = yEnd.map((v, i) => {
    const eb = errSum[i] + EPS * Math.abs(v) * (steps + 1);
    const dg = v === 0 ? 0 : Math.max(0, Math.min(15, Math.floor(-Math.log10(eb / Math.abs(v)))));
    return record({ value: fmtNum(v, Math.max(1, dg)), digits: dg, requested: opts.digits ?? Math.round(-Math.log10(rtol)), errorBound: fmtErr(eb),
      method: "dormand-prince 5(4)", iterations: steps, converged,
      warnings: ["errorBound is the accumulated local error estimate (heuristic; global error is not certified)."] });
  });
  return { t: ts, y: yOut, tEnd, final, steps, rejected, evaluations: evals, converged, method: "dormand-prince 5(4) adaptive, cubic hermite dense output", warnings };
}

// ---------------------------------------------------------------------------------------
// linear systems in floating point
// ---------------------------------------------------------------------------------------
export function luDecompose(A) {
  const n = A.length;
  const lu = A.map((r) => r.slice());
  const perm = [...Array(n).keys()];
  let sign = 1, singular = false;
  const scale = Math.max(1e-300, ...A.flat().map(Math.abs));
  for (let k = 0; k < n; k++) {
    let p = k;
    for (let i = k + 1; i < n; i++) if (Math.abs(lu[i][k]) > Math.abs(lu[p][k])) p = i;
    if (Math.abs(lu[p][k]) <= n * EPS * scale) { singular = true; continue; }
    if (p !== k) { [lu[p], lu[k]] = [lu[k], lu[p]]; [perm[p], perm[k]] = [perm[k], perm[p]]; sign = -sign; }
    for (let i = k + 1; i < n; i++) {
      const m = (lu[i][k] /= lu[k][k]);
      if (m !== 0) for (let j = k + 1; j < n; j++) lu[i][j] -= m * lu[k][j];
    }
  }
  return { lu, perm, sign, singular };
}
export function luSolve(dec, b) {
  const { lu, perm } = dec;
  const n = lu.length;
  const x = perm.map((p) => b[p]);
  for (let i = 0; i < n; i++) for (let j = 0; j < i; j++) x[i] -= lu[i][j] * x[j];
  for (let i = n - 1; i >= 0; i--) {
    for (let j = i + 1; j < n; j++) x[i] -= lu[i][j] * x[j];
    x[i] /= lu[i][i];
  }
  return x;
}
export function det(A) {
  const d = luDecompose(A);
  if (d.singular) return 0;
  let r = d.sign;
  for (let i = 0; i < A.length; i++) r *= d.lu[i][i];
  return r;
}
export function inverse(A) {
  const d = luDecompose(A);
  if (d.singular) return null;
  const n = A.length;
  const cols = [];
  for (let j = 0; j < n; j++) { const e = new Array(n).fill(0); e[j] = 1; cols.push(luSolve(d, e)); }
  return A.map((_, i) => cols.map((c) => c[i]));
}
const norm1 = (A) => Math.max(...A[0].map((_, j) => A.reduce((s, r) => s + Math.abs(r[j]), 0)));
// 1-norm condition number (exact for small matrices via the explicit inverse).
export function conditionNumber(A) {
  const inv = inverse(A);
  return inv ? norm1(A) * norm1(inv) : Infinity;
}
export function solveLinear(A, b) {
  const d = luDecompose(A);
  const warnings = [];
  if (d.singular) return { x: null, cond: Infinity, singular: true, residual: null, warnings: ["The matrix is singular to working precision."] };
  const x = luSolve(d, b);
  // one step of iterative refinement
  const r = b.map((bi, i) => bi - A[i].reduce((s, a, j) => s + a * x[j], 0));
  const dx = luSolve(d, r);
  for (let i = 0; i < x.length; i++) x[i] += dx[i];
  const cond = conditionNumber(A);
  const res = Math.max(...b.map((bi, i) => Math.abs(bi - A[i].reduce((s, a, j) => s + a * x[j], 0))));
  if (cond > 1e12) warnings.push(`Ill-conditioned matrix (cond ~ ${cond.toExponential(1)}); about ${Math.max(0, Math.floor(16 - Math.log10(cond)))} digits can be trusted.`);
  return { x, cond, singular: false, residual: res, relErrorEstimate: cond * EPS, warnings };
}

// ---------------------------------------------------------------------------------------
// infinite series: Levin u-transform in BigFloat
// ---------------------------------------------------------------------------------------
// term(k: BigInt) -> BigFloat. Returns { valueBF, converged, errBF, terms, warning }.
function levinSum(term, n0, { digits, wp: wpIn, maxTerms = 160, timeLimitMs = 8000 }) {
  const dl = deadline(timeLimitMs);
  const target = B.digitsToBits(digits) + 8;
  const S = [], a = [];
  let s = B.ZERO;
  const wpTerms = Math.max(wpIn || 0, 2 * target + 64);
  const getTerm = (j) => {
    const v = term(n0 + BigInt(j));
    if (v instanceof Complex) throw unsupported("complex series terms");
    return v;
  };
  const Ts = [];
  let converged = false, errBF = null, warning = null;
  const need = (T) => B.mulPow2(B.abs(T), -target);
  for (let j = 0; j < maxTerms; j++) {
    if (dl.expired()) { warning = "time limit reached"; break; }
    const t = getTerm(j);
    a.push(t);
    s = B.add(s, t, wpTerms);
    S.push(s);
    if (t.m === 0n) {
      // exactly zero term: check whether the series terminates
      let allZero = true;
      for (let q = 1; q <= 3; q++) if (getTerm(j + q).m !== 0n) { allZero = false; break; }
      if (allZero && j >= 3) { return { valueBF: s, converged: true, errBF: B.ZERO, terms: j + 1 }; }
      continue;
    }
    const k = j; // use terms 0..k
    if (k < 3 || a.some((x) => x.m === 0n)) continue;
    // Levin u: T_k = sum c_j S_j/w_j / sum c_j / w_j, c_j = (-1)^j C(k,j) (j+1)^(k-1), w_j = (j+1) a_j
    let maxc = 0n;
    const cs = [];
    let binom = 1n;
    for (let i = 0; i <= k; i++) {
      if (i > 0) binom = (binom * BigInt(k - i + 1)) / BigInt(i);
      const cj = (i % 2 ? -1n : 1n) * binom * BigInt(i + 1) ** BigInt(k - 1);
      cs.push(cj);
      const ac = cj < 0n ? -cj : cj;
      if (ac > maxc) maxc = ac;
    }
    const w = wpTerms + B.bitLen(maxc) + 32;
    let num = B.ZERO, den = B.ZERO;
    for (let i = 0; i <= k; i++) {
      const wi = B.mul(B.fromInt(i + 1), a[i], w);
      const ci = B.fromBigInt(cs[i]);
      const q = B.div(ci, wi, w);
      den = B.add(den, q, w);
      num = B.add(num, B.mul(q, S[i], w), w);
    }
    if (den.m === 0n) continue;
    const T = B.div(num, den, wpTerms);
    Ts.push(T);
    const L = Ts.length;
    if (L >= 3) {
      const d1 = B.abs(B.sub(Ts[L - 1], Ts[L - 2], wpTerms)), d2 = B.abs(B.sub(Ts[L - 2], Ts[L - 3], wpTerms));
      const nd = need(Ts[L - 1]);
      if (B.cmp(d1, nd) <= 0 && B.cmp(d2, B.mulPow2(nd, 8)) <= 0) { converged = true; errBF = B.max(d1, B.mulPow2(d2, -4)); break; }
      errBF = d1;
    }
  }
  // divergence check for positive, slowly decaying terms: a_n ~ C n^-p with p <= 1
  const kk = a.length;
  if (kk >= 16) {
    const x1 = a[Math.floor(kk / 2) - 1], x2 = a[kk - 1];
    if (x1.m > 0n && x2.m > 0n && a.slice(kk / 2).every((v) => v.m > 0n)) {
      const n1 = Number(n0) + Math.floor(kk / 2) - 1, n2 = Number(n0) + kk - 1;
      const p = Math.log(B.toNumber(x1) / B.toNumber(x2)) / Math.log(Math.max(n2, 1) / Math.max(n1, 1));
      if (Number.isFinite(p) && p > 0 && p <= 1.02 && n1 > 0) {
        return { valueBF: Ts.length ? Ts[Ts.length - 1] : s, converged: false, errBF: null, terms: kk, warning: `the series appears divergent (terms decay like n^-${p.toFixed(2)}, exponent <= 1)` };
      }
    }
  }
  if (!Ts.length) return { valueBF: s, converged: false, errBF: null, terms: kk, warning: warning || "not enough nonzero terms" };
  return { valueBF: Ts[Ts.length - 1], converged, errBF, terms: kk, warning: converged ? null : warning || "the Levin transform did not stabilise" };
}
// sumInfinite(node, n, n0, {digits}): sum_{n=n0}^{oo} node, via the Levin u-transform.
export function sumInfinite(node, n, n0 = 1, opts = {}) {
  const requested = Math.max(1, Math.floor(opts.digits ?? 15));
  const name = varName(n);
  const wp = 2 * B.digitsToBits(requested) + 64;
  const BA = new BFAlgebra(wp, "real");
  const f = compile(eqToExpr(node), [name], BA);
  const start = typeof n0 === "object" && n0 && n0.k ? B.toNumber(evalTree(n0, {}, { digits: 20 })) : Number(n0);
  let r;
  try {
    r = levinSum((k) => f([B.fromBigInt(k)]), BigInt(start), { digits: requested, wp, maxTerms: opts.maxTerms ?? 160, timeLimitMs: opts.timeLimitMs ?? 8000 });
  } catch (e) {
    if (isUndefCode(e)) return record({ value: "undefined", digits: 0, requested, errorBound: null, method: "levin u-transform", iterations: 0, converged: false, warnings: ["A term of the series is undefined: " + e.message.replace(/^Quelvra: /, "")] });
    throw e;
  }
  const v = r.valueBF;
  const warnings = [];
  if (r.warning) warnings.push(r.warning);
  if (r.converged) warnings.push("errorBound is estimated from successive Levin transforms (heuristic, not certified).");
  const eb = r.errBF ?? null;
  const dg = r.converged ? requested : eb ? digitsFrom(v, eb, requested) : 0;
  const ulpHalf = v.m === 0n ? B.ZERO : B.mulPow2(pow10(decExp(v) - Math.max(1, dg) + 1, 64), -1);
  return record({
    value: v.m === 0n ? "0" : B.toString(v, Math.max(1, dg)), digits: dg, requested,
    errorBound: eb ? fmtErr(B.add(eb, ulpHalf, 64)) : null, method: "levin u-transform (multiprecision)",
    iterations: r.terms, converged: r.converged, warnings,
  });
}
