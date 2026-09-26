// Shared helpers for the calculus engines (limits, series, sums, ODEs).
//
//   Budget          time / operation guard every loop in these modules checks
//   simp(u)         canonical simplification with a fresh, generous context
//   hp(u, env)      high-precision evaluation (BigFloat via numeric.js) with precision agreement
//   isZeroStrong    exact-then-numeric zero recognition of coefficient trees
//   constSign       sign of a real constant expression (exact when possible, else certified numeric)
//
// Nothing here guesses: undecidable questions throw an Error with code "UNDECIDABLE".

import * as X from "../expr.js";
import * as N from "../num.js";
import { simplify, expand, makeCtx, together, numerDenom } from "../simplify.js";
import * as NU from "../numeric.js";
import * as B from "../bigfloat.js";

export const now = () => (typeof performance !== "undefined" ? performance.now() : Date.now());

export function qerr(code, message) {
  const e = new Error(message);
  e.code = code;
  return e;
}

// ---------------------------------------------------------------- budget
let DEADLINE = Infinity;
let OPS = 0;
export const Budget = {
  // run fn with a deadline (ms from now); nested calls keep the tighter deadline
  with(ms, fn) {
    const prevD = DEADLINE;
    const d = now() + ms;
    if (d < DEADLINE) DEADLINE = d;
    try { return fn(); } finally { DEADLINE = prevD; }
  },
  withDeadline(deadline, fn) {
    const prevD = DEADLINE;
    if (deadline && deadline < DEADLINE) DEADLINE = deadline;
    try { return fn(); } finally { DEADLINE = prevD; }
  },
  check() {
    if ((++OPS & 63) === 0 && now() > DEADLINE) throw qerr("TIMEOUT", "time limit reached");
  },
  hard() { if (now() > DEADLINE) throw qerr("TIMEOUT", "time limit reached"); },
  remaining() { return DEADLINE - now(); },
};

// ---------------------------------------------------------------- simplification
export function simp(u) {
  Budget.check();
  return simplify(u, makeCtx({ budget: { ops: 400000 } }));
}
export function simpExpand(u) {
  try { return expand(u, makeCtx({ budget: { ops: 400000 } })); } catch (e) { if (e && e.code === "BUDGET") return simp(u); throw e; }
}
// A smaller of the canonical and expanded forms (expanded when it cancels to something shorter).
export function tidy(u) {
  const s = simp(u);
  if (X.isNum(s) || X.size(s) > 400) return s;
  try {
    const e = expand(s, makeCtx({ budget: { ops: 200000 } }));
    if (e === X.ZERO || X.size(e) < X.size(s)) return e;
  } catch (e) { if (!e || e.code !== "BUDGET") throw e; }
  return s;
}

export const sym = (n) => (typeof n === "string" ? X.sym(n) : n);
export const nameOf = (v) => (typeof v === "string" ? v : v.name);
export const isNegInf = (u) => u.k === "mul" && u.args.length === 2 && X.isNum(u.args[0]) && N.isNeg(u.args[0].v) && u.args[1] === X.OO;
export const NEG_OO = X.mul(X.NEG_ONE, X.OO);
export const hasInf = (u) => X.contains(u, X.OO);

// ---------------------------------------------------------------- high precision evaluation
// Returns { re, im } as JS numbers (re may be +-Infinity for huge magnitudes, 0 for tiny ones),
// plus `big` (the BigFloat real part) and `ok`. Precision is raised until two evaluations agree.
function toEnv(env) {
  const out = {};
  for (const [k, v] of Object.entries(env || {})) out[k] = v;
  return out;
}
function bfToNum(v) {
  if (!v) return NaN;
  if (v instanceof B.BigFloat) return B.toNumber(v);
  return NaN;
}
function evalOnce(u, env, digits, mode) {
  const v = NU.evalTree(u, env, { digits, mode: mode || "real" });
  if (NU.isUndefined(v)) return null;
  if (v instanceof B.BigFloat) return { re: v, im: B.ZERO };
  if (v && v.re !== undefined) return { re: v.re, im: v.im };
  return null;
}
function relClose(a, b, digits) {
  // BigFloat agreement to about `digits` significant digits (absolute near zero)
  const d = B.abs(B.sub(a, b, 64));
  if (d.m === 0n) return true;
  const scale = B.max(B.abs(a), B.abs(b));
  const td = B.top(d), ts = scale.m === 0n ? -Infinity : B.top(scale);
  return td - ts < -digits * 3.32 || td < -3.32 * (digits + 30);
}
export function hp(u, env = {}, opts = {}) {
  const e = toEnv(env);
  let digits = opts.digits || 30;
  const maxDigits = opts.maxDigits || 600;
  let prev = null;
  for (let it = 0; it < 7; it++) {
    Budget.hard();
    let v;
    try { v = evalOnce(u, e, digits, opts.mode); } catch (err) {
      if (err && (err.code === "BUDGET" || err.code === "UNSUPPORTED" || err.code === "UNBOUND" || err.code === "DOMAIN" || err.code === "UNDEFINED" || err.code === "UNDERFLOW" || err.code === "NOCONVERGE" || err.code === "NOT_CONSTANT")) return { ok: false, reason: err.message };
      throw err;
    }
    if (!v) return { ok: false, reason: "undefined" };
    if (prev && relClose(prev.re, v.re, 12) && relClose(prev.im, v.im, 12)) {
      const re = bfToNum(v.re), im = bfToNum(v.im);
      return { ok: true, re, im, big: v.re, bigIm: v.im, digits };
    }
    prev = v;
    if (digits >= maxDigits) break;
    digits = Math.min(maxDigits, digits * 2);
  }
  if (prev) return { ok: true, re: bfToNum(prev.re), im: bfToNum(prev.im), big: prev.re, bigIm: prev.im, digits, unstable: true };
  return { ok: false, reason: "no agreement" };
}
// log10 of |value| from a BigFloat (works far outside the double range)
export function log10Abs(big) {
  if (!big || big.m === 0n) return -Infinity;
  const bl = B.bitLen(big.m < 0n ? -big.m : big.m);
  const lead = Number((big.m < 0n ? -big.m : big.m) >> BigInt(Math.max(0, bl - 53)));
  return (Math.log2(lead) + Math.max(0, bl - 53) + big.e) * 0.30102999566398120;
}
export const bigSign = (big) => (!big ? 0 : big.m > 0n ? 1 : big.m < 0n ? -1 : 0);

// ---------------------------------------------------------------- zero recognition / signs
const PARAM_VALUES = [0.7310585786, 1.618033988, 2.302585093, 0.4142135624, 3.141592654 / 2];
export function probeEnvs(u, special = {}) {
  const names = [...X.freeSymbols(u)];
  const out = [];
  for (let i = 0; i < 4; i++) {
    const env = {};
    for (const n of names) {
      if (special[n]) env[n] = special[n][i % special[n].length];
      else env[n] = PARAM_VALUES[(i + n.length + n.charCodeAt(0)) % PARAM_VALUES.length] + 0.137 * i;
    }
    out.push(env);
  }
  return out;
}
// Is the coefficient tree identically zero? true / false, or throws UNDECIDABLE.
// `special` maps symbol names to probe values to use (e.g. large x for asymptotic coefficients).
export function isZeroStrong(c, special = {}) {
  if (X.isNum(c)) return X.isZero(c);
  if (c === X.UNDEF) throw qerr("UNDEFINED", "undefined coefficient");
  let s = simp(c);
  if (s === X.ZERO) return true;
  if (X.isNum(s)) return false;
  const e = X.size(s) < 300 ? simpExpand(s) : s;
  if (e === X.ZERO) return true;
  if (X.isNum(e)) return false;
  let zeroCount = 0, tried = 0;
  const mode = X.contains(s, X.I) ? "complex" : "real";
  for (const env of probeEnvs(s, special)) {
    const v = hp(s, env, { digits: 40, maxDigits: 160, mode });
    if (!v.ok) continue;
    tried++;
    const mag = Math.max(Math.abs(log10Abs(v.big)) === Infinity ? -Infinity : log10Abs(v.big), v.bigIm ? log10Abs(v.bigIm) : -Infinity);
    if (mag > -25) return false;
    if (mag < -35 || (v.big.m === 0n && (!v.bigIm || v.bigIm.m === 0n))) zeroCount++;
  }
  if (tried >= 2 && zeroCount === tried) return true;
  throw qerr("UNDECIDABLE", "cannot decide whether a coefficient is zero");
}
// Sign of a real constant tree: 1, -1, 0. Throws UNDECIDABLE when it cannot be certified.
export function constSign(c) {
  const s = simp(c);
  if (X.isNum(s)) return N.sign(s.v);
  if (s === X.PI || s === X.E) return 1;
  if (X.freeSymbols(s).size) throw qerr("UNDECIDABLE", "the sign depends on a parameter");
  const v = hp(s, {}, { digits: 40, maxDigits: 300 });
  if (!v.ok) throw qerr("UNDEFINED", "the value is undefined");
  if (v.bigIm && v.bigIm.m !== 0n && log10Abs(v.bigIm) > log10Abs(v.big) - 30 && log10Abs(v.bigIm) > -40) throw qerr("COMPLEX", "the value is not real");
  if (v.big.m === 0n || log10Abs(v.big) < -60) {
    if (isZeroStrong(s)) return 0;
    throw qerr("UNDECIDABLE", "cannot decide the sign of a constant");
  }
  return bigSign(v.big);
}
// Is the constant real (imaginary part zero)? Uses the exact form first.
export function isRealConst(c) {
  if (!X.contains(c, X.I)) {
    const v = hp(c, {}, { digits: 30, maxDigits: 120 });
    if (!v.ok) return false;
    return !v.bigIm || v.bigIm.m === 0n || log10Abs(v.bigIm) < log10Abs(v.big) - 25;
  }
  return false;
}

// Real and imaginary parts of a tree built from real symbols and the constant I (x, parameters
// assumed real). e^(a + i b) is expanded with Euler's formula; quotients are rationalised.
// Returns { re, im } or null when the structure is not supported.
export function complexParts(u) {
  if (!X.contains(u, X.I)) return { re: u, im: X.ZERO };
  let failed = false;
  const zi = X.sym("__i");
  const pre = X.mapTree(u, (w) => {
    if (w.k === "pow" && X.contains(w.args[1], X.I)) {
      if (w.args[0] !== X.E) { failed = true; return w; }
      const p = complexParts(simp(w.args[1]));
      if (!p) { failed = true; return w; }
      return X.mul(X.pow(X.E, p.re), X.add(X.fn("cos", p.im), X.mul(X.I, X.fn("sin", p.im))));
    }
    if (w.k === "fn" && w.args.some((a) => X.contains(a, X.I))) { failed = true; return w; }
    return w;
  });
  if (failed) return null;
  const v = X.replace(simp(pre), X.I, zi);
  const ctx = () => makeCtx({ budget: { ops: 400000 } });
  const t = together(simp(v), ctx());
  const [nu, de] = numerDenom(t);
  const fold = (w) => {
    const e = expand(w, ctx());
    const cs = coeffsIn(e, "__i");
    if (!cs) return null;
    const re = [], im = [];
    cs.forEach((c, j) => { const sg = j % 4 < 2 ? c : X.mul(X.NEG_ONE, c); (j % 2 ? im : re).push(sg); });
    return [simp(X.add(...re)), simp(X.add(...im))];
  };
  const A = fold(nu), Bd = fold(de);
  if (!A || !Bd) return null;
  const [a, b] = A, [c, d] = Bd;
  if (d === X.ZERO) return { re: simp(X.mul(a, X.pow(c, X.NEG_ONE))), im: simp(X.mul(b, X.pow(c, X.NEG_ONE))) };
  const den = X.pow(X.add(X.pow(c, X.TWO), X.pow(d, X.TWO)), X.NEG_ONE);
  return { re: simp(X.mul(X.add(X.mul(a, c), X.mul(b, d)), den)), im: simp(X.mul(X.add(X.mul(b, c), X.mul(X.NEG_ONE, a, d)), den)) };
}
// coefficients of a polynomial in the symbol `name` (other factors are coefficients)
function coeffsIn(e, name) {
  const terms = e.k === "add" ? e.args : [e];
  const out = [];
  for (const t of terms) {
    const fs = t.k === "mul" ? t.args : [t];
    let d = 0;
    const rest = [];
    for (const f of fs) {
      if (f.k === "sym" && f.name === name) d += 1;
      else if (f.k === "pow" && f.args[0].k === "sym" && f.args[0].name === name && X.isInt(f.args[1]) && f.args[1].v.n > 0n) d += Number(f.args[1].v.n);
      else if (X.hasSym(f, name)) return null;
      else rest.push(f);
    }
    out[d] = out[d] ? X.add(out[d], X.mul(...rest)) : X.mul(...rest);
  }
  return Array.from(out, (c) => c || X.ZERO);
}

// Rational helpers
export const R = {
  of: (u) => (X.isNum(u) ? u.v : null),
  key: (r) => `${r.n}/${r.d}`,
  min: (a, b) => (a === null ? b : b === null ? a : N.cmp(a, b) <= 0 ? a : b),
  max: (a, b) => (a === null ? b : b === null ? a : N.cmp(a, b) >= 0 ? a : b),
};

export { X, N };
