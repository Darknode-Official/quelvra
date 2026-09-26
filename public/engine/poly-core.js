// Quelvra polynomial engine, core layer.
//
// Representations
//   UPoly  univariate polynomial over Q: dense array of Rationals, index = degree, no trailing
//          zeros. The zero polynomial is []. Degree of [] is -1 by convention.
//   ZPoly  univariate polynomial over Z: dense array of BigInt, same conventions (internal fast path).
//   MPoly  sparse multivariate polynomial over Q: { vars: string[], terms: Map<key, Rational> }
//          where key is the exponent vector joined with "," (in `vars` order) and every stored
//          coefficient is nonzero.
//   Rec    recursive dense form used internally for multivariate gcd / division / resultants:
//          a level-0 Rec is a Rational, a level-L Rec is an array of level-(L-1) Recs indexed by
//          the degree of the outermost variable. A level-1 Rec is exactly a UPoly.
//
// All arithmetic is exact (BigInt / Rational). JS Number is used only for exponents, loop
// counters and heuristics. Long-running algorithms tick a shared operation budget and throw an
// Error with code "BUDGET" when it is exhausted; every loop also has an explicit bound.

import * as N from "./num.js";
import * as X from "./expr.js";
import { simplify, expand, makeCtx } from "./simplify.js";

// simplify.js keeps ONE default budget object for the whole process and never refills it, so
// the S.* builders and simplify(u) without a ctx eventually throw BUDGET in long sessions.
// This module (and the other poly modules) therefore builds RAW trees and canonicalises them
// with a fresh context per call.
export const canon = (u) => simplify(u, makeCtx());
export const RB = {
  add: (...a) => X.add(...a),
  sub: (a, b) => X.add(a, X.mul(X.NEG_ONE, b)),
  mul: (...a) => X.mul(...a),
  div: (a, b) => X.mul(a, X.pow(b, X.NEG_ONE)),
  pow: (a, b) => X.pow(a, b),
  neg: (a) => X.mul(X.NEG_ONE, a),
  sqrt: (a) => X.pow(a, X.HALF),
  fn: (name, ...a) => X.fn(name, ...a),
};

const Q0 = N.ZERO, Q1 = N.ONE;

// ---------------------------------------------------------------- budget
let BUD = null;
const DEFAULT_OPS = 4_000_000;
export function budgetError(what = "polynomial") {
  const e = new Error(`Quelvra: operation budget exhausted (${what})`);
  e.code = "BUDGET";
  return e;
}
export function tick(n = 1) {
  if (BUD && (BUD.ops -= n) < 0) throw budgetError();
}
// Run fn under a budget. opts.budget = { ops } (the same shape simplify uses). Nested calls
// without an explicit budget share the caller's budget.
export function guard(opts, fn) {
  const b = opts && opts.budget;
  if (BUD && !b) return fn();
  const prev = BUD;
  BUD = b || { ops: DEFAULT_OPS };
  try { return fn(); } finally { BUD = prev; }
}

// ---------------------------------------------------------------- rationals
export function toRat(v) {
  if (v && typeof v === "object" && typeof v.n === "bigint" && typeof v.d === "bigint") return v;
  if (typeof v === "bigint") return N.Q(v);
  if (typeof v === "number") {
    if (!Number.isInteger(v)) throw new TypeError("Quelvra: non-integer JS number; pass a string or Rational");
    return N.Q(BigInt(v));
  }
  if (typeof v === "string") {
    const m = v.match(/^\s*([+-]?\d+)\s*\/\s*(\d+)\s*$/);
    if (m) return N.Q(BigInt(m[1]), BigInt(m[2]));
    return N.fromDecimal(v);
  }
  if (v && v.k === "num") return v.v;
  throw new TypeError("Quelvra: cannot convert value to a Rational");
}
const blcm = (a, b) => (a / N.bgcd(a, b)) * b;

// ---------------------------------------------------------------- ZPoly (BigInt[])
export function zNorm(a) {
  let n = a.length;
  while (n > 0 && a[n - 1] === 0n) n--;
  return n === a.length ? a : a.slice(0, n);
}
export function zAdd(a, b) {
  const n = Math.max(a.length, b.length), out = new Array(n);
  for (let i = 0; i < n; i++) out[i] = (i < a.length ? a[i] : 0n) + (i < b.length ? b[i] : 0n);
  return zNorm(out);
}
export function zSub(a, b) {
  const n = Math.max(a.length, b.length), out = new Array(n);
  for (let i = 0; i < n; i++) out[i] = (i < a.length ? a[i] : 0n) - (i < b.length ? b[i] : 0n);
  return zNorm(out);
}
export const zScale = (a, k) => (k === 0n ? [] : a.map((v) => v * k));
function schoolbook(a, b) {
  const out = new Array(a.length + b.length - 1).fill(0n);
  for (let i = 0; i < a.length; i++) {
    const ai = a[i];
    if (ai === 0n) continue;
    for (let j = 0; j < b.length; j++) out[i + j] += ai * b[j];
  }
  return out;
}
function rawAdd(a, b) {
  const n = Math.max(a.length, b.length), out = new Array(n);
  for (let i = 0; i < n; i++) out[i] = (i < a.length ? a[i] : 0n) + (i < b.length ? b[i] : 0n);
  return out;
}
function kara(a, b) {
  if (!a.length || !b.length) return [];
  if (a.length < 40 || b.length < 40) return schoolbook(a, b);
  const h = Math.max(a.length, b.length) >> 1;
  const a0 = a.slice(0, h), a1 = a.slice(h), b0 = b.slice(0, h), b1 = b.slice(h);
  const z0 = kara(a0, b0), z2 = kara(a1, b1), z1 = kara(rawAdd(a0, a1), rawAdd(b0, b1));
  const out = new Array(a.length + b.length + 2 * h + 2).fill(0n);
  for (let i = 0; i < z0.length; i++) { out[i] += z0[i]; out[i + h] -= z0[i]; }
  for (let i = 0; i < z2.length; i++) { out[i + 2 * h] += z2[i]; out[i + h] -= z2[i]; }
  for (let i = 0; i < z1.length; i++) out[i + h] += z1[i];
  return out;
}
export function zMul(a, b) {
  if (!a.length || !b.length) return [];
  tick((a.length * b.length) >> 6);
  return zNorm(a.length >= 40 && b.length >= 40 ? kara(a, b) : schoolbook(a, b));
}
export function zContent(a) {
  let g = 0n;
  for (const v of a) { g = N.bgcd(g, v); if (g === 1n) break; }
  return g;
}
// Primitive part with positive leading coefficient.
export function zPrimitive(a) {
  a = zNorm(a);
  if (!a.length) return a;
  let g = zContent(a);
  if (a[a.length - 1] < 0n) g = -g;
  return g === 1n ? a : a.map((v) => v / g);
}
// Primitive part keeping the sign (divide by the positive content).
export function zPrimPos(a) {
  a = zNorm(a);
  if (!a.length) return a;
  const g = zContent(a);
  return g === 1n ? a : a.map((v) => v / g);
}
export function zDeriv(a) {
  const out = [];
  for (let i = 1; i < a.length; i++) out.push(a[i] * BigInt(i));
  return zNorm(out);
}
// Pseudo-remainder: lc(b)^(deg a - deg b + 1) * a = q*b + r.
export function zPrem(a, b) {
  b = zNorm(b);
  if (!b.length) throw new RangeError("Quelvra: pseudo-division by zero polynomial");
  let r = zNorm(a);
  const db = b.length - 1, l = b[db];
  if (r.length - 1 < db) return r;
  let e = r.length - 1 - db + 1;
  for (let guardN = r.length + 1; r.length && r.length - 1 >= db; ) {
    if (--guardN < 0) throw budgetError("prem");
    tick();
    const c = r[r.length - 1], s = r.length - 1 - db;
    const nr = r.map((v) => v * l);
    for (let j = 0; j <= db; j++) nr[s + j] -= c * b[j];
    r = zNorm(nr);
    e--;
  }
  if (e > 0 && r.length) { const k = l ** BigInt(e); r = r.map((v) => v * k); }
  return r;
}
// Exact division over Z; null when b does not divide a exactly.
export function zDivExact(a, b) {
  b = zNorm(b);
  if (!b.length) throw new RangeError("Quelvra: division by zero polynomial");
  a = zNorm(a);
  if (!a.length) return [];
  const db = b.length - 1;
  if (a.length - 1 < db) return null;
  const r = a.slice(), q = new Array(a.length - db).fill(0n), l = b[db];
  for (let i = a.length - 1; i >= db; i--) {
    const c = r[i];
    if (c === 0n) continue;
    if (c % l !== 0n) return null;
    const t = c / l;
    q[i - db] = t;
    for (let j = 0; j <= db; j++) r[i - db + j] -= t * b[j];
  }
  for (let i = 0; i < db; i++) if (r[i] !== 0n) return null;
  return zNorm(q);
}
export function zEval(a, x) {
  let acc = 0n;
  for (let i = a.length - 1; i >= 0; i--) acc = acc * x + a[i];
  return acc;
}
// sign of a(r) for a Rational r (q^n a(p/q) has the sign of a(p/q) since q > 0)
export function zSignAt(a, r) {
  if (!a.length) return 0;
  const n = a.length - 1;
  let acc = 0n, qpow = 1n;
  const qs = [1n];
  for (let i = 1; i <= n; i++) { qpow *= r.d; qs.push(qpow); }
  for (let i = n; i >= 0; i--) acc = acc * r.n + a[i] * qs[n - i];
  return acc > 0n ? 1 : acc < 0n ? -1 : 0;
}
export function zSignAtInf(a, s) {
  if (!a.length) return 0;
  const l = a[a.length - 1] > 0n ? 1 : -1;
  return s > 0 || (a.length - 1) % 2 === 0 ? l : -l;
}
export function zEq(a, b) {
  if (a.length !== b.length) return false;
  for (let i = 0; i < a.length; i++) if (a[i] !== b[i]) return false;
  return true;
}
export function zPow(a, n) {
  let r = [1n], b = a;
  n = BigInt(n);
  while (n > 0n) { if (n & 1n) r = zMul(r, b); n >>= 1n; if (n) b = zMul(b, b); }
  return r;
}
// primitive gcd over Z (positive leading coefficient)
export function zGcd(a, b) {
  a = zPrimitive(a); b = zPrimitive(b);
  if (!a.length) return b;
  if (!b.length) return a;
  if (a.length < b.length) [a, b] = [b, a];
  for (let guardN = a.length + 2; b.length; ) {
    if (--guardN < 0) throw budgetError("gcd");
    tick();
    const r = zPrem(a, b);
    a = b;
    b = r.length ? zPrimitive(r) : r;
  }
  return zPrimitive(a);
}

// ---------------------------------------------------------------- UPoly (Rational[])
export function norm(p) {
  let n = p.length;
  while (n > 0 && p[n - 1].n === 0n) n--;
  return n === p.length ? p : p.slice(0, n);
}
// poly([c0, c1, ...]) from numbers / BigInt / strings / Rationals, low degree first.
export const poly = (coeffs) => norm(coeffs.map(toRat));
export const deg = (p) => p.length - 1;
export const lc = (p) => (p.length ? p[p.length - 1] : Q0);
export const isZeroPoly = (p) => p.length === 0;
export const constPoly = (c) => norm([toRat(c)]);
export function polyEq(a, b) {
  if (a.length !== b.length) return false;
  for (let i = 0; i < a.length; i++) if (!N.eq(a[i], b[i])) return false;
  return true;
}
export function add(a, b) {
  const n = Math.max(a.length, b.length), out = new Array(n);
  for (let i = 0; i < n; i++) out[i] = i < a.length ? (i < b.length ? N.add(a[i], b[i]) : a[i]) : b[i];
  return norm(out);
}
export function sub(a, b) {
  const n = Math.max(a.length, b.length), out = new Array(n);
  for (let i = 0; i < n; i++) out[i] = i < a.length ? (i < b.length ? N.sub(a[i], b[i]) : a[i]) : N.neg(b[i]);
  return norm(out);
}
export const neg = (a) => a.map(N.neg);
export const scale = (p, c) => (N.isZero(c) ? [] : norm(p.map((v) => N.mul(v, c))));
export const monic = (p) => (p.length ? scale(p, N.inv(lc(p))) : p);
function toZden(p) {
  let L = 1n;
  for (const r of p) if (r.d !== 1n) L = blcm(L, r.d);
  return { z: p.map((r) => (L === 1n ? r.n : r.n * (L / r.d))), d: L };
}
// p = c * z with z primitive over Z and lc(z) > 0.
export function toZ(p) {
  p = norm(p);
  if (!p.length) return { c: Q0, z: [] };
  const { z, d } = toZden(p);
  let g = zContent(z);
  if (z[z.length - 1] < 0n) g = -g;
  return { c: N.Q(g, d), z: g === 1n ? z : z.map((v) => v / g) };
}
export const fromZ = (z, c = Q1) => norm(N.isOne(c) ? z.map((v) => N.Q(v)) : z.map((v) => N.mul(N.Q(v), c)));
export function mul(a, b) {
  if (!a.length || !b.length) return [];
  const A = toZden(a), B = toZden(b);
  const z = zMul(A.z, B.z), d = A.d * B.d;
  return norm(z.map((v) => N.Q(v, d)));
}
export function divmod(a, b) {
  b = norm(b); a = norm(a);
  if (!b.length) throw new RangeError("Quelvra: polynomial division by zero");
  const db = b.length - 1;
  if (a.length - 1 < db) return { q: [], r: a };
  const r = a.slice(), q = new Array(a.length - db).fill(Q0), inv = N.inv(b[db]);
  for (let i = a.length - 1; i >= db; i--) {
    const c = r[i];
    if (c.n === 0n) continue;
    const t = N.mul(c, inv);
    q[i - db] = t;
    for (let j = 0; j <= db; j++) r[i - db + j] = N.sub(r[i - db + j], N.mul(t, b[j]));
  }
  return { q: norm(q), r: norm(r.slice(0, db)) };
}
export const rem = (a, b) => divmod(a, b).r;
export const quo = (a, b) => divmod(a, b).q;
// Divide by (x - r) with Horner's scheme: p = (x - r) q + rem.
export function syntheticDivide(p, r) {
  r = toRat(r);
  p = norm(p);
  if (!p.length) return { q: [], rem: Q0 };
  const n = p.length - 1, q = new Array(n);
  let acc = p[n];
  for (let i = n - 1; i >= 0; i--) { q[i] = acc; acc = N.add(p[i], N.mul(acc, r)); }
  return { q: norm(q), rem: acc };
}
// lc(b)^m a = q b + r with m = max(deg a - deg b + 1, 0).
export function pseudoDivmod(a, b) {
  a = norm(a); b = norm(b);
  const m = Math.max(a.length - b.length + 1, 0);
  const { q, r } = divmod(a, b);
  const k = N.pow(lc(b), m);
  return { q: scale(q, k), r: scale(r, k), m };
}
// Exact quotient a / b, or null when b does not divide a.
export function exactDiv(a, b) {
  const { q, r } = divmod(a, b);
  return r.length ? null : q;
}
export function pow(p, n) {
  n = BigInt(n);
  if (n < 0n) throw new RangeError("Quelvra: negative polynomial power");
  if (n === 0n) return [Q1];
  if (p.length > 1 && BigInt(p.length - 1) * n > 100000n) throw budgetError("power degree");
  let r = [Q1], b = p;
  while (n > 0n) { if (n & 1n) r = mul(r, b); n >>= 1n; if (n) b = mul(b, b); }
  return r;
}
export function evalAt(p, x) {
  x = toRat(x);
  let acc = Q0;
  for (let i = p.length - 1; i >= 0; i--) acc = N.add(N.mul(acc, x), p[i]);
  return acc;
}
export function deriv(p) {
  const out = [];
  for (let i = 1; i < p.length; i++) out.push(N.mul(p[i], N.Q(i)));
  return norm(out);
}
// p(q(x))
export function compose(p, q) {
  let acc = [];
  for (let i = p.length - 1; i >= 0; i--) acc = add(mul(acc, q), p[i].n === 0n ? [] : [p[i]]);
  return acc;
}
// Rational content: p = content(p) * primitivePart(p) with primitivePart integer, primitive, lc > 0.
export const content = (p) => toZ(p).c;
export const primitivePart = (p) => fromZ(toZ(p).z);

// ---------------------------------------------------------------- GCD family
// Monic gcd over Q (primitive PRS over Z). gcd(0, 0) = [].
export function gcd(a, b, opts) {
  return guard(opts, () => {
    a = norm(a); b = norm(b);
    if (!a.length) return monic(b);
    if (!b.length) return monic(a);
    return monic(fromZ(zGcd(toZ(a).z, toZ(b).z)));
  });
}
// Extended gcd: s*a + t*b = g with g monic.
export function xgcd(a, b, opts) {
  return guard(opts, () => {
    let r0 = norm(a), r1 = norm(b), s0 = [Q1], s1 = [], t0 = [], t1 = [Q1];
    for (let guardN = r0.length + r1.length + 2; r1.length; ) {
      if (--guardN < 0) throw budgetError("xgcd");
      tick();
      const { q, r } = divmod(r0, r1);
      [r0, r1] = [r1, r];
      [s0, s1] = [s1, sub(s0, mul(q, s1))];
      [t0, t1] = [t1, sub(t0, mul(q, t1))];
    }
    if (!r0.length) return { g: [], s: [], t: [] };
    const k = N.inv(lc(r0));
    return { g: scale(r0, k), s: scale(s0, k), t: scale(t0, k) };
  });
}
export function lcm(a, b, opts) {
  a = norm(a); b = norm(b);
  if (!a.length || !b.length) return [];
  return monic(exactDiv(mul(a, b), gcd(a, b, opts)));
}

// Square-free factorisation (Yun). p = unit * prod poly_i^mult_i with poly_i square-free,
// pairwise coprime, integer primitive with positive leading coefficient.
export function squareFree(p, opts) {
  return guard(opts, () => {
    p = norm(p);
    if (p.length <= 1) return { unit: lc(p), factors: [] };
    const f = monic(p);
    const out = [];
    let a = gcd(f, deriv(f));
    let b = exactDiv(f, a), c = exactDiv(deriv(f), a);
    let d = sub(c, deriv(b));
    let i = 1;
    while (b.length > 1) {
      if (i > p.length + 1) throw budgetError("square-free");
      tick();
      a = gcd(b, d);
      if (a.length > 1) out.push({ poly: fromZ(toZ(a).z), mult: i });
      b = exactDiv(b, a);
      c = exactDiv(d, a);
      d = sub(c, deriv(b));
      i++;
    }
    let unit = lc(p);
    for (const { poly: q, mult } of out) unit = N.div(unit, N.pow(lc(q), mult));
    return { unit, factors: out };
  });
}
// Square-free part as an integer primitive polynomial (positive leading coefficient).
export function squareFreePart(p, opts) {
  p = norm(p);
  if (p.length <= 1) return p.length ? [Q1] : [];
  const g = gcd(p, deriv(p), opts);
  return fromZ(toZ(exactDiv(p, g)).z);
}

// ---------------------------------------------------------------- rational roots
function divisors(n) {
  n = N.babs(n);
  const { factors, rest } = N.trialFactor(n);
  if (rest !== 1n) return null;
  let ds = [1n];
  for (const [p, e] of factors) {
    const next = [];
    for (const d of ds) { let pk = 1n; for (let k = 0n; k <= e; k++) { next.push(d * pk); pk *= p; } }
    ds = next;
    if (ds.length > 20000) return null;
  }
  return ds.sort((a, b) => (a < b ? -1 : a > b ? 1 : 0));
}
// Distinct rational roots of p, ascending. Uses the rational root theorem with divisibility
// filters f(1) and f(-1); falls back to exact real-root isolation when the coefficients cannot be
// factored quickly (a rational root p/q with q | lc makes lc*root an integer in a known interval).
export function rationalRoots(p, opts) {
  return guard(opts, () => {
    p = norm(p);
    if (p.length <= 1) return [];
    let z = toZ(p).z;
    const roots = [];
    if (z[0] === 0n) { roots.push(Q0); let k = 0; while (z[k] === 0n) k++; z = z.slice(k); }
    if (z.length > 1) {
      const a0 = z[0], an = z[z.length - 1];
      const P = divisors(a0), Qd = divisors(an);
      if (P && Qd && P.length * Qd.length <= 40000) {
        const f1 = zEval(z, 1n), fm1 = zEval(z, -1n);
        const B = rootBound(fromZ(z));
        const seen = new Set();
        for (const q of Qd) for (const pp of P) {
          if (N.bgcd(pp, q) !== 1n) continue;
          for (const s of [1n, -1n]) {
            tick();
            const num = s * pp;
            const r = N.Q(num, q);
            const key = r.n + "/" + r.d;
            if (seen.has(key)) continue;
            seen.add(key);
            if (N.cmp(N.abs(r), B) > 0) continue;
            if (f1 !== 0n && q - num !== 0n && f1 % (q - num) !== 0n) continue;
            if (fm1 !== 0n && q + num !== 0n && fm1 % (q + num) !== 0n) continue;
            if (zSignAt(z, r) === 0) roots.push(r);
          }
        }
      } else {
        const lcz = N.Q(z[z.length - 1] < 0n ? -z[z.length - 1] : z[z.length - 1]);
        for (const iv of isolateRealRoots(fromZ(z))) {
          if (iv.exact) { roots.push(iv.lo); continue; }
          let { lo, hi } = iv;
          // refine until (lc*lo, lc*hi) contains at most one integer, then test it
          const one = N.inv(lcz);
          let it = 0;
          while (N.cmp(N.sub(hi, lo), one) >= 0) {
            if (++it > 4000) throw budgetError("rational roots");
            const r = bisectStep(z, lo, hi);
            if (r.exact) { lo = hi = r.exact; break; }
            lo = r.lo; hi = r.hi;
          }
          if (N.eq(lo, hi)) { roots.push(lo); continue; }
          const m = N.ceil(N.mul(lo, lcz));
          const cand = N.div(N.Q(m), lcz);
          if (N.cmp(cand, hi) <= 0 && zSignAt(z, cand) === 0) roots.push(cand);
        }
      }
    }
    const uniq = [];
    for (const r of roots.sort(N.cmp)) if (!uniq.length || !N.eq(uniq[uniq.length - 1], r)) uniq.push(r);
    return uniq;
  });
}

// ---------------------------------------------------------------- resultant / discriminant
function bareiss(M, R) {
  const n = M.length;
  if (n === 0) return R.one;
  let sign = 1, prev = R.one;
  for (let k = 0; k < n - 1; k++) {
    tick(n);
    if (R.isZero(M[k][k])) {
      let s = -1;
      for (let i = k + 1; i < n; i++) if (!R.isZero(M[i][k])) { s = i; break; }
      if (s < 0) return R.zero;
      [M[k], M[s]] = [M[s], M[k]];
      sign = -sign;
    }
    for (let i = k + 1; i < n; i++) {
      for (let j = k + 1; j < n; j++) {
        M[i][j] = R.div(R.sub(R.mul(M[i][j], M[k][k]), R.mul(M[i][k], M[k][j])), prev);
      }
    }
    prev = M[k][k];
  }
  const d = M[n - 1][n - 1];
  return sign < 0 ? R.neg(d) : d;
}
function sylvester(a, b, zero) {
  // a, b coefficient arrays low->high of degrees m, n (both >= 1)
  const m = a.length - 1, n = b.length - 1, size = m + n;
  const M = [];
  for (let i = 0; i < n; i++) {
    const row = new Array(size).fill(zero);
    for (let j = 0; j <= m; j++) row[i + j] = a[m - j];
    M.push(row);
  }
  for (let i = 0; i < m; i++) {
    const row = new Array(size).fill(zero);
    for (let j = 0; j <= n; j++) row[i + j] = b[n - j];
    M.push(row);
  }
  return M;
}
const ZRING = { one: 1n, zero: 0n, isZero: (v) => v === 0n, mul: (a, b) => a * b, sub: (a, b) => a - b, div: (a, b) => a / b, neg: (a) => -a };
// res(a, b) = lc(a)^deg(b) * prod b(alpha) over the roots alpha of a (Sylvester determinant,
// computed with fraction-free Bareiss elimination over Z).
export function resultant(a, b, opts) {
  return guard(opts, () => {
    a = norm(a); b = norm(b);
    if (!a.length || !b.length) return Q0;
    const m = a.length - 1, n = b.length - 1;
    if (m === 0) return N.pow(a[0], n);
    if (n === 0) return N.pow(b[0], m);
    const A = toZ(a), B = toZ(b);
    const d = bareiss(sylvester(A.z, B.z, 0n), ZRING);
    return N.mul(N.mul(N.pow(A.c, n), N.pow(B.c, m)), N.Q(d));
  });
}
// disc(f) = (-1)^(n(n-1)/2) res(f, f') / lc(f)
export function discriminant(p, opts) {
  p = norm(p);
  const n = p.length - 1;
  if (n < 1) return Q0;
  if (n === 1) return Q1;
  const r = N.div(resultant(p, deriv(p), opts), lc(p));
  return (n * (n - 1) / 2) % 2 ? N.neg(r) : r;
}

// ---------------------------------------------------------------- remainder sequences
// kind: "euclid" (monic remainders over Q), "primitive" (primitive parts over Z),
// "subresultant" (Brown-Collins subresultant PRS over Z). Returns UPoly[] starting with a, b.
export function prs(a, b, kind = "subresultant", opts) {
  return guard(opts, () => {
    a = norm(a); b = norm(b);
    if (a.length < b.length) [a, b] = [b, a];
    const out = [a, b];
    if (!b.length) return out.slice(0, 1);
    if (kind === "euclid") {
      let r0 = a, r1 = b;
      for (let g = a.length + 2; ; ) {
        if (--g < 0) throw budgetError("prs");
        tick();
        const r = rem(r0, r1);
        if (!r.length) break;
        out.push(r);
        [r0, r1] = [r1, r];
      }
      return out;
    }
    let A = toZ(a).z, B = toZ(b).z;
    if (kind === "primitive") {
      out[0] = fromZ(A); out[1] = fromZ(B);
      for (let g = A.length + 2; ; ) {
        if (--g < 0) throw budgetError("prs");
        tick();
        const r = zPrem(A, B);
        if (!r.length) break;
        const pr = zPrimPos(r);
        out.push(fromZ(pr));
        [A, B] = [B, pr];
      }
      return out;
    }
    // subresultant on the original (possibly rational) inputs scaled to Z
    const sa = toZden(a), sb = toZden(b);
    A = sa.z; B = sb.z;
    out[0] = fromZ(A); out[1] = fromZ(B);
    let g = 1n, h = 1n;
    for (let guardN = A.length + 2; ; ) {
      if (--guardN < 0) throw budgetError("prs");
      tick();
      const d = A.length - B.length;
      const r = zPrem(A, B);
      if (!r.length) break;
      const div = g * h ** BigInt(d);
      const nb = r.map((v) => v / div);
      A = B; B = nb;
      out.push(fromZ(B));
      g = A[A.length - 1];
      h = d === 0 ? h : d === 1 ? g : g ** BigInt(d) / h ** BigInt(d - 1);
    }
    return out;
  });
}

// ---------------------------------------------------------------- real roots (exact)
// Strict bound on |root|: 2*max(|a_{n-k}/a_n|^(1/k)) (Fujiwara), rounded up, plus 1.
export function rootBound(p) {
  p = norm(p);
  const n = p.length - 1;
  if (n < 1) return Q1;
  const an = N.abs(p[n]);
  let best = 0n;
  for (let k = 1; k <= n; k++) {
    let v = N.div(N.abs(p[n - k]), an);
    if (k === n) v = N.div(v, N.TWO);
    if (v.n === 0n) continue;
    const c = N.ceil(v);
    const [r] = N.iroot(c, k);
    const up = r ** BigInt(k) === c ? r : r + 1n;
    if (up > best) best = up;
  }
  return N.Q(2n * best + 1n);
}
function sturmZ(z) {
  const seq = [zPrimPos(z)];
  const d = zPrimPos(zDeriv(z));
  if (!d.length) return seq;
  seq.push(d);
  for (let g = z.length + 2; ; ) {
    if (--g < 0) throw budgetError("sturm");
    tick();
    const a = seq[seq.length - 2], b = seq[seq.length - 1];
    if (b.length <= 1) break;
    let r = zPrem(a, b);
    const e = a.length - b.length + 1;
    if (b[b.length - 1] < 0n && e % 2 === 1) r = r.map((v) => -v);
    if (!r.length) break;
    seq.push(zPrimPos(r.map((v) => -v)));
  }
  return seq;
}
// Sturm sequence of the square-free part of p (each element a positive multiple of the
// classical remainder, so sign counts are unchanged). Returned as UPoly[].
export function sturmSequence(p, opts) {
  return guard(opts, () => {
    const s = squareFreePart(p);
    if (s.length <= 1) return s.length ? [s] : [];
    return sturmZ(toZ(s).z).map((z) => fromZ(z));
  });
}
function variations(signs) {
  let v = 0, last = 0;
  for (const s of signs) { if (s === 0) continue; if (last && s !== last) v++; last = s; }
  return v;
}
const vAt = (seq, x) => variations(seq.map((z) => zSignAt(z, x)));
const vInf = (seq, s) => variations(seq.map((z) => zSignAtInf(z, s)));
// Number of DISTINCT real roots in the closed interval [lo, hi]; null means -oo / +oo.
export function countRealRoots(p, lo = null, hi = null, opts) {
  return guard(opts, () => {
    p = norm(p);
    if (!p.length) throw new RangeError("Quelvra: the zero polynomial has infinitely many roots");
    if (p.length === 1) return 0;
    lo = lo === null ? null : toRat(lo);
    hi = hi === null ? null : toRat(hi);
    if (lo && hi && N.cmp(lo, hi) > 0) return 0;
    const z = toZ(squareFreePart(p)).z;
    const seq = sturmZ(z);
    const vl = lo === null ? vInf(seq, -1) : vAt(seq, lo);
    const vh = hi === null ? vInf(seq, 1) : vAt(seq, hi);
    return vl - vh + (lo !== null && zSignAt(z, lo) === 0 ? 1 : 0);
  });
}
function bisectStep(z, lo, hi) {
  const m = N.div(N.add(lo, hi), N.TWO);
  const sm = zSignAt(z, m);
  if (sm === 0) return { exact: m };
  const sl = zSignAt(z, lo);
  return sm === sl ? { lo: m, hi } : { lo, hi: m };
}
// Isolate the real roots of p: sorted list of { lo, hi, exact }. When exact is true lo = hi is a
// rational root; otherwise the OPEN interval (lo, hi) contains exactly one real root, p(lo) and
// p(hi) are nonzero with opposite signs (for the square-free part), and intervals are disjoint.
export function isolateRealRoots(p, opts) {
  return guard(opts, () => {
    p = norm(p);
    if (!p.length) throw new RangeError("Quelvra: the zero polynomial has infinitely many roots");
    if (p.length === 1) return [];
    const z = toZ(squareFreePart(p)).z;
    const seq = sturmZ(z);
    const B = rootBound(fromZ(z));
    const out = [];
    const stack = [[N.neg(B), B, vAt(seq, N.neg(B)), vAt(seq, B)]];
    let it = 0;
    while (stack.length) {
      if (++it > 200000) throw budgetError("isolation");
      tick();
      const [lo, hi, vl, vh] = stack.pop();
      const c = vl - vh;
      if (c === 0) continue;
      if (c === 1) { out.push({ lo, hi, exact: false }); continue; }
      let m = N.div(N.add(lo, hi), N.TWO);
      // prefer a short rational (an integer) inside when possible
      const fl = N.Q(N.floor(m));
      if (N.cmp(fl, lo) > 0 && N.cmp(fl, hi) < 0) m = fl;
      const vm = vAt(seq, m);
      if (zSignAt(z, m) === 0) {
        out.push({ lo: m, hi: m, exact: true });
        // exclude a small neighbourhood [m - d, m + d] that contains only the root m
        const dl = N.sub(m, lo), dh = N.sub(hi, m);
        let d = N.div(N.cmp(dl, dh) < 0 ? dl : dh, N.TWO);
        let a, b, va, vb;
        for (let k = 0; ; k++) {
          if (k > 4000) throw budgetError("isolation");
          a = N.sub(m, d); b = N.add(m, d);
          if (zSignAt(z, a) !== 0 && zSignAt(z, b) !== 0) {
            va = vAt(seq, a); vb = vAt(seq, b);
            if (va - vb === 1) break;
          }
          d = N.div(d, N.TWO);
        }
        if (vl - va > 0) stack.push([lo, a, vl, va]);
        if (vb - vh > 0) stack.push([b, hi, vb, vh]);
      } else {
        stack.push([m, hi, vm, vh]);
        stack.push([lo, m, vl, vm]);
      }
    }
    return out.sort((a, b) => N.cmp(a.lo, b.lo));
  });
}
// Shrink an isolating interval of p by bisection until hi - lo <= width.
export function refineInterval(p, iv, width, opts) {
  return guard(opts, () => {
    if (iv.exact) return iv;
    width = toRat(width);
    const z = toZ(squareFreePart(p)).z;
    let { lo, hi } = iv;
    for (let it = 0; N.cmp(N.sub(hi, lo), width) > 0; it++) {
      if (it > 100000) throw budgetError("refine");
      tick();
      const r = bisectStep(z, lo, hi);
      if (r.exact) return { lo: r.exact, hi: r.exact, exact: true };
      lo = r.lo; hi = r.hi;
    }
    return { lo, hi, exact: false };
  });
}
// Real roots with multiplicities: [{ lo, hi, exact, multiplicity }], disjoint and sorted.
export function realRoots(p, opts) {
  return guard(opts, () => {
    p = norm(p);
    if (!p.length) throw new RangeError("Quelvra: the zero polynomial has infinitely many roots");
    const sf = squareFree(p);
    const zs = sf.factors.map((f) => ({ z: toZ(f.poly).z, mult: f.mult }));
    return isolateRealRoots(p).map((iv) => {
      let mult = 0;
      for (const { z, mult: m } of zs) {
        if (iv.exact ? zSignAt(z, iv.lo) === 0 : zSignAt(z, iv.lo) * zSignAt(z, iv.hi) < 0) { mult = m; break; }
      }
      return { ...iv, multiplicity: mult };
    });
  });
}
function roundTo(x, k) { // round rational x to a dyadic with denominator 2^k (floor)
  const den = 1n << BigInt(k);
  return N.Q(N.floor(N.mul(x, N.Q(den))), den);
}
// Certified decimal approximation of the real root of p inside the isolating interval iv.
// Returns an Approx record; the true root lies within errorBound = 10^-digits of value.
export function approxRealRoot(p, iv, digits = 20, opts) {
  return guard(opts, () => {
    if (!Number.isInteger(digits) || digits < 0 || digits > 5000) throw new RangeError("Quelvra: digits must be an integer in [0, 5000]");
    const rec = (value, it, method) => ({ value, digits, requested: digits, errorBound: `1e-${digits}`, method, iterations: it, converged: true });
    if (iv.exact) return rec(N.toDecimalString(iv.lo, digits), 0, "exact");
    const z = toZ(squareFreePart(p)).z;
    const dz = zDeriv(z);
    const target = N.Q(1n, 10n ** BigInt(digits));
    let { lo, hi } = iv;
    let slo = zSignAt(z, lo);
    let it = 0;
    const evalQ = (a, x) => { let acc = Q0; for (let i = a.length - 1; i >= 0; i--) acc = N.add(N.mul(acc, x), N.Q(a[i])); return acc; };
    while (N.cmp(N.sub(hi, lo), target) >= 0) {
      if (++it > 40000) throw budgetError("root approximation");
      tick();
      const w = N.sub(hi, lo);
      const m = N.div(N.add(lo, hi), N.TWO);
      const sm = zSignAt(z, m);
      if (sm === 0) return rec(N.toDecimalString(m, digits), it, "exact");
      // Newton attempt from the midpoint, accepted only when certified by a sign change
      const fm = evalQ(z, m), dm = evalQ(dz, m);
      if (dm.n !== 0n) {
        const xn = N.sub(m, N.div(fm, dm));
        if (N.cmp(xn, lo) > 0 && N.cmp(xn, hi) < 0) {
          let eps = N.cmp(w, Q1) < 0 ? N.mul(w, w) : N.div(w, N.Q(4));
          if (N.cmp(eps, N.div(w, N.Q(4))) > 0) eps = N.div(w, N.Q(4));
          const bits = Math.max(4, eps.d.toString(2).length - eps.n.toString(2).length + 4);
          const x = roundTo(xn, bits);
          let a = N.sub(x, eps), b = N.add(x, eps);
          if (N.cmp(a, lo) < 0) a = lo;
          if (N.cmp(b, hi) > 0) b = hi;
          const sa = zSignAt(z, a), sb = zSignAt(z, b);
          if (sa === 0) return rec(N.toDecimalString(a, digits), it, "exact");
          if (sb === 0) return rec(N.toDecimalString(b, digits), it, "exact");
          if (sa !== sb && N.cmp(N.sub(b, a), N.div(w, N.TWO)) < 0) { lo = a; hi = b; slo = sa; continue; }
        }
      }
      if (sm === slo) lo = m; else hi = m;
    }
    const mid = N.div(N.add(lo, hi), N.TWO);
    return { ...rec(N.toDecimalString(mid, digits), it, "bisection-newton"), lo, hi };
  });
}

// ---------------------------------------------------------------- interpolation
// Newton divided differences over Q. points: [[x, y], ...] with distinct x.
export function interpolate(points) {
  const xs = points.map((p) => toRat(p[0])), ys = points.map((p) => toRat(p[1]));
  const n = xs.length;
  for (let i = 0; i < n; i++) for (let j = i + 1; j < n; j++) if (N.eq(xs[i], xs[j])) throw new RangeError("Quelvra: interpolation nodes must be distinct");
  const c = ys.slice();
  for (let j = 1; j < n; j++) for (let i = n - 1; i >= j; i--) c[i] = N.div(N.sub(c[i], c[i - 1]), N.sub(xs[i], xs[i - j]));
  let acc = [];
  for (let i = n - 1; i >= 0; i--) acc = add(mul(acc, [N.neg(xs[i]), Q1]), c[i].n === 0n ? [] : [c[i]]);
  return acc;
}
// Lagrange form (same polynomial; provided for step explanations / cross-checks).
export function lagrange(points) {
  const xs = points.map((p) => toRat(p[0])), ys = points.map((p) => toRat(p[1]));
  let acc = [];
  for (let i = 0; i < xs.length; i++) {
    let term = [ys[i]];
    for (let j = 0; j < xs.length; j++) {
      if (j === i) continue;
      const d = N.sub(xs[i], xs[j]);
      if (d.n === 0n) throw new RangeError("Quelvra: interpolation nodes must be distinct");
      term = mul(term, [N.div(N.neg(xs[j]), d), N.inv(d)]);
    }
    acc = add(acc, term);
  }
  return acc;
}

// ---------------------------------------------------------------- Rec (recursive dense)
const rZero = (L) => (L === 0 ? Q0 : []);
const rOne = (L) => (L === 0 ? Q1 : [rOne(L - 1)]);
const rIsZero = (a, L) => (L === 0 ? a.n === 0n : a.length === 0);
function rTrim(a, L) {
  let n = a.length;
  while (n > 0 && rIsZero(a[n - 1], L - 1)) n--;
  return n === a.length ? a : a.slice(0, n);
}
function rAdd(a, b, L) {
  if (L === 0) return N.add(a, b);
  if (L === 1) return add(a, b);
  const n = Math.max(a.length, b.length), out = new Array(n);
  for (let i = 0; i < n; i++) out[i] = i >= a.length ? b[i] : i >= b.length ? a[i] : rAdd(a[i], b[i], L - 1);
  return rTrim(out, L);
}
function rNeg(a, L) { return L === 0 ? N.neg(a) : a.map((c) => rNeg(c, L - 1)); }
const rSub = (a, b, L) => rAdd(a, rNeg(b, L), L);
function rMul(a, b, L) {
  if (L === 0) return N.mul(a, b);
  if (L === 1) { tick(1 + ((a.length * b.length) >> 4)); return mul(a, b); }
  if (!a.length || !b.length) return [];
  tick(a.length * b.length);
  const out = new Array(a.length + b.length - 1).fill(null);
  for (let i = 0; i < a.length; i++) {
    if (rIsZero(a[i], L - 1)) continue;
    for (let j = 0; j < b.length; j++) {
      if (rIsZero(b[j], L - 1)) continue;
      const t = rMul(a[i], b[j], L - 1);
      out[i + j] = out[i + j] === null ? t : rAdd(out[i + j], t, L - 1);
    }
  }
  return rTrim(out.map((v) => (v === null ? rZero(L - 1) : v)), L);
}
function rScale(a, r, L) {
  if (L === 0) return N.mul(a, r);
  if (r.n === 0n) return [];
  return a.map((c) => rScale(c, r, L - 1));
}
const rMulCoeff = (a, c, L) => (rIsZero(c, L - 1) ? [] : rTrim(a.map((x) => rMul(x, c, L - 1)), L));
function rLead(a, L) { return L === 0 ? a : a.length ? rLead(a[a.length - 1], L - 1) : Q0; }
function rFlat(a, L, out) {
  if (L === 0) { if (a.n !== 0n) out.push(a); return out; }
  for (const c of a) rFlat(c, L - 1, out);
  return out;
}
// a = unit * p with p integer primitive and positive innermost leading coefficient.
function rNormalize(a, L) {
  if (rIsZero(a, L)) return { unit: Q0, p: a };
  if (L === 0) return { unit: a, p: Q1 };
  const rs = rFlat(a, L, []);
  let den = 1n;
  for (const r of rs) den = blcm(den, r.d);
  let g = 0n;
  for (const r of rs) g = N.bgcd(g, r.n * (den / r.d));
  let unit = N.Q(g, den);
  if (N.isNeg(rLead(a, L))) unit = N.neg(unit);
  return { unit, p: N.isOne(unit) ? a : rScale(a, N.inv(unit), L) };
}
function rDivExact(a, b, L) {
  if (L === 0) return N.div(a, b);
  if (rIsZero(b, L)) throw new RangeError("Quelvra: division by zero polynomial");
  if (L === 1) return exactDiv(a, b);
  if (!a.length) return [];
  const db = b.length - 1;
  if (a.length - 1 < db) return null;
  const r = a.slice(), q = new Array(a.length - db).fill(null), lb = b[db];
  for (let i = a.length - 1; i >= db; i--) {
    tick();
    const c = r[i];
    if (rIsZero(c, L - 1)) { q[i - db] = rZero(L - 1); continue; }
    const t = rDivExact(c, lb, L - 1);
    if (t === null) return null;
    q[i - db] = t;
    for (let j = 0; j <= db; j++) r[i - db + j] = rSub(r[i - db + j], rMul(t, b[j], L - 1), L - 1);
  }
  for (let i = 0; i < db; i++) if (!rIsZero(r[i], L - 1)) return null;
  return rTrim(q.map((v) => (v === null ? rZero(L - 1) : v)), L);
}
function rDivCoeffExact(a, c, L) {
  const out = [];
  for (const x of a) {
    const t = rDivExact(x, c, L - 1);
    if (t === null) return null;
    out.push(t);
  }
  return rTrim(out, L);
}
function rPrem(a, b, L) {
  const db = b.length - 1, l = b[db];
  let r = a;
  let e = Math.max(a.length - 1 - db + 1, 0);
  for (let g = a.length + 1; r.length && r.length - 1 >= db; ) {
    if (--g < 0) throw budgetError("prem");
    tick();
    const s = r.length - 1 - db, c = r[r.length - 1];
    const nr = r.map((v) => rMul(v, l, L - 1));
    for (let j = 0; j <= db; j++) nr[s + j] = rSub(nr[s + j], rMul(c, b[j], L - 1), L - 1);
    r = rTrim(nr, L);
    e--;
  }
  for (; e > 0 && r.length; e--) r = rMulCoeff(r, l, L);
  return r;
}
function rDeriv(a, L) {
  const out = [];
  for (let i = 1; i < a.length; i++) out.push(rScale(a[i], N.Q(i), L - 1));
  return rTrim(out, L);
}
function rContent(a, L) {
  let g = rZero(L - 1);
  for (const c of a) {
    if (rIsZero(c, L - 1)) continue;
    g = rIsZero(g, L - 1) ? rNormalize(c, L - 1).p : rGcd(g, c, L - 1);
    if (L - 1 === 0) break;
  }
  return g;
}
function rPrimPart(a, L) {
  if (!a.length) return a;
  const c = rContent(a, L);
  const q = rDivCoeffExact(a, c, L);
  if (q === null) throw new Error("Quelvra: internal error (content division)");
  return q;
}
// Evaluate every variable except the outermost at pts: level-L Rec -> UPoly.
function rEvalInner(a, L, pts) {
  const full = (c, lvl, k) => {
    if (lvl === 0) return c;
    let acc = Q0;
    for (let i = c.length - 1; i >= 0; i--) acc = N.add(N.mul(acc, pts[k]), full(c[i], lvl - 1, k + 1));
    return acc;
  };
  return norm(a.map((c) => full(c, L - 1, 0)));
}
function rGcd(a, b, L) {
  tick();
  if (rIsZero(a, L)) return rNormalize(b, L).p;
  if (rIsZero(b, L)) return rNormalize(a, L).p;
  if (L === 0) return Q1;
  if (L === 1) return fromZ(zGcd(toZ(a).z, toZ(b).z));
  const ca = rContent(a, L), cb = rContent(b, L);
  const c = rGcd(ca, cb, L - 1);
  let pa = rDivCoeffExact(a, ca, L), pb = rDivCoeffExact(b, cb, L);
  const cOnly = () => rNormalize([c], L).p;
  if (pa.length === 1 || pb.length === 1) return cOnly();
  // Coprimality test by evaluation: when lc(pa) does not vanish at the point, the degree of the
  // image gcd bounds the degree of the true gcd from above.
  for (let t = 0; t < 3; t++) {
    const pts = [];
    for (let j = 0; j < L - 1; j++) pts.push(N.Q(BigInt(((t * 7 + j * 3 + 2) * (j % 2 ? -1 : 1)))));
    const ia = rEvalInner(pa, L, pts), ib = rEvalInner(pb, L, pts);
    if (ia.length !== pa.length) continue;
    const gi = gcd(ia, ib);
    if (gi.length === 1) return cOnly();
    break;
  }
  if (pa.length < pb.length) [pa, pb] = [pb, pa];
  // subresultant PRS over Q[others][x]: only exact divisions, one content at the end
  const one = rOne(L - 1);
  let g = one, h = one;
  for (let guardN = pa.length + 2; ; ) {
    if (--guardN < 0) throw budgetError("gcd");
    tick();
    const d = pa.length - pb.length;
    const r = rPrem(pa, pb, L);
    if (!r.length) break;
    if (r.length === 1) return cOnly();
    let div = g;
    for (let i = 0; i < d; i++) div = rMul(div, h, L - 1);
    const nb = rDivCoeffExact(r, div, L);
    if (nb === null) throw new Error("Quelvra: internal error (subresultant division)");
    pa = pb; pb = nb;
    g = pa[pa.length - 1];
    if (d === 0) { /* h unchanged */ } else if (d === 1) h = g;
    else {
      let gd = one; for (let i = 0; i < d; i++) gd = rMul(gd, g, L - 1);
      let hd = one; for (let i = 0; i < d - 1; i++) hd = rMul(hd, h, L - 1);
      const nh = rDivExact(gd, hd, L - 1);
      if (nh === null) throw new Error("Quelvra: internal error (subresultant h)");
      h = nh;
    }
  }
  const res = rMulCoeff(rPrimPart(pb, L), c, L);
  return rNormalize(res, L).p;
}
// Yun square-free decomposition of a primitive (w.r.t. the outer variable) Rec at level L.
function rYun(f, L) {
  const out = [];
  const fp = rDeriv(f, L);
  let a = rGcd(f, fp, L);
  let b = rDivExact(f, a, L), c = rDivExact(fp, a, L);
  let d = rSub(c, rDeriv(b, L), L);
  for (let i = 1; b.length > 1; i++) {
    if (i > f.length + 1) throw budgetError("square-free");
    a = rGcd(b, d, L);
    if (a.length > 1) out.push({ p: a, mult: i });
    b = rDivExact(b, a, L);
    c = rDivExact(d, a, L);
    if (b === null || c === null) throw new Error("Quelvra: internal error (Yun)");
    d = rSub(c, rDeriv(b, L), L);
  }
  return out;
}

// ---------------------------------------------------------------- MPoly (sparse)
const keyOf = (e) => e.join(",");
export const expsOf = (k, nv) => (nv === 0 ? [] : k.split(",").map(Number));
export function mpoly(vars, entries = []) {
  const terms = new Map();
  for (const [e, c] of entries) {
    const r = toRat(c);
    if (r.n === 0n) continue;
    const k = keyOf(e);
    const s = terms.has(k) ? N.add(terms.get(k), r) : r;
    if (s.n === 0n) terms.delete(k); else terms.set(k, s);
  }
  return { vars: vars.slice(), terms };
}
export const mZero = (vars) => ({ vars: vars.slice(), terms: new Map() });
export const mConst = (vars, c) => mpoly(vars, [[vars.map(() => 0), c]]);
export function mVar(vars, name) {
  const i = vars.indexOf(name);
  if (i < 0) throw new RangeError("Quelvra: unknown variable " + name);
  return mpoly(vars, [[vars.map((_, j) => (j === i ? 1 : 0)), Q1]]);
}
export const mIsZero = (p) => p.terms.size === 0;
const sameVars = (a, b) => a.length === b.length && a.every((v, i) => v === b[i]);
export function mReorder(p, vars) {
  if (sameVars(p.vars, vars)) return p;
  const map = p.vars.map((v) => vars.indexOf(v));
  const terms = new Map();
  for (const [k, c] of p.terms) {
    const e = expsOf(k, p.vars.length), ne = vars.map(() => 0);
    e.forEach((x, i) => {
      if (!x) return;
      if (map[i] < 0) throw new RangeError("Quelvra: variable " + p.vars[i] + " missing from target order");
      ne[map[i]] = x;
    });
    terms.set(keyOf(ne), c);
  }
  return { vars: vars.slice(), terms };
}
function align(a, b) {
  if (sameVars(a.vars, b.vars)) return [a, b];
  const vars = a.vars.slice();
  for (const v of b.vars) if (!vars.includes(v)) vars.push(v);
  return [mReorder(a, vars), mReorder(b, vars)];
}
export function mAdd(a, b) {
  [a, b] = align(a, b);
  const terms = new Map(a.terms);
  for (const [k, c] of b.terms) {
    const s = terms.has(k) ? N.add(terms.get(k), c) : c;
    if (s.n === 0n) terms.delete(k); else terms.set(k, s);
  }
  return { vars: a.vars, terms };
}
export function mScale(p, c) {
  c = toRat(c);
  if (c.n === 0n) return mZero(p.vars);
  const terms = new Map();
  for (const [k, v] of p.terms) terms.set(k, N.mul(v, c));
  return { vars: p.vars, terms };
}
export const mNeg = (p) => mScale(p, N.NEG_ONE);
export const mSub = (a, b) => mAdd(a, mNeg(b));
export function mMul(a, b) {
  [a, b] = align(a, b);
  const nv = a.vars.length, terms = new Map();
  const bt = [...b.terms].map(([k, c]) => [expsOf(k, nv), c]);
  tick(a.terms.size * b.terms.size);
  for (const [ka, ca] of a.terms) {
    const ea = expsOf(ka, nv);
    for (const [eb, cb] of bt) {
      const k = keyOf(ea.map((x, i) => x + eb[i]));
      const s = terms.has(k) ? N.add(terms.get(k), N.mul(ca, cb)) : N.mul(ca, cb);
      if (s.n === 0n) terms.delete(k); else terms.set(k, s);
    }
  }
  return { vars: a.vars, terms };
}
export function mPow(p, n) {
  n = BigInt(n);
  if (n < 0n) throw new RangeError("Quelvra: negative polynomial power");
  if (mTotalDegree(p) > 0 && BigInt(mTotalDegree(p)) * n > 5000n) throw budgetError("power degree");
  let r = mConst(p.vars, Q1), b = p;
  while (n > 0n) { if (n & 1n) r = mMul(r, b); n >>= 1n; if (n) b = mMul(b, b); }
  return r;
}
export function mEq(a, b) {
  [a, b] = align(a, b);
  if (a.terms.size !== b.terms.size) return false;
  for (const [k, c] of a.terms) { const d = b.terms.get(k); if (!d || !N.eq(c, d)) return false; }
  return true;
}
export function mDegree(p, name) {
  const i = p.vars.indexOf(name);
  if (!p.terms.size) return -1;
  if (i < 0) return 0;
  let d = 0;
  for (const k of p.terms.keys()) d = Math.max(d, expsOf(k, p.vars.length)[i]);
  return d;
}
export function mTotalDegree(p) {
  let d = -1;
  for (const k of p.terms.keys()) d = Math.max(d, expsOf(k, p.vars.length).reduce((s, x) => s + x, 0));
  return d;
}
export const mUsedVars = (p) => p.vars.filter((v) => mDegree(p, v) > 0);
export function mEval(p, name, value) {
  const i = p.vars.indexOf(name);
  if (i < 0) return p;
  value = toRat(value);
  const nv = p.vars.length, out = [];
  for (const [k, c] of p.terms) {
    const e = expsOf(k, nv);
    const v = N.mul(c, N.pow(value, e[i]));
    e[i] = 0;
    out.push([e, v]);
  }
  return mpoly(p.vars, out);
}
export function mDeriv(p, name) {
  const i = p.vars.indexOf(name), nv = p.vars.length, out = [];
  if (i < 0) return mZero(p.vars);
  for (const [k, c] of p.terms) {
    const e = expsOf(k, nv);
    if (!e[i]) continue;
    const v = N.mul(c, N.Q(e[i]));
    e[i]--;
    out.push([e, v]);
  }
  return mpoly(p.vars, out);
}
// lexicographic comparison of exponent vectors (vars order)
const lexCmp = (a, b) => { for (let i = 0; i < a.length; i++) if (a[i] !== b[i]) return a[i] - b[i]; return 0; };
export function mLeadTerm(p) {
  let best = null, bc = Q0;
  for (const [k, c] of p.terms) {
    const e = expsOf(k, p.vars.length);
    if (!best || lexCmp(e, best) > 0) { best = e; bc = c; }
  }
  return { exps: best, coeff: bc };
}
// p = unit * prim with prim integer primitive and positive lex-leading coefficient.
export function mNormalize(p) {
  if (!p.terms.size) return { unit: Q0, p };
  let den = 1n;
  for (const c of p.terms.values()) den = blcm(den, c.d);
  let g = 0n;
  for (const c of p.terms.values()) g = N.bgcd(g, c.n * (den / c.d));
  let unit = N.Q(g, den);
  if (N.isNeg(mLeadTerm(p).coeff)) unit = N.neg(unit);
  return { unit, p: N.isOne(unit) ? p : mScale(p, N.inv(unit)) };
}
export function mToU(p, name) {
  const i = p.vars.indexOf(name), nv = p.vars.length, out = [];
  for (const [k, c] of p.terms) {
    const e = expsOf(k, nv);
    e.forEach((x, j) => { if (x && j !== i) throw new RangeError("Quelvra: polynomial is not univariate in " + name); });
    const d = i < 0 ? 0 : e[i];
    while (out.length <= d) out.push(Q0);
    out[d] = N.add(out[d], c);
  }
  return norm(out);
}
export function mFromU(u, vars, name) {
  const i = vars.indexOf(name);
  return mpoly(vars, u.map((c, d) => [vars.map((_, j) => (j === i ? d : 0)), c]));
}
export function mToRec(p, order) {
  const nv = p.vars.length;
  const idx = order.map((v) => p.vars.indexOf(v));
  const terms = [];
  for (const [k, c] of p.terms) {
    const e = expsOf(k, nv);
    e.forEach((x, j) => { if (x && !idx.includes(j)) throw new RangeError("Quelvra: variable " + p.vars[j] + " missing from order"); });
    terms.push([e, c]);
  }
  const L = idx.length;
  const build = (list, depth) => {
    if (depth === L) { let s = Q0; for (const [, c] of list) s = N.add(s, c); return s; }
    const groups = [];
    for (const t of list) { const e = idx[depth] < 0 ? 0 : t[0][idx[depth]]; (groups[e] ||= []).push(t); }
    const out = [];
    for (let i = 0; i < groups.length; i++) out.push(groups[i] ? build(groups[i], depth + 1) : rZero(L - depth - 1));
    return rTrim(out, L - depth);
  };
  return build(terms, 0);
}
export function mFromRec(r, order, vars) {
  const idx = order.map((v) => vars.indexOf(v));
  const terms = new Map(), e = new Array(vars.length).fill(0);
  const walk = (a, depth) => {
    if (depth === idx.length) { if (a.n !== 0n) terms.set(keyOf(e), a); return; }
    for (let i = 0; i < a.length; i++) { e[idx[depth]] = i; walk(a[i], depth + 1); }
    e[idx[depth]] = 0;
  };
  walk(r, 0);
  return { vars: vars.slice(), terms };
}
function usedUnion(a, b) {
  const s = new Set([...mUsedVars(a), ...mUsedVars(b)]);
  return a.vars.filter((v) => s.has(v));
}
// Exact quotient a / b or null.
export function mDivExact(a, b, opts) {
  return guard(opts, () => {
    [a, b] = align(a, b);
    if (!b.terms.size) throw new RangeError("Quelvra: division by zero polynomial");
    if (!a.terms.size) return mZero(a.vars);
    const order = usedUnion(a, b);
    if (!order.length) return mConst(a.vars, N.div([...a.terms.values()][0], [...b.terms.values()][0]));
    const q = rDivExact(mToRec(a, order), mToRec(b, order), order.length);
    return q === null ? null : mFromRec(q, order, a.vars);
  });
}
// Multivariate gcd over Q (recursive primitive PRS); integer primitive, positive lex lead.
export function mGcd(a, b, opts) {
  return guard(opts, () => {
    [a, b] = align(a, b);
    if (!a.terms.size) return mNormalize(b).p;
    if (!b.terms.size) return mNormalize(a).p;
    const order = usedUnion(a, b);
    if (!order.length) return mConst(a.vars, Q1);
    const g = rGcd(mToRec(a, order), mToRec(b, order), order.length);
    return mNormalize(mFromRec(g, order, a.vars)).p;
  });
}
export function mLcm(a, b, opts) {
  return guard(opts, () => {
    [a, b] = align(a, b);
    if (!a.terms.size || !b.terms.size) return mZero(a.vars);
    return mNormalize(mDivExact(mMul(a, b), mGcd(a, b))).p;
  });
}
// Content of p viewed as a polynomial in `name` (gcd of its coefficients), as an MPoly.
export function mContentIn(p, name, opts) {
  return guard(opts, () => {
    const others = mUsedVars(p).filter((v) => v !== name);
    const order = [name, ...others];
    const r = mToRec(p, order);
    const c = rContent(r, order.length);
    return mNormalize(mFromRec(c, others, p.vars)).p;
  });
}
// Resultant with respect to `name`; the result does not involve `name`.
export function mResultant(a, b, name, opts) {
  return guard(opts, () => {
    [a, b] = align(a, b);
    if (!a.terms.size || !b.terms.size) return mZero(a.vars);
    const others = usedUnion(a, b).filter((v) => v !== name);
    const order = [name, ...others], L = order.length;
    const A = mToRec(a, order), B = mToRec(b, order);
    const m = A.length - 1, n = B.length - 1;
    const back = (r) => mFromRec(r, others, a.vars);
    const rpow = (x, k) => { let r = rOne(L - 1); for (let i = 0; i < k; i++) r = rMul(r, x, L - 1); return r; };
    if (m === 0) return back(rpow(A[0], n));
    if (n === 0) return back(rpow(B[0], m));
    const R = {
      one: rOne(L - 1), zero: rZero(L - 1), isZero: (v) => rIsZero(v, L - 1),
      mul: (x, y) => rMul(x, y, L - 1), sub: (x, y) => rSub(x, y, L - 1), neg: (x) => rNeg(x, L - 1),
      div: (x, y) => { const q = rDivExact(x, y, L - 1); if (q === null) throw new Error("Quelvra: internal error (Bareiss)"); return q; },
    };
    return back(bareiss(sylvester(A, B, R.zero), R));
  });
}

// Multivariate square-free decomposition and content helpers used by the factoriser.
export const _rec = { rToM: mFromRec, mToRec, rContent, rYun, rDivExact, rGcd, rNormalize, rIsZero };

// ---------------------------------------------------------------- trees
function nameOfVar(v) { return typeof v === "string" ? v : v && v.k === "sym" ? v.name : null; }
const MAX_TREE_DEG = 5000;
function treeToM(u, vars) {
  const go = (w) => {
    tick();
    switch (w.k) {
      case "num": return mConst(vars, w.v);
      case "sym": return vars.includes(w.name) ? mVar(vars, w.name) : null;
      case "add": {
        let acc = mZero(vars);
        for (const a of w.args) { const t = go(a); if (!t) return null; acc = mAdd(acc, t); }
        return acc;
      }
      case "mul": {
        let acc = mConst(vars, Q1);
        for (const a of w.args) { const t = go(a); if (!t) return null; acc = mMul(acc, t); }
        return acc;
      }
      case "pow": {
        const [b, e] = w.args;
        if (!X.isInt(e)) return null;
        const bp = go(b);
        if (!bp) return null;
        const n = e.v.n;
        if (n >= 0n) {
          const td = mTotalDegree(bp);
          if (td > 0 && BigInt(td) * n > BigInt(MAX_TREE_DEG)) throw budgetError("polynomial degree");
          return mPow(bp, n);
        }
        if (mTotalDegree(bp) === 0) { const c = [...bp.terms.values()][0]; if (!c) return null; return mConst(vars, N.pow(c, n)); }
        return null;
      }
      default: return null;
    }
  };
  return go(u);
}
// fromTree(node, "x") -> UPoly or null; fromTree(node, ["x", "y"]) -> MPoly or null.
// Only rational (exact numeric) coefficients are accepted; other symbols make it return null.
export function fromTree(node, vars, opts) {
  return guard(opts, () => {
    const u = canon(node);
    if (Array.isArray(vars)) return treeToM(u, vars.map(nameOfVar));
    const x = nameOfVar(vars);
    const m = treeToM(u, [x]);
    return m ? mToU(m, x) : null;
  });
}
// toTree(UPoly, "x") or toTree(MPoly): canonical simplified tree.
export function toTree(p, vars = "x") {
  if (Array.isArray(p)) {
    const x = X.sym(nameOfVar(Array.isArray(vars) ? vars[0] : vars));
    const terms = [];
    p.forEach((c, i) => { if (c.n !== 0n) terms.push(X.mul(X.num(c), X.pow(x, X.num(i)))); });
    return canon(X.add(...terms));
  }
  const terms = [];
  for (const [k, c] of p.terms) {
    const e = expsOf(k, p.vars.length);
    terms.push(X.mul(X.num(c), ...e.map((x, j) => (x ? X.pow(X.sym(p.vars[j]), X.num(x)) : X.ONE))));
  }
  return canon(X.add(...terms));
}
// Coefficient trees of node as a polynomial in x (index = degree); symbolic coefficients allowed
// (the node is expanded first). Returns null when node is not a polynomial in x. Zero -> [].
export function coefficients(node, x) {
  const xn = nameOfVar(x);
  const xs = X.sym(xn);
  let e;
  try { e = expand(node, makeCtx()); } catch (err) { if (err && err.code === "BUDGET") throw err; return null; }
  if (e === X.UNDEF) return null;
  const terms = e.k === "add" ? e.args : [e];
  const buckets = [];
  for (const t of terms) {
    const fs = t.k === "mul" ? t.args : [t];
    let d = 0;
    const rest = [];
    for (const f of fs) {
      if (f === xs) d += 1;
      else if (f.k === "pow" && f.args[0] === xs && X.isInt(f.args[1]) && f.args[1].v.n > 0n) {
        if (f.args[1].v.n > BigInt(MAX_TREE_DEG)) throw budgetError("polynomial degree");
        d += Number(f.args[1].v.n);
      } else if (X.freeOf(f, xn) && !X.contains(f, X.UNDEF)) rest.push(f);
      else return null;
    }
    (buckets[d] ||= []).push(X.mul(...rest));
  }
  const out = [];
  for (let i = 0; i < buckets.length; i++) out.push(buckets[i] ? canon(X.add(...buckets[i])) : X.ZERO);
  while (out.length && X.isZero(out[out.length - 1])) out.pop();
  return out;
}
export function degree(node, x) {
  const c = coefficients(node, x);
  return c === null ? null : c.length - 1;
}
export function leadingCoeff(node, x) {
  const c = coefficients(node, x);
  return c === null ? null : c.length ? c[c.length - 1] : X.ZERO;
}
export function isPolynomial(node, x) {
  if (Array.isArray(x)) return x.every((v) => coefficients(node, v) !== null);
  return coefficients(node, x) !== null;
}
