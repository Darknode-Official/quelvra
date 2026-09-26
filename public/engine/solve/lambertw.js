// Lambert W on the real line: the principal branch W0 (z >= -1/e) and the lower branch W-1
// (-1/e <= z < 0). w = W(z) solves w e^w = z.
//
// Double precision (Halley) for scanning, multiprecision (BigFloat Halley with precision
// doubling) for reported values. The multiprecision value is CERTIFIED: w e^w - z is monotone on
// each branch, so a sign change of g(w) = w e^w - z at w -+ delta encloses the true value.
// Trees: principal W(z) is fn("W", z); the lower branch is fn("W", z, -1) (sympy's LambertW(z, k)).

import * as B from "../bigfloat.js";
import * as X from "../expr.js";

const INV_E = Math.exp(-1);

export function lambertWDouble(z, branch = 0) {
  if (!Number.isFinite(z)) return NaN;
  if (z < -INV_E - 1e-15) return NaN;
  if (branch === -1 && (z >= 0)) return NaN;
  if (Math.abs(z + INV_E) < 1e-15) return -1;
  let w;
  if (branch === 0) {
    if (z < -0.25) { const p = Math.sqrt(Math.max(0, 2 * (Math.E * z + 1))); w = -1 + p - p * p / 3 + 11 / 72 * p * p * p; }
    else if (z < 3) w = Math.log1p(z);
    else { const L1 = Math.log(z), L2 = Math.log(L1); w = L1 - L2 + L2 / L1; }
  } else {
    if (z < -0.25) { const p = -Math.sqrt(2 * (Math.E * z + 1)); w = -1 + p - p * p / 3 + 11 / 72 * p * p * p; }
    else { const L1 = Math.log(-z), L2 = Math.log(-L1); w = L1 - L2 + L2 / L1; }
  }
  for (let i = 0; i < 60; i++) {
    const ew = Math.exp(w), f = w * ew - z;
    const wp1 = w + 1;
    if (wp1 === 0) break;
    const d = ew * wp1 - (w + 2) * f / (2 * wp1);
    const step = f / d;
    w -= step;
    if (!Number.isFinite(w)) return NaN;
    if (Math.abs(step) <= 1e-16 * (1 + Math.abs(w))) break;
  }
  return w;
}

// Multiprecision W with a certified error bound.
// zStr: decimal string of z (at least digits + 10 correct digits). Returns
// { value: string, bf: BigFloat, errorBound: number (absolute), certified } or null.
export function lambertWBig(zStr, branch, digits) {
  const prec = B.digitsToBits(digits + 12) + 32;
  const z = B.fromString(zStr, prec);
  const zd = B.toNumber(z);
  let w0 = lambertWDouble(zd, branch);
  if (!Number.isFinite(w0)) return null;
  if (w0 === -1 && Math.abs(zd + INV_E) < 1e-15) {
    // z within 1e-15 of -1/e: branch point, value -1 only if z is exactly -1/e (caller decides)
    return { value: "-1", bf: B.fromInt(-1), errorBound: 0, certified: false, branchPoint: true };
  }
  let w = B.fromNumber(w0);
  let p = 64;
  for (let it = 0; it < 200; it++) {
    p = Math.min(prec, p * 2);
    const ew = B.exp(w, p);
    const f = B.sub(B.mul(w, ew, p), z, p);
    const wp1 = B.add(w, B.ONE, p);
    if (B.isZero(wp1)) break;
    const d = B.sub(B.mul(ew, wp1, p), B.div(B.mul(B.add(w, B.TWO, p), f, p), B.mul(B.TWO, wp1, p), p), p);
    if (B.isZero(d)) break;
    const step = B.div(f, d, p);
    w = B.sub(w, step, p);
    if (p === prec && (B.isZero(step) || B.top(step) < B.top(w) - prec + 8 || B.top(step) < -prec + 8)) break;
  }
  // certify by a sign change of g(w) = w e^w - z; g is increasing on W0 (w > -1), decreasing on W-1 (w < -1)
  const g = (t) => B.sub(B.mul(t, B.exp(t, prec), prec), z, prec);
  let delta = B.mulPow2(B.ONE, -(B.digitsToBits(digits + 4)));
  if (B.top(w) > 0) delta = B.mulPow2(delta, B.top(w));
  let certified = false;
  for (let t = 0; t < 6; t++) {
    const gl = g(B.sub(w, delta, prec)), gr = g(B.add(w, delta, prec));
    if (B.sign(gl) * B.sign(gr) < 0) { certified = true; break; }
    delta = B.mulPow2(delta, 4);
  }
  const eb = B.toNumber(delta);
  return { value: B.toString(w, digits + 6), bf: w, errorBound: eb, certified };
}

export const W = (z, branch = 0) => (branch === -1 ? X.fn("W", z, X.NEG_ONE) : X.fn("W", z));
export const isW = (u) => u.k === "fn" && u.name === "W";
export const branchOf = (u) => (u.args.length > 1 && X.isNum(u.args[1]) && u.args[1].v.n === -1n ? -1 : 0);
