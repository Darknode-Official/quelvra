// Polynomials over GF(p) as BigInt coefficient arrays (index = power, trimmed, entries in [0, p)).
// Two independent irreducibility routes are provided: Rabin's test (x^(p^n) = x mod f plus gcd
// conditions) and exhaustive trial division by monic polynomials of degree <= n / 2.

import { refuse, mod, modInv, factorSmall, polyText, X } from "./util.js";
import { simplify } from "../simplify.js";

export const trim = (a) => { const r = a.slice(); while (r.length && r[r.length - 1] === 0n) r.pop(); return r; };
export const red = (a, p) => trim(a.map((c) => mod(BigInt(c), p)));
export const deg = (a) => a.length - 1;
export const lc = (a) => a[a.length - 1];
export function add(a, b, p) { const r = []; for (let i = 0; i < Math.max(a.length, b.length); i++) r.push(mod((a[i] || 0n) + (b[i] || 0n), p)); return trim(r); }
export function sub(a, b, p) { const r = []; for (let i = 0; i < Math.max(a.length, b.length); i++) r.push(mod((a[i] || 0n) - (b[i] || 0n), p)); return trim(r); }
export function mul(a, b, p) { if (!a.length || !b.length) return []; const r = Array(a.length + b.length - 1).fill(0n); for (let i = 0; i < a.length; i++) if (a[i]) for (let j = 0; j < b.length; j++) r[i + j] = (r[i + j] + a[i] * b[j]) % p; return trim(r); }
export const scale = (a, k, p) => trim(a.map((c) => mod(c * k, p)));
export function divmod(a, b, p) {
  if (!b.length) throw refuse("division by the zero polynomial");
  const inv = modInv(lc(b), p);
  let r = a.slice(); const q = Array(Math.max(0, a.length - b.length + 1)).fill(0n);
  while (r.length >= b.length && r.length) {
    const c = mod(lc(r) * inv, p), s = r.length - b.length;
    q[s] = c;
    for (let i = 0; i < b.length; i++) r[s + i] = mod(r[s + i] - c * b[i], p);
    r = trim(r);
  }
  return [trim(q), r];
}
export const rem = (a, b, p) => divmod(a, b, p)[1];
export const monic = (a, p) => (a.length ? scale(a, modInv(lc(a), p), p) : a);
export function gcd(a, b, p) { while (b.length) [a, b] = [b, rem(a, b, p)]; return monic(a, p); }
export function powmod(b, e, m, p) { let r = [1n], x = rem(b, m, p); while (e > 0n) { if (e & 1n) r = rem(mul(r, x, p), m, p); x = rem(mul(x, x, p), m, p); e >>= 1n; } return rem(r, m, p); }
export const eq = (a, b) => a.length === b.length && a.every((c, i) => c === b[i]);
export const isOne = (a) => a.length === 1 && a[0] === 1n;
// extended Euclid: s with s a = g (mod m)
export function inverse(a, m, p) {
  let [r0, r1, s0, s1] = [m, rem(a, m, p), [], [1n]];
  while (r1.length) { const [q, r] = divmod(r0, r1, p); [r0, r1] = [r1, r]; [s0, s1] = [s1, sub(s0, mul(q, s1, p), p)]; }
  if (r0.length !== 1) return null;
  return scale(s0, modInv(r0[0], p), p);
}

// Rabin's irreducibility test (f of degree n >= 1)
export function rabin(f, p) {
  f = monic(f, p); const n = deg(f);
  if (n < 1) return false;
  if (n === 1) return true;
  const x = [0n, 1n];
  const frob = (g, times) => { let r = g; for (let i = 0; i < times; i++) r = powmod(r, p, f, p); return r; };
  if (!eq(frob(x, n), rem(x, f, p))) return false;
  for (const [q] of factorSmall(BigInt(n))) {
    const h = sub(frob(x, n / Number(q)), x, p);
    if (!isOne(gcd(f, h, p))) return false;
  }
  return true;
}
// all monic polynomials of degree d (lexicographic in the lower coefficients)
function* monics(d, p) {
  const c = Array(d).fill(0n);
  for (;;) {
    yield [...c, 1n];
    let i = 0;
    while (i < d) { c[i]++; if (c[i] < p) break; c[i] = 0n; i++; }
    if (i === d) return;
  }
}
// trial-division factorisation of a nonzero polynomial: { lc, factors: [{ poly, mult }] }
export function factorTrial(f, p, limit = 300000) {
  f = red(f, p);
  if (!f.length) throw refuse("the zero polynomial has no factorisation");
  const lead = lc(f);
  let g = monic(f, p);
  let budget = 0;
  const out = [];
  for (let d = 1; 2 * d <= deg(g); d++) {
    budget += Number(p) ** d;
    if (budget > limit) throw refuse("the polynomial is too large to factor by exhaustive trial division");
    for (const h of monics(d, p)) {
      let m = 0;
      for (;;) { const [q, r] = divmod(g, h, p); if (r.length) break; g = q; m++; }
      if (m) out.push({ poly: h, mult: m });
      if (2 * d > deg(g)) break;
    }
  }
  if (deg(g) >= 1) {
    const k = out.findIndex((o) => eq(o.poly, g));
    if (k >= 0) out[k].mult++; else out.push({ poly: g, mult: 1 });
  }
  return { lc: lead, factors: sortFactors(out) };
}
export function sortFactors(fs) {
  return fs.sort((a, b) => {
    if (a.poly.length !== b.poly.length) return a.poly.length - b.poly.length;
    for (let i = a.poly.length - 1; i >= 0; i--) if (a.poly[i] !== b.poly[i]) return a.poly[i] < b.poly[i] ? -1 : 1;
    return 0;
  });
}
export const ptext = (a, x = "x") => polyText(a.length ? a : [0n], x);
export function ptree(a, x = "x") {
  if (!a.length) return X.ZERO;
  const terms = [];
  a.forEach((c, i) => { if (c !== 0n) terms.push(i === 0 ? X.num(c) : X.mul(X.num(c), X.pow(X.sym(x), X.num(i)))); });
  return simplify(terms.length === 1 ? terms[0] : X.add(...terms));
}
