// Shared helpers for the advanced discrete-mathematics commands: exact integer / rational
// arithmetic, answer and check records, refusal errors and small formatting helpers.
//
// Every command returns { answers, steps, checks: () => [check], solutionStatus?, note? }.
// checks() runs the INDEPENDENT verification (a certificate check, a second algorithm or brute
// force); the strategy withholds the answer unless every check passes.

import * as N from "../num.js";
import * as X from "../expr.js";
import { makeStep } from "../steps.js";

export { N, X };

// ---------------------------------------------------------------- errors
export function refuse(message) { const e = new Error(message); e.code = "UNSUPPORTED"; return e; }
export function budget(message = "search too large") { const e = new Error(message); e.code = "BUDGET"; return e; }

// ---------------------------------------------------------------- integers
export const babs = (a) => (a < 0n ? -a : a);
export function gcd(a, b) { a = babs(a); b = babs(b); while (b) [a, b] = [b, a % b]; return a; }
export const lcm = (a, b) => (a === 0n || b === 0n ? 0n : babs(a / gcd(a, b) * b));
export function egcd(a, b) { // [g, x, y] with a x + b y = g >= 0
  let [r0, r1, s0, s1, t0, t1] = [a, b, 1n, 0n, 0n, 1n];
  while (r1 !== 0n) { const q = r0 / r1; [r0, r1] = [r1, r0 - q * r1]; [s0, s1] = [s1, s0 - q * s1]; [t0, t1] = [t1, t0 - q * t1]; }
  if (r0 < 0n) { r0 = -r0; s0 = -s0; t0 = -t0; }
  return [r0, s0, t0];
}
export const mod = (a, m) => { const r = a % m; return r < 0n ? r + m : r; };
export function modInv(a, m) { const [g, x] = egcd(mod(a, m), m); if (g !== 1n) return null; return mod(x, m); }
// left-to-right square and multiply
export function powMod(b, e, m) {
  if (m === 1n) return 0n;
  if (e < 0n) { const i = modInv(b, m); if (i === null) return null; b = i; e = -e; }
  b = mod(b, m);
  let r = 1n;
  for (const bit of e.toString(2)) { r = r * r % m; if (bit === "1") r = r * b % m; }
  return r;
}
// right-to-left binary method (the independent route used by verifiers)
export function powModRL(b, e, m) {
  if (m === 1n) return 0n;
  b = mod(b, m);
  let r = 1n;
  while (e > 0n) { if (e & 1n) r = r * b % m; b = b * b % m; e >>= 1n; }
  return r;
}
export function isqrt(n) { if (n < 2n) return n; let x = BigInt(Math.floor(Math.sqrt(Number(n)))); while (x * x > n) x--; while ((x + 1n) * (x + 1n) <= n) x++; return x; }
// deterministic trial-division primality for small n; callers use numtheory for large n
export function isPrimeSmall(n) {
  if (n < 2n) return false;
  for (const p of [2n, 3n, 5n, 7n]) { if (n === p) return true; if (n % p === 0n) return false; }
  for (let d = 11n; d * d <= n; d += 2n) if (n % d === 0n) return false;
  return true;
}
// prime factorisation by trial division (bounded); returns [[p, e], ...] or null when too big
export function factorSmall(n, limit = 10n ** 7n) {
  n = babs(n);
  const out = [];
  for (let p = 2n; p * p <= n; p += p === 2n ? 1n : 2n) {
    if (p > limit) return null;
    let e = 0;
    while (n % p === 0n) { n /= p; e++; }
    if (e) out.push([p, e]);
  }
  if (n > 1n) out.push([n, 1]);
  return out;
}
export const big = (v) => (typeof v === "bigint" ? v : BigInt(v));

// ---------------------------------------------------------------- rationals (num.js Q)
export const Q = N.Q;
export const qstr = (r) => (r.d === 1n ? String(r.n) : `${r.n}/${r.d}`);
export const qtree = (r) => X.num(r);
export const qint = (n) => N.Q(big(n));

// ---------------------------------------------------------------- answers
export const ansNum = (label, v) => ({ kind: "exact", label, tree: X.num(typeof v === "object" ? v : N.Q(big(v))) });
export const ansTree = (label, tree) => ({ kind: "exact", label, tree });
export const ansText = (label, text) => ({ kind: "exact", label, text: String(text) });
export const ansYes = (label, b) => ({ kind: "exact", label, text: b ? "yes" : "no" });
export const check = (kind, ok, detail) => ({ kind, ok: !!ok, detail });
export const step = (rule, title, why = "") => makeStep({ rule: `discrete.${rule}`, title, why });

// ---------------------------------------------------------------- formatting
export const joinList = (xs, sep = ", ") => xs.map(String).join(sep);
export function fmtSet(items) { return `{${items.join(", ")}}`; }
// value (number | string | array tuple | {set:[...]}) -> text
export function fmtVal(v) {
  if (Array.isArray(v)) return `(${v.map(fmtVal).join(", ")})`;
  if (v && typeof v === "object" && v.set) return `{${v.set.map(fmtVal).join(", ")}}`;
  return String(v);
}
// canonical order: numbers (numerically), then strings, then tuples, then sets
export function cmpVal(a, b) {
  const rank = (v) => (typeof v === "bigint" || typeof v === "number" ? 0 : typeof v === "string" ? 1 : Array.isArray(v) ? 2 : 3);
  const ra = rank(a), rb = rank(b);
  if (ra !== rb) return ra - rb;
  if (ra === 0) return BigInt(a) < BigInt(b) ? -1 : BigInt(a) > BigInt(b) ? 1 : 0;
  if (ra === 1) return a < b ? -1 : a > b ? 1 : 0;
  const la = ra === 2 ? a : a.set, lb = ra === 2 ? b : b.set;
  if (ra === 3 && la.length !== lb.length) return la.length - lb.length;
  for (let i = 0; i < Math.min(la.length, lb.length); i++) { const c = cmpVal(la[i], lb[i]); if (c) return c; }
  return la.length - lb.length;
}
export const keyOf = (v) => (typeof v === "bigint" ? `n${v}` : typeof v === "string" ? `s${v}` : Array.isArray(v) ? `t(${v.map(keyOf).join(",")})` : `S{${v.set.map(keyOf).sort().join(",")}}`);

// polynomial with BigInt / rational coefficients (index = power) -> text "x^2 + 2x + 1"
export function polyText(cs, x = "x", coefText = (c) => String(c)) {
  const terms = [];
  for (let i = cs.length - 1; i >= 0; i--) {
    const c = cs[i];
    const s = coefText(c);
    if (s === "0") continue;
    const neg = s.startsWith("-");
    const mag = neg ? s.slice(1) : s;
    const mon = i === 0 ? "" : i === 1 ? x : `${x}^${i}`;
    const body = i === 0 ? mag : mag === "1" ? mon : /\//.test(mag) ? `(${mag})*${mon}` : `${mag}*${mon}`;
    terms.push({ neg, body });
  }
  if (!terms.length) return "0";
  return terms.map((t, i) => (i === 0 ? (t.neg ? "-" : "") + t.body : (t.neg ? " - " : " + ") + t.body)).join("");
}
