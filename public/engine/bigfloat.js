// Quelvra arbitrary-precision binary floating point on BigInt.
//
// A BigFloat is { m: BigInt, e: number } with value m * 2^e. Every operation takes a
// precision `prec` in BITS (use digitsToBits(d) for decimal digits) and returns a result
// rounded to at most `prec` significant bits:
//   * add, sub, mul, div, sqrt, nthRoot, fromRational, fromString: correctly rounded
//     (round half to even) from exact inputs.
//   * transcendental functions (exp, ln, sin, cos, atan, gamma, erf, ...): computed with
//     internal guard bits (>= 24) so the error is far below one unit in the last place;
//     they are faithful, not necessarily correctly rounded. Callers that need a certified
//     number of decimal digits evaluate at two precisions and compare (see numeric.js N()).
// Special values (NaN, infinities) do not exist: invalid operations throw an Error with
// code "DOMAIN"; operations whose cost would explode throw code "BUDGET".
// Nothing here uses JavaScript Number for arithmetic except to pick initial guesses.

import * as Q from "./num.js";

const LOG2_10 = 3.321928094887362;
export const digitsToBits = (d) => Math.ceil(d * LOG2_10);
export const bitsToDigits = (b) => Math.floor(b / LOG2_10);
export const DEFAULT_PREC = 128;

const HEXB = [0, 1, 2, 2, 3, 3, 3, 3, 4, 4, 4, 4, 4, 4, 4, 4];
export function bitLen(n) {
  if (n < 0n) n = -n;
  if (n === 0n) return 0;
  const s = n.toString(16);
  return (s.length - 1) * 4 + HEXB[parseInt(s[0], 16)];
}
function err(code, msg) {
  const e = new Error("Quelvra: " + msg);
  e.code = code;
  return e;
}
export const domainError = (msg) => err("DOMAIN", msg);

export class BigFloat {
  constructor(m, e) {
    this.m = m;
    this.e = m === 0n ? 0 : e;
  }
  toString() { return toString(this, 20); }
}
export const ZERO = new BigFloat(0n, 0);
export const ONE = new BigFloat(1n, 0);
export const TWO = new BigFloat(1n, 1);
export const HALF = new BigFloat(1n, -1);

// Top exponent: |x| < 2^top(x) and |x| >= 2^(top(x)-1). top(0) = -Infinity.
export const top = (x) => (x.m === 0n ? -Infinity : bitLen(x.m) + x.e);

// ---------------- rounding core ----------------
// Round m*2^e to prec bits, half to even. `sticky` means the true value is strictly larger in
// magnitude than |m|*2^e by less than one unit of m's last bit (callers supply >= prec+2 bits).
export function rnd(m, e, prec, sticky = false) {
  if (m === 0n) return ZERO;
  if (prec === Infinity) return new BigFloat(m, e);
  const neg = m < 0n;
  let a = neg ? -m : m;
  const n = bitLen(a);
  if (n > prec) {
    const sh = BigInt(n - prec);
    let q = a >> sh;
    const rem = a - (q << sh);
    const half = 1n << (sh - 1n);
    if (rem > half || (rem === half && (sticky || (q & 1n) === 1n))) q += 1n;
    a = q;
    e += n - prec;
    if (bitLen(a) > prec) { a >>= 1n; e += 1; }
  }
  return new BigFloat(neg ? -a : a, e);
}
export const round = (x, prec) => rnd(x.m, x.e, prec);

// Integer division rounded half to even.
function divRound(num, den) {
  const neg = (num < 0n) !== (den < 0n);
  if (num < 0n) num = -num;
  if (den < 0n) den = -den;
  let q = num / den;
  const r2 = (num - q * den) * 2n;
  if (r2 > den || (r2 === den && (q & 1n) === 1n)) q += 1n;
  return neg ? -q : q;
}
// m / 2^s rounded half-even (s may be negative: shift left).
function shiftRound(m, s) {
  if (s <= 0) return m << BigInt(-s);
  const neg = m < 0n;
  let a = neg ? -m : m;
  const sb = BigInt(s);
  let q = a >> sb;
  const rem = a - (q << sb);
  const half = 1n << (sb - 1n);
  if (rem > half || (rem === half && (q & 1n) === 1n)) q += 1n;
  return neg ? -q : q;
}

// ---------------- conversions ----------------
export const fromBigInt = (n) => new BigFloat(BigInt(n), 0);
export const fromInt = (n) => new BigFloat(BigInt(n), 0);
export function fromRational(r, prec = DEFAULT_PREC) {
  if (r.d === 1n) return rnd(r.n, 0, prec);
  return div(new BigFloat(r.n, 0), new BigFloat(r.d, 0), prec);
}
export function fromString(s, prec = DEFAULT_PREC) {
  return fromRational(Q.fromDecimal(String(s).trim()), prec);
}
export function fromNumber(x) {
  if (!Number.isFinite(x)) throw domainError("cannot convert a non-finite number");
  if (x === 0) return ZERO;
  const dv = new DataView(new ArrayBuffer(8));
  dv.setFloat64(0, x);
  const hi = dv.getUint32(0), lo = dv.getUint32(4);
  const sign = hi >>> 31;
  const ex = (hi >>> 20) & 0x7ff;
  let mant = (BigInt(hi & 0xfffff) << 32n) | BigInt(lo);
  let e;
  if (ex === 0) e = -1074;
  else { mant |= 1n << 52n; e = ex - 1075; }
  return new BigFloat(sign ? -mant : mant, e);
}
// Accept BigFloat | number | bigint | Rational | decimal string.
export function from(v, prec = DEFAULT_PREC) {
  if (v instanceof BigFloat) return v;
  if (typeof v === "number") return fromNumber(v);
  if (typeof v === "bigint") return fromBigInt(v);
  if (typeof v === "string") return fromString(v, prec);
  if (v && typeof v.n === "bigint" && typeof v.d === "bigint") return fromRational(v, prec);
  throw new TypeError("Quelvra: cannot convert to BigFloat");
}
export function toNumber(x) {
  if (x.m === 0n) return 0;
  const r = rnd(x.m, x.e, 53);
  let v = Number(r.m);
  let e = r.e;
  while (e > 1000) { v *= 2 ** 1000; e -= 1000; if (!Number.isFinite(v)) return v; }
  while (e < -1000) { v *= 2 ** -1000; e += 1000; if (v === 0) return v; }
  return v * 2 ** e;
}
// Exact rational value.
export function toRational(x) {
  if (x.e >= 0) return Q.Q(x.m << BigInt(x.e));
  return Q.Q(x.m, 1n << BigInt(-x.e));
}
// value * 2^wp rounded to an integer (fixed point)
export function toFixed(x, wp) { return shiftRound(x.m, -(x.e + wp)); }
const fixed = (X, wp) => new BigFloat(X, -wp);

// ---------------- basic predicates ----------------
export const isZero = (x) => x.m === 0n;
export const sign = (x) => (x.m > 0n ? 1 : x.m < 0n ? -1 : 0);
export const neg = (x) => new BigFloat(-x.m, x.e);
export const abs = (x) => (x.m < 0n ? new BigFloat(-x.m, x.e) : x);
export const mulPow2 = (x, k) => new BigFloat(x.m, x.e + k);
export function isInteger(x) {
  if (x.m === 0n || x.e >= 0) return true;
  const s = BigInt(-x.e);
  return (x.m >> s) << s === x.m;
}
export function floorBig(x) {
  if (x.e >= 0) return x.m << BigInt(x.e);
  return x.m >> BigInt(-x.e); // BigInt >> floors toward -infinity
}
export const floor = (x) => fromBigInt(floorBig(x));
export const ceil = (x) => fromBigInt(-floorBig(neg(x)));
export function roundBig(x) { // half away from zero
  const h = floorBig(add(abs(x), HALF, Infinity));
  return x.m < 0n ? -h : h;
}
export const roundInt = (x) => fromBigInt(roundBig(x));
export const trunc = (x) => (x.m < 0n ? ceil(x) : floor(x));

export function cmp(a, b) {
  const sa = sign(a), sb = sign(b);
  if (sa !== sb) return sa < sb ? -1 : 1;
  if (sa === 0) return 0;
  const ta = top(a), tb = top(b);
  if (ta !== tb) return (ta < tb ? -1 : 1) * sa;
  const e = Math.min(a.e, b.e);
  const ma = a.m << BigInt(a.e - e), mb = b.m << BigInt(b.e - e);
  return ma < mb ? -1 : ma > mb ? 1 : 0;
}
export const eq = (a, b) => cmp(a, b) === 0;
export const lt = (a, b) => cmp(a, b) < 0;
export const min = (a, b) => (cmp(a, b) <= 0 ? a : b);
export const max = (a, b) => (cmp(a, b) >= 0 ? a : b);

// ---------------- arithmetic ----------------
export function add(a, b, prec = DEFAULT_PREC) {
  if (a.m === 0n) return rnd(b.m, b.e, prec);
  if (b.m === 0n) return rnd(a.m, a.e, prec);
  if (prec !== Infinity) {
    let big = a, small = b;
    if (top(b) > top(a)) { big = b; small = a; }
    const L = Math.min(big.e, top(big) - prec - 4);
    if (top(small) <= L - 2) {
      // |small| < 2^(L-2): value = M*2^L + small = (2M +- 1)*2^(L-1) plus a sticky remainder
      const M = big.m << BigInt(big.e - L);
      const s = small.m > 0n ? 1n : -1n;
      const sameSign = (small.m > 0n) === (big.m > 0n);
      return rnd(sameSign ? 2n * M : 2n * M + s, L - 1, prec, true);
    }
  }
  const e = Math.min(a.e, b.e);
  const m = (a.m << BigInt(a.e - e)) + (b.m << BigInt(b.e - e));
  return rnd(m, e, prec);
}
export const sub = (a, b, prec = DEFAULT_PREC) => add(a, neg(b), prec);
export const mul = (a, b, prec = DEFAULT_PREC) => rnd(a.m * b.m, a.e + b.e, prec);
export function div(a, b, prec = DEFAULT_PREC) {
  if (b.m === 0n) throw domainError("division by zero");
  if (a.m === 0n) return ZERO;
  if (prec === Infinity) throw err("BUDGET", "exact division needs a finite precision");
  const na = a.m < 0n ? -a.m : a.m, nb = b.m < 0n ? -b.m : b.m;
  let s = prec + 3 + bitLen(nb) - bitLen(na);
  if (s < 0) s = 0;
  const num = na << BigInt(s);
  const q = num / nb;
  const r = num - q * nb;
  const negr = (a.m < 0n) !== (b.m < 0n);
  return rnd(negr ? -q : q, a.e - b.e - s, prec, r !== 0n);
}
export const inv = (a, prec = DEFAULT_PREC) => div(ONE, a, prec);

export function isqrtBig(n) {
  if (n < 0n) throw domainError("isqrt of negative");
  if (n < 2n) return n;
  let x = 1n << BigInt((bitLen(n) >> 1) + 1);
  for (;;) {
    const y = (x + n / x) >> 1n;
    if (y >= x) return x;
    x = y;
  }
}
export function sqrt(a, prec = DEFAULT_PREC) {
  if (a.m < 0n) throw domainError("square root of a negative number");
  if (a.m === 0n) return ZERO;
  let s = Math.max(0, 2 * (prec + 2) - bitLen(a.m));
  if ((a.e - s) % 2 !== 0) s++;
  const M = a.m << BigInt(s);
  const r = isqrtBig(M);
  return rnd(r, (a.e - s) / 2, prec, r * r !== M);
}
// floor(n^(1/k)) for n >= 0
export function irootBig(n, k) {
  if (n < 2n) return n;
  if (k === 1) return n;
  const K = BigInt(k);
  let x = 1n << BigInt(Math.ceil(bitLen(n) / k) + 1);
  for (let it = 0; it < 100000; it++) {
    const y = ((K - 1n) * x + n / x ** (K - 1n)) / K;
    if (y >= x) break;
    x = y;
  }
  while (x ** K > n) x -= 1n;
  return x;
}
export function nthRoot(a, n, prec = DEFAULT_PREC) {
  n = Number(n);
  if (!Number.isInteger(n) || n < 1) throw domainError("nthRoot needs a positive integer index");
  if (n === 1) return round(a, prec);
  if (n === 2) return sqrt(a, prec);
  if (a.m === 0n) return ZERO;
  if (a.m < 0n) {
    if (n % 2 === 0) throw domainError("even root of a negative number");
    return neg(nthRoot(neg(a), n, prec));
  }
  if (n > 64) return exp(div(ln(a, prec + 32), fromInt(n), prec + 32), prec);
  let s = Math.max(0, n * (prec + 2) - bitLen(a.m));
  s += ((((a.e - s) % n) + n) % n);
  const M = a.m << BigInt(s);
  const r = irootBig(M, n);
  return rnd(r, (a.e - s) / n, prec, r ** BigInt(n) !== M);
}
export function powInt(a, n, prec = DEFAULT_PREC) {
  n = BigInt(n);
  if (n === 0n) {
    if (a.m === 0n) throw domainError("0^0 is undefined");
    return ONE;
  }
  if (n < 0n) {
    if (a.m === 0n) throw domainError("division by zero (0 to a negative power)");
    return div(ONE, powInt(a, -n, prec + 8), prec);
  }
  const wp = prec + 2 * bitLen(n) + 10;
  let r = ONE, b = a, k = n;
  let first = true;
  while (k > 0n) {
    if (k & 1n) { r = first ? b : mul(r, b, wp); first = false; }
    k >>= 1n;
    if (k) b = mul(b, b, wp);
  }
  return round(r, prec);
}

// ---------------- constants (cached) ----------------
function atanInvFixed(q, wp) { // atan(1/q) * 2^wp
  const one = 1n << BigInt(wp);
  const q2 = q * q;
  let term = one / q, sum = term, k = 1n, sgn = -1n;
  while (term !== 0n) {
    term /= q2;
    sum += sgn * (term / (2n * k + 1n));
    sgn = -sgn;
    k++;
  }
  return sum;
}
function atanhInvFixed(q, wp) { // atanh(1/q) * 2^wp
  const one = 1n << BigInt(wp);
  const q2 = q * q;
  let term = one / q, sum = term, k = 1n;
  while (term !== 0n) {
    term /= q2;
    sum += term / (2n * k + 1n);
    k++;
  }
  return sum;
}
const CACHE = { pi: null, ln2: null, e: null };
function cached(name, prec, compute) {
  const c = CACHE[name];
  if (c && c.prec >= prec) return round(c.v, prec);
  const p = Math.max(prec, c ? c.prec * 2 : 0) + 32;
  const v = compute(p);
  CACHE[name] = { prec: p, v };
  return round(v, prec);
}
export const pi = (prec = DEFAULT_PREC) => cached("pi", prec, (p) => {
  const wp = p + 16;
  return rnd(16n * atanInvFixed(5n, wp) - 4n * atanInvFixed(239n, wp), -wp, p);
});
export const ln2 = (prec = DEFAULT_PREC) => cached("ln2", prec, (p) => {
  const wp = p + 16;
  return rnd(18n * atanhInvFixed(26n, wp) - 2n * atanhInvFixed(4801n, wp) + 8n * atanhInvFixed(8749n, wp), -wp, p);
});
export const e = (prec = DEFAULT_PREC) => cached("e", prec, (p) => exp(ONE, p));

// ---------------- exp / ln ----------------
export function exp(x, prec = DEFAULT_PREC) {
  if (x.m === 0n) return ONE;
  const tx = top(x);
  if (tx > 48) {
    if (x.m < 0n && tx > 60) throw err("UNDERFLOW", "exp underflow beyond the supported exponent range (|result| < 2^(-2^59))");
    if (x.m > 0n) throw err("BUDGET", "exp overflow beyond the supported exponent range");
  }
  const wp = prec + 24;
  const xn = toNumber(x);
  const k = Math.round(xn / Math.LN2);
  let r = x;
  if (k !== 0) {
    const kb = BigInt(k);
    const p2 = wp + bitLen(kb) + 8;
    r = sub(x, mul(fromBigInt(kb), ln2(p2), p2), p2);
  }
  const s = Math.max(0, Math.ceil(Math.sqrt(wp) / 2));
  const w2 = wp + s + 8;
  const W = BigInt(w2);
  const R = toFixed(r, w2 - s);
  const one = 1n << W;
  let sum = one, term = one;
  for (let n = 1n; ; n++) {
    term = ((term * R) >> W) / n;
    if (term === 0n) break;
    sum += term;
  }
  for (let i = 0; i < s; i++) sum = (sum * sum) >> W;
  return rnd(sum, k - w2, prec);
}
function exactAdd(a, b) { return add(a, b, Infinity); }
export function ln(x, prec = DEFAULT_PREC) {
  if (x.m <= 0n) throw domainError(x.m === 0n ? "logarithm of zero" : "logarithm of a negative number");
  const L = bitLen(x.m);
  let K = L + x.e - 1;
  if (L >= 2 && x.m >> BigInt(L - 2) === 3n) K += 1;
  const f = new BigFloat(x.m, x.e - K);
  const fm1 = exactAdd(f, new BigFloat(-1n, 0));
  const wp0 = prec + 24;
  let lnf = ZERO;
  if (fm1.m !== 0n) {
    const extra = K === 0 ? Math.max(0, -top(fm1)) : 0;
    const wp = wp0 + extra;
    const W = BigInt(wp);
    const z = div(fm1, exactAdd(f, ONE), wp);
    const Z = toFixed(z, wp);
    const Z2 = (Z * Z) >> W;
    let sum = Z, term = Z;
    for (let k = 1n; ; k++) {
      term = (term * Z2) >> W;
      const t = term / (2n * k + 1n);
      if (t === 0n) break;
      sum += t;
    }
    lnf = fixed(2n * sum, wp);
  }
  if (K === 0) return round(lnf, prec);
  const Kb = BigInt(K);
  const p2 = wp0 + bitLen(Kb) + 4;
  return add(lnf, mul(fromBigInt(Kb), ln2(p2), p2), prec);
}
export const log = (b, x, prec = DEFAULT_PREC) => div(ln(x, prec + 16), ln(b, prec + 16), prec);
export const log10 = (x, prec = DEFAULT_PREC) => log(fromInt(10), x, prec);
export function pow(a, b, prec = DEFAULT_PREC) {
  if (isInteger(b)) {
    const n = floorBig(b);
    if (bitLen(n) <= 40) return powInt(a, n, prec);
  }
  if (a.m === 0n) {
    if (b.m > 0n) return ZERO;
    throw domainError("0 to a non-positive power");
  }
  if (a.m < 0n) throw domainError("negative base with a non-integer exponent (real mode)");
  const mag = Math.abs(toNumber(b)) * Math.abs(toNumber(ln(a, 53)));
  const extra = Math.max(0, Math.ceil(Math.log2(mag + 1))) + 8;
  const wp = prec + 24 + extra;
  return exp(mul(b, ln(a, wp), wp), prec);
}
// a^(p/q), real convention: odd roots of negatives are real.
export function powRat(a, p, q, prec = DEFAULT_PREC) {
  p = BigInt(p); q = BigInt(q);
  if (q === 1n) return powInt(a, p, prec);
  if (a.m === 0n) {
    if (p > 0n) return ZERO;
    throw domainError("0 to a non-positive power");
  }
  if (a.m < 0n) {
    if (q % 2n === 0n) throw domainError("even root of a negative number (real mode)");
    const r = powRat(neg(a), p, q, prec);
    return p % 2n === 0n ? r : neg(r);
  }
  const wp = prec + 16;
  const ap = p < 0n ? -p : p;
  let r;
  if (ap <= 64n && q <= 64n) r = nthRoot(powInt(a, ap, wp + 8), Number(q), wp);
  else r = pow(a, div(fromBigInt(ap), fromBigInt(q), wp + 64), wp);
  return p < 0n ? div(ONE, r, prec) : round(r, prec);
}

// ---------------- trigonometric ----------------
export function sincos(x, prec = DEFAULT_PREC) {
  if (x.m === 0n) return [ZERO, ONE];
  const tx = top(x);
  if (tx > 4096) throw err("BUDGET", "trigonometric argument too large");
  let wp = prec + 24;
  let r, k;
  for (let attempt = 0; ; attempt++) {
    if (attempt > 12) throw err("BUDGET", "trigonometric argument reduction did not settle");
    const pw = wp + Math.max(0, tx) + 8;
    const halfPi = mulPow2(pi(pw), -1);
    k = roundBig(div(x, halfPi, Math.max(64, tx + 16)));
    r = k === 0n ? x : sub(x, mul(fromBigInt(k), halfPi, pw + bitLen(k)), pw);
    if (r.m === 0n) { wp *= 2; continue; }
    const tr = top(r);
    const good = pw - Math.max(0, tx) + Math.min(0, tr) - 4;
    if (k === 0n || good >= prec + 16) break;
    wp += prec + 16 - good + 16;
  }
  const tr = top(r);
  const wf = wp + Math.max(0, -tr) + 8;
  const W = BigInt(wf);
  const R = toFixed(r, wf);
  const R2 = (R * R) >> W;
  let s = R, term = R;
  for (let n = 1n; ; n++) {
    term = -((term * R2) >> W) / (2n * n * (2n * n + 1n));
    if (term === 0n) break;
    s += term;
  }
  const one = 1n << W;
  let c = one;
  term = one;
  for (let n = 1n; ; n++) {
    term = -((term * R2) >> W) / ((2n * n - 1n) * (2n * n));
    if (term === 0n) break;
    c += term;
  }
  const q = Number(((k % 4n) + 4n) % 4n);
  const S = [s, c, -s, -c][q], C = [c, -s, -c, s][q];
  return [rnd(S, -wf, prec), rnd(C, -wf, prec)];
}
export const sin = (x, prec = DEFAULT_PREC) => sincos(x, prec)[0];
export const cos = (x, prec = DEFAULT_PREC) => sincos(x, prec)[1];
export function tan(x, prec = DEFAULT_PREC) {
  const [s, c] = sincos(x, prec + 16);
  return div(s, c, prec);
}
export function atan(x, prec = DEFAULT_PREC) {
  if (x.m === 0n) return ZERO;
  const negx = x.m < 0n;
  let a = abs(x);
  const wp = prec + 24;
  const c1 = cmp(a, ONE);
  if (c1 === 0) { const r = mulPow2(pi(prec), -2); return negx ? neg(r) : r; }
  let invd = false;
  if (c1 > 0) { a = div(ONE, a, wp); invd = true; }
  let halv = 0;
  if (top(a) > -12) {
    halv = 4 + (wp > 300 ? Math.ceil(Math.sqrt(wp) / 3) : 0);
    for (let i = 0; i < halv; i++) a = div(a, add(ONE, sqrt(add(ONE, mul(a, a, wp), wp), wp), wp), wp);
  }
  const wf = wp + Math.max(0, -top(a)) + 8;
  const W = BigInt(wf);
  const A = toFixed(a, wf);
  const A2 = (A * A) >> W;
  let sum = A, term = A;
  for (let k = 1n; ; k++) {
    term = -((term * A2) >> W);
    const t = term / (2n * k + 1n);
    if (t === 0n) break;
    sum += t;
  }
  let res = fixed(sum << BigInt(halv), wf);
  if (invd) res = sub(mulPow2(pi(wf), -1), res, wf);
  res = round(res, prec);
  return negx ? neg(res) : res;
}
export function asin(x, prec = DEFAULT_PREC) {
  const c = cmp(abs(x), ONE);
  if (c > 0) throw domainError("asin argument outside [-1, 1]");
  if (c === 0) { const r = mulPow2(pi(prec), -1); return x.m < 0n ? neg(r) : r; }
  if (x.m === 0n) return ZERO;
  const wp = prec + 24;
  const d = mul(sub(ONE, x, Infinity), add(ONE, x, Infinity), wp); // (1-x)(1+x) with exact factors
  return atan(div(x, sqrt(d, wp), wp), prec);
}
export function acos(x, prec = DEFAULT_PREC) {
  if (cmp(abs(x), ONE) > 0) throw domainError("acos argument outside [-1, 1]");
  if (cmp(x, ONE) === 0) return ZERO;
  const negOne = new BigFloat(-1n, 0);
  if (cmp(x, negOne) === 0) return pi(prec);
  const wp = prec + 24;
  const t = sqrt(div(sub(ONE, x, Infinity), add(ONE, x, Infinity), wp), wp);
  return mulPow2(atan(t, prec), 1);
}
export function atan2(y, x, prec = DEFAULT_PREC) {
  if (x.m === 0n && y.m === 0n) throw domainError("atan2(0, 0) is undefined");
  const wp = prec + 16;
  if (x.m === 0n) { const r = mulPow2(pi(prec), -1); return y.m < 0n ? neg(r) : r; }
  if (y.m === 0n) return x.m > 0n ? ZERO : pi(prec);
  const a = atan(div(y, x, wp), wp);
  if (x.m > 0n) return round(a, prec);
  return y.m >= 0n ? add(a, pi(wp), prec) : sub(a, pi(wp), prec);
}

// ---------------- hyperbolic ----------------
const extraFor = (x) => Math.max(0, -top(x));
export function sinh(x, prec = DEFAULT_PREC) {
  if (x.m === 0n) return ZERO;
  const wp = prec + 24 + extraFor(x);
  const ex = exp(x, wp);
  return mulPow2(sub(ex, div(ONE, ex, wp), prec), -1);
}
export function cosh(x, prec = DEFAULT_PREC) {
  const wp = prec + 24;
  const ex = exp(x, wp);
  return mulPow2(add(ex, div(ONE, ex, wp), prec), -1);
}
export function tanh(x, prec = DEFAULT_PREC) {
  if (x.m === 0n) return ZERO;
  const wp = prec + 24 + extraFor(x);
  if (top(x) > 0 && toNumber(abs(x)) * 2.9 > wp) { // |tanh| = 1 - 2e^{-2|x|} rounds to 1
    return x.m > 0n ? ONE : neg(ONE);
  }
  const e2 = exp(mulPow2(x, 1), wp);
  return div(sub(e2, ONE, wp), add(e2, ONE, wp), prec);
}
export function asinh(x, prec = DEFAULT_PREC) {
  if (x.m === 0n) return ZERO;
  const a = abs(x);
  const wp = prec + 24 + extraFor(x);
  const r = ln(add(a, sqrt(add(mul(a, a, wp), ONE, wp), wp), wp), prec);
  return x.m < 0n ? neg(r) : r;
}
export function acosh(x, prec = DEFAULT_PREC) {
  const c = cmp(x, ONE);
  if (c < 0) throw domainError("acosh argument below 1");
  if (c === 0) return ZERO;
  const xm1 = sub(x, ONE, Infinity);
  const wp = prec + 24 + extraFor(xm1);
  const d = mul(xm1, add(x, ONE, Infinity), wp);
  return ln(add(x, sqrt(d, wp), wp), prec);
}
export function atanh(x, prec = DEFAULT_PREC) {
  if (cmp(abs(x), ONE) >= 0) throw domainError("atanh argument outside (-1, 1)");
  if (x.m === 0n) return ZERO;
  const wp = prec + 24 + extraFor(x);
  return mulPow2(ln(div(add(ONE, x, Infinity), sub(ONE, x, Infinity), wp), prec), -1);
}

// ---------------- Bernoulli numbers (Brent-Harvey tangent numbers) ----------------
let BERN = []; // BERN[k] = B_{2k} as Rational, k >= 1
function ensureBernoulli(n) {
  if (BERN.length > n) return;
  const m = Math.max(n, 2 * (BERN.length - 1), 16);
  if (m > 2000) throw err("BUDGET", "too many Bernoulli numbers requested");
  const T = new Array(m + 1).fill(0n);
  T[1] = 1n;
  for (let k = 2; k <= m; k++) T[k] = BigInt(k - 1) * T[k - 1];
  for (let k = 2; k <= m; k++) for (let j = k; j <= m; j++) T[j] = BigInt(j - k) * T[j - 1] + BigInt(j - k + 2) * T[j];
  const out = [null];
  for (let k = 1; k <= m; k++) {
    const p = 1n << BigInt(2 * k);
    const num = BigInt(2 * k) * T[k] * (k % 2 === 1 ? 1n : -1n);
    out.push(Q.Q(num, p * (p - 1n)));
  }
  BERN = out;
}
export function bernoulli2k(k) { ensureBernoulli(k); return BERN[k]; }

// ---------------- gamma, digamma, erf ----------------
function lgammaShifted(x, wp) {
  // ln Gamma(x) for x >= 1/2 with absolute error < 2^-wp
  const z0 = Math.ceil(0.2 * wp) + 10;
  const xn = toNumber(x);
  const N = xn < z0 ? Math.ceil(z0 - xn) : 0;
  if (N > 200000) throw err("BUDGET", "gamma shift too large");
  const mag = Math.abs(xn + N) * Math.log(Math.abs(xn + N) + 2) + 16;
  const w = wp + Math.ceil(Math.log2(mag)) + bitLen(BigInt(N + 1)) + 16;
  const z = add(x, fromInt(N), w);
  let P = ONE;
  for (let i = 0; i < N; i++) P = mul(P, add(x, fromInt(i), w), w);
  let s = sub(mul(sub(z, HALF, w), ln(z, w), w), z, w);
  s = add(s, mulPow2(ln(mulPow2(pi(w), 1), w), -1), w);
  const z2 = mul(z, z, w);
  let zp = z;
  let prevTop = Infinity;
  for (let k = 1; ; k++) {
    if (k > 1500) throw err("BUDGET", "Stirling series did not reach the target precision");
    ensureBernoulli(k);
    const B = BERN[k];
    const coef = Q.div(B, Q.Q(2 * k * (2 * k - 1)));
    const term = div(fromRational(coef, w), zp, w);
    const tt = top(term);
    if (tt < -(wp + 8)) break;
    if (tt > prevTop) throw err("BUDGET", "Stirling series diverged before reaching the target precision");
    prevTop = tt;
    s = add(s, term, w);
    zp = mul(zp, z2, w);
  }
  if (N > 0) s = sub(s, ln(P, w), w);
  return s;
}
export function lgamma(x, prec = DEFAULT_PREC) {
  if (cmp(x, HALF) < 0) throw domainError("lgamma implemented for x >= 1/2");
  return round(lgammaShifted(x, prec + 24), prec);
}
export function gamma(x, prec = DEFAULT_PREC) {
  const wp = prec + 24;
  if (isInteger(x)) {
    if (x.m <= 0n) throw domainError("gamma has a pole at a non-positive integer");
    const n = floorBig(x);
    if (n <= 5000n) return rnd(Q.factorial(n - 1n), 0, prec);
  }
  if (cmp(x, HALF) < 0) {
    const n = roundBig(x);
    const fr = sub(x, fromBigInt(n), Infinity);
    const w = wp + 8;
    let s = sin(mul(pi(w + 8), fr, w + 8), w);
    if (n % 2n !== 0n) s = neg(s);
    const g1 = gamma(sub(ONE, x, Infinity), w);
    return div(pi(w), mul(s, g1, w), prec);
  }
  const L = lgammaShifted(x, wp);
  return exp(L, prec);
}
export function factorial(x, prec = DEFAULT_PREC) { return gamma(add(x, ONE, Infinity), prec); }
export function digamma(x, prec = DEFAULT_PREC) {
  if (isInteger(x) && x.m <= 0n) throw domainError("digamma has a pole at a non-positive integer");
  const wp = prec + 24;
  if (cmp(x, HALF) < 0) {
    const n = roundBig(x);
    const fr = sub(x, fromBigInt(n), Infinity);
    const [s, c] = sincos(mul(pi(wp + 8), fr, wp + 8), wp);
    const cot = div(c, s, wp);
    return sub(digamma(sub(ONE, x, Infinity), wp), mul(pi(wp), cot, wp), prec);
  }
  const z0 = Math.ceil(0.2 * wp) + 10;
  const xn = toNumber(x);
  const N = xn < z0 ? Math.ceil(z0 - xn) : 0;
  const w = wp + 16;
  let S = ZERO;
  for (let i = 0; i < N; i++) S = add(S, div(ONE, add(x, fromInt(i), w), w), w);
  const z = add(x, fromInt(N), w);
  let r = sub(ln(z, w), div(ONE, mulPow2(z, 1), w), w);
  const z2 = mul(z, z, w);
  let zp = z2;
  for (let k = 1; ; k++) {
    if (k > 1500) throw err("BUDGET", "digamma series did not converge");
    ensureBernoulli(k);
    const term = div(fromRational(Q.div(BERN[k], Q.Q(2 * k)), w), zp, w);
    if (top(term) < -(wp + 8)) break;
    r = sub(r, term, w);
    zp = mul(zp, z2, w);
  }
  return sub(r, S, prec);
}
export function erf(x, prec = DEFAULT_PREC) {
  if (x.m === 0n) return ZERO;
  const negx = x.m < 0n;
  const a = abs(x);
  const wp = prec + 24;
  const an = toNumber(a);
  if (an * an > (wp + 16) * Math.LN2 + 4) return negx ? neg(ONE) : ONE; // erfc(a) < 2^-(wp+16)
  const w = wp + Math.ceil(an * an * 1.4427) + 16;
  const a2x2 = mulPow2(mul(a, a, w), 1);
  let term = a, sum = a;
  for (let n = 1; ; n++) {
    if (n > 1000000) throw err("BUDGET", "erf series too long");
    term = div(mul(term, a2x2, w), fromInt(2 * n + 1), w);
    sum = add(sum, term, w);
    if (top(term) < top(sum) - w - 2) break;
  }
  const f = div(mulPow2(exp(neg(mul(a, a, w)), w), 1), sqrt(pi(w), w), w);
  const r = mul(sum, f, prec);
  return negx ? neg(r) : r;
}

// ---------------- decimal output ----------------
// Correctly rounded (half to even) to `digits` significant decimal digits.
// opts.trim: drop trailing zeros; opts.sci: "auto" | true | false.
export function toDigits(x, digits) {
  // returns { neg, ds (string of exactly `digits` digits), k (decimal exponent of first digit) }
  const negx = x.m < 0n;
  const M = negx ? -x.m : x.m;
  let k = Math.floor((bitLen(M) + x.e - 1) * 0.30102999566398120);
  const lim = 10n ** BigInt(digits), lo = 10n ** BigInt(digits - 1);
  let D;
  for (let it = 0; it < 6; it++) {
    const s = digits - 1 - k;
    let num = M, den = 1n;
    if (x.e >= 0) num <<= BigInt(x.e); else den <<= BigInt(-x.e);
    if (s >= 0) num *= 10n ** BigInt(s); else den *= 10n ** BigInt(-s);
    D = divRound(num, den);
    if (D >= lim) { k++; continue; }
    if (D < lo) { k--; continue; }
    break;
  }
  return { neg: negx, ds: D.toString(), k };
}
export function formatDigits(negx, ds, k, opts = {}) {
  const digits = ds.length;
  let body;
  const sci = opts.sci === true || (opts.sci !== false && (k >= Math.max(digits, 21) || k < -7));
  if (!sci) {
    if (k >= 0) {
      if (k + 1 >= digits) body = ds + "0".repeat(k + 1 - digits);
      else body = ds.slice(0, k + 1) + "." + ds.slice(k + 1);
    } else body = "0." + "0".repeat(-k - 1) + ds;
    if (opts.trim && body.includes(".")) body = body.replace(/0+$/, "").replace(/\.$/, "");
  } else {
    let mant = ds.length > 1 ? ds[0] + "." + ds.slice(1) : ds;
    if (opts.trim && mant.includes(".")) mant = mant.replace(/0+$/, "").replace(/\.$/, "");
    body = mant + "e" + k;
  }
  return (negx ? "-" : "") + body;
}
export function toString(x, digits = 20, opts = {}) {
  if (!(x instanceof BigFloat)) x = from(x);
  if (x.m === 0n) return "0";
  digits = Math.max(1, Math.floor(digits));
  const { neg: n, ds, k } = toDigits(x, digits);
  return formatDigits(n, ds, k, opts);
}

// ---------------- complex numbers over BigFloat ----------------
export class Complex {
  constructor(re, im) { this.re = re; this.im = im; }
  toString() { return cToString(this, 20); }
}
export const toComplex = (x) => (x instanceof Complex ? x : new Complex(x, ZERO));
export const CI = new Complex(ZERO, ONE);
export const cadd = (a, b, prec = DEFAULT_PREC) => { a = toComplex(a); b = toComplex(b); return new Complex(add(a.re, b.re, prec), add(a.im, b.im, prec)); };
export const csub = (a, b, prec = DEFAULT_PREC) => { a = toComplex(a); b = toComplex(b); return new Complex(sub(a.re, b.re, prec), sub(a.im, b.im, prec)); };
export const cneg = (a) => { a = toComplex(a); return new Complex(neg(a.re), neg(a.im)); };
export function cmul(a, b, prec = DEFAULT_PREC) {
  a = toComplex(a); b = toComplex(b);
  const w = prec + 8;
  return new Complex(
    sub(mul(a.re, b.re, w), mul(a.im, b.im, w), prec),
    add(mul(a.re, b.im, w), mul(a.im, b.re, w), prec),
  );
}
export function cdiv(a, b, prec = DEFAULT_PREC) {
  a = toComplex(a); b = toComplex(b);
  if (b.re.m === 0n && b.im.m === 0n) throw domainError("division by zero");
  const w = prec + 16;
  const d = add(mul(b.re, b.re, w), mul(b.im, b.im, w), w);
  const re = add(mul(a.re, b.re, w), mul(a.im, b.im, w), w);
  const im = sub(mul(a.im, b.re, w), mul(a.re, b.im, w), w);
  return new Complex(div(re, d, prec), div(im, d, prec));
}
export function cabs(a, prec = DEFAULT_PREC) {
  a = toComplex(a);
  return sqrt(add(mul(a.re, a.re, prec + 8), mul(a.im, a.im, prec + 8), prec + 8), prec);
}
export const carg = (a, prec = DEFAULT_PREC) => { a = toComplex(a); return atan2(a.im, a.re, prec); };
export function cexp(a, prec = DEFAULT_PREC) {
  a = toComplex(a);
  const w = prec + 8;
  const r = exp(a.re, w);
  if (a.im.m === 0n) return new Complex(round(r, prec), ZERO);
  const [s, c] = sincos(a.im, w);
  return new Complex(mul(r, c, prec), mul(r, s, prec));
}
export function cln(a, prec = DEFAULT_PREC) {
  a = toComplex(a);
  if (a.re.m === 0n && a.im.m === 0n) throw domainError("logarithm of zero");
  const w = prec + 16;
  const m2 = add(mul(a.re, a.re, 2 * w), mul(a.im, a.im, 2 * w), 2 * w);
  return new Complex(mulPow2(ln(m2, prec), -1), atan2(a.im, a.re, prec));
}
export function csqrt(a, prec = DEFAULT_PREC) {
  a = toComplex(a);
  if (a.im.m === 0n) {
    if (a.re.m >= 0n) return new Complex(sqrt(a.re, prec), ZERO);
    return new Complex(ZERO, sqrt(neg(a.re), prec));
  }
  const w = prec + 16;
  const r = cabs(a, w);
  if (a.re.m >= 0n) {
    const t = sqrt(mulPow2(add(r, a.re, w), -1), w);
    return new Complex(round(t, prec), div(a.im, mulPow2(t, 1), prec));
  }
  const t = sqrt(mulPow2(sub(r, a.re, w), -1), w);
  const re = div(abs(a.im), mulPow2(t, 1), prec);
  return new Complex(re, a.im.m < 0n ? neg(round(t, prec)) : round(t, prec));
}
export function cpow(z, w, prec = DEFAULT_PREC) {
  z = toComplex(z); w = toComplex(w);
  if (w.im.m === 0n && isInteger(w.re) && bitLen(floorBig(w.re)) <= 20) {
    let n = floorBig(w.re);
    if (n === 0n) {
      if (z.re.m === 0n && z.im.m === 0n) throw domainError("0^0 is undefined");
      return new Complex(ONE, ZERO);
    }
    const invd = n < 0n;
    if (invd) n = -n;
    const wp = prec + 2 * bitLen(n) + 10;
    let r = null, b = z;
    while (n > 0n) {
      if (n & 1n) r = r ? cmul(r, b, wp) : b;
      n >>= 1n;
      if (n) b = cmul(b, b, wp);
    }
    if (invd) return cdiv(new Complex(ONE, ZERO), r, prec);
    return new Complex(round(r.re, prec), round(r.im, prec));
  }
  if (z.re.m === 0n && z.im.m === 0n) {
    if (w.re.m > 0n) return new Complex(ZERO, ZERO);
    throw domainError("0 to a power with non-positive real part");
  }
  const wp = prec + 32;
  return cexp(cmul(w, cln(z, wp), wp), prec);
}
export function csin(a, prec = DEFAULT_PREC) {
  a = toComplex(a);
  const w = prec + 16;
  const [s, c] = sincos(a.re, w);
  return new Complex(mul(s, cosh(a.im, w), prec), mul(c, sinh(a.im, w), prec));
}
export function ccos(a, prec = DEFAULT_PREC) {
  a = toComplex(a);
  const w = prec + 16;
  const [s, c] = sincos(a.re, w);
  return new Complex(mul(c, cosh(a.im, w), prec), neg(mul(s, sinh(a.im, w), prec)));
}
export function cToString(z, digits = 20, opts = {}) {
  z = toComplex(z);
  if (z.im.m === 0n) return toString(z.re, digits, opts);
  const im = toString(abs(z.im), digits, opts);
  const imPart = (im === "1" ? "" : im) + "i";
  if (z.re.m === 0n) return (z.im.m < 0n ? "-" : "") + imPart;
  return toString(z.re, digits, opts) + (z.im.m < 0n ? " - " : " + ") + imPart;
}
