// Quelvra exact number tower: arbitrary-size integers and reduced rationals on BigInt.
// A Rational is a frozen { n: BigInt, d: BigInt } with d > 0 and gcd(|n|, d) = 1.
// JavaScript Number is never used for exact mathematics.

export const bgcd = (a, b) => {
  a = a < 0n ? -a : a;
  b = b < 0n ? -b : b;
  while (b) [a, b] = [b, a % b];
  return a;
};
export const babs = (a) => (a < 0n ? -a : a);

const CACHE = new Map();
export function Q(n, d = 1n) {
  n = BigInt(n);
  d = BigInt(d);
  if (d === 0n) throw new RangeError("Quelvra: rational with zero denominator");
  if (d < 0n) { n = -n; d = -d; }
  const g = bgcd(n, d);
  if (g !== 1n && g !== 0n) { n /= g; d /= g; }
  if (n === 0n) d = 1n;
  if (d === 1n && n >= -64n && n <= 64n) {
    const c = CACHE.get(n);
    if (c) return c;
    const r = Object.freeze({ n, d });
    CACHE.set(n, r);
    return r;
  }
  return Object.freeze({ n, d });
}

export const ZERO = Q(0), ONE = Q(1), TWO = Q(2), NEG_ONE = Q(-1), HALF = Q(1, 2);

export const isInt = (r) => r.d === 1n;
export const isZero = (r) => r.n === 0n;
export const isOne = (r) => r.n === 1n && r.d === 1n;
export const isNeg = (r) => r.n < 0n;
export const isPos = (r) => r.n > 0n;
export const sign = (r) => (r.n > 0n ? 1 : r.n < 0n ? -1 : 0);
export const eq = (a, b) => a.n === b.n && a.d === b.d;

export const add = (a, b) => Q(a.n * b.d + b.n * a.d, a.d * b.d);
export const sub = (a, b) => Q(a.n * b.d - b.n * a.d, a.d * b.d);
export const mul = (a, b) => Q(a.n * b.n, a.d * b.d);
export const div = (a, b) => {
  if (b.n === 0n) throw new RangeError("Quelvra: division by zero");
  return Q(a.n * b.d, a.d * b.n);
};
export const neg = (a) => Q(-a.n, a.d);
export const inv = (a) => div(ONE, a);
export const abs = (a) => (a.n < 0n ? Q(-a.n, a.d) : a);
export const cmp = (a, b) => {
  const l = a.n * b.d, r = b.n * a.d;
  return l < r ? -1 : l > r ? 1 : 0;
};
export const lt = (a, b) => cmp(a, b) < 0;

// Integer power (exponent a BigInt or safe integer). Negative exponents invert.
export function pow(a, e) {
  e = BigInt(e);
  if (e === 0n) return ONE;
  if (e < 0n) return inv(pow(a, -e));
  return Q(a.n ** e, a.d ** e);
}

// floor / ceil / truncating integer division
export const floor = (a) => {
  const q = a.n / a.d;
  return a.n < 0n && q * a.d !== a.n ? q - 1n : q;
};
export const ceil = (a) => -floor(neg(a));
export const frac = (a) => sub(a, Q(floor(a)));

// Integer k-th root: returns [root, exact] where root = floor(|n|^(1/k)) (sign kept for odd k).
export function iroot(n, k) {
  k = BigInt(k);
  if (n < 0n) {
    if (k % 2n === 0n) return [null, false];
    const [r, ex] = iroot(-n, k);
    return [-r, ex];
  }
  if (n < 2n) return [n, true];
  // Newton iteration on BigInt
  const kn = Number(k);
  let x = BigInt(Math.floor(Math.pow(Number(n), 1 / kn))) + 1n;
  if (x < 1n) x = 1n;
  // guard against float overflow for huge n
  if (!isFinite(Math.pow(Number(n), 1 / kn))) x = 1n << BigInt(Math.ceil(n.toString(2).length / kn) + 1);
  for (;;) {
    const y = ((k - 1n) * x + n / x ** (k - 1n)) / k;
    if (y >= x) break;
    x = y;
  }
  while (x ** k > n) x -= 1n;
  while ((x + 1n) ** k <= n) x += 1n;
  return [x, x ** k === n];
}

// Small-prime factorisation with a work limit. Returns { factors: Map<BigInt, BigInt>, rest }
// where rest is the cofactor that was not fully factored (1n when complete).
const SMALL_PRIMES = (() => {
  const out = [];
  const lim = 10000;
  const sieve = new Uint8Array(lim + 1);
  for (let i = 2; i <= lim; i++) {
    if (!sieve[i]) { out.push(BigInt(i)); for (let j = i * i; j <= lim; j += i) sieve[j] = 1; }
  }
  return out;
})();
export function trialFactor(n) {
  n = babs(n);
  const factors = new Map();
  if (n < 2n) return { factors, rest: n === 0n ? 0n : 1n };
  for (const p of SMALL_PRIMES) {
    if (p * p > n) break;
    while (n % p === 0n) { factors.set(p, (factors.get(p) || 0n) + 1n); n /= p; }
  }
  if (n > 1n) {
    const lim = SMALL_PRIMES[SMALL_PRIMES.length - 1];
    if (n <= lim * lim) { factors.set(n, (factors.get(n) || 0n) + 1n); n = 1n; }
  }
  return { factors, rest: n };
}

// Split |n| = c^k * m where c is as large as the small-prime factorisation allows.
// Used to extract exact k-th roots: sqrt(72) = 6 sqrt(2).
export function extractPower(n, k) {
  k = BigInt(k);
  const { factors, rest } = trialFactor(n);
  let outside = 1n, inside = 1n;
  for (const [p, e] of factors) {
    outside *= p ** (e / k);
    inside *= p ** (e % k);
  }
  if (rest > 1n) {
    const [r, ex] = iroot(rest, k);
    if (ex) outside *= r; else inside *= rest;
  }
  return { outside, inside };
}

export function toString(r) {
  return r.d === 1n ? r.n.toString() : `${r.n}/${r.d}`;
}

// Exact rational from a decimal literal "12.5", "1e-3", "0.1".
export function fromDecimal(s) {
  s = String(s).trim();
  const m = s.match(/^([+-]?)(\d*)(?:\.(\d*))?(?:[eE]([+-]?\d+))?$/);
  if (!m) throw new SyntaxError("Quelvra: bad number " + s);
  const [, sg, ip = "", fp = "", ex = "0"] = m;
  let n = BigInt((ip || "0") + fp);
  let d = 10n ** BigInt(fp.length);
  const e = BigInt(ex);
  if (e > 0n) n *= 10n ** e; else if (e < 0n) d *= 10n ** -e;
  return Q(sg === "-" ? -n : n, d);
}

// Approximate as a JS double (for plotting / quick numeric checks only).
export function toFloat(r) {
  const n = r.n, d = r.d;
  const fn = Number(n), fd = Number(d);
  if (isFinite(fn) && isFinite(fd)) return fn / fd;
  // scale down huge values
  const shift = BigInt(Math.max(0, Math.max(n.toString(2).length, d.toString(2).length) - 1000));
  return Number(n >> shift) / Number(d >> shift);
}

// Exact decimal expansion to `digits` places (rounded half away from zero).
export function toDecimalString(r, digits = 20) {
  const neg = r.n < 0n;
  let n = neg ? -r.n : r.n;
  const scale = 10n ** BigInt(digits);
  let q = (n * scale * 2n + r.d) / (2n * r.d);
  let s = q.toString().padStart(digits + 1, "0");
  let out = digits ? s.slice(0, -digits) + "." + s.slice(-digits) : s;
  if (digits) out = out.replace(/0+$/, "").replace(/\.$/, "");
  return (neg && out !== "0" ? "-" : "") + out;
}

export function factorial(n) {
  n = BigInt(n);
  if (n < 0n) throw new RangeError("factorial of negative integer");
  let r = 1n;
  for (let i = 2n; i <= n; i++) r *= i;
  return r;
}
export function binom(n, k) {
  n = BigInt(n); k = BigInt(k);
  if (k < 0n || k > n) return 0n;
  if (k > n - k) k = n - k;
  let r = 1n;
  for (let i = 1n; i <= k; i++) r = (r * (n - k + i)) / i;
  return r;
}
