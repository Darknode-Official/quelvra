// Verifier-side values of the discrete / probability functions (independent of discrete.js).
//
// Every function here uses a DIFFERENT method from the solver: Binet's formula for Fibonacci numbers,
// the sieve of Sundaram for primes, inclusion-exclusion for Stirling numbers, divisor trial loops,
// log-gamma for binomial / Poisson / hypergeometric probabilities, and Simpson integration of the
// normal density for normalcdf. A value that cannot be computed reliably returns NaN, which makes
// the check inconclusive (the answer is then withheld, never passed).

const SQRT2PI = Math.sqrt(2 * Math.PI);
// Lanczos log-gamma (g = 7, n = 9)
const LG = [0.99999999999980993, 676.5203681218851, -1259.1392167224028, 771.32342877765313, -176.61502916214059,
  12.507343278686905, -0.13857109526572012, 9.9843695780195716e-6, 1.5056327351493116e-7];
function lgamma(x) {
  if (x < 0.5) return Math.log(Math.PI / Math.abs(Math.sin(Math.PI * x))) - lgamma(1 - x);
  x -= 1;
  let a = LG[0];
  const t = x + 7.5;
  for (let i = 1; i < 9; i++) a += LG[i] / (x + i);
  return 0.5 * Math.log(2 * Math.PI) + (x + 0.5) * Math.log(t) - t + Math.log(a);
}
const lnC = (n, k) => lgamma(n + 1) - lgamma(k + 1) - lgamma(n - k + 1);
const isNat = (x) => Number.isInteger(x) && x >= 0;
const bigToNum = (b) => Number(b);

function bigBinom(n, k) { // multiplicative formula
  if (k < 0n || k > n) return 0n;
  let r = 1n;
  for (let i = 1n; i <= k; i++) r = (r * (n - k + i)) / i;
  return r;
}
function stirlingIE(n, k) { // S(n, k) = (1/k!) sum_i (-1)^i C(k, i) (k - i)^n
  let s = 0n, f = 1n;
  for (let i = 0n; i <= k; i++) s += (i % 2n ? -1n : 1n) * bigBinom(k, i) * (k - i) ** n;
  for (let i = 2n; i <= k; i++) f *= i;
  return s / f;
}
function sundaramNth(n) {
  if (n === 1) return 2;
  const lim = n < 6 ? 15 : Math.ceil(n * (Math.log(n) + Math.log(Math.log(n)))) + 10;
  const m = Math.floor((lim - 1) / 2);
  const out = new Uint8Array(m + 1);
  for (let i = 1; i <= m; i++) for (let j = i; i + j + 2 * i * j <= m; j++) out[i + j + 2 * i * j] = 1;
  let c = 1; // the prime 2
  for (let i = 1; i <= m; i++) if (!out[i] && ++c === n) return 2 * i + 1;
  return NaN;
}
function divisorLoop(n, what) {
  if (!Number.isSafeInteger(n) || n < 1 || n > 1e13) return NaN;
  let s = 0, c = 0;
  for (let d = 1; d * d <= n; d++) {
    if (n % d) continue;
    const e = n / d;
    s += d; c++;
    if (e !== d) { s += e; c++; }
  }
  return what === "sum" ? s : c;
}
function egcdBig(a, b) { // iterative extended Euclid: returns [g, x] with a x = g (mod b)
  let [r0, r1, s0, s1] = [a, b, 1n, 0n];
  while (r1 !== 0n) { const q = r0 / r1; [r0, r1] = [r1, r0 - q * r1]; [s0, s1] = [s1, s0 - q * s1]; }
  return [r0, s0];
}
const modB = (a, m) => ((a % m) + m) % m;
function powmodLR(a, e, m) { // left-to-right binary exponentiation
  let r = 1n % m;
  const bits = e.toString(2);
  for (const bit of bits) { r = (r * r) % m; if (bit === "1") r = (r * a) % m; }
  return r;
}
function normalCdfStd(z) {
  if (z === Infinity) return 1;
  if (z === -Infinity) return 0;
  if (Math.abs(z) > 12) return z > 0 ? 1 : 0;
  // Simpson's rule for the integral of the density on [0, |z|]
  const a = Math.abs(z), n = 4000, h = a / n;
  const f = (t) => Math.exp(-t * t / 2) / SQRT2PI;
  let s = f(0) + f(a);
  for (let i = 1; i < n; i++) s += (i % 2 ? 4 : 2) * f(i * h);
  const half = (s * h) / 3;
  return z >= 0 ? 0.5 + half : 0.5 - half;
}
const probOK = (p) => p >= 0 && p <= 1;

export const DISCRETE_FLOAT = {
  catalan: ([n]) => {
    if (!isNat(n) || n > 3000) return NaN;
    let c = 1n; // C(k+1) = C(k) * 2(2k+1)/(k+2)
    for (let k = 0n; k < BigInt(n); k++) c = (c * 2n * (2n * k + 1n)) / (k + 2n);
    return bigToNum(c);
  },
  fibonacci: ([n]) => {
    if (!Number.isInteger(n) || Math.abs(n) > 1400) return NaN;
    const phi = (1 + Math.sqrt(5)) / 2, psi = (1 - Math.sqrt(5)) / 2;
    return (Math.pow(phi, n) - Math.pow(psi, n)) / Math.sqrt(5);
  },
  lucas: ([n]) => (isNat(n) && n <= 1400 ? Math.pow((1 + Math.sqrt(5)) / 2, n) + Math.pow((1 - Math.sqrt(5)) / 2, n) : NaN),
  subfactorial: ([n]) => {
    if (!isNat(n) || n > 170) return NaN;
    if (n === 0) return 1;
    let s = 0, t = 1; // n! sum_{i<=n} (-1)^i / i!
    for (let i = 0; i <= n; i++) { if (i > 0) t /= i; s += (i % 2 ? -1 : 1) * t; }
    const v = Math.exp(lgamma(n + 1)) * s;
    return n <= 20 ? Math.round(v) : v;
  },
  multinomial: (ks) => (ks.length && ks.every(isNat) ? Math.exp(lgamma(ks.reduce((a, b) => a + b, 0) + 1) - ks.reduce((a, k) => a + lgamma(k + 1), 0)) : NaN),
  stirling: ([n, k]) => (isNat(n) && isNat(k) && n <= 400 ? bigToNum(stirlingIE(BigInt(n), BigInt(k))) : NaN),
  bell: ([n]) => {
    if (!isNat(n) || n > 120) return NaN;
    let s = 0n;
    for (let k = 0n; k <= BigInt(n); k++) s += stirlingIE(BigInt(n), k);
    return bigToNum(s);
  },
  nthprime: ([n]) => (Number.isInteger(n) && n >= 1 && n <= 300000 ? sundaramNth(n) : NaN),
  divisorsum: ([n]) => divisorLoop(n, "sum"),
  numdivisors: ([n]) => divisorLoop(n, "count"),
  modinv: ([a, m]) => {
    if (!Number.isSafeInteger(a) || !Number.isSafeInteger(m) || m < 2) return NaN;
    const A = modB(BigInt(a), BigInt(m)), M = BigInt(m);
    const [g, x] = egcdBig(A, M);
    if (g !== 1n) return NaN;
    const r = modB(x, M);
    return (A * r) % M === 1n ? bigToNum(r) : NaN;
  },
  powmod: ([a, e, m]) => {
    if (![a, e, m].every(Number.isSafeInteger) || m < 1) return NaN;
    const M = BigInt(m);
    let A = modB(BigInt(a), M), E = BigInt(e);
    if (E < 0n) { const [g, x] = egcdBig(A, M); if (g !== 1n) return NaN; A = modB(x, M); E = -E; }
    return bigToNum(powmodLR(A, E, M));
  },
  binompdf: ([n, p, k]) => {
    if (!isNat(n) || !probOK(p) || !Number.isInteger(k)) return NaN;
    if (k < 0 || k > n) return 0;
    if (p === 0) return k === 0 ? 1 : 0;
    if (p === 1) return k === n ? 1 : 0;
    return Math.exp(lnC(n, k) + k * Math.log(p) + (n - k) * Math.log(1 - p));
  },
  binomcdf: ([n, p, k]) => {
    if (!isNat(n) || !probOK(p) || !Number.isInteger(k) || n > 100000) return NaN;
    let s = 0;
    for (let i = 0; i <= Math.min(k, n); i++) s += DISCRETE_FLOAT.binompdf([n, p, i]);
    return s;
  },
  geompdf: ([p, k]) => (probOK(p) && p > 0 && Number.isInteger(k) ? (k < 1 ? 0 : p * Math.pow(1 - p, k - 1)) : NaN),
  geomcdf: ([p, k]) => {
    if (!(probOK(p) && p > 0 && Number.isInteger(k))) return NaN;
    let s = 0;
    for (let i = 1; i <= Math.min(k, 100000); i++) s += p * Math.pow(1 - p, i - 1);
    return s;
  },
  poissonpdf: ([L, k]) => (L > 0 && Number.isInteger(k) ? (k < 0 ? 0 : Math.exp(-L + k * Math.log(L) - lgamma(k + 1))) : NaN),
  poissoncdf: ([L, k]) => {
    if (!(L > 0 && Number.isInteger(k)) || k > 2000) return NaN;
    let s = 0;
    for (let i = 0; i <= k; i++) s += Math.exp(-L + i * Math.log(L) - lgamma(i + 1));
    return s;
  },
  hypergeompdf: ([Np, K, n, k]) => {
    if (![Np, K, n, k].every(isNat) || K > Np || n > Np) return NaN;
    if (k > K || k > n || n - k > Np - K) return 0;
    return Math.exp(lnC(K, k) + lnC(Np - K, n - k) - lnC(Np, n));
  },
  normalpdf: (xs) => {
    const [x, mu, s] = xs.length === 3 ? xs : [xs[0], 0, 1];
    if (!(s > 0)) return NaN;
    return Math.exp(-(((x - mu) / s) ** 2) / 2) / (s * SQRT2PI);
  },
  normalcdf: (xs) => {
    const [a, b, mu, s] = xs.length === 4 ? xs : [xs[0], xs[1], 0, 1];
    if (!(s > 0)) return NaN;
    return normalCdfStd((b - mu) / s) - normalCdfStd((a - mu) / s);
  },
  round: ([x, d = 0]) => {
    if (!Number.isInteger(d) || Math.abs(d) > 300) return NaN;
    const k = Math.pow(10, d), y = Math.abs(x) * k, f = y - Math.floor(y);
    // a decimal input exactly on a half (2.675 to 2 places) is a float hair away from it: treat as the tie
    const r = Math.abs(f - 0.5) < 1e-9 * Math.max(1, y) ? Math.floor(y) + 1 : Math.round(y);
    return Math.sign(x) * r / k;
  },
  zscore: ([x, mu, s]) => (s > 0 ? (x - mu) / s : NaN),
};
DISCRETE_FLOAT.fib = DISCRETE_FLOAT.fibonacci;
DISCRETE_FLOAT.derangements = DISCRETE_FLOAT.subfactorial;
