// Quelvra research lab: prime sieves, Goldbach verification, twin primes, prime gaps.
//
// All searches are exhaustive up to a stated bound N (exact integer arithmetic; numbers stay far
// below 2^53). They are EVIDENCE for open conjectures, never proofs of them.

import * as T from "../numtheory.js";
import { Budget, asBudget, toBigIntArg, budgetError } from "./budget.js";

export const GOLDBACH_MAX = 4e9;       // hard ceiling for goldbachVerify (the time budget usually binds first)
export const PRIMES_MAX = 4e10;        // hard ceiling for twinPrimes / primeGaps
const SEG = 1 << 18;

// Primes <= n as an Int32Array-backed plain array (n <= ~2e7).
export function primesUpTo(n, budget) {
  n = Math.floor(Number(n));
  if (n < 2) return [];
  const comp = new Uint8Array(n + 1);
  const out = [];
  for (let i = 2; i <= n; i++) {
    if (comp[i]) continue;
    out.push(i);
    if (i * i <= n) { for (let j = i * i; j <= n; j += i) comp[j] = 1; if (budget) budget.tick(n / i); }
  }
  return out;
}

// Mark composites in [lo, hi) into buf (buf[i] = 1 means lo + i is NOT prime). basePrimes must cover sqrt(hi).
export function sieveSegment(lo, hi, basePrimes, buf) {
  const len = hi - lo;
  buf.fill(0, 0, len);
  for (let i = lo; i < Math.min(hi, 2); i++) buf[i - lo] = 1;
  for (const p of basePrimes) {
    const pp = p * p;
    if (pp >= hi) break;
    let start = pp >= lo ? pp : Math.ceil(lo / p) * p;
    for (let j = start - lo; j < len; j += p) buf[j] = 1;
  }
  return buf;
}

// Independent primality for cross-checks: plain trial division (n < 2^53, cost sqrt(n)).
export function isPrimeTrial(n) {
  n = Number(n);
  if (n < 2) return false;
  if (n % 2 === 0) return n === 2;
  if (n % 3 === 0) return n === 3;
  for (let d = 5; d * d <= n; d += 6) if (n % d === 0 || n % (d + 2) === 0) return false;
  return true;
}
// Independent Miller-Rabin (separate code and different bases from numtheory.js): deterministic below 2^64
// with the Jim Sinclair base set; above 2^64 it is a strong probable-prime test only.
const SINCLAIR = [2n, 325n, 9375n, 28178n, 450775n, 9780504n, 1795265022n];
function powmod(b, e, m) { let r = 1n; b %= m; while (e > 0n) { if (e & 1n) r = (r * b) % m; b = (b * b) % m; e >>= 1n; } return r; }
export function isPrimeMR2(n) {
  n = BigInt(n);
  if (n < 2n) return { prime: false, proven: true };
  for (const p of [2n, 3n, 5n, 7n, 11n, 13n, 17n, 19n, 23n, 29n, 31n, 37n]) if (n % p === 0n) return { prime: n === p, proven: true };
  let d = n - 1n, s = 0;
  while ((d & 1n) === 0n) { d >>= 1n; s++; }
  const bases = n < 1n << 64n ? SINCLAIR : [...SINCLAIR, 41n, 43n, 47n, 53n, 59n, 61n, 67n, 71n];
  for (let a of bases) {
    a %= n;
    if (a === 0n) continue;
    let x = powmod(a, d, n);
    if (x === 1n || x === n - 1n) continue;
    let comp = true;
    for (let r = 1; r < s; r++) { x = (x * x) % n; if (x === n - 1n) { comp = false; break; } }
    if (comp) return { prime: false, proven: true };
  }
  return { prime: true, proven: n < 1n << 64n };
}

// ------------------------------------------------------------------ Goldbach (strong / binary)
// Every even 4 <= n <= N is checked; for each n the least prime p with n - p prime is recorded.
export function goldbachVerify(N = 1000000, opts = {}) {
  const budget = asBudget(opts, "Goldbach verification");
  let n0 = Number(toBigIntArg(N, "N"));
  if (n0 < 4) throw budgetError("UNSUPPORTED", "Goldbach verification needs N >= 4");
  if (n0 > GOLDBACH_MAX) throw budgetError("BUDGET", `N is capped at ${GOLDBACH_MAX} (the conjecture has been verified by others up to 4 * 10^18; this browser-side check is for reproducing the method).`);
  if (n0 % 2) n0 -= 1;
  const P = Math.min(40000, n0);                  // least p is < 10^4 for all n <= 4 * 10^18
  const small = primesUpTo(P);
  const oddSmall = small.filter((p) => p > 2);
  const base = primesUpTo(Math.floor(Math.sqrt(n0)) + 2);
  const buf = new Uint8Array(SEG + P + 2);
  let checked = 0, sumMin = 0, hardest = { n: 4, p: 2 }, records = [{ n: 4, p: 2, q: 2 }];
  const hist = new Map();
  const sample = [];
  const sampleEvery = Math.max(1, Math.floor(n0 / 2 / 200));
  const failures = [];
  // n = 4 is the only even number needing p = 2
  checked = 1; sumMin = 2; hist.set(2, 1); sample.push({ n: 4, p: 2, q: 2 });
  for (let lo = 6; lo <= n0; lo += SEG) {
    const hi = Math.min(n0 + 1, lo + SEG);
    const wlo = Math.max(0, lo - P);
    sieveSegment(wlo, hi, base, buf);
    budget.tick(hi - wlo);
    for (let n = lo % 2 ? lo + 1 : lo; n < hi; n += 2) {
      let found = 0, tries = 0;
      for (const p of oddSmall) {
        tries++;
        if (p > n - p) break;
        if (!buf[n - p - wlo]) { found = p; break; }
      }
      if (!found) {
        // beyond the precomputed prime table (never observed in practice): fall back to Miller-Rabin
        for (let p = P + 1; p <= n / 2; p++) {
          budget.tick(50);
          if (T.isPrime(p) && T.isPrime(n - p)) { found = p; break; }
        }
      }
      budget.tick(tries);
      if (!found) { failures.push(n); continue; }
      checked++; sumMin += found;
      hist.set(found, (hist.get(found) || 0) + 1);
      if (found > hardest.p) { hardest = { n, p: found }; records.push({ n, p: found, q: n - found }); }
      if (((n >> 1) % sampleEvery) === 0 && sample.length < 400) sample.push({ n, p: found, q: n - found });
    }
    budget.progress((hi - 6) / (n0 - 5), "Goldbach verification");
  }
  hardest.q = hardest.n - hardest.p;
  if (!sample.some((s) => s.n === hardest.n)) sample.push({ ...hardest });
  const minPHistogram = [...hist.entries()].sort((a, b) => a[0] - b[0]).slice(0, 12).map(([p, count]) => ({ p, count }));
  return {
    N: n0, evensChecked: checked, failures, allHold: failures.length === 0,
    hardest, records, meanMinP: sumMin / checked, minPHistogram, sample,
    method: "segmented sieve of Eratosthenes; for each even n the primes p = 3, 5, 7, ... are tried until n - p is prime",
    ms: budget.elapsed(),
    status: failures.length ? "COUNTEREXAMPLE CANDIDATE (re-check required)" : "verified for every even n with 4 <= n <= N",
  };
}

// Goldbach decomposition of a single even n (BigInt allowed).
export function goldbach(n, opts = {}) {
  const budget = asBudget(opts, "Goldbach decomposition");
  n = toBigIntArg(n, "n");
  if (n < 4n || n % 2n) return { n, ok: false, reason: n % 2n ? "The strong Goldbach conjecture is about even numbers. For odd n >= 7 the weak (ternary) conjecture applies, and that one was proved by Helfgott (2013)." : "n must be at least 4." };
  if (n === 4n) return { n, ok: true, p: 2n, q: 2n, qStatus: "prime", method: "trivial", tries: 1, deterministic: true };
  const table = primesUpTo(200000);
  let tries = 0;
  const deterministic = n < T.MR_DETERMINISTIC_LIMIT;
  const tryP = (p) => {
    tries++;
    budget.tick(Math.max(1, Number(BigInt(n.toString(2).length) ** 2n / 64n)));
    const q = n - p;
    if (q < p) throw budgetError("UNSUPPORTED", "no decomposition found (this would be a counterexample; please report it)");
    const r = T.primality(q);
    return r.isPrime ? { q, r } : null;
  };
  for (const pp of table) {
    if (pp === 2) continue;
    const p = BigInt(pp);
    const hit = tryP(p);
    if (hit) return { n, ok: true, p, q: hit.q, qStatus: hit.r.status, method: hit.r.method, tries, deterministic: deterministic && hit.r.status === "prime" };
  }
  for (let p = T.nextPrime(200000n); ; p = T.nextPrime(p)) {
    const hit = tryP(p);
    if (hit) return { n, ok: true, p, q: hit.q, qStatus: hit.r.status, method: hit.r.method, tries, deterministic: deterministic && hit.r.status === "prime" };
  }
}

// ------------------------------------------------------------------ twin primes and prime gaps (one pass)
export function primeStats(N = 1000000, opts = {}) {
  const budget = asBudget(opts, "prime sieve");
  const n0 = Number(toBigIntArg(N, "N"));
  if (n0 < 2) return { N: n0, pi: 0, twinCount: 0, firstPairs: [], lastPairs: [], brunPartial: 0, gapRecords: [], maxGap: null, ms: 0 };
  if (n0 > PRIMES_MAX) throw budgetError("BUDGET", `N is capped at ${PRIMES_MAX}.`);
  const base = primesUpTo(Math.floor(Math.sqrt(n0)) + 2);
  const buf = new Uint8Array(SEG);
  let pi = 0, twin = 0, last = 0, maxGap = 0;
  const first = [], lastPairs = [], gapRecords = [];
  let brun = 0, brunC = 0; // Kahan-compensated partial Brun sum
  const addBrun = (v) => { const y = v - brunC; const t = brun + y; brunC = (t - brun) - y; brun = t; };
  for (let lo = 0; lo <= n0; lo += SEG) {
    const hi = Math.min(n0 + 1, lo + SEG);
    sieveSegment(lo, hi, base, buf);
    budget.tick(hi - lo);
    for (let i = 0, len = hi - lo; i < len; i++) {
      if (buf[i]) continue;
      const p = lo + i;
      pi++;
      if (last) {
        const g = p - last;
        if (g === 2) {
          twin++;
          addBrun(1 / last + 1 / p);
          if (first.length < 10) first.push([last, p]);
          lastPairs.push([last, p]); if (lastPairs.length > 10) lastPairs.shift();
        }
        if (g > maxGap) { maxGap = g; gapRecords.push({ gap: g, after: last, before: p }); }
      }
      last = p;
    }
    budget.progress(hi / (n0 + 1), "prime sieve");
  }
  return {
    N: n0, pi, twinCount: twin, firstPairs: first, lastPairs, brunPartial: brun, gapRecords,
    maxGap: gapRecords.length ? gapRecords[gapRecords.length - 1] : null, largestPrime: last,
    method: "segmented sieve of Eratosthenes (exact)", ms: budget.elapsed(),
  };
}
export const twinPrimes = primeStats;
export const primeGaps = primeStats;

// Published reference values (used only as an extra consistency check, never as the answer).
export const KNOWN_PI = { 10: 4, 100: 25, 1000: 168, 10000: 1229, 100000: 9592, 1000000: 78498, 10000000: 664579, 100000000: 5761455, 1000000000: 50847534 };
export const KNOWN_PI2 = { 1000: 35, 10000: 205, 100000: 1224, 1000000: 8169, 10000000: 58980, 100000000: 440312, 1000000000: 3424506 };
export { Budget };
