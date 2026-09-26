// Quelvra primality PROOFS (as opposed to probable-prime tests).
//
// proveprime(n) -> { status: "prime" | "composite" | "unknown", method, certificate, witness? }
//   * n < 3.317e24: deterministic Miller-Rabin with a proven witness set (via numtheory.primality)
//   * n = 2^p - 1: Lucas-Lehmer test (a proof for Mersenne numbers)
//   * otherwise: Pocklington / Brillhart-Lehmer-Selfridge n-1 certificate: if n - 1 = F * R with
//     F fully factored into PROVEN primes, F > sqrt(n), and for each prime q | F some a has
//     a^(n-1) = 1 (mod n) and gcd(a^((n-1)/q) - 1, n) = 1, then n is prime. Prime factors of F are
//     proven recursively, so the certificate is a complete proof tree.
// The certificate can be re-checked independently by checkCertificate().

import * as T from "./numtheory.js";

const modPow = (b, e, m) => { let r = 1n; b %= m; if (b < 0n) b += m; while (e > 0n) { if (e & 1n) r = (r * b) % m; b = (b * b) % m; e >>= 1n; } return r; };
const gcd = (a, b) => { a = a < 0n ? -a : a; b = b < 0n ? -b : b; while (b) [a, b] = [b, a % b]; return a; };
const isqrt = (n) => { if (n < 2n) return n; let x = BigInt(Math.floor(Math.sqrt(Number(n)))); while (x * x > n) x--; while ((x + 1n) * (x + 1n) <= n) x++; for (;;) { const y = (x + n / x) >> 1n; if (y >= x) break; x = y; } while (x * x > n) x--; return x; };
const bitLen = (n) => n.toString(2).length;

function lucasLehmer(p) {
  const M = (1n << BigInt(p)) - 1n;
  let s = 4n;
  for (let i = 0; i < p - 2; i++) {
    s = s * s - 2n;
    s = (s & M) + (s >> BigInt(p)); // fast reduction mod 2^p - 1
    if (s >= M) s -= M;
  }
  return s === 0n || s === M;
}

export function proveprime(n, opts = {}, depth = 0) {
  n = BigInt(n);
  if (n < 2n) return { status: "composite", method: "definition", certificate: { n: String(n), type: "not-prime" } };
  const quick = T.primality(n);
  if (quick.status === "composite" || quick.status === "neither") return { status: "composite", method: quick.method, certificate: { n: String(n), type: "composite" } };
  if (n < T.MR_DETERMINISTIC_LIMIT) return { status: "prime", method: quick.method, certificate: { n: String(n), type: "deterministic-mr" } };
  // Mersenne
  const b = bitLen(n);
  if (n === (1n << BigInt(b)) - 1n) {
    const pr = proveprime(BigInt(b), opts, depth + 1);
    if (pr.status !== "prime") return { status: "composite", method: "2^p - 1 with p composite is composite", certificate: { n: String(n), type: "mersenne-composite-exponent" } };
    if (b <= 20000) {
      const ok = lucasLehmer(b);
      return { status: ok ? "prime" : "composite", method: `Lucas-Lehmer test for 2^${b} - 1`, certificate: { n: String(n), type: "lucas-lehmer", p: b, pCert: pr.certificate } };
    }
  }
  if (depth > 40) return { status: "unknown", method: "certificate depth limit", certificate: null };
  // Pocklington n-1
  const m = n - 1n;
  const fac = T.factor(m, { budget: opts.budget || 3_000_000 });
  let F = 1n;
  const primes = [];
  for (const [q, e] of fac.factors) {
    const pq = proveprime(q, opts, depth + 1);
    if (pq.status !== "prime") continue;
    F *= q ** e;
    primes.push({ q, cert: pq.certificate });
  }
  if (F * F <= n) return { status: "unknown", method: "Baillie-PSW says probable prime; n - 1 could not be factored far enough for a proof", certificate: null };
  const witnesses = [];
  for (const { q } of primes) {
    let found = null;
    for (let a = 2n; a < 200n; a++) {
      if (modPow(a, m, n) !== 1n) return { status: "composite", method: `Fermat witness ${a}`, certificate: { n: String(n), type: "fermat-witness", a: String(a) } };
      if (gcd(modPow(a, m / q, n) - 1n, n) === 1n) { found = a; break; }
    }
    if (found === null) return { status: "unknown", method: "no Pocklington witness found", certificate: null };
    witnesses.push({ q: String(q), a: String(found) });
  }
  return { status: "prime", method: "Pocklington n - 1 certificate", certificate: { n: String(n), type: "pocklington", F: String(F), witnesses, factors: primes.map((p) => p.cert) } };
}

// Independent re-check of a certificate (does not trust how it was produced).
export function checkCertificate(c) {
  if (!c) return false;
  const n = BigInt(c.n);
  switch (c.type) {
    case "deterministic-mr": return T.primality(n).status === "prime" && n < T.MR_DETERMINISTIC_LIMIT;
    case "lucas-lehmer": return n === (1n << BigInt(c.p)) - 1n && checkCertificate(c.pCert) && lucasLehmer(c.p);
    case "pocklington": {
      const F = BigInt(c.F), m = n - 1n;
      if (m % F !== 0n || F * F <= n) return false;
      let prod = 1n;
      for (const f of c.factors) { if (!checkCertificate(f)) return false; }
      // F must be composed exactly of the certified primes
      let rest = F;
      for (const f of c.factors) { const q = BigInt(f.n); while (rest % q === 0n) { rest /= q; prod *= q; } }
      if (rest !== 1n) return false;
      for (const { q, a } of c.witnesses) {
        const Q = BigInt(q), A = BigInt(a);
        if (modPow(A, m, n) !== 1n || gcd(modPow(A, m / Q, n) - 1n, n) !== 1n) return false;
      }
      return c.factors.every((f) => c.witnesses.some((w) => w.q === f.n));
    }
    default: return false;
  }
}
export { isqrt };
