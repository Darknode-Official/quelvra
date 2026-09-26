// Number-theoretic cryptography on explicit integers.
//
//   rsakeys(p, q, e[, m])   rsadecrypt(c, n, d)   rsacrt(c, p, q, d)
//   modpow(a, b, m)         modinverse(a, m)      dlog(g, h, m)       diffiehellman(p, g, a, b)
//
// Routes: modular powers use left-to-right square-and-multiply and are checked with the
// right-to-left binary method (and, for RSA, with CRT recombination); inverses are checked by
// multiplying back; discrete logarithms (baby-step giant-step) are checked by powering and by the
// element order (minimality), and "no solution" by h^ord(g) != 1 in the cyclic group mod a prime or
// by listing the subgroup.

import { refuse, ansNum, ansText, check, step, gcd, egcd, mod, modInv, powMod, powModRL, isqrt, isPrimeSmall, factorSmall } from "./util.js";
import { intOf } from "./decode.js";

const I = (u, what) => intOf(u, what);
function prime(p, name) {
  if (p < 2n) throw refuse(`${name} = ${p} is not prime`);
  if (p > 10n ** 14n) throw refuse(`${name} is too large to certify as prime here`);
  if (!isPrimeSmall(p)) throw refuse(`${name} = ${p} is not prime`);
}
function crtPow(c, d, p, q) { // Garner recombination
  const dp = d % (p - 1n), dq = d % (q - 1n), qinv = modInv(q, p);
  const m1 = powMod(c, dp, p), m2 = powMod(c, dq, q);
  const h = mod(qinv * (m1 - m2), p);
  return { m: m2 + h * q, dp, dq, qinv, m1, m2 };
}

function cmdRSA(args) {
  if (args.length < 3 || args.length > 4) throw refuse("rsakeys(p, q, e[, message])");
  const [p, q, e] = args.slice(0, 3).map((a) => I(a));
  prime(p, "p"); prime(q, "q");
  if (p === q) throw refuse("p and q must be different primes");
  const n = p * q, phi = (p - 1n) * (q - 1n);
  if (e <= 1n || e >= phi) throw refuse(`e must satisfy 1 < e < φ(n) = ${phi}`);
  const g = gcd(e, phi);
  if (g !== 1n) throw refuse(`e = ${e} is not coprime to φ(n) = ${phi} (gcd ${g}), so it has no inverse and is not a valid RSA exponent`);
  const d = modInv(e, phi);
  const answers = [ansNum("n", n), ansNum("phi(n)", phi), ansNum("d", d), ansText("public key", `(n, e) = (${n}, ${e})`), ansText("private key", `(n, d) = (${n}, ${d})`)];
  let m = null, c = null;
  if (args[3]) {
    m = I(args[3]);
    if (m < 0n || m >= n) throw refuse(`the message must satisfy 0 <= m < n = ${n}`);
    c = powMod(m, e, n);
    answers.push(ansNum("ciphertext", c));
  }
  return {
    answers,
    steps: [step("rsa.n", "n = p q and φ(n) = (p - 1)(q - 1)", `n = ${n}, φ(n) = ${phi}.`), step("rsa.d", "d = e^(-1) mod φ(n) by the extended Euclidean algorithm", `d = ${d}.`),
      ...(m !== null ? [step("rsa.enc", "Encrypt: c = m^e mod n", `${m}^${e} mod ${n} = ${c}.`)] : [])],
    checks: () => {
      const cs = [check("n and φ", p * q === n && n - p - q + 1n === phi, "n = pq and φ(n) = n - p - q + 1"), check("e d ≡ 1", (e * d) % phi === 1n, `e·d = ${e * d} ≡ 1 (mod ${phi})`)];
      if (m !== null) {
        cs.push(check("right-to-left power", powModRL(m, e, n) === c, "the right-to-left binary method gives the same ciphertext"));
        cs.push(check("decrypts", crtPow(c, d, p, q).m === m, "decrypting the ciphertext (CRT with d) recovers the message"));
      }
      return cs;
    },
  };
}
function cmdRSADecrypt(args) {
  if (args.length !== 3) throw refuse("rsadecrypt(c, n, d)");
  const [c, n, d] = args.map((a) => I(a));
  if (n < 2n || d < 1n || c < 0n || c >= n) throw refuse("need 0 <= c < n and d >= 1");
  const m = powMod(c, d, n);
  return {
    answers: [ansNum("plaintext", m)],
    steps: [step("rsa.dec", "Decrypt: m = c^d mod n (square and multiply)", `${c}^${d} mod ${n} = ${m}.`)],
    checks: () => {
      const cs = [check("right-to-left power", powModRL(c, d, n) === m, "the right-to-left binary method gives the same value")];
      const f = n <= 10n ** 14n ? factorSmall(n) : null;
      if (f && f.length === 2 && f.every(([, e]) => e === 1)) cs.push(check("CRT", crtPow(c, d, f[0][0], f[1][0]).m === m, `recombining the powers mod ${f[0][0]} and mod ${f[1][0]} gives the same value`));
      return cs;
    },
  };
}
function cmdRSACRT(args) {
  if (args.length !== 4) throw refuse("rsacrt(c, p, q, d)");
  const [c, p, q, d] = args.map((a) => I(a));
  prime(p, "p"); prime(q, "q");
  if (p === q) throw refuse("p and q must differ");
  const n = p * q;
  if (c < 0n || c >= n) throw refuse(`the ciphertext must satisfy 0 <= c < n = ${n}`);
  const r = crtPow(c, d, p, q);
  return {
    answers: [ansNum("plaintext", r.m), ansText("crt values", `d_p = ${r.dp}, d_q = ${r.dq}, q^(-1) mod p = ${r.qinv}, m_p = ${r.m1}, m_q = ${r.m2}`)],
    steps: [step("rsa.crt", "Reduce the exponent: d_p = d mod (p - 1), d_q = d mod (q - 1)", `d_p = ${r.dp}, d_q = ${r.dq}.`), step("rsa.crt.pow", "Power separately", `m_p = c^d_p mod p = ${r.m1}, m_q = c^d_q mod q = ${r.m2}.`),
      step("rsa.crt.garner", "Recombine (Garner): m = m_q + q · (q^(-1) (m_p - m_q) mod p)", `m = ${r.m}.`)],
    checks: () => [check("direct power", powModRL(c, d, n) === r.m, `computing c^d mod ${n} directly gives the same plaintext`)],
  };
}
function cmdModPow(args) {
  if (args.length !== 3) throw refuse("modpow(a, b, m)");
  const [a, b, m] = args.map((x) => I(x));
  if (m < 1n) throw refuse("the modulus must be positive");
  if (b < 0n && gcd(a, m) !== 1n) throw refuse(`${a} has no inverse mod ${m}, so a negative power is undefined`);
  const r = powMod(a, b, m);
  return {
    answers: [ansNum("result", r)],
    steps: [step("nt.powmod", "Square and multiply", `Scan the ${b < 0n ? -b : b} in binary, squaring each step and multiplying when the bit is 1, all mod ${m}: ${a}^${b} ≡ ${r}.`)],
    checks: () => {
      const alt = b < 0n ? powModRL(modInv(a, m), -b, m) : powModRL(a, b, m);
      const cs = [check("right-to-left power", alt === r, "the right-to-left binary method gives the same residue")];
      // Euler reduction as a third route when gcd(a, m) = 1 and m factors
      const f = m <= 10n ** 12n ? factorSmall(m) : null;
      if (f && gcd(a, m) === 1n && b >= 0n) { const ph = f.reduce((s, [p, e]) => s * (p - 1n) * p ** BigInt(e - 1), 1n); cs.push(check("Euler reduction", powModRL(a, b % ph, m) === r, `reducing the exponent mod φ(${m}) = ${ph} gives the same residue`)); }
      return cs;
    },
  };
}
function cmdModInverse(args) {
  if (args.length !== 2) throw refuse("modinverse(a, m)");
  const [a, m] = args.map((x) => I(x));
  if (m < 2n) throw refuse("the modulus must be at least 2");
  const [g, x] = egcd(mod(a, m), m);
  if (g !== 1n) throw refuse(`${a} has no inverse modulo ${m}, because gcd(${a}, ${m}) = ${g} ≠ 1`);
  const inv = mod(x, m);
  return {
    answers: [ansNum("inverse", inv)],
    steps: [step("nt.inverse", "Extended Euclidean algorithm", `${a}·${inv} + ${m}·k = 1 for some integer k, so ${a}^(-1) ≡ ${inv} (mod ${m}).`)],
    checks: () => [check("multiply back", mod(a * inv, m) === 1n, `${a} · ${inv} = ${a * inv} ≡ 1 (mod ${m})`)],
  };
}
function multOrder(g, m) {
  const f = factorSmall(m); if (!f) return null;
  const ph = f.reduce((s, [p, e]) => s * (p - 1n) * p ** BigInt(e - 1), 1n);
  let k = ph;
  for (const [p] of factorSmall(ph)) while (k % p === 0n && powModRL(g, k / p, m) === 1n) k /= p;
  return k;
}
function cmdDlog(args) {
  if (args.length !== 3) throw refuse("dlog(g, h, m): solve g^x ≡ h (mod m)");
  const [g0, h0, m] = args.map((x) => I(x));
  if (m < 2n) throw refuse("the modulus must be at least 2");
  if (m > 10n ** 14n) throw refuse("the modulus is too large for baby-step giant-step here");
  const g = mod(g0, m), h = mod(h0, m);
  if (gcd(g, m) !== 1n) throw refuse(`${g0} is not a unit mod ${m}`);
  const ord = multOrder(g, m);
  if (ord === null) throw refuse("the modulus is too large to factor");
  const s = isqrt(ord) + 1n;
  if (s > 2000000n) throw refuse("the group is too large for baby-step giant-step here");
  // baby steps: g^j for j < s (keep the smallest j)
  const table = new Map();
  let e = 1n;
  for (let j = 0n; j < s; j++) { if (!table.has(e)) table.set(e, j); e = e * g % m; }
  const gInvS = powMod(modInv(g, m), s, m);
  let gamma = h, x = null;
  for (let i = 0n; i <= s; i++) { if (table.has(gamma)) { x = i * s + table.get(gamma); break; } gamma = gamma * gInvS % m; }
  if (x !== null) x = x % ord;
  const answers = [ansText("x", x === null ? "none" : String(x))];
  if (x !== null) answers.push(ansText("all solutions", `x ≡ ${x} (mod ${ord})`));
  return {
    answers,
    steps: [step("nt.bsgs", "Baby-step giant-step", `ord(${g}) = ${ord}; with s = ${s}, store g^j for j < s, then look for h·g^(-si) in the table.`),
      step("nt.bsgs.result", x === null ? "No match" : "Match found", x === null ? `${h} is not a power of ${g} mod ${m}.` : `${g}^${x} ≡ ${h} (mod ${m}); the solutions are x ≡ ${x} (mod ${ord}).`)],
    checks: () => {
      const ordOk = powModRL(g, ord, m) === 1n;
      if (x !== null) return [check("power", powModRL(g, x, m) === h, `${g}^${x} ≡ ${h} (mod ${m})`), check("smallest", ordOk && x < ord, `g has order ${ord}, so x is the unique solution in [0, ${ord})`)];
      if (m <= 10n ** 12n && isPrimeSmall(m)) return [check("not in subgroup", ordOk && powModRL(h, ord, m) !== 1n, `mod the prime ${m} the powers of g are exactly the solutions of y^${ord} = 1, and ${h}^${ord} ≢ 1`)];
      if (ord <= 2000000n) { let y = 1n, hit = false; for (let k = 0n; k < ord; k++) { if (y === h) { hit = true; break; } y = y * g % m; } return [check("subgroup listed", !hit, `listing all ${ord} powers of ${g} never reaches ${h}`)]; }
      return [check("certificate", false, "no certificate that the logarithm does not exist")];
    },
  };
}
function cmdDH(args) {
  if (args.length !== 4) throw refuse("diffiehellman(p, g, a, b)");
  const [p, g, a, b] = args.map((x) => I(x));
  prime(p, "p");
  if (a < 1n || b < 1n) throw refuse("the secret exponents must be positive");
  if (mod(g, p) === 0n) throw refuse("the generator must not be divisible by p");
  const A = powMod(g, a, p), B = powMod(g, b, p), s = powMod(B, a, p);
  return {
    answers: [ansNum("A", A), ansNum("B", B), ansNum("shared secret", s)],
    steps: [step("dh.public", "Public values A = g^a mod p and B = g^b mod p", `A = ${A}, B = ${B}.`), step("dh.shared", "Each side raises the other's value to its own secret", `B^a mod p = ${s}.`)],
    checks: () => [check("both sides agree", powModRL(A, b, p) === s, `A^b mod p = ${powModRL(A, b, p)} equals B^a mod p`), check("g^(ab)", powModRL(g, (a * b) % (p - 1n), p) === s, "g^(ab mod (p - 1)) mod p gives the same secret (Fermat)")],
  };
}

export const CRYPTO_HANDLERS = { rsakeys: cmdRSA, rsadecrypt: cmdRSADecrypt, rsacrt: cmdRSACRT, modpow: cmdModPow, modinverse: cmdModInverse, dlog: cmdDlog, diffiehellman: cmdDH };
