// Quelvra number theory. Everything is exact BigInt / Rational arithmetic.
// Inputs may be BigInt, safe JS integers, integer strings, or integer num nodes.
// Primality: deterministic Miller-Rabin below 3.317e24 (bases = first 13 primes),
// Baillie-PSW beyond (reported honestly as "probable prime").
// Every loop is bounded; exhausted budgets throw { code: "BUDGET" } or are reported as partial results.

import * as N from "./num.js";
import * as X from "./expr.js";

const fail = (msg, code) => Object.assign(new Error("Quelvra: " + msg), { code });
const budget = (msg) => fail(msg, "BUDGET");
const step = (rule, title, why, before = null, after = null, extra = {}) =>
  ({ rule, title, why, before, after, conditions: extra.conditions || [], sub: extra.sub || [], kind: extra.kind || "equivalent" });

export function toBig(x) {
  if (typeof x === "bigint") return x;
  if (typeof x === "number") {
    if (!Number.isSafeInteger(x)) throw fail("expected an integer, got " + x, "DOMAIN");
    return BigInt(x);
  }
  if (typeof x === "string" && /^\s*[+-]?\d+\s*$/.test(x)) return BigInt(x.trim());
  if (x && typeof x === "object") {
    if (x.k === "num" && x.v.d === 1n) return x.v.n;
    if (typeof x.n === "bigint" && x.d === 1n) return x.n;
  }
  throw fail("expected an integer, got " + String(x), "DOMAIN");
}
const toRat = (x) => {
  if (x && typeof x === "object" && typeof x.n === "bigint") return x;
  if (x && typeof x === "object" && x.k === "num") return x.v;
  if (typeof x === "string" && x.includes("/")) { const [a, b] = x.split("/"); return N.Q(toBig(a), toBig(b)); }
  if (typeof x === "string" || (typeof x === "number" && !Number.isInteger(x))) return N.fromDecimal(String(x));
  return N.Q(toBig(x));
};
const abs = (a) => (a < 0n ? -a : a);

// ------------------------------------------------------------------ gcd / lcm / Bezout
export function gcd(...xs) { let g = 0n; for (const x of xs) g = N.bgcd(g, toBig(x)); return g; }
export function lcm(...xs) {
  let l = 1n;
  for (const x of xs) { const v = abs(toBig(x)); if (v === 0n) return 0n; l = (l / N.bgcd(l, v)) * v; }
  return l;
}
// Extended Euclid: g = gcd(a, b) >= 0 and a*x + b*y = g.
export function egcd(a, b) {
  a = toBig(a); b = toBig(b);
  const steps = [];
  let [r0, r1, s0, s1, t0, t1] = [a, b, 1n, 0n, 0n, 1n];
  while (r1 !== 0n) {
    const q = r0 / r1 - (r0 % r1 !== 0n && (r0 < 0n) !== (r1 < 0n) ? 1n : 0n); // floor division
    const r = r0 - q * r1;
    steps.push(step("nt.euclid.divide", `${r0} = ${q}*${r1} + ${r}`, "Division with remainder; gcd(a, b) = gcd(b, r)."));
    [r0, r1] = [r1, r];
    [s0, s1] = [s1, s0 - q * s1];
    [t0, t1] = [t1, t0 - q * t1];
  }
  if (r0 < 0n) { r0 = -r0; s0 = -s0; t0 = -t0; }
  steps.push(step("nt.euclid.bezout", `${a}*(${s0}) + ${b}*(${t0}) = ${r0}`, "Back-substitution gives the Bezout coefficients."));
  return { g: r0, x: s0, y: t0, steps };
}

// ------------------------------------------------------------------ modular arithmetic
export function mod(a, m) {
  a = toBig(a); m = toBig(m);
  if (m === 0n) throw fail("modulus must be nonzero", "DOMAIN");
  m = abs(m);
  const r = a % m;
  return r < 0n ? r + m : r;
}
export const modAdd = (a, b, m) => mod(toBig(a) + toBig(b), m);
export const modSub = (a, b, m) => mod(toBig(a) - toBig(b), m);
export const modMul = (a, b, m) => mod(toBig(a) * toBig(b), m);
export function modInverse(a, m) {
  a = toBig(a); m = abs(toBig(m));
  const { g, x } = egcd(mod(a, m), m);
  if (g !== 1n) throw fail(`${a} has no inverse modulo ${m} (gcd = ${g})`, "DOMAIN");
  return mod(x, m);
}
export const modDiv = (a, b, m) => mod(toBig(a) * modInverse(b, m), m);
export function modPow(b, e, m) {
  b = toBig(b); e = toBig(e); m = abs(toBig(m));
  if (m === 1n) return 0n;
  if (e < 0n) { b = modInverse(b, m); e = -e; }
  let r = 1n;
  b = mod(b, m);
  while (e > 0n) {
    if (e & 1n) r = (r * b) % m;
    b = (b * b) % m;
    e >>= 1n;
  }
  return r;
}

// a x = b (mod m): all solutions modulo m.
export function solveLinearCongruence(a, b, m, opts = {}) {
  a = toBig(a); b = toBig(b); m = abs(toBig(m));
  if (m === 0n) throw fail("modulus must be nonzero", "DOMAIN");
  const g = N.bgcd(a, m);
  const steps = [step("nt.congruence.gcd", `gcd(${a}, ${m}) = ${g}`, "a x = b (mod m) is solvable exactly when gcd(a, m) divides b.")];
  if (mod(b, g) !== 0n) {
    steps.push(step("nt.congruence.none", "No solution", `${g} does not divide ${b}.`));
    return { solvable: false, solutions: [], count: 0n, steps };
  }
  const m2 = m / g;
  const x0 = m2 === 1n ? 0n : mod((b / g) * modInverse(a / g, m2), m2);
  steps.push(step("nt.congruence.reduce", `Divide by ${g}: ${a / g} x = ${b / g} (mod ${m2})`, `Multiply by the inverse of ${a / g} modulo ${m2}: x = ${x0} (mod ${m2}).`));
  const cap = BigInt(opts.maxList || 1000);
  const solutions = [];
  for (let k = 0n; k < g && k < cap; k++) solutions.push(x0 + k * m2);
  steps.push(step("nt.congruence.all", `${g} solution${g === 1n ? "" : "s"} modulo ${m}`, `x = ${x0} + ${m2} k for k = 0..${g - 1n}.`));
  return { solvable: true, residue: x0, modulus: m2, solutions, count: g, truncated: g > cap, steps };
}

// Chinese remainder theorem for x = a_i (mod m_i), moduli need not be coprime.
export function crt(pairs) {
  let a = 0n, m = 1n;
  const steps = [];
  for (const pr of pairs) {
    const [ai, mi0] = Array.isArray(pr) ? pr : [pr.a ?? pr.residue, pr.m ?? pr.modulus];
    const mi = abs(toBig(mi0));
    if (mi === 0n) throw fail("modulus must be nonzero", "DOMAIN");
    const bi = mod(toBig(ai), mi);
    const g = N.bgcd(m, mi);
    if (mod(bi - a, g) !== 0n) {
      steps.push(step("nt.crt.inconsistent", "Inconsistent congruences", `x = ${a} (mod ${m}) and x = ${bi} (mod ${mi}) disagree modulo gcd = ${g}.`));
      return { consistent: false, residue: null, modulus: null, steps };
    }
    const l = (m / g) * mi;
    const t = mi / g === 1n ? 0n : mod(((bi - a) / g) * modInverse(m / g, mi / g), mi / g);
    const na = mod(a + m * t, l);
    steps.push(step("nt.crt.combine", `Combine with x = ${bi} (mod ${mi})`, `Write x = ${a} + ${m} t; then ${m} t = ${bi - a} (mod ${mi}) gives t = ${t} (mod ${mi / g}), so x = ${na} (mod ${l}).`));
    a = na; m = l;
  }
  return { consistent: true, residue: a, modulus: m, steps };
}

// ------------------------------------------------------------------ primality
const MR_BASES = [2n, 3n, 5n, 7n, 11n, 13n, 17n, 19n, 23n, 29n, 31n, 37n, 41n];
export const MR_DETERMINISTIC_LIMIT = 3317044064679887385961981n;
const MR_TIERS = [
  [2047n, 1], [1373653n, 2], [25326001n, 3], [3215031751n, 4], [2152302898747n, 5], [3474749660383n, 6],
  [341550071728321n, 7], [3825123056546413051n, 9], [318665857834031151167461n, 12], [MR_DETERMINISTIC_LIMIT, 13],
];
function strongProbablePrime(n, a) {
  let d = n - 1n, s = 0n;
  while ((d & 1n) === 0n) { d >>= 1n; s++; }
  let x = modPow(a, d, n);
  if (x === 1n || x === n - 1n) return true;
  for (let r = 1n; r < s; r++) {
    x = (x * x) % n;
    if (x === n - 1n) return true;
    if (x === 1n) return false;
  }
  return false;
}
function isSquare(n) { if (n < 0n) return false; return N.iroot(n, 2)[1]; }
function strongLucas(n) {
  // Selfridge method A
  let D = 5n;
  for (let i = 0; ; i++) {
    if (i === 20 && isSquare(n)) return false;
    if (i > 100000) throw budget("Lucas parameter search");
    const j = jacobi(D, n);
    if (j === -1) break;
    if (j === 0 && abs(D) !== n) return false;
    D = D > 0n ? -(D + 2n) : -D + 2n;
  }
  const P = 1n, Q = (1n - D) / 4n;
  let d = n + 1n, s = 0n;
  while ((d & 1n) === 0n) { d >>= 1n; s++; }
  const half = (v) => { v = mod(v, n); return (v & 1n ? v + n : v) >> 1n; };
  let U = 1n, V = P, Qk = mod(Q, n);
  const bits = d.toString(2);
  for (let i = 1; i < bits.length; i++) {
    U = mod(U * V, n);
    V = mod(V * V - 2n * Qk, n);
    Qk = mod(Qk * Qk, n);
    if (bits[i] === "1") {
      const U2 = half(P * U + V), V2 = half(D * U + P * V);
      U = U2; V = V2;
      Qk = mod(Qk * Q, n);
    }
  }
  if (U === 0n || V === 0n) return true;
  for (let r = 1n; r < s; r++) {
    V = mod(V * V - 2n * Qk, n);
    Qk = mod(Qk * Qk, n);
    if (V === 0n) return true;
  }
  return false;
}
const SMALL = [2n, 3n, 5n, 7n, 11n, 13n, 17n, 19n, 23n, 29n, 31n, 37n, 41n, 43n, 47n];
// Detailed primality: { isPrime, status: "prime" | "composite" | "probable prime" | "neither", method }
export function primality(n) {
  n = toBig(n);
  if (n < 2n) return { n, isPrime: false, status: "neither", method: "definition (primes are integers >= 2)" };
  for (const p of SMALL) {
    if (n === p) return { n, isPrime: true, status: "prime", method: "small prime" };
    if (n % p === 0n) return { n, isPrime: false, status: "composite", method: `divisible by ${p}`, factor: p };
  }
  if (n < 2209n) return { n, isPrime: true, status: "prime", method: "trial division up to sqrt(n)" };
  if (n < MR_DETERMINISTIC_LIMIT) {
    // smallest proven witness set for the size of n (Jaeschke; Sorenson-Webster)
    const k = MR_TIERS.find(([lim]) => n < lim)[1];
    for (const a of MR_BASES.slice(0, k)) if (!strongProbablePrime(n, a)) return { n, isPrime: false, status: "composite", method: `Miller-Rabin witness ${a}`, witness: a };
    return { n, isPrime: true, status: "prime", method: "deterministic Miller-Rabin (bases 2..41, valid below 3.317e24)" };
  }
  if (!strongProbablePrime(n, 2n)) return { n, isPrime: false, status: "composite", method: "Miller-Rabin witness 2", witness: 2n };
  if (!strongLucas(n)) return { n, isPrime: false, status: "composite", method: "strong Lucas test (BPSW)" };
  return { n, isPrime: true, status: "probable prime", method: "Baillie-PSW (no known counterexample; not a proof)" };
}
export const isPrime = (n) => primality(n).isPrime;
export function nextPrime(n) {
  n = toBig(n);
  let c = n < 2n ? 2n : n + 1n;
  for (let i = 0; i < 1000000; i++, c++) if (isPrime(c)) return c;
  throw budget("nextPrime search");
}

// ------------------------------------------------------------------ factorisation
function brent(n, c, budgetRef) {
  const f = (v) => (v * v + c) % n;
  let y = 2n, r = 1n, q = 1n, g = 1n, x = 0n, ys = 0n;
  const m = 64n;
  do {
    x = y;
    for (let i = 0n; i < r; i++) y = f(y);
    let k = 0n;
    while (k < r && g === 1n) {
      ys = y;
      const lim = m < r - k ? m : r - k;
      for (let i = 0n; i < lim; i++) { y = f(y); q = (q * abs(x - y)) % n; }
      budgetRef.left -= Number(lim);
      if (budgetRef.left < 0) return null;
      g = N.bgcd(q, n);
      k += m;
    }
    r *= 2n;
  } while (g === 1n);
  if (g === n) {
    for (let i = 0; i < 100000; i++) {
      ys = f(ys);
      g = N.bgcd(abs(x - ys), n);
      if (g > 1n) break;
    }
  }
  return g;
}
// factor(n, {budget}) -> { sign, factors: [[p, e]], complete, unfactored: [composite cofactors], probable: [p] }
export function factor(n, opts = {}) {
  n = toBig(n);
  if (n === 0n) throw fail("0 has no prime factorisation", "DOMAIN");
  const sign = n < 0n ? -1n : 1n;
  n = abs(n);
  const map = new Map();
  const addF = (p, e = 1n) => map.set(p, (map.get(p) || 0n) + e);
  const steps = [];
  const { factors, rest } = N.trialFactor(n);
  for (const [p, e] of factors) addF(p, e);
  if (factors.size) steps.push(step("nt.factor.trial", "Trial division by small primes", `Primes up to 10000 were divided out: ${[...factors].map(([p, e]) => (e > 1n ? `${p}^${e}` : `${p}`)).join(" * ")}.`));
  const budgetRef = { left: opts.budget ?? 3000000 };
  const unfactored = [], probable = [];
  const stack = rest > 1n ? [rest] : [];
  let guard = 0;
  while (stack.length) {
    if (++guard > 10000) throw budget("factor stack");
    const m = stack.pop();
    if (m === 1n) continue;
    const pr = primality(m);
    if (pr.isPrime) { addF(m); if (pr.status === "probable prime") probable.push(m); continue; }
    const [r, ex] = N.iroot(m, 2);
    if (ex) { stack.push(r, r); continue; }
    let d = null;
    for (let c = 1n; c < 40n && !d; c++) {
      const g = brent(m, c, budgetRef);
      if (g === null) break;
      if (g !== m && g !== 1n) d = g;
    }
    if (!d) { unfactored.push(m); continue; }
    steps.push(step("nt.factor.rho", `Pollard rho (Brent) splits ${m}`, `${m} = ${d} * ${m / d}.`));
    stack.push(d, m / d);
  }
  const list = [...map].sort((a, b) => (a[0] < b[0] ? -1 : 1));
  return { n: sign * n, sign, factors: list, complete: unfactored.length === 0, unfactored, probable, steps };
}
// Factorisation as a tree: 2^3 * 3 * 5 (raw product so it is not multiplied back).
export function factorTree(n) {
  const f = factor(n);
  const parts = f.factors.map(([p, e]) => (e === 1n ? X.num(p) : X.pow(X.num(p), X.num(e))));
  for (const u of f.unfactored) parts.push(X.num(u));
  if (f.sign < 0n) parts.unshift(X.NEG_ONE);
  return parts.length === 0 ? X.ONE : parts.length === 1 ? parts[0] : X.mul(...parts);
}
function fullFactor(n) {
  const f = factor(n);
  if (!f.complete) throw budget(`could not fully factor ${n} within the budget`);
  return f.factors;
}
export function phi(n) {
  n = toBig(n);
  if (n < 1n) throw fail("phi is defined for positive integers", "DOMAIN");
  let r = n;
  for (const [p] of fullFactor(n)) r = (r / p) * (p - 1n);
  return r;
}
export function divisors(n) {
  n = abs(toBig(n));
  if (n === 0n) throw fail("0 has infinitely many divisors", "DOMAIN");
  let ds = [1n];
  for (const [p, e] of fullFactor(n)) {
    const next = [];
    for (const d of ds) { let q = 1n; for (let i = 0n; i <= e; i++) { next.push(d * q); q *= p; } }
    ds = next;
    if (ds.length > 2000000) throw budget("too many divisors");
  }
  return ds.sort((a, b) => (a < b ? -1 : a > b ? 1 : 0));
}
export function numDivisors(n) {
  n = abs(toBig(n));
  let r = 1n;
  for (const [, e] of fullFactor(n)) r *= e + 1n;
  return r;
}
export function sigma(n, k = 1) {
  n = abs(toBig(n)); k = toBig(k);
  if (k < 0n) throw fail("sigma_k needs k >= 0", "DOMAIN");
  let r = 1n;
  for (const [p, e] of fullFactor(n)) {
    if (k === 0n) { r *= e + 1n; continue; }
    const pk = p ** k;
    r *= (pk ** (e + 1n) - 1n) / (pk - 1n);
  }
  return r;
}
export function mobius(n) {
  n = toBig(n);
  if (n < 1n) throw fail("mobius is defined for positive integers", "DOMAIN");
  const f = fullFactor(n);
  if (f.some(([, e]) => e > 1n)) return 0n;
  return f.length % 2 ? -1n : 1n;
}

// ------------------------------------------------------------------ Diophantine
// a x + b y = c: general integer solution x = x0 + (b/g) t, y = y0 - (a/g) t.
export function linearDiophantine(a, b, c, param = "t") {
  a = toBig(a); b = toBig(b); c = toBig(c);
  const t = X.sym(param);
  const steps = [];
  if (a === 0n && b === 0n) {
    return { solvable: c === 0n, x: c === 0n ? X.sym("x") : null, y: c === 0n ? X.sym("y") : null, steps: [step("nt.diophantine.trivial", "0 = c", c === 0n ? "Every pair (x, y) works." : "No pair works.")] };
  }
  const e = egcd(a, b);
  steps.push(...e.steps);
  if (c % e.g !== 0n) {
    steps.push(step("nt.diophantine.none", "No integer solution", `gcd(${a}, ${b}) = ${e.g} does not divide ${c}.`));
    return { solvable: false, steps };
  }
  const k = c / e.g, x0 = e.x * k, y0 = e.y * k;
  const bx = b / e.g, ay = a / e.g;
  const x = X.add(X.num(x0), X.mul(X.num(bx), t)), y = X.add(X.num(y0), X.mul(X.num(-ay), t));
  steps.push(step("nt.diophantine.particular", `Particular solution (${x0}, ${y0})`, `Scale the Bezout identity by c/g = ${k}.`));
  steps.push(step("nt.diophantine.general", "General solution", `x = ${x0} + ${bx} t, y = ${y0} - ${ay} t for any integer t.`));
  return { solvable: true, x0, y0, stepX: bx, stepY: -ay, param: t, x, y, steps };
}
export function isPythagoreanTriple(a, b, c) {
  const v = [toBig(a), toBig(b), toBig(c)].map(abs).sort((p, q) => (p < q ? -1 : 1));
  const ok = v[0] > 0n && v[0] * v[0] + v[1] * v[1] === v[2] * v[2];
  return { triple: ok, primitive: ok && gcd(v[0], v[1], v[2]) === 1n, sorted: v };
}

// ------------------------------------------------------------------ continued fractions
export function continuedFraction(x) {
  const r = toRat(x);
  let n = r.n, d = r.d;
  const out = [];
  for (let i = 0; d !== 0n; i++) {
    if (i > 100000) throw budget("continued fraction");
    const q = N.floor(N.Q(n, d));
    out.push(q);
    [n, d] = [d, n - q * d];
  }
  return out;
}
// sqrt(n) = [a0; (a1, ..., ak)] with the period repeating.
export function continuedFractionSqrt(n) {
  n = toBig(n);
  if (n < 0n) throw fail("sqrt of a negative number has no real continued fraction", "DOMAIN");
  const [a0, exact] = N.iroot(n, 2);
  if (exact) return { a0, period: [], exact: true };
  let m = 0n, d = 1n, a = a0;
  const period = [];
  for (let i = 0; ; i++) {
    if (i > 2000000) throw budget("sqrt continued fraction period");
    m = d * a - m;
    d = (n - m * m) / d;
    a = (a0 + m) / d;
    period.push(a);
    if (a === 2n * a0) break;
  }
  return { a0, period, exact: false };
}
export function convergents(cf) {
  const out = [];
  let [h0, h1, k0, k1] = [0n, 1n, 1n, 0n];
  for (const a0 of cf) {
    const a = toBig(a0);
    [h0, h1] = [h1, a * h1 + h0];
    [k0, k1] = [k1, a * k1 + k0];
    out.push(N.Q(h1, k1));
  }
  return out;
}
export const fromContinuedFraction = (cf) => { const c = convergents(cf); return c[c.length - 1]; };
// Closest rational with denominator <= maxDen (ties go to the smaller denominator).
export function bestRational(x, maxDen) {
  const r = toRat(x);
  maxDen = toBig(maxDen);
  if (maxDen < 1n) throw fail("maxDen must be >= 1", "DOMAIN");
  if (r.d <= maxDen) return r;
  let [p0, q0, p1, q1] = [0n, 1n, 1n, 0n];
  let n = r.n, d = r.d;
  for (let i = 0; i < 100000; i++) {
    const a = N.floor(N.Q(n, d));
    const q2 = q0 + a * q1;
    if (q2 > maxDen) break;
    [p0, q0, p1, q1] = [p1, q1, p0 + a * p1, q2];
    [n, d] = [d, n - a * d];
    if (d === 0n) break;
  }
  const k = (maxDen - q0) / q1;
  const b1 = N.Q(p0 + k * p1, q0 + k * q1), b2 = N.Q(p1, q1);
  return N.cmp(N.abs(N.sub(b2, r)), N.abs(N.sub(b1, r))) <= 0 ? b2 : b1;
}

// ------------------------------------------------------------------ residues
export function jacobi(a, n) {
  a = toBig(a); n = toBig(n);
  if (n <= 0n || (n & 1n) === 0n) throw fail("the Jacobi symbol needs an odd positive modulus", "DOMAIN");
  a = mod(a, n);
  let t = 1n;
  while (a !== 0n) {
    while ((a & 1n) === 0n) {
      a >>= 1n;
      const r = n % 8n;
      if (r === 3n || r === 5n) t = -t;
    }
    [a, n] = [n, a];
    if (a % 4n === 3n && n % 4n === 3n) t = -t;
    a %= n;
  }
  return n === 1n ? Number(t) : 0;
}
export function legendre(a, p) {
  p = toBig(p);
  if (p === 2n || !isPrime(p)) throw fail("the Legendre symbol needs an odd prime", "DOMAIN");
  return jacobi(a, p);
}
export function isQuadraticResidue(a, p) {
  p = toBig(p);
  if (p === 2n) return true;
  return legendre(a, p) >= 0;
}
export function quadraticResidues(m) {
  m = toBig(m);
  if (m > 100000n) throw budget("listing residues for a large modulus");
  const s = new Set();
  for (let x = 0n; x < m; x++) s.add((x * x) % m);
  return [...s].sort((a, b) => (a < b ? -1 : 1));
}
// Tonelli-Shanks: square roots of a modulo an odd prime p (sorted), [] if none.
export function sqrtMod(a, p) {
  a = toBig(a); p = toBig(p);
  if (!isPrime(p)) throw fail("sqrtMod needs a prime modulus", "DOMAIN");
  a = mod(a, p);
  if (a === 0n) return [0n];
  if (p === 2n) return [a];
  if (jacobi(a, p) !== 1) return [];
  let q = p - 1n, s = 0n;
  while ((q & 1n) === 0n) { q >>= 1n; s++; }
  let z = 2n;
  while (jacobi(z, p) !== -1) { z++; if (z > 100000n) throw budget("non-residue search"); }
  let m = s, c = modPow(z, q, p), t = modPow(a, q, p), r = modPow(a, (q + 1n) / 2n, p);
  for (let guard = 0; t !== 1n; guard++) {
    if (guard > 10000) throw budget("Tonelli-Shanks");
    let i = 0n, tt = t;
    while (tt !== 1n) { tt = (tt * tt) % p; i++; }
    const b = modPow(c, 1n << (m - i - 1n), p);
    m = i; c = (b * b) % p; t = (t * c) % p; r = (r * b) % p;
  }
  const r2 = p - r;
  return r === r2 ? [r] : [r < r2 ? r : r2, r < r2 ? r2 : r];
}
export function multiplicativeOrder(a, n) {
  a = toBig(a); n = abs(toBig(n));
  if (N.bgcd(a, n) !== 1n) throw fail(`${a} is not a unit modulo ${n}`, "DOMAIN");
  let ord = phi(n);
  for (const [p, e] of fullFactor(ord)) {
    for (let i = 0n; i < e; i++) {
      if (modPow(a, ord / p, n) === 1n) ord /= p; else break;
    }
  }
  return ord;
}
// Smallest primitive root modulo n, or null when none exists.
export function primitiveRoot(n) {
  n = toBig(n);
  if (n < 2n) throw fail("primitive roots need n >= 2", "DOMAIN");
  if (n === 2n) return 1n;
  if (n === 4n) return 3n;
  let m = n % 2n === 0n ? n / 2n : n;
  if (m % 2n === 0n) return null;
  const f = fullFactor(m);
  if (f.length !== 1) return null;
  const ph = phi(n);
  const qs = fullFactor(ph).map(([p]) => p);
  for (let g = 2n; g < n; g++) {
    if (g > 1000000n) throw budget("primitive root search");
    if (N.bgcd(g, n) !== 1n) continue;
    if (qs.every((q) => modPow(g, ph / q, n) !== 1n)) return g;
  }
  return null;
}

// ------------------------------------------------------------------ base conversion
const DIGITS = "0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZ";
const checkBase = (b) => { b = toBig(b); if (b < 2n || b > 36n) throw fail("base must be between 2 and 36", "DOMAIN"); return b; };
export function toBase(n, b) {
  n = toBig(n); b = checkBase(b);
  if (n === 0n) return "0";
  const neg = n < 0n;
  n = abs(n);
  let s = "";
  while (n > 0n) { s = DIGITS[Number(n % b)] + s; n /= b; }
  return (neg ? "-" : "") + s;
}
function digitVal(ch, b) {
  const v = DIGITS.indexOf(ch.toUpperCase());
  if (v < 0 || BigInt(v) >= b) throw fail(`digit "${ch}" is not valid in base ${b}`, "INPUT");
  return BigInt(v);
}
export function fromBase(s, b) {
  b = checkBase(b);
  s = String(s).trim();
  const neg = s.startsWith("-");
  if (neg || s.startsWith("+")) s = s.slice(1);
  if (!s) throw fail("empty number", "INPUT");
  let n = 0n;
  for (const ch of s) n = n * b + digitVal(ch, b);
  return neg ? -n : n;
}
// Expansion of a rational in base b with the repeating block found exactly:
// 1/6 in base 10 -> { integer: "0", prefix: "1", repetend: "6", text: "0.1(6)" }
export function rationalToBase(x, b, opts = {}) {
  const r = toRat(x);
  b = checkBase(b);
  const neg = r.n < 0n;
  const a = N.abs(r);
  const ip = a.n / a.d;
  let rem = a.n % a.d;
  const seen = new Map();
  let digits = "";
  const cap = opts.maxDigits || 100000;
  while (rem !== 0n && !seen.has(rem)) {
    if (digits.length >= cap) throw budget("repeating block longer than " + cap + " digits");
    seen.set(rem, digits.length);
    rem *= b;
    digits += DIGITS[Number(rem / a.d)];
    rem %= a.d;
  }
  const start = rem === 0n ? digits.length : seen.get(rem);
  const prefix = digits.slice(0, start), repetend = digits.slice(start);
  const sign = neg ? "-" : "";
  const ints = toBase(ip, b);
  const text = sign + ints + (prefix || repetend ? "." + prefix + (repetend ? `(${repetend})` : "") : "");
  const latex = sign + ints + (prefix || repetend ? "." + prefix + (repetend ? `\\overline{${repetend}}` : "") : "");
  return { sign: neg ? -1 : 1, integer: ints, prefix, repetend, terminating: !repetend, text, latex };
}
// Parse "12.3(45)" in base b back to an exact Rational.
export function baseToRational(s, b) {
  b = checkBase(b);
  s = String(s).trim();
  const m = s.match(/^([+-]?)([0-9A-Za-z]*)(?:\.([0-9A-Za-z]*)(?:\(([0-9A-Za-z]+)\))?)?$/);
  if (!m) throw fail("cannot read " + s, "INPUT");
  const [, sg, ip, pre = "", rep = ""] = m;
  let v = N.Q(ip ? fromBase(ip, b) : 0n);
  if (pre) v = N.add(v, N.Q(fromBase(pre, b), b ** BigInt(pre.length)));
  if (rep) v = N.add(v, N.Q(fromBase(rep, b), b ** BigInt(pre.length) * (b ** BigInt(rep.length) - 1n)));
  return sg === "-" ? N.neg(v) : v;
}
