import { test, eq, ok, throws, rng } from "./harness.js";
import * as T from "../public/engine/numtheory.js";
import * as N from "../public/engine/num.js";
import { toText } from "../public/engine/print.js";

const big = (r, lo, hi) => BigInt(r.int(lo, hi));
const bigRand = (r, bits) => { let v = 0n; for (let i = 0; i < bits; i += 16) v = (v << 16n) | BigInt(r.int(0, 65535)); return v; };
const s = (a) => a.map(String).join(",");

// ---------------- unit tests
test("nt: gcd, lcm, extended Euclid", () => {
  eq(T.gcd(12, 18), 6n); eq(T.gcd(-12, 18), 6n); eq(T.gcd(0, 5), 5n); eq(T.gcd(12, 18, 27), 3n);
  eq(T.lcm(4, 6), 12n); eq(T.lcm(4, 6, 10), 60n); eq(T.lcm(0, 5), 0n);
  const e = T.egcd(240, 46);
  eq(e.g, 2n); eq(240n * e.x + 46n * e.y, 2n);
  ok(e.steps.some((x) => x.rule === "nt.euclid.bezout"));
});
test("nt: modular arithmetic", () => {
  eq(T.mod(-7, 5), 3n);
  eq(T.modInverse(3, 11), 4n);
  eq(T.modPow(2, 100, 1000000007), 976371285n);
  eq(T.modPow(3, -1, 7), 5n);
  eq(T.modDiv(1, 3, 7), 5n);
  throws(() => T.modInverse(6, 9));
});
test("nt: linear congruence with several solutions", () => {
  const r = T.solveLinearCongruence(6, 4, 10);
  ok(r.solvable);
  eq(s(r.solutions), "4,9");
  eq(r.modulus, 5n);
  eq(T.solveLinearCongruence(6, 5, 10).solvable, false);
});
test("nt: CRT coprime, non-coprime, inconsistent", () => {
  const a = T.crt([[2, 3], [3, 5], [2, 7]]);
  eq(a.residue, 23n); eq(a.modulus, 105n);
  const b = T.crt([[1, 4], [3, 6]]);
  eq(b.residue, 9n); eq(b.modulus, 12n);
  const c = T.crt([[1, 4], [2, 6]]);
  eq(c.consistent, false);
  ok(c.steps.some((x) => x.rule === "nt.crt.inconsistent"));
});
test("nt: Carmichael numbers are composite", () => {
  for (const n of [561, 1105, 1729, 2465, 2821, 6601, 8911, 10585, 15841, 29341, 41041, 46657, 52633, 62745, 63973, 75361, 101101, 115921, 126217, 162401, 172081, 188461, 252601, 278545, 294409, 314821, 334153, 340561, 399001, 410041, 449065, 488881, 512461])
    eq(T.isPrime(n), false, String(n));
  eq(T.isPrime(9746347772161n), false); // Carmichael with 4 prime factors
});
test("nt: strong pseudoprimes are caught", () => {
  for (const n of [2047n, 3277n, 4033n, 1373653n, 25326001n, 3215031751n, 2152302898747n, 3474749660383n, 341550071728321n, 3825123056546413051n, 318665857834031151167461n])
    eq(T.primality(n).status, "composite", String(n));
});
test("nt: known primes and honest labelling", () => {
  eq(T.primality(2n ** 61n - 1n).status, "prime");
  eq(T.primality(1000000007n).status, "prime");
  eq(T.primality(2n ** 127n - 1n).status, "probable prime");
  eq(T.primality((2n ** 61n - 1n) * (2n ** 31n - 1n)).status, "composite");
  eq(T.primality(1).status, "neither");
  eq(T.primality(2).status, "prime");
  eq(T.nextPrime(100), 101n);
});
test("nt: factorisation", () => {
  eq(s(T.factor(600851475143n).factors.map(([p]) => p)), "71,839,1471,6857");
  const f = T.factor(2n ** 64n + 1n);
  ok(f.complete);
  eq(s(f.factors.map(([p]) => p)), "274177,67280421310721");
  const g = T.factor(-360);
  eq(g.sign, -1n);
  const ft = T.factorTree(360);
  eq(ft.k, "mul");
  eq(ft.args.map(toText).join(" "), "2^3 3^2 5");
  const h = T.factor(1000000007n * 998244353n);
  eq(s(h.factors.map(([p]) => p)), "998244353,1000000007");
});
test("nt: partial factorisation is reported honestly", () => {
  const n = 3n * 1000000007n * 998244353n;
  const f = T.factor(n, { budget: 5 });
  eq(f.complete, false);
  eq(s(f.factors.map(([p]) => p)), "3");
  eq(f.unfactored[0], 1000000007n * 998244353n);
});
test("nt: arithmetic functions", () => {
  eq(T.phi(36), 12n); eq(T.phi(1), 1n); eq(T.phi(97), 96n);
  eq(s(T.divisors(28)), "1,2,4,7,14,28");
  eq(T.numDivisors(360), 24n);
  eq(T.sigma(28), 56n); eq(T.sigma(6, 2), 50n); eq(T.sigma(12, 0), 6n);
  eq(T.mobius(30), -1n); eq(T.mobius(12), 0n); eq(T.mobius(1), 1n); eq(T.mobius(6), 1n);
});
test("nt: linear Diophantine general solution", () => {
  const r = T.linearDiophantine(6, 15, 9);
  ok(r.solvable);
  for (const t of [-3n, 0n, 7n]) eq(6n * (r.x0 + r.stepX * t) + 15n * (r.y0 + r.stepY * t), 9n);
  eq(toText(r.x), "5t - 6");
  eq(T.linearDiophantine(6, 15, 10).solvable, false);
});
test("nt: Pythagorean triples", () => {
  ok(T.isPythagoreanTriple(3, 4, 5).primitive);
  ok(T.isPythagoreanTriple(6, 8, 10).triple && !T.isPythagoreanTriple(6, 8, 10).primitive);
  ok(!T.isPythagoreanTriple(2, 3, 4).triple);
});
test("nt: continued fractions", () => {
  eq(s(T.continuedFraction("415/93")), "4,2,6,7");
  eq(s(T.continuedFraction("-7/3")), "-3,1,2");
  const q = T.continuedFractionSqrt(23);
  eq(q.a0, 4n); eq(s(q.period), "1,3,1,8");
  eq(s(T.continuedFractionSqrt(2).period), "2");
  ok(T.continuedFractionSqrt(49).exact);
});
test("nt: sqrt(2) convergents solve Pell's equation", () => {
  const q = T.continuedFractionSqrt(2);
  const cf = [q.a0, ...Array(12).fill(2n)];
  for (const c of T.convergents(cf)) {
    const v = c.n * c.n - 2n * c.d * c.d;
    ok(v === 1n || v === -1n);
  }
});
test("nt: best rational approximation", () => {
  eq(N.toString(T.bestRational("3.14159265358979", 1000)), "355/113");
  eq(N.toString(T.bestRational("3.14159265358979", 100)), "311/99");
  eq(N.toString(T.bestRational("0.333", 10)), "1/3");
  eq(N.toString(T.bestRational(N.Q(1, 7), 100)), "1/7");
});
test("nt: Legendre, Jacobi, Tonelli-Shanks", () => {
  eq(T.legendre(2, 7), 1); eq(T.legendre(3, 7), -1); eq(T.legendre(14, 7), 0);
  eq(T.jacobi(1001, 9907), -1);
  eq(s(T.sqrtMod(10, 13)), "6,7");
  eq(s(T.sqrtMod(3, 7)), "");
  const r = T.sqrtMod(2, 1000000009n);
  ok(r.length === 0 || r.every((x) => (x * x) % 1000000009n === 2n));
  eq(s(T.quadraticResidues(7)), "0,1,2,4");
  throws(() => T.legendre(3, 9));
});
test("nt: primitive roots and orders", () => {
  eq(T.primitiveRoot(7), 3n); eq(T.primitiveRoot(23), 5n); eq(T.primitiveRoot(8), null); eq(T.primitiveRoot(18), 5n);
  eq(T.multiplicativeOrder(2, 7), 3n); eq(T.multiplicativeOrder(3, 7), 6n);
});
test("nt: base conversion", () => {
  eq(T.toBase(255, 16), "FF"); eq(T.toBase(-10, 2), "-1010"); eq(T.fromBase("ff", 16), 255n); eq(T.fromBase("zz", 36), 1295n);
  eq(T.rationalToBase("1/6", 10).text, "0.1(6)");
  eq(T.rationalToBase("1/7", 2).text, "0.(001)");
  eq(T.rationalToBase("3/8", 10).text, "0.375");
  eq(T.rationalToBase("-22/7", 10).text, "-3.(142857)");
  eq(T.rationalToBase("1/3", 3).text, "0.1");
  eq(T.rationalToBase("1/6", 10).latex, "0.1\\overline{6}");
  eq(N.toString(T.baseToRational("0.1(6)", 10)), "1/6");
  throws(() => T.toBase(5, 37));
  throws(() => T.fromBase("12", 2));
});

// ---------------- properties
test("property: gcd divides both and Bezout holds", () => {
  const r = rng(11);
  for (let i = 0; i < 300; i++) {
    const a = bigRand(r, 64) - bigRand(r, 64), b = bigRand(r, 48) - bigRand(r, 48);
    const e = T.egcd(a, b);
    eq(e.g, T.gcd(a, b));
    if (e.g) ok(a % e.g === 0n && b % e.g === 0n, "divides");
    eq(a * e.x + b * e.y, e.g, "Bezout");
    ok(e.g >= 0n);
  }
});
test("property: CRT solutions satisfy every congruence (and inconsistency is real)", () => {
  const r = rng(12);
  for (let i = 0; i < 300; i++) {
    const k = r.int(1, 4);
    const pairs = Array.from({ length: k }, () => [big(r, -50, 50), big(r, 1, 30)]);
    const res = T.crt(pairs);
    if (res.consistent) {
      for (const [a, m] of pairs) eq(T.mod(res.residue - a, m), 0n);
      eq(res.modulus, T.lcm(...pairs.map(([, m]) => m)));
    } else {
      const L = T.lcm(...pairs.map(([, m]) => m));
      for (let x = 0n; x < L; x++) ok(!pairs.every(([a, m]) => T.mod(x - a, m) === 0n), "no solution exists");
    }
  }
});
test("property: factorisation multiplies back into primes", () => {
  const r = rng(13);
  for (let i = 0; i < 60; i++) {
    const n = bigRand(r, 48) + 2n;
    const f = T.factor(n);
    ok(f.complete);
    let p = 1n;
    for (const [q, e] of f.factors) { ok(T.isPrime(q)); p *= q ** e; }
    eq(p, n);
  }
});
test("property: Miller-Rabin agrees with a sieve up to 10^5", () => {
  const LIM = 100000;
  const comp = new Uint8Array(LIM + 1);
  comp[0] = comp[1] = 1;
  for (let i = 2; i * i <= LIM; i++) if (!comp[i]) for (let j = i * i; j <= LIM; j += i) comp[j] = 1;
  for (let n = 0; n <= LIM; n++) if (T.isPrime(n) !== !comp[n]) throw new Error("disagree at " + n);
});
test("property: continued fraction convergents reconstruct the rational", () => {
  const r = rng(14);
  for (let i = 0; i < 300; i++) {
    const x = N.Q(bigRand(r, 40) - bigRand(r, 40), bigRand(r, 32) + 1n);
    const cf = T.continuedFraction(x);
    ok(N.eq(T.fromContinuedFraction(cf), x));
    for (let j = 1; j < cf.length; j++) ok(cf[j] >= 1n);
  }
});
test("property: best rational is optimal (brute force)", () => {
  const r = rng(15);
  for (let i = 0; i < 40; i++) {
    const x = N.Q(big(r, -100000, 100000), big(r, 1000, 100000));
    const M = r.int(1, 40);
    const b = T.bestRational(x, M);
    ok(b.d <= BigInt(M));
    const err = N.abs(N.sub(b, x));
    for (let q = 1n; q <= BigInt(M); q++) {
      const p = N.floor(N.mul(x, N.Q(q)));
      for (const c of [p, p + 1n]) ok(N.cmp(N.abs(N.sub(N.Q(c, q), x)), err) >= 0);
    }
  }
});
test("property: Jacobi symbol matches Euler's criterion for primes", () => {
  const r = rng(16);
  const primes = [3n, 5n, 7n, 11n, 13n, 101n, 1009n, 65537n, 1000003n];
  for (let i = 0; i < 300; i++) {
    const p = r.pick(primes), a = big(r, -100000, 100000);
    const e = T.modPow(a, (p - 1n) / 2n, p);
    const j = T.jacobi(a, p);
    eq(e === 0n ? 0 : e === 1n ? 1 : -1, j);
    if (j === 1) for (const x of T.sqrtMod(a, p)) eq((x * x) % p, T.mod(a, p));
  }
});
test("property: modular inverse and linear congruence solutions check", () => {
  const r = rng(17);
  for (let i = 0; i < 300; i++) {
    const m = big(r, 2, 500), a = big(r, -1000, 1000), b = big(r, -1000, 1000);
    const res = T.solveLinearCongruence(a, b, m);
    for (const x of res.solutions) eq(T.mod(a * x - b, m), 0n);
    let brute = 0n;
    for (let x = 0n; x < m; x++) if (T.mod(a * x - b, m) === 0n) brute++;
    eq(res.solvable ? res.count : 0n, brute);
  }
});
test("property: divisor-sum identities", () => {
  for (let n = 1n; n <= 300n; n++) {
    const ds = T.divisors(n);
    eq(ds.reduce((s, d) => s + T.phi(d), 0n), n, "sum phi(d) = n");
    eq(ds.reduce((s, d) => s + T.mobius(d), 0n), n === 1n ? 1n : 0n, "sum mu(d)");
    eq(BigInt(ds.length), T.numDivisors(n));
    eq(ds.reduce((s, d) => s + d, 0n), T.sigma(n));
  }
});
test("property: base conversion round trips (integers and repeating rationals)", () => {
  const r = rng(18);
  for (let i = 0; i < 300; i++) {
    const b = r.int(2, 36);
    const n = bigRand(r, 64) - bigRand(r, 64);
    eq(T.fromBase(T.toBase(n, b), b), n);
    const q = N.Q(big(r, -5000, 5000), big(r, 1, 500));
    ok(N.eq(T.baseToRational(T.rationalToBase(q, b).text, b), q));
  }
});
