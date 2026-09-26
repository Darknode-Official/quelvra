// Quelvra exact values of discrete-math, number-theory and probability functions (solver side).
//
// simplify() calls evalDiscrete(name, args, T) for these names; T carries simplify's constructors
// (num, simpMul, simpAdd, simpPow, simpFn and constants) so this module does not import simplify.
// A function returns an exact tree, UNDEF when the value does not exist, or null to stay unevaluated
// (symbolic or out-of-range arguments). The verifier (verify.js) has its own independent
// floating-point implementation of every name here, so evaluate-then-check stays independent.
//
//   catalan(n)  fibonacci(n) / fib(n)  lucas(n)  subfactorial(n) / derangements(n)
//   multinomial(k1, ..., km)  stirling(n, k) (second kind)  bell(n)  nthprime(n)
//   divisorsum(n)  numdivisors(n)  modinv(a, m)  powmod(a, b, m)
//   binompdf(n, p, k)  binomcdf(n, p, k)  geompdf(p, k)  geomcdf(p, k)  (trials: k >= 1)
//   poissonpdf(lambda, k)  poissoncdf(lambda, k)  hypergeompdf(N, K, n, k)
//   normalpdf(x[, mu, sigma])  normalcdf(a, b[, mu, sigma])  (as erf expressions)  zscore(x, mu, sigma)

import * as N from "./num.js";
import * as NT from "./numtheory.js";

export const DISCRETE_NAMES = ["catalan", "fibonacci", "fib", "lucas", "subfactorial", "derangements", "multinomial", "stirling", "bell",
  "nthprime", "divisorsum", "numdivisors", "modinv", "powmod", "binompdf", "binomcdf", "geompdf", "geomcdf",
  "poissonpdf", "poissoncdf", "hypergeompdf", "normalpdf", "normalcdf", "zscore", "round"];

const isInt = (t) => t && t.k === "num" && t.v.d === 1n;
const isRat = (t) => t && t.k === "num";
const big = (t) => t.v.n;
const nonneg = (t, max) => isInt(t) && big(t) >= 0n && (max === undefined || big(t) <= BigInt(max));

function fibPair(n) { // [F(n), F(n+1)] by fast doubling
  if (n === 0n) return [0n, 1n];
  const [a, b] = fibPair(n >> 1n);
  const c = a * (2n * b - a), d = a * a + b * b;
  return n & 1n ? [d, c + d] : [c, d];
}
function sieveNth(n) {
  // nth prime: bound p_n < n (ln n + ln ln n) for n >= 6
  const nn = Number(n);
  const lim = nn < 6 ? 15 : Math.ceil(nn * (Math.log(nn) + Math.log(Math.log(nn)))) + 10;
  const comp = new Uint8Array(lim + 1);
  let count = 0;
  for (let i = 2; i <= lim; i++) {
    if (comp[i]) continue;
    if (++count === nn) return BigInt(i);
    for (let j = i * i; j <= lim; j += i) comp[j] = 1;
  }
  return null;
}
const probOK = (p) => isRat(p) && !N.isNeg(p.v) && N.cmp(p.v, N.ONE) <= 0;
const binomPmf = (n, p, k) => (k < 0n || k > n ? N.ZERO : N.mul(N.Q(N.binom(n, k)), N.mul(N.pow(p, k), N.pow(N.sub(N.ONE, p), n - k))));

export function evalDiscrete(name, args, T) {
  const [a, b, c, d] = args;
  const num = (r) => (typeof r === "bigint" ? T.num(r) : T.numQ(r));
  switch (name) {
    case "catalan": return nonneg(a, 20000) ? num(N.binom(2n * big(a), big(a)) / (big(a) + 1n)) : null;
    case "fib": case "fibonacci": {
      if (!isInt(a) || big(a) > 200000n || big(a) < -200000n) return null;
      const n = big(a);
      const f = fibPair(n < 0n ? -n : n)[0];
      return num(n < 0n && (-n) % 2n === 0n ? -f : f); // F(-n) = (-1)^(n+1) F(n)
    }
    case "lucas": {
      if (!nonneg(a, 200000)) return null;
      const [f, g] = fibPair(big(a));
      return num(2n * g - f); // L(n) = F(n-1) + F(n+1) = 2F(n+1) - F(n)
    }
    case "subfactorial": case "derangements": {
      if (!nonneg(a, 5000)) return null;
      let d0 = 1n, d1 = 0n;
      const n = big(a);
      if (n === 0n) return num(1n);
      for (let i = 2n; i <= n; i++) [d0, d1] = [d1, (i - 1n) * (d0 + d1)];
      return num(d1);
    }
    case "multinomial": {
      if (!args.length || !args.every((t) => nonneg(t, 20000))) return null;
      let s = 0n, den = 1n;
      for (const t of args) { s += big(t); den *= N.factorial(big(t)); }
      if (s > 20000n) return null;
      return num(N.factorial(s) / den);
    }
    case "stirling": {
      if (!nonneg(a, 1000) || !nonneg(b, 1000)) return null;
      const n = Number(big(a)), k = Number(big(b));
      if (k > n) return num(0n);
      let row = [1n];
      for (let i = 1; i <= n; i++) {
        const nxt = new Array(i + 1).fill(0n);
        for (let j = 1; j <= i; j++) nxt[j] = (row[j - 1] || 0n) + BigInt(j) * (row[j] || 0n);
        row = nxt;
      }
      return num(row[k] || 0n);
    }
    case "bell": {
      if (!nonneg(a, 1000)) return null;
      let row = [1n];
      for (let i = 0; i < Number(big(a)); i++) {
        const nxt = [row[row.length - 1]];
        for (const v of row) nxt.push(nxt[nxt.length - 1] + v);
        row = nxt;
      }
      return num(row[0]);
    }
    case "nthprime": {
      if (!isInt(a) || big(a) < 1n || big(a) > 300000n) return null;
      const p = sieveNth(big(a));
      return p === null ? null : num(p);
    }
    case "divisorsum": case "numdivisors": {
      if (!isInt(a) || big(a) < 1n || big(a) > 10n ** 24n) return null;
      const f = NT.factor(big(a), { budget: 2_000_000 });
      if (!f || !f.complete) return null;
      let r = 1n;
      for (const [p, e] of f.factors) {
        if (name === "numdivisors") r *= BigInt(e) + 1n;
        else r *= (p ** (BigInt(e) + 1n) - 1n) / (p - 1n);
      }
      return num(r);
    }
    case "modinv": {
      if (!isInt(a) || !isInt(b) || big(b) < 2n) return null;
      const m = big(b), x = ((big(a) % m) + m) % m;
      if (NT.gcd(x, m) !== 1n) return T.UNDEF;
      return num(NT.modInverse(x, m));
    }
    case "powmod": {
      if (!isInt(a) || !isInt(b) || !isInt(c) || big(c) < 1n) return null;
      if (big(b) < 0n) {
        const m = big(c), x = ((big(a) % m) + m) % m;
        if (NT.gcd(x, m) !== 1n) return T.UNDEF;
        return num(NT.modPow(NT.modInverse(x, m), -big(b), m));
      }
      return num(NT.modPow(big(a), big(b), big(c)));
    }
    case "binompdf": case "binomcdf": {
      if (!nonneg(a, 100000) || !probOK(b) || !isInt(c)) return null;
      const n = big(a), p = b.v, k = big(c);
      if (name === "binompdf") return num(binomPmf(n, p, k));
      let s = N.ZERO;
      for (let i = 0n; i <= (k < n ? k : n); i++) s = N.add(s, binomPmf(n, p, i));
      return num(s);
    }
    case "geompdf": case "geomcdf": {
      if (!probOK(a) || N.isZero(a.v) || !isInt(b)) return null;
      const p = a.v, q = N.sub(N.ONE, p), k = big(b);
      if (k < 1n) return num(0n);
      if (k > 100000n) return null;
      return num(name === "geompdf" ? N.mul(N.pow(q, k - 1n), p) : N.sub(N.ONE, N.pow(q, k)));
    }
    case "poissonpdf": case "poissoncdf": {
      if (!isRat(a) || !N.isPos(a.v) || !isInt(b)) return null;
      const L = a.v, k = big(b);
      if (k < 0n) return num(0n);
      if (k > 2000n) return null;
      let s = N.ZERO, term = N.ONE; // term = L^i / i!
      for (let i = 0n; i <= k; i++) {
        if (i > 0n) term = N.div(N.mul(term, L), N.Q(i));
        if (name === "poissoncdf" || i === k) s = name === "poissoncdf" ? N.add(s, term) : term;
      }
      return T.simpMul([num(s), T.simpPow(T.E, num(N.neg(L)))]);
    }
    case "hypergeompdf": {
      if (!args.every((t) => nonneg(t, 100000)) || args.length !== 4) return null;
      const [Np, K, n, k] = args.map(big);
      if (K > Np || n > Np) return T.UNDEF;
      if (k > K || k > n || n - k > Np - K) return num(0n);
      return num(N.Q(N.binom(K, k) * N.binom(Np - K, n - k), N.binom(Np, n)));
    }
    case "normalpdf": {
      if (args.length !== 1 && args.length !== 3) return null;
      const [x, mu, s] = args.length === 3 ? args : [a, T.ZERO, T.ONE];
      if (isRat(s) && !N.isPos(s.v)) return T.UNDEF;
      const z = T.simpMul([T.simpAdd([x, T.simpMul([T.NEG_ONE, mu])]), T.simpPow(s, T.NEG_ONE)]);
      return T.simpMul([T.simpPow(T.simpMul([s, T.simpPow(T.simpMul([T.num(2n), T.PI]), T.HALF)]), T.NEG_ONE),
        T.simpPow(T.E, T.simpMul([T.numQ(N.Q(-1n, 2n)), T.simpPow(z, T.num(2n))]))]);
    }
    case "normalcdf": {
      if (args.length !== 2 && args.length !== 4) return null;
      const [lo, hi, mu, s] = args.length === 4 ? args : [a, b, T.ZERO, T.ONE];
      if (isRat(s) && !N.isPos(s.v)) return T.UNDEF;
      // Phi(z) = (1 + erf(z / sqrt 2)) / 2; the two bounds give (erf(zb) - erf(za)) / 2
      const erfAt = (t) => {
        if (t === T.OO) return T.ONE;
        if (t.k === "mul" && t.args.length === 2 && isInt(t.args[0]) && big(t.args[0]) === -1n && t.args[1] === T.OO) return T.NEG_ONE;
        const z = T.simpMul([T.simpAdd([t, T.simpMul([T.NEG_ONE, mu])]), T.simpPow(T.simpMul([s, T.simpPow(T.num(2n), T.HALF)]), T.NEG_ONE)]);
        return T.simpFn("erf", [z]);
      };
      return T.simpMul([T.HALF, T.simpAdd([erfAt(hi), T.simpMul([T.NEG_ONE, erfAt(lo)])])]);
    }
    case "round": {
      // round half away from zero, to d decimal places (d may be negative: round(1234, -2) = 1200)
      if (!isRat(a) || (b !== undefined && !isInt(b)) || args.length > 2) return null;
      const d = b === undefined ? 0n : big(b);
      if (d > 1000n || d < -1000n) return null;
      const scale = d >= 0n ? N.Q(10n ** d) : N.Q(1n, 10n ** -d);
      const y = N.mul(N.abs ? N.abs(a.v) : (N.isNeg(a.v) ? N.neg(a.v) : a.v), scale);
      const r = N.div(N.Q((2n * y.n + y.d) / (2n * y.d)), scale); // floor(y + 1/2) / scale
      return num(N.isNeg(a.v) ? N.neg(r) : r);
    }
    case "zscore": {
      if (args.length !== 3) return null;
      if (isRat(c) && !N.isPos(c.v)) return T.UNDEF;
      return T.simpMul([T.simpAdd([a, T.simpMul([T.NEG_ONE, b])]), T.simpPow(c, T.NEG_ONE)]);
    }
    default: return null;
  }
}
