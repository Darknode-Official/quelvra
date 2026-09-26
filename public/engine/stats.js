// Quelvra probability and statistics.
//
// Exactness policy
//   * combinatorics return BigInt
//   * event probabilities (complement, independence, conditional, Bayes) return Rationals
//   * distribution pmf / cdf / mean / variance and descriptive statistics return exact trees
//     (rational numbers, radicals such as a standard deviation sqrt(10)/2, or e^-lambda terms)
//   * anything that needs erf / incomplete gamma / incomplete beta is computed in double
//     precision and returned as an Approx record (CONTRACT.md) with its method and error bound.

import * as N from "./num.js";
import * as X from "./expr.js";
import { simplify, makeCtx } from "./simplify.js";
import { parse } from "./parse.js";
import { evalFloat } from "./linalg.js";

const Z = (u) => simplify(u, makeCtx());
const fail = (msg, code = "DOMAIN") => Object.assign(new Error("Quelvra: " + msg), { code });
const budget = (msg) => fail(msg, "BUDGET");
const step = (rule, title, why, before = null, after = null, extra = {}) =>
  ({ rule, title, why, before, after, conditions: extra.conditions || [], sub: extra.sub || [], kind: extra.kind || "equivalent" });
const big = (x) => {
  if (typeof x === "bigint") return x;
  if (typeof x === "number" && Number.isSafeInteger(x)) return BigInt(x);
  if (typeof x === "string" && /^\s*-?\d+\s*$/.test(x)) return BigInt(x.trim());
  if (x && x.k === "num" && x.v.d === 1n) return x.v.n;
  if (x && typeof x.n === "bigint" && x.d === 1n) return x.n;
  throw fail("expected an integer, got " + String(x));
};
const nonneg = (x, what) => { x = big(x); if (x < 0n) throw fail(`${what} must be a nonnegative integer`); return x; };

// Exact rational from number / decimal string / "a/b" / Rational / num node.
export function rat(x) {
  if (typeof x === "bigint") return N.Q(x);
  if (x && typeof x === "object" && typeof x.n === "bigint") return x;
  if (x && typeof x === "object" && x.k === "num") return x.v;
  if (typeof x === "number") {
    if (!Number.isFinite(x)) throw fail("non-finite number");
    return Number.isInteger(x) ? N.Q(BigInt(x)) : N.fromDecimal(String(x));
  }
  if (typeof x === "string") {
    const s = x.trim();
    const m = s.match(/^([+-]?[\d.eE+-]+)\s*\/\s*([+-]?[\d.eE+-]+)$/);
    if (m) return N.div(N.fromDecimal(m[1]), N.fromDecimal(m[2]));
    if (/%$/.test(s)) return N.div(N.fromDecimal(s.slice(0, -1)), N.Q(100));
    return N.fromDecimal(s);
  }
  throw fail("expected an exact number, got " + String(x));
}
const isRatLike = (x) => { try { rat(x); return true; } catch (_) { return false; } };
const tree = (x) => (x && x.k ? Z(x) : isRatLike(x) ? X.num(rat(x)) : Z(parse(String(x))));
const Nt = (r) => X.num(r);

// Approx record (CONTRACT.md)
function approx(v, { method, errorBound = null, iterations = null, converged = true, digits = 15 } = {}) {
  return { value: Number.isFinite(v) ? Number(v.toPrecision(digits)).toString() : String(v), number: v, digits, requested: digits, errorBound, method, iterations, converged };
}

// ------------------------------------------------------------------ combinatorics (BigInt)
export function nPr(n, r) {
  n = nonneg(n, "n"); r = nonneg(r, "r");
  if (r > n) return 0n;
  let p = 1n;
  for (let i = 0n; i < r; i++) p *= n - i;
  return p;
}
export const nCr = (n, r) => N.binom(nonneg(n, "n"), nonneg(r, "r"));
export function multinomial(ks) {
  ks = ks.map((k) => nonneg(k, "k"));
  let r = 1n, s = 0n;
  for (const k of ks) { s += k; r *= N.binom(s, k); }
  return r;
}
export const permutationsWithRepetition = (n, r) => nonneg(n, "n") ** nonneg(r, "r");
export const multisetPermutations = (counts) => multinomial(counts);
export const combinationsWithRepetition = (n, r) => { n = nonneg(n, "n"); r = nonneg(r, "r"); return n === 0n ? (r === 0n ? 1n : 0n) : N.binom(n + r - 1n, r); };
export function derangements(n) {
  n = nonneg(n, "n");
  if (n > 100000n) throw budget("derangements of a very large n");
  let a = 1n, b = 0n; // D0, D1
  if (n === 0n) return 1n;
  for (let i = 2n; i <= n; i++) [a, b] = [b, (i - 1n) * (a + b)];
  return b;
}
function tableDP(n, k, rec) {
  n = Number(nonneg(n, "n")); k = Number(nonneg(k, "k"));
  if (n > 2000) throw budget("Stirling number table");
  if (k > n) return 0n;
  let row = [1n];
  for (let i = 1; i <= n; i++) {
    const next = new Array(i + 1).fill(0n);
    for (let j = 1; j <= i; j++) next[j] = rec(i, j, row[j - 1] || 0n, row[j] || 0n);
    row = next;
  }
  return row[k] || 0n;
}
// Stirling numbers of the second kind S(n, k) and unsigned first kind c(n, k).
export const stirling2 = (n, k) => tableDP(n, k, (i, j, a, b) => a + BigInt(j) * b);
export const stirling1 = (n, k) => tableDP(n, k, (i, j, a, b) => a + BigInt(i - 1) * b);
export const catalan = (n) => { n = nonneg(n, "n"); return N.binom(2n * n, n) / (n + 1n); };
export function bell(n) {
  n = Number(nonneg(n, "n"));
  if (n > 2000) throw budget("Bell number");
  let row = [1n];
  for (let i = 0; i < n; i++) {
    const next = [row[row.length - 1]];
    for (const v of row) next.push(next[next.length - 1] + v);
    row = next;
  }
  return row[0];
}

// ------------------------------------------------------------------ event probabilities (Rational)
export function prob(x) {
  const r = rat(x);
  if (N.isNeg(r) || N.cmp(r, N.ONE) > 0) throw fail(`probability ${N.toString(r)} is outside [0, 1]`);
  return r;
}
export const complement = (p) => N.sub(N.ONE, prob(p));
export const andIndependent = (...ps) => ps.map(prob).reduce(N.mul, N.ONE);
// P(A or B) = P(A) + P(B) - P(A and B); independent when pAB is omitted
export function or(pA, pB, pAB) {
  const a = prob(pA), b = prob(pB);
  const ab = pAB === undefined ? N.mul(a, b) : prob(pAB);
  return prob(N.sub(N.add(a, b), ab));
}
export const orExclusive = (...ps) => prob(ps.map(prob).reduce(N.add, N.ZERO));
// P(A | B) = P(A and B) / P(B)
export function conditional(pAandB, pB) {
  const b = prob(pB);
  if (N.isZero(b)) throw fail("conditioning on an event of probability 0");
  return prob(N.div(prob(pAandB), b));
}
// Bayes: P(H | E) from prior P(H), P(E | H) and P(E | not H).
export function bayes({ prior, likelihood, likelihoodNot }) {
  const h = prob(prior), l = prob(likelihood), ln = prob(likelihoodNot);
  const num = N.mul(l, h);
  const evidence = N.add(num, N.mul(ln, N.sub(N.ONE, h)));
  if (N.isZero(evidence)) throw fail("the evidence has probability 0");
  const posterior = N.div(num, evidence);
  const steps = [
    step("prob.total", "Total probability of the evidence", `P(E) = P(E|H)P(H) + P(E|not H)P(not H) = ${N.toString(l)}*${N.toString(h)} + ${N.toString(ln)}*${N.toString(N.sub(N.ONE, h))} = ${N.toString(evidence)}.`, null, Nt(evidence)),
    step("prob.bayes", "Bayes' theorem", `P(H|E) = P(E|H)P(H) / P(E) = ${N.toString(num)} / ${N.toString(evidence)}.`, null, Nt(posterior)),
  ];
  return { posterior, evidence, steps };
}
// Bayes over a partition H_1..H_k: posteriors P(H_i | E).
export function bayesPartition(priors, likelihoods) {
  const p = priors.map(prob), l = likelihoods.map(prob);
  if (p.length !== l.length) throw fail("priors and likelihoods differ in length");
  if (!N.eq(p.reduce(N.add, N.ZERO), N.ONE)) throw fail("priors must sum to 1");
  const joint = p.map((v, i) => N.mul(v, l[i]));
  const evidence = joint.reduce(N.add, N.ZERO);
  if (N.isZero(evidence)) throw fail("the evidence has probability 0");
  return { evidence, posteriors: joint.map((j) => N.div(j, evidence)) };
}

// ------------------------------------------------------------------ discrete distributions (exact trees)
function distPMFsum(pmfR, lo, hi) {
  let s = N.ZERO;
  if (hi - lo > 1000000n) throw budget("cdf summation");
  for (let k = lo; k <= hi; k++) s = N.add(s, pmfR(k));
  return s;
}
export function binomial(n, p) {
  n = nonneg(n, "n");
  const P = prob(p), Qp = N.sub(N.ONE, P);
  const pmfR = (k) => (k < 0n || k > n ? N.ZERO : N.mul(N.Q(N.binom(n, k)), N.mul(N.pow(P, k), N.pow(Qp, n - k))));
  return {
    name: "binomial", params: { n, p: P }, support: [0n, n],
    pmf: (k) => Nt(pmfR(big(k))),
    cdf: (k) => { k = big(k); return Nt(k < 0n ? N.ZERO : distPMFsum(pmfR, 0n, k < n ? k : n)); },
    mean: Nt(N.mul(N.Q(n), P)),
    variance: Nt(N.mul(N.Q(n), N.mul(P, Qp))),
    pmfRational: pmfR,
  };
}
// kind "trials": X = number of trials up to and including the first success (k >= 1);
// kind "failures": X = failures before the first success (k >= 0).
export function geometric(p, kind = "trials") {
  const P = prob(p);
  if (N.isZero(P)) throw fail("geometric distribution needs p > 0");
  const Qp = N.sub(N.ONE, P), off = kind === "failures" ? 0n : 1n;
  const pmfR = (k) => (k < off ? N.ZERO : N.mul(N.pow(Qp, k - off), P));
  return {
    name: "geometric", params: { p: P, kind }, support: [off, null],
    pmf: (k) => Nt(pmfR(big(k))),
    cdf: (k) => { k = big(k); return Nt(k < off ? N.ZERO : N.sub(N.ONE, N.pow(Qp, k - off + 1n))); },
    mean: Nt(kind === "failures" ? N.div(Qp, P) : N.inv(P)),
    variance: Nt(N.div(Qp, N.mul(P, P))),
    pmfRational: pmfR,
  };
}
// Poisson: pmf = e^-lambda lambda^k / k!  (exact tree; e^-lambda kept symbolic)
export function poisson(lambda) {
  const L = tree(lambda);
  const eL = Z(X.pow(X.E, X.neg(L)));
  const partial = (k) => Z(X.mul(X.pow(L, X.num(k)), X.num(N.Q(1n, N.factorial(k)))));
  return {
    name: "poisson", params: { lambda: L }, support: [0n, null],
    pmf: (k) => { k = big(k); return k < 0n ? X.ZERO : Z(X.mul(partial(k), eL)); },
    cdf: (k) => {
      k = big(k);
      if (k < 0n) return X.ZERO;
      if (k > 100000n) throw budget("Poisson cdf summation");
      const terms = [];
      for (let i = 0n; i <= k; i++) terms.push(partial(i));
      return Z(X.mul(Z(X.add(...terms)), eL));
    },
    mean: L, variance: L,
  };
}
export function hypergeometric(Npop, K, n) {
  Npop = nonneg(Npop, "N"); K = nonneg(K, "K"); n = nonneg(n, "n");
  if (K > Npop || n > Npop) throw fail("hypergeometric needs K <= N and n <= N");
  const tot = N.binom(Npop, n);
  const pmfR = (k) => N.Q(N.binom(K, k) * N.binom(Npop - K, n - k), tot);
  const lo = n + K > Npop ? n + K - Npop : 0n, hi = n < K ? n : K;
  const NN = N.Q(Npop);
  const mean = N.div(N.mul(N.Q(n), N.Q(K)), NN);
  const variance = Npop > 1n
    ? N.mul(N.mul(mean, N.div(N.Q(Npop - K), NN)), N.div(N.Q(Npop - n), N.Q(Npop - 1n)))
    : N.ZERO;
  return {
    name: "hypergeometric", params: { N: Npop, K, n }, support: [lo, hi],
    pmf: (k) => { k = big(k); return Nt(k < lo || k > hi ? N.ZERO : pmfR(k)); },
    cdf: (k) => { k = big(k); return Nt(k < lo ? N.ZERO : distPMFsum(pmfR, lo, k < hi ? k : hi)); },
    mean: Nt(mean), variance: Nt(variance), pmfRational: (k) => (k < lo || k > hi ? N.ZERO : pmfR(k)),
  };
}
export function uniformDiscrete(a, b) {
  a = big(a); b = big(b);
  if (b < a) throw fail("uniform discrete needs a <= b");
  const m = b - a + 1n;
  return {
    name: "uniform-discrete", params: { a, b }, support: [a, b],
    pmf: (k) => { k = big(k); return Nt(k < a || k > b ? N.ZERO : N.Q(1n, m)); },
    cdf: (k) => { k = big(k); return Nt(k < a ? N.ZERO : k >= b ? N.ONE : N.Q(k - a + 1n, m)); },
    mean: Nt(N.Q(a + b, 2n)), variance: Nt(N.Q(m * m - 1n, 12n)),
    pmfRational: (k) => (k < a || k > b ? N.ZERO : N.Q(1n, m)),
  };
}

// ------------------------------------------------------------------ special functions (double precision)
const LANCZOS = [0.99999999999980993, 676.5203681218851, -1259.1392167224028, 771.32342877765313, -176.61502916214059, 12.507343278686905, -0.13857109526572012, 9.9843695780195716e-6, 1.5056327351493116e-7];
export function lgamma(x) {
  if (x < 0.5) return Math.log(Math.PI / Math.abs(Math.sin(Math.PI * x))) - lgamma(1 - x);
  x -= 1;
  let a = LANCZOS[0];
  const t = x + 7.5;
  for (let i = 1; i < 9; i++) a += LANCZOS[i] / (x + i);
  return 0.5 * Math.log(2 * Math.PI) + (x + 0.5) * Math.log(t) - t + Math.log(a);
}
// Regularised lower incomplete gamma P(a, x) and upper Q(a, x).
function gser(a, x) {
  let sum = 1 / a, del = sum, ap = a;
  for (let n = 1; n <= 10000; n++) {
    ap += 1; del *= x / ap; sum += del;
    if (Math.abs(del) < Math.abs(sum) * 1e-17) return { v: sum * Math.exp(-x + a * Math.log(x) - lgamma(a)), it: n };
  }
  throw budget("incomplete gamma series");
}
function gcf(a, x) {
  const FPMIN = 1e-300;
  let b = x + 1 - a, c = 1 / FPMIN, d = 1 / b, h = d;
  for (let i = 1; i <= 10000; i++) {
    const an = -i * (i - a);
    b += 2;
    d = an * d + b; if (Math.abs(d) < FPMIN) d = FPMIN;
    c = b + an / c; if (Math.abs(c) < FPMIN) c = FPMIN;
    d = 1 / d;
    const del = d * c;
    h *= del;
    if (Math.abs(del - 1) < 1e-16) return { v: Math.exp(-x + a * Math.log(x) - lgamma(a)) * h, it: i };
  }
  throw budget("incomplete gamma continued fraction");
}
export function gammaP(a, x) { if (x <= 0) return 0; return x < a + 1 ? gser(a, x).v : 1 - gcf(a, x).v; }
export function gammaQ(a, x) { if (x <= 0) return 1; return x < a + 1 ? 1 - gser(a, x).v : gcf(a, x).v; }
export function erf(x) { return x >= 0 ? gammaP(0.5, x * x) : -gammaP(0.5, x * x); }
export function erfc(x) { return x >= 0 ? gammaQ(0.5, x * x) : 1 + gammaP(0.5, x * x); }
function betacf(a, b, x) {
  const FPMIN = 1e-300;
  let c = 1, d = 1 - ((a + b) * x) / (a + 1);
  if (Math.abs(d) < FPMIN) d = FPMIN;
  d = 1 / d;
  let h = d;
  for (let m = 1; m <= 10000; m++) {
    const m2 = 2 * m;
    let aa = (m * (b - m) * x) / ((a - 1 + m2) * (a + m2));
    d = 1 + aa * d; if (Math.abs(d) < FPMIN) d = FPMIN;
    c = 1 + aa / c; if (Math.abs(c) < FPMIN) c = FPMIN;
    d = 1 / d; h *= d * c;
    aa = (-(a + m) * (a + b + m) * x) / ((a + m2) * (a + 1 + m2));
    d = 1 + aa * d; if (Math.abs(d) < FPMIN) d = FPMIN;
    c = 1 + aa / c; if (Math.abs(c) < FPMIN) c = FPMIN;
    d = 1 / d;
    const del = d * c;
    h *= del;
    if (Math.abs(del - 1) < 1e-16) return h;
  }
  throw budget("incomplete beta continued fraction");
}
// Regularised incomplete beta I_x(a, b)
export function betaI(a, b, x) {
  if (x <= 0) return 0;
  if (x >= 1) return 1;
  const bt = Math.exp(lgamma(a + b) - lgamma(a) - lgamma(b) + a * Math.log(x) + b * Math.log(1 - x));
  return x < (a + 1) / (a + b + 2) ? (bt * betacf(a, b, x)) / a : 1 - (bt * betacf(b, a, 1 - x)) / b;
}
// Bisection on a monotone increasing cdf: smallest x with cdf(x) >= p (double precision).
export function invertCdf(cdf, p, lo = -1, hi = 1, { lowerBound = -Infinity } = {}) {
  if (!(p > 0 && p < 1)) throw fail("quantile needs 0 < p < 1");
  let it = 0;
  while (cdf(lo) > p) { const w = hi - lo; lo = Math.max(lowerBound, lo - 2 * w); if (++it > 2000) throw budget("quantile bracket"); if (lo === lowerBound && cdf(lo) > p) break; }
  while (cdf(hi) < p) { hi += 2 * (hi - lo); if (++it > 2000) throw budget("quantile bracket"); }
  let n = 0;
  for (; n < 300; n++) {
    const mid = 0.5 * (lo + hi);
    if (mid === lo || mid === hi || hi - lo <= 4e-16 * Math.max(1, Math.abs(mid))) break;
    if (cdf(mid) < p) lo = mid; else hi = mid;
  }
  return { x: 0.5 * (lo + hi), iterations: n, converged: n < 300, width: hi - lo };
}

// ------------------------------------------------------------------ continuous distributions
const fl = (x) => (typeof x === "number" ? x : evalFloat(tree(x)));
export function normal(mu = 0, sigma = 1) {
  const M = tree(mu), S = tree(sigma);
  const m = evalFloat(M), s = evalFloat(S);
  if (!(s > 0)) throw fail("normal distribution needs sigma > 0");
  const cdfF = (x) => { const z = (x - m) / s; return z < 0 ? 0.5 * erfc(-z / Math.SQRT2) : 1 - 0.5 * erfc(z / Math.SQRT2); };
  return {
    name: "normal", params: { mu: M, sigma: S },
    mean: M, variance: Z(X.pow(S, X.TWO)),
    pdf: (x) => { const xt = tree(x); return Z(X.mul(X.pow(X.mul(S, X.sqrt(X.mul(X.TWO, X.PI))), X.NEG_ONE), X.pow(X.E, X.mul(X.num(N.Q(-1, 2)), X.pow(X.div(X.sub(xt, M), S), X.TWO))))); },
    cdf: (x) => approx(cdfF(fl(x)), { method: "Phi(z) via erfc = regularised incomplete gamma Q(1/2, z^2/2)", errorBound: "1e-14" }),
    cdfFloat: cdfF,
    quantile: (p) => { const r = invertCdf(cdfF, fl(p), m - s, m + s); return approx(r.x, { method: "bisection on the normal cdf", errorBound: "1e-12", iterations: r.iterations, converged: r.converged }); },
  };
}
export function uniform(a, b) {
  const A = tree(a), B = tree(b);
  const af = evalFloat(A), bf = evalFloat(B);
  if (!(bf > af)) throw fail("uniform distribution needs a < b");
  const W = Z(X.sub(B, A));
  const clampExact = (x) => { const xt = tree(x), xf = evalFloat(xt); return xf <= af ? X.ZERO : xf >= bf ? X.ONE : Z(X.div(X.sub(xt, A), W)); };
  return {
    name: "uniform", params: { a: A, b: B },
    mean: Z(X.div(X.add(A, B), X.TWO)), variance: Z(X.div(X.pow(W, X.TWO), X.num(12))),
    pdf: (x) => { const xf = fl(x); return xf < af || xf > bf ? X.ZERO : Z(X.pow(W, X.NEG_ONE)); },
    cdf: clampExact,
    quantile: (p) => Z(X.add(A, X.mul(tree(p), W))),
  };
}
export function exponential(rate) {
  const L = tree(rate);
  if (!(evalFloat(L) > 0)) throw fail("exponential distribution needs rate > 0");
  return {
    name: "exponential", params: { rate: L },
    mean: Z(X.pow(L, X.NEG_ONE)), variance: Z(X.pow(L, X.num(-2))),
    pdf: (x) => { const xt = tree(x); return evalFloat(xt) < 0 ? X.ZERO : Z(X.mul(L, X.pow(X.E, X.neg(X.mul(L, xt))))); },
    cdf: (x) => { const xt = tree(x); return evalFloat(xt) <= 0 ? X.ZERO : Z(X.sub(X.ONE, X.pow(X.E, X.neg(X.mul(L, xt))))); },
    quantile: (p) => { const P = tree(p); return Z(X.div(X.neg(X.fn("ln", X.sub(X.ONE, P))), L)); },
  };
}
export function studentT(df) {
  const v = fl(df);
  if (!(v > 0)) throw fail("t distribution needs df > 0");
  const cdfF = (t) => { const x = v / (v + t * t); const tail = 0.5 * betaI(v / 2, 0.5, x); return t >= 0 ? 1 - tail : tail; };
  const pdfF = (t) => Math.exp(lgamma((v + 1) / 2) - lgamma(v / 2) - 0.5 * Math.log(v * Math.PI) - ((v + 1) / 2) * Math.log(1 + (t * t) / v));
  return {
    name: "t", params: { df: v },
    mean: v > 1 ? X.ZERO : X.UNDEF, variance: v > 2 ? X.num(N.div(rat(v), rat(v - 2))) : v > 1 ? X.OO : X.UNDEF,
    pdf: (t) => approx(pdfF(fl(t)), { method: "Gamma-function formula (Lanczos)", errorBound: "1e-13" }),
    cdf: (t) => approx(cdfF(fl(t)), { method: "regularised incomplete beta (Lentz continued fraction)", errorBound: "1e-13" }),
    cdfFloat: cdfF,
    quantile: (p) => { const r = invertCdf(cdfF, fl(p), -1, 1); return approx(r.x, { method: "bisection on the t cdf", errorBound: "1e-11", iterations: r.iterations, converged: r.converged }); },
  };
}
export function chiSquare(k) {
  const v = fl(k);
  if (!(v > 0)) throw fail("chi-square distribution needs k > 0");
  const cdfF = (x) => (x <= 0 ? 0 : gammaP(v / 2, x / 2));
  const sfF = (x) => (x <= 0 ? 1 : gammaQ(v / 2, x / 2));
  return {
    name: "chi-square", params: { k: v }, mean: X.num(rat(v)), variance: X.num(N.mul(N.Q(2), rat(v))),
    pdf: (x) => { x = fl(x); return approx(x <= 0 ? 0 : Math.exp((v / 2 - 1) * Math.log(x) - x / 2 - (v / 2) * Math.LN2 - lgamma(v / 2)), { method: "closed form (Lanczos Gamma)", errorBound: "1e-13" }); },
    cdf: (x) => approx(cdfF(fl(x)), { method: "regularised incomplete gamma P(k/2, x/2)", errorBound: "1e-13" }),
    cdfFloat: cdfF, sfFloat: sfF,
    quantile: (p) => { const r = invertCdf(cdfF, fl(p), 0, Math.max(1, v), { lowerBound: 0 }); return approx(r.x, { method: "bisection on the chi-square cdf", errorBound: "1e-11", iterations: r.iterations, converged: r.converged }); },
  };
}

// ------------------------------------------------------------------ descriptive statistics (exact)
export function data(xs) {
  if (typeof xs === "string") xs = xs.split(/[\s,;]+/).filter(Boolean);
  if (xs && xs.k) xs = xs.args;
  if (!Array.isArray(xs) || !xs.length) throw fail("data list is empty", "INPUT");
  return xs.map(rat);
}
const sumR = (a) => a.reduce(N.add, N.ZERO);
const sortR = (a) => a.slice().sort(N.cmp);
const meanR = (a) => N.div(sumR(a), N.Q(a.length));
const medianSorted = (s) => { const n = s.length, h = n >> 1; return n % 2 ? s[h] : N.div(N.add(s[h - 1], s[h]), N.TWO); };
export const mean = (xs) => Nt(meanR(data(xs)));
export const median = (xs) => Nt(medianSorted(sortR(data(xs))));
export function mode(xs) {
  const d = data(xs);
  const cnt = new Map();
  for (const v of d) { const k = N.toString(v); cnt.set(k, { v, c: (cnt.get(k)?.c || 0) + 1 }); }
  const max = Math.max(...[...cnt.values()].map((e) => e.c));
  const modes = [...cnt.values()].filter((e) => e.c === max).map((e) => e.v).sort(N.cmp);
  return { modes: modes.map(Nt), frequency: max, noMode: max === 1 && d.length > 1 };
}
// Sum of squared deviations sum (x - mean)^2, exactly.
const ssR = (d) => { const m = meanR(d); return d.reduce((s, x) => N.add(s, N.mul(N.sub(x, m), N.sub(x, m))), N.ZERO); };
export function varianceR(xs, { population = false } = {}) {
  const d = data(xs);
  const den = population ? d.length : d.length - 1;
  if (den <= 0) throw fail("sample variance needs at least two values");
  return N.div(ssR(d), N.Q(den));
}
export const variance = (xs, opts) => Nt(varianceR(xs, opts));
export const stdDev = (xs, opts) => Z(X.sqrt(X.num(varianceR(xs, opts))));
// Quartiles by the "median of halves" method (Tukey / Moore-McCabe, as on TI calculators):
// Q2 is the median; Q1 and Q3 are medians of the lower and upper halves, excluding the
// middle value when n is odd.
export function quartiles(xs) {
  const s = sortR(data(xs));
  const n = s.length, h = n >> 1;
  if (n < 2) return { q1: Nt(s[0]), q2: Nt(s[0]), q3: Nt(s[0]), method: "median-of-halves" };
  const lower = s.slice(0, h), upper = s.slice(n % 2 ? h + 1 : h);
  return { q1: Nt(medianSorted(lower)), q2: Nt(medianSorted(s)), q3: Nt(medianSorted(upper)), method: "median-of-halves (exclusive, Tukey/Moore-McCabe)" };
}
export const iqr = (xs) => { const q = quartiles(xs); return Nt(N.sub(q.q3.v, q.q1.v)); };
export const range = (xs) => { const s = sortR(data(xs)); return Nt(N.sub(s[s.length - 1], s[0])); };
export function zScores(xs, opts = {}) {
  const d = data(xs), m = meanR(d);
  const sd = stdDev(d, opts);
  if (sd === X.ZERO) throw fail("z-scores need a nonzero standard deviation");
  return d.map((x) => Z(X.div(X.num(N.sub(x, m)), sd)));
}
export function summary(xs, opts = {}) {
  const d = data(xs), s = sortR(d);
  const q = quartiles(d);
  return {
    n: d.length, sum: Nt(sumR(d)), mean: Nt(meanR(d)), median: q.q2, mode: mode(d),
    min: Nt(s[0]), max: Nt(s[s.length - 1]), range: Nt(N.sub(s[s.length - 1], s[0])),
    q1: q.q1, q3: q.q3, iqr: Nt(N.sub(q.q3.v, q.q1.v)), quartileMethod: q.method,
    variance: d.length > 1 || opts.population ? variance(d, opts) : null,
    stdDev: d.length > 1 || opts.population ? stdDev(d, opts) : null,
    population: !!opts.population,
  };
}
function pairs(xs, ys) {
  const a = data(xs), b = data(ys);
  if (a.length !== b.length) throw fail("x and y lists have different lengths", "INPUT");
  if (a.length < 2) throw fail("need at least two data pairs", "INPUT");
  return [a, b];
}
const sxy = (a, b) => { const ma = meanR(a), mb = meanR(b); return a.reduce((s, x, i) => N.add(s, N.mul(N.sub(x, ma), N.sub(b[i], mb))), N.ZERO); };
export function covariance(xs, ys, { population = false } = {}) {
  const [a, b] = pairs(xs, ys);
  return Nt(N.div(sxy(a, b), N.Q(population ? a.length : a.length - 1)));
}
export function correlation(xs, ys) {
  const [a, b] = pairs(xs, ys);
  const Sxx = ssR(a), Syy = ssR(b), Sxy = sxy(a, b);
  if (N.isZero(Sxx) || N.isZero(Syy)) throw fail("correlation is undefined when one variable is constant");
  return Z(X.mul(X.num(Sxy), X.pow(X.num(N.mul(Sxx, Syy)), X.num(N.Q(-1, 2)))));
}
// Least-squares line y = slope x + intercept, exact for rational data.
export function linearRegression(xs, ys) {
  const [a, b] = pairs(xs, ys);
  const Sxx = ssR(a), Syy = ssR(b), Sxy = sxy(a, b);
  if (N.isZero(Sxx)) throw fail("all x values are equal; the regression line is vertical");
  const slope = N.div(Sxy, Sxx), intercept = N.sub(meanR(b), N.mul(slope, meanR(a)));
  const r2 = N.isZero(Syy) ? N.ONE : N.div(N.mul(Sxy, Sxy), N.mul(Sxx, Syy));
  const r = N.isZero(Syy) ? null : correlation(a, b);
  const x = X.sym("x");
  const eqn = X.eq(X.sym("y"), Z(X.add(X.mul(X.num(slope), x), X.num(intercept))));
  const steps = [
    step("stats.regression.sums", "Sums of squares", `Sxx = ${N.toString(Sxx)}, Sxy = ${N.toString(Sxy)}, Syy = ${N.toString(Syy)}.`),
    step("stats.regression.slope", "Slope m = Sxy / Sxx", `m = ${N.toString(Sxy)} / ${N.toString(Sxx)}.`, null, Nt(slope)),
    step("stats.regression.intercept", "Intercept b = mean(y) - m mean(x)", "The least-squares line passes through (mean x, mean y).", null, Nt(intercept)),
  ];
  return { slope: Nt(slope), intercept: Nt(intercept), r, r2: Nt(r2), equation: eqn, steps };
}

// ------------------------------------------------------------------ inference (numeric p-values)
const STD = normal(0, 1);
const zCrit = (conf) => STD.quantile(1 - (1 - conf) / 2).number;
const confOf = (c) => { const v = typeof c === "number" ? c : N.toFloat(rat(c)); if (!(v > 0 && v < 1)) throw fail("confidence level must be in (0, 1)"); return v; };
function meanStats(src) {
  if (Array.isArray(src) || typeof src === "string") {
    const d = data(src);
    return { mean: meanR(d), n: d.length, s: d.length > 1 ? varianceR(d) : null };
  }
  return { mean: rat(src.mean), n: Number(big(src.n)), s: src.sd !== undefined ? N.mul(rat(src.sd), rat(src.sd)) : null };
}
// Confidence interval for a mean: z when sigma is known, t (df = n - 1) otherwise.
export function ciMean(src, opts = {}) {
  const st = meanStats(src);
  const conf = confOf(opts.confidence ?? 0.95);
  const useZ = opts.sigma !== undefined;
  if (!useZ && st.s === null) throw fail("need a sample standard deviation or a known sigma");
  const sd = useZ ? fl(opts.sigma) : Math.sqrt(N.toFloat(st.s));
  const crit = useZ ? zCrit(conf) : studentT(st.n - 1).quantile(1 - (1 - conf) / 2).number;
  const se = sd / Math.sqrt(st.n);
  const c = N.toFloat(st.mean);
  return {
    method: useZ ? "z" : "t", df: useZ ? null : st.n - 1, confidence: conf, center: Nt(st.mean),
    critical: approx(crit, { method: useZ ? "normal quantile" : "t quantile", errorBound: "1e-11" }),
    standardError: approx(se, { method: "sd / sqrt(n)" }), margin: approx(crit * se, { method: "critical * SE" }),
    lower: approx(c - crit * se, { method: "center - margin" }), upper: approx(c + crit * se, { method: "center + margin" }),
  };
}
// Wald interval for a proportion.
export function ciProportion(x, n, opts = {}) {
  x = big(x); n = big(n);
  if (n <= 0n || x < 0n || x > n) throw fail("need 0 <= x <= n and n > 0");
  const conf = confOf(opts.confidence ?? 0.95);
  const ph = N.Q(x, n), p = N.toFloat(ph);
  const crit = zCrit(conf), se = Math.sqrt((p * (1 - p)) / Number(n));
  return {
    method: "Wald z-interval", confidence: conf, center: Nt(ph),
    standardError: Z(X.sqrt(X.num(N.div(N.mul(ph, N.sub(N.ONE, ph)), N.Q(n))))),
    critical: approx(crit, { method: "normal quantile", errorBound: "1e-11" }), margin: approx(crit * se, { method: "critical * SE" }),
    lower: approx(p - crit * se, { method: "center - margin" }), upper: approx(p + crit * se, { method: "center + margin" }),
  };
}
function decide(pv, alpha, extra) {
  const a = typeof alpha === "number" ? alpha : N.toFloat(rat(alpha ?? 0.05));
  return { ...extra, pValue: pv, alpha: a, decision: pv.number < a ? "reject H0" : "fail to reject H0" };
}
function tailP(cdf, stat, tail) {
  if (tail === "left") return cdf(stat);
  if (tail === "right") return 1 - cdf(stat);
  return Math.min(1, 2 * Math.min(cdf(stat), 1 - cdf(stat)));
}
// One-sample z test: statistic = (xbar - mu0) / (sigma / sqrt(n)) (exact tree).
export function zTest(src, { mu0 = 0, sigma, alpha = 0.05, tail = "two" } = {}) {
  if (sigma === undefined) throw fail("z test needs the population sigma");
  const st = meanStats(src);
  const stat = Z(X.div(X.sub(X.num(st.mean), tree(mu0)), X.div(tree(sigma), X.sqrt(X.num(st.n)))));
  const z = evalFloat(stat);
  const pv = approx(tailP(STD.cdfFloat, z, tail), { method: `${tail}-tailed normal probability (erfc)`, errorBound: "1e-14" });
  return decide(pv, alpha, { test: "one-sample z", tail, statistic: stat, statisticValue: z });
}
export function tTest(src, { mu0 = 0, alpha = 0.05, tail = "two" } = {}) {
  const st = meanStats(src);
  if (st.s === null) throw fail("t test needs a sample standard deviation");
  const stat = Z(X.div(X.sub(X.num(st.mean), tree(mu0)), X.sqrt(X.div(X.num(st.s), X.num(st.n)))));
  const t = evalFloat(stat), T = studentT(st.n - 1);
  const pv = approx(tailP(T.cdfFloat, t, tail), { method: `${tail}-tailed t probability (incomplete beta)`, errorBound: "1e-12" });
  return decide(pv, alpha, { test: "one-sample t", tail, df: st.n - 1, statistic: stat, statisticValue: t });
}
// Two-proportion z test with pooled proportion.
export function twoProportionZ(x1, n1, x2, n2, { alpha = 0.05, tail = "two" } = {}) {
  x1 = big(x1); n1 = big(n1); x2 = big(x2); n2 = big(n2);
  const p1 = N.Q(x1, n1), p2 = N.Q(x2, n2), pp = N.Q(x1 + x2, n1 + n2);
  const v = N.mul(N.mul(pp, N.sub(N.ONE, pp)), N.add(N.Q(1n, n1), N.Q(1n, n2)));
  if (N.isZero(v)) throw fail("pooled proportion is 0 or 1; the z statistic is undefined");
  const stat = Z(X.div(X.num(N.sub(p1, p2)), X.sqrt(X.num(v))));
  const z = evalFloat(stat);
  const pv = approx(tailP(STD.cdfFloat, z, tail), { method: `${tail}-tailed normal probability (erfc)`, errorBound: "1e-14" });
  return decide(pv, alpha, { test: "two-proportion z", tail, pooled: Nt(pp), statistic: stat, statisticValue: z });
}
// Chi-square goodness of fit. expected: counts, or probabilities (summing to 1).
export function chiSquareGOF(observed, expected, { alpha = 0.05 } = {}) {
  const O = data(observed), E0 = data(expected);
  if (O.length !== E0.length) throw fail("observed and expected differ in length", "INPUT");
  const tot = sumR(O);
  const isProb = N.eq(sumR(E0), N.ONE) && !N.eq(tot, N.ONE);
  const E = isProb ? E0.map((p) => N.mul(p, tot)) : E0;
  if (E.some((e) => !N.isPos(e))) throw fail("expected counts must be positive");
  let chi = N.ZERO;
  for (let i = 0; i < O.length; i++) { const d = N.sub(O[i], E[i]); chi = N.add(chi, N.div(N.mul(d, d), E[i])); }
  const df = O.length - 1;
  const C = chiSquare(df);
  const pv = approx(C.sfFloat(N.toFloat(chi)), { method: "upper regularised incomplete gamma Q(df/2, x/2)", errorBound: "1e-13" });
  const warn = E.some((e) => N.cmp(e, N.Q(5)) < 0) ? ["some expected counts are below 5; the chi-square approximation may be poor"] : [];
  return decide(pv, alpha, { test: "chi-square goodness of fit", df, expected: E.map(Nt), statistic: Nt(chi), statisticValue: N.toFloat(chi), warnings: warn });
}
