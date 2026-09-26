import { test, eq, ok, throws, close, rng } from "./harness.js";
import * as S from "../public/engine/stats.js";
import * as N from "../public/engine/num.js";
import * as X from "../public/engine/expr.js";
import { simplify, makeCtx } from "../public/engine/simplify.js";
import { toText } from "../public/engine/print.js";
import { evalFloat } from "../public/engine/linalg.js";

const t = toText;
const Zs = (u) => simplify(u, makeCtx());
const randRat = (r, lo, hi, den = 12) => N.Q(BigInt(r.int(lo, hi)), BigInt(r.int(1, den)));

// ---------------- combinatorics
test("stats: counting functions", () => {
  eq(S.nPr(5, 2), 20n); eq(S.nPr(3, 5), 0n); eq(S.nCr(52, 5), 2598960n); eq(S.nCr(10, 0), 1n);
  eq(S.multinomial([2, 2, 1]), 30n); eq(S.multisetPermutations([1, 4, 4, 2]), 34650n); // MISSISSIPPI
  eq(S.permutationsWithRepetition(10, 3), 1000n); eq(S.combinationsWithRepetition(3, 2), 6n);
  eq(S.derangements(0), 1n); eq(S.derangements(1), 0n); eq(S.derangements(4), 9n); eq(S.derangements(10), 1334961n);
  eq(S.stirling2(5, 2), 15n); eq(S.stirling2(10, 3), 9330n); eq(S.stirling1(4, 2), 11n);
  eq(S.catalan(0), 1n); eq(S.catalan(5), 42n); eq(S.catalan(10), 16796n);
  eq(S.bell(5), 52n); eq(S.bell(10), 115975n);
  throws(() => S.nCr(-1, 2));
});
test("stats: exact event probabilities", () => {
  eq(N.toString(S.complement("1/3")), "2/3");
  eq(N.toString(S.andIndependent("1/2", "1/3")), "1/6");
  eq(N.toString(S.or("1/2", "1/3")), "2/3");
  eq(N.toString(S.or("0.5", "0.4", "0.2")), "7/10");
  eq(N.toString(S.conditional("1/6", "1/2")), "1/3");
  throws(() => S.prob("3/2"));
  throws(() => S.conditional("1/6", 0));
});
test("stats: Bayes theorem (rare disease)", () => {
  const b = S.bayes({ prior: "1/100", likelihood: "0.99", likelihoodNot: "0.05" });
  eq(N.toString(b.posterior), "1/6");
  eq(b.steps.map((s) => s.rule).join(), "prob.total,prob.bayes");
  const p = S.bayesPartition(["1/2", "3/10", "1/5"], ["1/100", "1/50", "3/100"]);
  eq(p.posteriors.map(N.toString).join(), "5/17,6/17,6/17");
  throws(() => S.bayesPartition(["1/2", "1/3"], ["1/2", "1/2"]));
});

// ---------------- discrete distributions
test("stats: binomial exact", () => {
  const b = S.binomial(10, "1/3");
  eq(t(b.pmf(3)), "5120/19683"); eq(t(b.cdf(10)), "1"); eq(t(b.mean), "10/3"); eq(t(b.variance), "20/9");
  eq(t(b.pmf(11)), "0"); eq(t(b.cdf(-1)), "0");
});
test("stats: geometric both conventions", () => {
  const g = S.geometric("1/4");
  eq(t(g.pmf(3)), "9/64"); eq(t(g.cdf(3)), "37/64"); eq(t(g.mean), "4"); eq(t(g.variance), "12");
  const f = S.geometric("1/4", "failures");
  eq(t(f.pmf(0)), "1/4"); eq(t(f.mean), "3");
});
test("stats: Poisson keeps e^-lambda symbolic", () => {
  const p = S.poisson(3);
  eq(t(p.pmf(2)), "9/(2e^3)");
  eq(t(p.cdf(2)), "17/(2e^3)");
  eq(t(p.mean), "3");
  eq(t(S.poisson("1/2").pmf(1)), "1/(2sqrt(e))");
});
test("stats: hypergeometric and discrete uniform", () => {
  const h = S.hypergeometric(50, 5, 10);
  eq(t(h.mean), "1"); eq(t(h.variance), "36/49");
  eq(t(h.pmf(1)), "45695/105938");
  const u = S.uniformDiscrete(1, 6);
  eq(t(u.pmf(3)), "1/6"); eq(t(u.cdf(4)), "2/3"); eq(t(u.mean), "7/2"); eq(t(u.variance), "35/12");
});

// ---------------- continuous distributions
test("stats: special functions", () => {
  close(S.erf(1), 0.8427007929497149, 1e-14);
  close(S.erf(-0.5), -0.5204998778130465, 1e-14);
  close(S.erfc(3), 2.209049699858544e-5, 1e-12);
  close(S.lgamma(10), Math.log(362880), 1e-13);
  close(S.betaI(2, 3, 0.4), 0.5248, 1e-13);
});
test("stats: normal distribution", () => {
  const n = S.normal(0, 1);
  close(n.cdf(1.96).number, 0.9750021048517795, 1e-13);
  close(n.cdf(-8).number, 6.22096057427178e-16, 1e-6);
  ok(n.cdf(0).method.includes("erfc"));
  close(n.quantile(0.975).number, 1.959963984540054, 1e-10);
  eq(t(n.pdf(0)), "sqrt(2)/(2sqrt(pi))");
  const m = S.normal(100, 15);
  close(m.cdf(130).number, 0.9772498680518208, 1e-12);
  eq(t(m.variance), "225");
});
test("stats: uniform and exponential are exact", () => {
  const u = S.uniform(2, 6);
  eq(t(u.cdf(3)), "1/4"); eq(t(u.cdf(10)), "1"); eq(t(u.pdf(4)), "1/4"); eq(t(u.mean), "4"); eq(t(u.variance), "4/3"); eq(t(u.quantile("1/2")), "4");
  const e = S.exponential("1/2");
  eq(t(e.cdf(2)), "-1/e + 1"); eq(t(e.mean), "2"); eq(t(e.variance), "4"); eq(t(e.pdf(0)), "1/2");
  close(evalFloat(S.exponential(1).quantile("1/2")), Math.log(2), 1e-15);
});
test("stats: t and chi-square tables", () => {
  close(S.studentT(10).quantile(0.975).number, 2.228138851986273, 1e-9);
  close(S.studentT(1).cdf(1).number, 0.75, 1e-12);
  close(S.chiSquare(3).quantile(0.95).number, 7.814727903251178, 1e-9);
  close(S.chiSquare(2).cdf(2).number, 1 - Math.exp(-1), 1e-13);
  eq(t(S.chiSquare(4).mean), "4"); eq(t(S.chiSquare(4).variance), "8");
});
test("stats: bisection quantile inverts the cdf", () => {
  for (const d of [S.normal(0, 1), S.studentT(5), S.chiSquare(7)])
    for (const p of [0.01, 0.2, 0.5, 0.9, 0.999]) close(d.cdfFloat(d.quantile(p).number), p, 1e-10);
  throws(() => S.normal().quantile(1));
});

// ---------------- descriptive
test("stats: descriptive statistics exact", () => {
  const d = [2, 4, 4, 4, 5, 5, 7, 9];
  eq(t(S.mean(d)), "5"); eq(t(S.median(d)), "9/2"); eq(S.mode(d).modes.map(t).join(), "4");
  eq(t(S.variance(d, { population: true })), "4"); eq(t(S.stdDev(d, { population: true })), "2");
  eq(t(S.variance(d)), "32/7"); eq(t(S.stdDev(d)), "4sqrt(14)/7");
  eq(t(S.range(d)), "7");
  eq(t(S.mean("0.1, 0.2")), "3/20");
  ok(S.mode([1, 2, 3]).noMode);
});
test("stats: quartiles by median of halves", () => {
  const q = S.quartiles([1, 2, 3, 4, 5, 6, 7, 8, 9]);
  eq(t(q.q1), "5/2"); eq(t(q.q2), "5"); eq(t(q.q3), "15/2");
  const q2 = S.quartiles([1, 2, 3, 4, 5, 6, 7, 8]);
  eq(t(q2.q1), "5/2"); eq(t(q2.q3), "13/2");
  eq(t(S.iqr([1, 2, 3, 4, 5, 6, 7, 8, 9])), "5");
  ok(q.method.includes("median-of-halves"));
});
test("stats: z-scores and summary", () => {
  eq(S.zScores([1, 2, 3]).map(t).join(), "-1,0,1");
  const s = S.summary([3, 1, 2]);
  eq(t(s.min), "1"); eq(t(s.max), "3"); eq(s.n, 3);
});
test("stats: covariance, correlation, regression", () => {
  const r = S.linearRegression([1, 2, 3, 4, 5], [2, 4, 5, 4, 5]);
  eq(t(r.slope), "3/5"); eq(t(r.intercept), "11/5"); eq(t(r.r2), "3/5"); eq(t(r.r), "sqrt(15)/5");
  eq(t(r.equation), "y = 3x/5 + 11/5");
  eq(t(S.correlation([1, 2, 3], [2, 4, 6])), "1");
  eq(t(S.correlation([1, 2, 3], [6, 4, 2])), "-1");
  eq(t(S.covariance([1, 2, 3], [2, 4, 7])), "5/2");
  throws(() => S.linearRegression([1, 1], [2, 3]));
});

// ---------------- inference
test("stats: confidence intervals", () => {
  const z = S.ciMean({ mean: 50, n: 25 }, { sigma: 10 });
  eq(z.method, "z");
  close(z.lower.number, 50 - 1.959963984540054 * 2, 1e-9);
  const tt = S.ciMean({ mean: 50, sd: 10, n: 25 });
  eq(tt.method, "t"); eq(tt.df, 24);
  close(tt.upper.number, 50 + 2.063898561628021 * 2, 1e-8);
  const p = S.ciProportion(40, 100);
  eq(t(p.center), "2/5");
  eq(t(p.standardError), "sqrt(6)/50");
  close(p.lower.number, 0.4 - 1.959963984540054 * Math.sqrt(0.0024), 1e-10);
});
test("stats: hypothesis tests", () => {
  const z = S.zTest({ mean: 105, n: 36 }, { mu0: 100, sigma: 15 });
  eq(t(z.statistic), "2"); close(z.pValue.number, 0.04550026389635842, 1e-12); eq(z.decision, "reject H0");
  const zr = S.zTest({ mean: 105, n: 36 }, { mu0: 100, sigma: 15, tail: "right" });
  close(zr.pValue.number, 0.02275013194817921, 1e-12);
  const tt = S.tTest([5.1, 4.9, 5.6, 5.8, 6.0, 5.2], { mu0: 5 });
  eq(tt.df, 5); eq(t(tt.statistic), "13sqrt(7)/14"); eq(tt.decision, "fail to reject H0");
  const c = S.chiSquareGOF([50, 30, 20], ["1/2", "1/4", "1/4"]);
  eq(t(c.statistic), "2"); eq(c.df, 2); close(c.pValue.number, Math.exp(-1), 1e-13);
  const tp = S.twoProportionZ(45, 100, 30, 100);
  eq(t(tp.statistic), "2sqrt(30)/5");
  close(tp.pValue.number, 2 * (1 - S.normal().cdfFloat(2 * Math.sqrt(30) / 5)), 1e-14);
  ok(tp.pValue.method.length > 0);
});

// ---------------- properties
test("property: binomial pmf sums to 1 exactly; mean and variance by summation", () => {
  const r = rng(31);
  for (let i = 0; i < 40; i++) {
    const n = r.int(0, 30), p = N.Q(BigInt(r.int(0, 20)), 20n);
    const b = S.binomial(n, p);
    let s = N.ZERO, m = N.ZERO, m2 = N.ZERO;
    for (let k = 0n; k <= BigInt(n); k++) {
      const v = b.pmfRational(k);
      s = N.add(s, v); m = N.add(m, N.mul(N.Q(k), v)); m2 = N.add(m2, N.mul(N.Q(k * k), v));
    }
    ok(N.isOne(s), "sum = 1");
    ok(N.eq(m, b.mean.v), "mean");
    ok(N.eq(N.sub(m2, N.mul(m, m)), b.variance.v), "variance");
  }
});
test("property: hypergeometric pmf sums to 1 with exact moments", () => {
  const r = rng(32);
  for (let i = 0; i < 40; i++) {
    const Np = r.int(1, 30), K = r.int(0, Np), n = r.int(0, Np);
    const h = S.hypergeometric(Np, K, n);
    let s = N.ZERO, m = N.ZERO, m2 = N.ZERO;
    for (let k = 0n; k <= BigInt(n); k++) {
      const v = h.pmfRational(k);
      s = N.add(s, v); m = N.add(m, N.mul(N.Q(k), v)); m2 = N.add(m2, N.mul(N.Q(k * k), v));
    }
    ok(N.isOne(s)); ok(N.eq(m, h.mean.v)); ok(N.eq(N.sub(m2, N.mul(m, m)), h.variance.v));
  }
});
test("property: geometric and Poisson cdf equal partial pmf sums", () => {
  const r = rng(33);
  for (let i = 0; i < 20; i++) {
    const g = S.geometric(N.Q(BigInt(r.int(1, 9)), 10n));
    const k = r.int(1, 15);
    let s = N.ZERO;
    for (let j = 1n; j <= BigInt(k); j++) s = N.add(s, g.pmfRational(j));
    ok(N.eq(s, g.cdf(k).v));
  }
  const p = S.poisson("5/2");
  const terms = [0, 1, 2, 3, 4].map((k) => p.pmf(k));
  ok(Zs(X.add(...terms)) === p.cdf(4));
});
test("property: variance formulas agree (definitional vs computational)", () => {
  const r = rng(34);
  for (let i = 0; i < 100; i++) {
    const n = r.int(2, 20);
    const d = Array.from({ length: n }, () => randRat(r, -50, 50));
    const mean = d.reduce(N.add, N.ZERO);
    const xbar = N.div(mean, N.Q(n));
    const sumsq = d.reduce((s, x) => N.add(s, N.mul(x, x)), N.ZERO);
    const comp = N.div(N.sub(sumsq, N.mul(N.Q(n), N.mul(xbar, xbar))), N.Q(n - 1));
    ok(N.eq(S.varianceR(d), comp), "sample");
    ok(N.eq(S.varianceR(d, { population: true }), N.div(N.mul(comp, N.Q(n - 1)), N.Q(n))), "population");
    // sd^2 = variance exactly
    ok(Zs(X.pow(S.stdDev(d), X.TWO)) === S.variance(d));
  }
});
test("property: regression r^2 equals r*r and residuals sum to zero", () => {
  const r = rng(35);
  for (let i = 0; i < 40; i++) {
    const n = r.int(3, 10);
    const xs = Array.from({ length: n }, (_, k) => N.Q(BigInt(k * 2 + r.int(0, 1))));
    const ys = Array.from({ length: n }, () => randRat(r, -20, 20, 4));
    let reg;
    try { reg = S.linearRegression(xs, ys); } catch (_) { continue; }
    if (reg.r) ok(Zs(X.pow(reg.r, X.TWO)) === reg.r2);
    let res = N.ZERO;
    for (let k = 0; k < n; k++) res = N.add(res, N.sub(ys[k], N.add(N.mul(reg.slope.v, xs[k]), reg.intercept.v)));
    ok(N.isZero(res));
  }
});
test("property: combinatorial identities", () => {
  for (let n = 0; n <= 15; n++) {
    let s2 = 0n, s1 = 0n;
    for (let k = 0; k <= n; k++) { s2 += S.stirling2(n, k); s1 += S.stirling1(n, k); }
    eq(s2, S.bell(n), "sum S2 = Bell");
    eq(s1, N.factorial(n), "sum c(n,k) = n!");
    for (let k = 1; k < n; k++) eq(S.nCr(n, k), S.nCr(n - 1, k - 1) + S.nCr(n - 1, k), "Pascal");
    let inc = 0n; // inclusion-exclusion for derangements
    for (let k = 0; k <= n; k++) inc += (k % 2 ? -1n : 1n) * S.nCr(n, k) * N.factorial(n - k);
    eq(inc, S.derangements(n));
  }
});
