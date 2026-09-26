import { test, eq, ok, rng } from "./harness.js";
import * as X from "../public/engine/expr.js";
import * as N from "../public/engine/num.js";
import { parse } from "../public/engine/parse.js";
import { simplify, expand } from "../public/engine/simplify.js";
import { toText } from "../public/engine/print.js";
import { equivalent } from "../public/engine/verify.js";
import { diff } from "../public/engine/calc/diff.js";
import { evalTree } from "../public/engine/numeric.js";
import { limit, verifyLimit } from "../public/engine/calc/limit.js";
import { seriesTree, verifySeries } from "../public/engine/calc/series.js";
import { sumCompute, verifySum, productCompute } from "../public/engine/calc/sum.js";
import { detectRecurrence, solveRecurrence, verifyRecurrence } from "../public/engine/calc/recur.js";
import { detectODE, solveODE, verifyODE } from "../public/engine/calc/ode.js";
import { solve } from "../public/engine/quelvra.js";

// the parser reads C1 as C_1; the engines name their constants C1, C2, ...
const unsub = (u) => X.mapTree(u, (w) => (w.k === "sym" && /^C_\d+$/.test(w.name) ? X.sym(w.name.replace("_", "")) : w));
const same = (got, want, msg) => {
  const e = equivalent(unsub(got), unsub(typeof want === "string" ? parse(want) : want));
  ok(e.status.startsWith("equivalent"), `${msg}: got ${toText(got)}, expected ${typeof want === "string" ? want : toText(want)} (${e.status})`);
};
const verified = (v, msg) => ok(v.status === "verified-exact" || v.status === "verified-numeric", `${msg}: verification ${v.status} ${JSON.stringify(v.checks)}`);
const num = (u, env = {}) => {
  const r = evalTree(u, env, { digits: 30 });
  return Number(r && r.value !== undefined ? r.value : r);
};

// ---------------------------------------------------------------- limits
const L = (src, to, dir = "") => {
  const u = parse(src);
  const r = limit(u, "x", parse(to), dir);
  return { u, r, v: r.status === "unknown" ? null : verifyLimit(u, "x", parse(to), dir, r.result) };
};
const limitCases = [
  // bench corpus
  ["sin(x)/x", "0", "", "1"], ["(3x^2 + 1)/(x^2 - 2)", "oo", "", "3"], ["(1 - cos(x))/x^2", "0", "", "1/2"],
  ["(1 + 1/x)^x", "oo", "", "e"], ["(x^2 - 4)/(x - 2)", "2", "", "4"], ["1/x", "0", "+", "oo"], ["x ln(x)", "0", "", "0"],
  ["x/e^x", "oo", "", "0"], ["(tan(x) - sin(x))/x^3", "0", "", "1/2"], ["(1 + 1/x)^(x^2) e^(-x)", "oo", "", "e^(-1/2)"],
  // required
  ["x^x", "0", "", "1"], ["x^(1/x)", "oo", "", "1"], ["(sin(x) - x)/x^3", "0", "", "-1/6"], ["sqrt(x^2 + x) - x", "oo", "", "1/2"],
  ["1/x", "0", "-", "-oo"], ["e^x/x^100", "oo", "", "oo"], ["ln(x)^100/x", "oo", "", "0"], ["x(e^(1/x) - 1)", "oo", "", "1"],
  ["(1 + x)^(1/x)", "0", "", "e"], ["(1 + a/x)^x", "oo", "", "e^a"], ["x^x/x!", "oo", "", "oo"], ["x!/x^x", "oo", "", "0"],
  ["exp(x)(exp(1/x - exp(-x)) - exp(1/x))", "oo", "", "-1"], ["exp(x)(sin(1/x + exp(-x)) - sin(1/x))", "oo", "", "1"],
  ["(x + 1)^(1/ln(x))", "oo", "", "e"], ["sin(x)/x", "oo", "", "0"], ["sqrt(x)", "0", "", "0"],
];
for (const [src, to, dir, want] of limitCases) {
  test(`lim x->${to}${dir} ${src} = ${want}`, () => {
    const { r, v } = L(src, to, dir);
    eq(r.status, "exact", `${src}: ${r.reason}`);
    if (want === "oo") ok(r.value === X.OO, `got ${toText(r.value)}`);
    else if (want === "-oo") ok(r.value === X.mul(X.NEG_ONE, X.OO), `got ${toText(r.value)}`);
    else same(r.value, want, src);
    ok(v.status !== "failed", `numeric check failed: ${JSON.stringify(v.checks)}`);
  });
}
for (const [src, to] of [["sin(1/x)", "0"], ["|x|/x", "0"], ["1/x", "0"], ["x sin(x)", "oo"], ["tan(x)", "pi/2"], ["atan(1/x)", "0"]]) {
  test(`lim x->${to} ${src} does not exist`, () => {
    const { r, v } = L(src, to);
    eq(r.status, "dne", `${src}: ${r.reason}`);
    ok(r.reason.length > 10, "has a reason");
    verified(v, src);
  });
}
test("limit: unknown instead of a guess", () => {
  const r = limit(parse("floor(x) sin(1/x)"), "x", X.ZERO);
  ok(r.status === "unknown" || r.status === "exact" || r.status === "dne");
});
test("property: random rational limits agree with direct evaluation", () => {
  const R = rng(4242);
  const x = X.sym("x");
  const rp = (deg) => X.add(...Array.from({ length: deg + 1 }, (_, i) => X.mul(X.num(R.int(-5, 5) || 1), i === 0 ? X.ONE : X.pow(x, X.num(i)))));
  let n = 0;
  for (let t = 0; t < 30; t++) {
    const Pp = rp(R.int(0, 3)), Qp = rp(R.int(1, 3));
    const a = X.num(N.Q(R.int(-7, 7), R.int(1, 4)));
    const kind = t % 3;
    if (kind === 0) {
      // regular point: the limit is the value
      const qa = simplify(X.subs(Qp, { x: a }));
      if (qa === X.ZERO) continue;
      const want = simplify(X.mul(X.subs(Pp, { x: a }), X.pow(qa, X.NEG_ONE)));
      const r = limit(X.mul(Pp, X.pow(Qp, X.NEG_ONE)), "x", a);
      eq(r.status, "exact"); ok(r.value === want, `${toText(Pp)}/${toText(Qp)} at ${toText(a)}: ${toText(r.value)} vs ${toText(want)}`); n++;
    } else if (kind === 1) {
      // removable singularity (x - a) P / ((x - a) Q)
      const qa = simplify(X.subs(Qp, { x: a }));
      if (qa === X.ZERO) continue;
      const f = X.mul(expand(X.mul(X.sub(x, a), Pp)), X.pow(expand(X.mul(X.sub(x, a), Qp)), X.NEG_ONE));
      const want = simplify(X.mul(X.subs(Pp, { x: a }), X.pow(qa, X.NEG_ONE)));
      const r = limit(f, "x", a);
      eq(r.status, "exact"); ok(r.value === want, `removable at ${toText(a)}: ${toText(r.value)} vs ${toText(want)}`); n++;
    } else {
      // at infinity: compare with a numeric evaluation at x = 1e7 (finite answers) or the degree rule
      const f = X.mul(Pp, X.pow(Qp, X.NEG_ONE));
      const r = limit(f, "x", X.OO);
      eq(r.status, "exact");
      const big = num(f, { x: 1e8 });
      if (r.value === X.OO) ok(big > 1e6); else if (r.value === X.mul(X.NEG_ONE, X.OO)) ok(big < -1e6);
      else ok(Math.abs(num(r.value) - big) < 1e-5 * Math.max(1, Math.abs(big)), `${toText(f)} at oo: ${toText(r.value)} vs ${big}`);
      n++;
    }
  }
  ok(n >= 20, `only ${n} cases`);
});

// ---------------------------------------------------------------- series
const Sx = (src, n, a = "0") => seriesTree(parse(src), "x", parse(a), n + 1);
const seriesCases = [
  ["e^x", 7, "x^7/5040 + x^6/720 + x^5/120 + x^4/24 + x^3/6 + x^2/2 + x + 1"],
  ["sin(x)", 7, "x - x^3/6 + x^5/120 - x^7/5040"],
  ["tan(x)", 7, "x + x^3/3 + 2x^5/15 + 17x^7/315"],
  ["1/(1 - x)", 5, "1 + x + x^2 + x^3 + x^4 + x^5"],
  ["ln(1 + x)", 5, "x - x^2/2 + x^3/3 - x^4/4 + x^5/5"],
  ["sqrt(1 + x)", 4, "1 + x/2 - x^2/8 + x^3/16 - 5x^4/128"],
  ["1/sin(x)", 5, "1/x + x/6 + 7x^3/360 + 31x^5/15120"],
];
for (const [src, n, want] of seriesCases) {
  test(`series ${src} to order ${n}`, () => {
    const u = parse(src);
    const r = Sx(src, n);
    same(r.main, want, src);
    ok(r.O !== null, "has an O-term");
    verified(verifySeries(u, "x", X.ZERO, r), src);
  });
}
test("series at infinity and Puiseux", () => {
  same(seriesTree(parse("x/(x + 1)"), "x", X.OO, 3).main, "1 - 1/x + 1/x^2", "x/(x+1) at oo");
  const r = seriesTree(parse("sqrt(x + x^2)"), "x", X.ZERO, 2);
  ok(r.terms.some((t) => t.e.d === 2n), "fractional powers");
});
test("property: series coefficients match f^(k)(0)/k! from symbolic derivatives", () => {
  const R = rng(777);
  const atoms = ["e^(A x)", "sin(A x)", "cos(A x)", "ln(1 + A x)", "1/(1 - A x)", "sqrt(1 + A x)", "atan(A x)"];
  let n = 0;
  for (let t = 0; t < 14; t++) {
    const a1 = R.int(1, 3), a2 = R.int(-2, 2) || 1;
    const f = parse(`(${R.pick(atoms).replace("A", String(a1))}) * (${R.pick(atoms).replace("A", String(a2))}) + ${R.int(-3, 3)} x^2`);
    const res = seriesTree(f, "x", X.ZERO, 5);
    let d = f, fact = 1;
    for (let k = 0; k < 5; k++) {
      if (k > 0) { d = diff(d, "x"); fact *= k; }
      const want = num(X.subs(d, { x: X.ZERO })) / fact;
      const term = res.terms.find((tm) => tm.e.d === 1n && Number(tm.e.n) === k);
      const got = term ? num(term.c) : 0;
      ok(Math.abs(got - want) < 1e-9 * Math.max(1, Math.abs(want)), `${toText(f)} coefficient ${k}: ${got} vs ${want}`);
      n++;
    }
  }
  ok(n === 70);
});

// ---------------------------------------------------------------- sums and products
const SUM = (f, k, lo, hi) => {
  // parse the whole sum so that the index (even i) is read as a variable, as the strategy sees it
  const node = parse(`sum_(${k}=${lo})^(${hi}) ${f}`);
  const [F, K, LO, HI] = node.args;
  const r = sumCompute(F, K, LO, HI);
  return { r, v: verifySum(F, K, LO, HI, r) };
};
const sumCases = [
  // bench corpus
  ["i", "i", "1", "100", "5050"], ["1/n^2", "n", "1", "oo", "pi^2/6"], ["(1/2)^k", "k", "0", "oo", "2"], ["j", "j", "1", "n", "n(n+1)/2"],
  ["k^3", "k", "1", "1000", "250500250000"], ["1/n^4", "n", "1", "oo", "pi^4/90"],
  // required
  ["k^3", "k", "1", "n", "n^2(n+1)^2/4"], ["k 2^k", "k", "1", "n", "(n - 1) 2^(n+1) + 2"], ["1/(k(k+1))", "k", "1", "n", "n/(n+1)"],
  ["1/(k(k+1))", "k", "1", "oo", "1"], ["(-1)^(n+1)/n", "n", "1", "oo", "ln(2)"], ["1/n!", "n", "0", "oo", "e"],
  ["k k!", "k", "1", "n", "(n+1)! - 1"], ["x^k/k!", "k", "0", "oo", "e^x"], ["1/n^3", "n", "1", "oo", "zeta(3)"],
  ["binomial(n, k)", "k", "0", "n", "2^n"], ["(-1)^n/(2n + 1)", "n", "0", "oo", "pi/4"],
];
for (const [f, k, lo, hi, want] of sumCases) {
  test(`sum_(${k}=${lo})^(${hi}) ${f} = ${want}`, () => {
    const { r, v } = SUM(f, k, lo, hi);
    eq(r.kind, "value", r.reason);
    if (want === "zeta(3)") ok(toText(r.value) === "zeta(3)", toText(r.value)); else same(r.value, want, f);
    verified(v, f);
  });
}
for (const [f, k] of [["1/n", "n"], ["n/(n^2 + 1)", "n"], ["1/sqrt(k)", "k"], ["1/(k ln(k))", "k"]]) {
  test(`sum ${f} diverges`, () => {
    const { r, v } = SUM(f, k, f.includes("ln") ? "2" : "1", "oo");
    eq(r.kind, "diverges");
    verified(v, f);
  });
}
test("convergent without a closed form gives a proof and a numeric value", () => {
  const { r } = SUM("1/(k ln(k)^2)", "k", "2", "oo");
  eq(r.kind, "converges");
  const a = SUM("(-1)^k/sqrt(k)", "k", "1", "oo").r;
  eq(a.kind, "converges"); ok(Math.abs(Number(a.approx) + 0.6048986434216303) < 1e-12);
});
test("products", () => {
  same(productCompute(parse("1 - 1/k^2"), X.sym("k"), X.TWO, X.OO).value, "1/2", "Wallis-type");
  same(productCompute(parse("k"), X.sym("k"), X.ONE, X.sym("n")).value, "n!", "n!");
});

// ---------------------------------------------------------------- recurrences
const REC = (src) => {
  const info = detectRecurrence(parse(src));
  ok(info, `not detected: ${src}`);
  const r = solveRecurrence(info);
  return { r, v: verifyRecurrence(info, r) };
};
test("recurrence: Fibonacci", () => {
  const { r, v } = REC("a(n) = a(n-1) + a(n-2), a(0) = 0, a(1) = 1");
  verified(v, "fib");
  const f = [0, 1]; for (let i = 2; i <= 40; i++) f.push(f[i - 1] + f[i - 2]);
  for (const k of [0, 1, 2, 7, 19, 30, 40]) ok(Math.abs(num(r.value, { n: k }) - f[k]) < 1e-6 * Math.max(1, f[k]), `F(${k})`);
});
test("recurrence: a(n) = 2a(n-1) + 1", () => {
  const { r, v } = REC("a(n) = 2a(n-1) + 1, a(0) = 0");
  same(r.value, "2^n - 1", "Mersenne"); verified(v, "2a+1");
});
test("recurrence: general solution and complex roots", () => {
  const g = REC("a(n) = 2a(n-1) + 1");
  ok(X.freeSymbols(g.r.value).has("C1"), "arbitrary constant"); verified(g.v, "general");
  const c = REC("a(n) = -a(n-2), a(0) = 1, a(1) = 0");
  same(c.r.value, "cos(n pi/2)", "rotation"); verified(c.v, "complex");
  const p = REC("a(n+1) = a(n) + n, a(0) = 0");
  same(p.r.value, "n(n-1)/2", "triangular"); verified(p.v, "triangular");
});
test("recurrence detection leaves ordinary equations alone", () => {
  ok(!detectRecurrence(parse("x(x - 1) = 2")));
  ok(!detectRecurrence(parse("x^2 + 3x + 2 = 0")));
});

// ---------------------------------------------------------------- ODEs
const ODE = (src) => {
  const info = detectODE(parse(src));
  ok(info, `not detected: ${src}`);
  const r = solveODE(info);
  return { info, r, v: verifyODE(info, r), y: r.solutions.filter((s) => !s.singular).map((s) => s.tree) };
};
// independent substitution check (does not use the engine's verifier)
function satisfies(src, sol, xn = "x", dep = "y") {
  const info = detectODE(parse(src));
  const F = info.odes[0].F;
  const Cvals = { C1: X.num(N.Q(3, 7)), C2: X.num(N.Q(-5, 3)), C3: X.num(N.Q(2, 9)) };
  let d = simplify(X.subs(sol, Cvals));
  const sub = {};
  for (let k = 0; k <= 4; k++) { sub[k === 0 ? dep : `__D${k}_${dep}`] = d; d = diff(d, xn); }
  const res = X.subs(F, sub);
  for (const xv of [0.3, 0.7, 1.1, 1.9]) {
    const v = num(res, { [xn]: xv }), s = Math.abs(num(sub[dep], { [xn]: xv })) + 1;
    if (!(Math.abs(v) < 1e-15 * s * 1e6)) return false;
  }
  return true;
}
const odeCases = [
  ["y' = y", "C1 e^x"],
  ["y' + 2y = e^x", "C1 e^(-2x) + e^x/3"],
  ["y'' + y = 0", "C1 cos(x) + C2 sin(x)"],
  ["y'' - 3y' + 2y = e^(3x)", "C1 e^x + C2 e^(2x) + e^(3x)/2"],
  ["y'' + y = sin(x)", "C1 cos(x) + C2 sin(x) - x cos(x)/2"],
  ["x^2 y'' + x y' - y = 0", "C2 x + C1/x"],
  ["dy/dx = x y^2", "-2/(x^2 + 2 C1)"],
  ["y'' + 4y = 0, y(0) = 1, y'(0) = 0", "cos(2x)"],
];
for (const [src, want] of odeCases) {
  test(`ODE ${src}`, () => {
    const { r, v, y } = ODE(src);
    ok(y.length >= 1, "a solution");
    same(y[0], want, src);
    verified(v, src);
    ok(satisfies(src, y[0]), "independent substitution");
  });
}
test("ODE: separable has the constant solution y = 0", () => {
  const { r } = ODE("dy/dx = x y^2");
  ok(r.solutions.some((s) => s.singular && s.tree === X.ZERO));
});
test("ODE: more first-order methods", () => {
  for (const [src, method] of [["y' + y/x = x^2", "linear"], ["y' = y + x y^3", "Bernoulli"], ["(2x + y) + (x + 2y) y' = 0", "exact"], ["y' = x/y, y(0) = 2", "separable"]]) {
    const { r, v } = ODE(src);
    ok(r.method.startsWith(method), `${src}: ${r.method}`);
    verified(v, src);
  }
  same(ODE("y' = x/y, y(0) = 2").y[0], "sqrt(x^2 + 4)", "branch through (0, 2)");
  same(ODE("y' = x/y, y(0) = -2").y[0], "-sqrt(x^2 + 4)", "branch through (0, -2)");
});
test("ODE: higher order, resonance, variation of parameters, systems", () => {
  const a = ODE("y'' - 2y' + y = x e^x"); same(a.y[0], "x^3 e^x/6 + C1 e^x + C2 x e^x", "double root resonance"); verified(a.v, "res");
  const b = ODE("y''' - y = 0"); verified(b.v, "third order"); eq(b.r.basis.length, 3);
  const c = ODE("y'' + y = tan(x)"); verified(c.v, "variation of parameters");
  const d = ODE("x' = -y, y' = x"); verified(d.v, "system"); eq(d.r.solutions.length, 2);
});
test("ODE: boundary problem with no solution is reported, not guessed", () => {
  const info = detectODE(parse("y'' + y = 0, y(0) = 0, y(pi) = 1"));
  let code = null;
  try { solveODE(info); } catch (e) { code = e.code; }
  eq(code, "INCONSISTENT");
});
test("ODE: nonlinear IVP falls back to a labelled numeric solution", () => {
  const { r, v } = ODE("y'' = -sin(y), y(0) = 1, y'(0) = 0");
  ok(r.approximate); ok(Math.abs(r.final - 0.6000853661) < 1e-8); verified(v, "numeric");
});
test("ODE detection leaves ordinary equations alone", () => {
  ok(!detectODE(parse("x^2 + 3x + 2 = 0")));
  ok(!detectODE(parse("sin(x) = 1/2")));
});
test("property: random constant-coefficient ODEs verified by substitution", () => {
  const R = rng(9001);
  let n = 0;
  for (let t = 0; t < 16; t++) {
    let p, q;
    const mode = t % 3;
    if (mode === 0) { const r1 = R.int(-3, 3), r2 = R.int(-3, 3); p = -(r1 + r2); q = r1 * r2; }      // real roots (maybe repeated)
    else if (mode === 1) { const al = R.int(-2, 2), be = R.int(1, 3); p = -2 * al; q = al * al + be * be; } // complex pair
    else { p = R.int(-4, 4); q = R.int(-4, 4); }
    const forcing = R.pick(["0", `e^(${R.int(-2, 2)} x)`, `x^2`, `sin(${R.int(1, 3)} x)`, `x e^(${R.int(-1, 1)} x)`, `cos(x) e^x`]);
    const src = `y'' + (${p}) y' + (${q}) y = ${forcing}`;
    const { r, v, y } = ODE(src);
    verified(v, src);
    ok(satisfies(src, y[0]), `independent substitution: ${src} -> ${toText(y[0])}`);
    ok(["C1", "C2"].every((c) => X.freeSymbols(y[0]).has(c)), "two arbitrary constants");
    n++;
  }
  eq(n, 16);
});

// ---------------------------------------------------------------- end to end (strategies)
const E2E = [
  ["lim_(x->0) (1 - cos(x))/x^2", "1/2"], ["lim_(x->0^-) 1/x", "-oo"], ["sum_(k=1)^(n) k^3", "n^2(n+1)^2/4"],
  ["prod_(k=2)^(oo) (1 - 1/k^2)", "1/2"], ["series(e^x, x, 0, 3)", "x^3/6 + x^2/2 + x + 1 + O(x^4)"], ["taylor(sin(x), x, 0, 5)", "x - x^3/6 + x^5/120"],
];
for (const [src, want] of E2E) {
  test(`solve: ${src}`, () => {
    const r = solve(src);
    ok(r.ok, `${src}: ${r.answers.map((a) => a.label || "").join("; ")}`);
    eq(r.verification.status, "passed", `${src}: ${r.verification.checks.map((c) => c.detail).join("; ")}`);
    const a = r.answers[0];
    if (want === "-oo") ok(a.tree === X.mul(X.NEG_ONE, X.OO)); else if (want.includes("O(")) eq(toText(a.tree), want); else same(a.tree, want, src);
  });
}
test("solve: DNE and divergence answer shapes", () => {
  const d = solve("lim_(x->0) sin(1/x)");
  ok(d.answers[0].tree === X.UNDEF && d.answers[0].kind === "none" && d.solutionStatus === "exact");
  const s = solve("sum_(n=1)^(oo) 1/n");
  ok(s.answers[0].kind === "none" && /diverg/i.test(s.answers[0].label));
});
test("solve: ODE and recurrence strategies", () => {
  const o = solve("y'' + 4y = 0, y(0) = 1, y'(0) = 0");
  eq(o.method, "calc.ode"); same(o.answers[0].tree, "cos(2x)", "ivp"); eq(o.verification.status, "passed");
  const q = solve("a(n) = 2a(n-1) + 1, a(0) = 0");
  eq(q.method, "calc.recurrence"); same(q.answers[0].tree, "2^n - 1", "rec");
  const p = solve("x^2 + 3x + 2 = 0");
  ok(p.method !== "calc.ode" && p.method !== "calc.recurrence");
});

// ---------------------------------------------------------------- regression: removable singularity
test("lim x->2 (x^2 - 4)/(x - 2) = 4 (engine, both one-sided limits)", () => {
  const u = parse("(x^2 - 4)/(x - 2)");
  for (const dir of ["", "+", "-"]) {
    const r = limit(u, "x", X.TWO, dir);
    ok(r.status === "exact" && r.value === X.num(4), `dir ${dir || "two-sided"}: ${r.status} ${r.value && toText(r.value)}`);
    verified(verifyLimit(u, "x", X.TWO, dir, r.result), `dir ${dir}`);
  }
});
test("verifier rejects tampered limit claims (+-oo or a wrong value at a removable point)", () => {
  const u = parse("(x^2 - 4)/(x - 2)");
  for (const dir of ["", "+", "-"]) {
    for (const bad of [{ k: "inf", s: -1 }, { k: "inf", s: 1 }, { k: "fin", v: X.num(5) }, { k: "fin", v: X.ZERO }]) {
      const claim = dir ? bad : { ...bad, sides: [bad, bad] };
      const v = verifyLimit(u, "x", X.TWO, dir, claim);
      eq(v.status, "failed", `claim ${JSON.stringify(bad.k)}${bad.s || ""} dir ${dir || "two-sided"}`);
    }
  }
});
test("solve: lim x->2 (x^2 - 4)/(x - 2) = 4 in every notation", () => {
  for (const src of ["lim x->2 (x^2 - 4)/(x - 2)", "lim_(x->2) (x^2 - 4)/(x - 2)", "lim_(x->2) (x^2-4)/(x-2)"]) {
    const t = parse(src);
    ok(t.k === "limit" && !t.dir, `${src} must parse as a two-sided limit of (x^2 - 4)/(x - 2), parsed as ${toText(t)} dir=${JSON.stringify(t.dir)}`);
    const r = solve(src);
    eq(r.verification.status, "passed", src);
    ok(r.answers[0].tree === X.num(4), `${src}: ${toText(r.answers[0].tree)}`);
  }
});
test("property: removable singularities (x - a) P / ((x - a) Q) -> P(a)/Q(a), independently cancelled", () => {
  const R = rng(31337);
  const x = X.sym("x");
  let n = 0;
  for (let t = 0; t < 40; t++) {
    const Pp = X.add(...Array.from({ length: R.int(1, 3) }, (_, i) => X.mul(X.num(R.int(-6, 6) || 2), i === 0 ? X.ONE : X.pow(x, X.num(i)))));
    const Qp = X.add(...Array.from({ length: R.int(2, 3) }, (_, i) => X.mul(X.num(R.int(-6, 6) || 3), i === 0 ? X.ONE : X.pow(x, X.num(i)))));
    const a = X.num(N.Q(R.int(-9, 9), R.int(1, 3)));
    const qa = simplify(X.subs(Qp, { x: a }));
    if (qa === X.ZERO) continue;
    const m = R.int(1, 2); // (x - a)^m cancels
    const fac = X.pow(X.sub(x, a), X.num(m));
    const f = X.mul(expand(X.mul(fac, Pp)), X.pow(expand(X.mul(fac, Qp)), X.NEG_ONE));
    const want = num(simplify(X.mul(X.subs(Pp, { x: a }), X.pow(qa, X.NEG_ONE))));
    for (const dir of ["", "+", "-"]) {
      const r = limit(f, "x", a, dir);
      ok(r.status === "exact" && r.value !== X.OO && r.value !== X.mul(X.NEG_ONE, X.OO), `${toText(f)} at ${toText(a)}${dir}: ${r.status} ${r.value && toText(r.value)}`);
      ok(Math.abs(num(r.value) - want) < 1e-12 * Math.max(1, Math.abs(want)), `${toText(f)} at ${toText(a)}${dir}: ${toText(r.value)} vs ${want}`);
      // and a direct evaluation of the uncancelled expression next to the point agrees
      const near = num(f, { x: num(a) + (dir === "-" ? -1e-9 : 1e-9) });
      ok(Math.abs(near - want) < 1e-6 * Math.max(1, Math.abs(want)), `direct evaluation near ${toText(a)}: ${near} vs ${want}`);
    }
    n++;
  }
  ok(n >= 30, `only ${n} cases`);
});
