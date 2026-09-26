// Tests for the Quelvra solvers (engine/solve/*, engine/strategies/solve.js).
import { test, eq, ok, close, rng } from "./harness.js";
import "../public/engine/strategies/basic.js";
import "../public/engine/strategies/solve.js";
import { solve } from "../public/engine/orchestrate.js";
import { parse } from "../public/engine/parse.js";
import { toText } from "../public/engine/print.js";
import { evalC, truth } from "../public/engine/verify.js";
import * as X from "../public/engine/expr.js";
import { groebner, GPoly } from "../public/engine/solve/groebner.js";
import { lambertWBig } from "../public/engine/solve/lambertw.js";
import * as P from "../public/engine/poly.js";

const S = (s, o = {}) => solve(typeof s === "string" ? s : s, o);
const val = (a) => (a.tree && !a.closedForm ? evalC(a.tree, {}, "complex").re : parseFloat(a.approx.value));
const roots = (r) => r.answers.filter((a) => a.kind === "exact" || a.kind === "approx").map(val).sort((p, q) => p - q);
const noSol = (r) => !!(r.noSolution || (r.extra && r.extra.noSolution));
const passed = (r) => r.verification && r.verification.status === "passed";
const near = (a, b, tol = 1e-9) => Math.abs(a - b) <= tol * Math.max(1, Math.abs(b));
function sameRoots(got, want, tol = 1e-9) {
  const w = want.slice().sort((p, q) => p - q);
  if (got.length !== w.length) return false;
  return got.every((g, i) => near(g, w[i], tol));
}
const rejectedValues = (r) => r.rejected.map((q) => (q.value && q.value.k ? evalC(q.value, {}, "complex").re : parseFloat(q.value)));
const setAns = (r) => r.answers.find((a) => a.kind === "set" || a.kind === "all");
function sameSet(r, x, wantFn, lo = -12, hi = 12) {
  const a = setAns(r);
  if (!a) return false;
  for (let i = 0; i <= 2400; i++) {
    const t = lo + ((hi - lo) * i) / 2400 + 1e-7;
    const w = wantFn(t);
    if (w === null) continue;
    const g = a.tree === X.TRUE ? true : truth(a.tree, { [x]: t }, "real", 1e-14) === true;
    if (g !== w) return false;
  }
  return true;
}

// ---------------------------------------------------------------- adversarial equations
test("sqrt(x+7) = x - 5 -> {9}, 2 rejected as extraneous", () => {
  const r = S("sqrt(x+7) = x - 5");
  ok(passed(r), "verified");
  ok(sameRoots(roots(r), [9]));
  ok(rejectedValues(r).some((v) => near(v, 2)), "x = 2 listed as rejected");
});
test("x^2/(x-2) = 4/(x-2) -> exactly {-2}; x = 2 rejected (zero denominator)", () => {
  const r = S("x^2/(x-2) = 4/(x-2)");
  ok(passed(r));
  ok(sameRoots(roots(r), [-2]));
  ok(!noSol(r));
  const rej = r.rejected.find((q) => near(evalC(q.value, {}, "complex").re, 2));
  ok(rej && /denominator/.test(rej.reason), "2 rejected because it zeroes the denominator");
});
test("|x^2 - 4| = x + 2 -> {-2, 1, 3}", () => {
  const r = S("|x^2 - 4| = x + 2");
  ok(passed(r));
  ok(sameRoots(roots(r), [-2, 1, 3]));
});
test("x^3 - 3x + 1 = 0: casus irreducibilis in real trig form", () => {
  const r = S("x^3 - 3x + 1 = 0");
  ok(passed(r));
  ok(sameRoots(roots(r), [2 * Math.cos(2 * Math.PI / 9), 2 * Math.cos(4 * Math.PI / 9), 2 * Math.cos(8 * Math.PI / 9)]));
  ok(r.answers.every((a) => a.kind === "exact" && /cos/.test(toText(a.tree))), "exact cosine form");
  ok(r.verification.checks.some((c) => c.name === "completeness" && /Sturm/.test(c.detail)));
});
test("2^x = x^2 -> 2, 4 (exact) and -0.766664695962123...", () => {
  const r = S("2^x = x^2");
  ok(passed(r));
  ok(sameRoots(roots(r), [2, 4, -0.766664695962123], 1e-12));
  const ex = r.answers.filter((a) => a.kind === "exact").map((a) => toText(a.tree)).sort();
  eq(ex.join(","), "2,4");
  const w = r.answers.find((a) => a.kind === "approx");
  ok(w.approx.value.startsWith("-0.76666469596212309311"), "20 correct digits");
  ok(w.closedForm && /W/.test(toText(w.closedForm)), "Lambert W closed form attached");
});
test("log_x(4) = 2 -> {2}", () => { const r = S("log_x(4) = 2"); ok(passed(r)); ok(sameRoots(roots(r), [2])); });
test("x^x = 4 -> {2}", () => { const r = S("x^x = 4"); ok(passed(r)); ok(sameRoots(roots(r), [2])); eq(toText(r.answers[0].tree), "2"); });
test("sin(x) = x/10 -> 7 certified roots, completeness proven", () => {
  const r = S("sin(x) = x/10");
  ok(passed(r));
  const g = roots(r);
  eq(g.length, 7);
  ok(sameRoots(g, [-8.423203932360492, -7.068174358095817, -2.852341894450092, 0, 2.852341894450092, 7.068174358095817, 8.423203932360492], 1e-12));
  ok(r.verification.checks.some((c) => c.name === "completeness" && c.passed && /every real root/.test(c.detail)));
  ok(r.verification.checks.some((c) => c.name === "cross-check" && c.passed));
});
test("x^4 - 10x^2 + 1 = 0 -> +-(sqrt3 +- sqrt2), exact radicals", () => {
  const r = S("x^4 - 10x^2 + 1 = 0");
  ok(passed(r));
  const s3 = Math.sqrt(3), s2 = Math.sqrt(2);
  ok(sameRoots(roots(r), [s3 + s2, s3 - s2, s2 - s3, -s3 - s2]));
  ok(r.answers.every((a) => a.kind === "exact" && /sqrt/.test(toText(a.tree))));
});
test("parametric a x^2 + x + 1 = 0: generic roots with conditions + a = 0 case", () => {
  const r = S("a x^2 + x + 1 = 0", { variable: "x" });
  ok(passed(r));
  const ex = r.answers.filter((a) => a.kind === "exact");
  eq(ex.length, 2);
  ok(ex.every((a) => a.condition), "conditions attached");
  const c0 = r.answers.find((a) => a.kind === "case" && /a = 0/.test(a.label));
  ok(c0 && /x = -1/.test(c0.label), "a = 0 gives the linear root -1");
  ok(r.answers.some((a) => a.kind === "case" && a.none), "negative-discriminant case listed");
});
test("linear parametric a x = b: three cases", () => {
  const r = S("a x = b", { variable: "x" });
  ok(passed(r));
  eq(toText(r.answers[0].tree), "b/a");
  ok(r.answers.some((a) => a.kind === "case" && a.all), "a = 0, b = 0: every x");
  ok(r.answers.some((a) => a.kind === "case" && a.none), "a = 0, b != 0: none");
});
test("identity and contradiction", () => {
  const a = S("2(x+1) = 2x + 2");
  eq(a.answers[0].kind, "all");
  ok(passed(a));
  const b = S("x + 1 = x + 2");
  ok(noSol(b));
  eq(b.answers[0].kind, "none");
  const c = S("(x^2-1)/(x-1) = x + 1");
  eq(c.answers[0].kind, "all");
  ok(c.answers[0].excluded.some((z) => toText(z) === "1"), "x = 1 excluded");
});

// ---------------------------------------------------------------- more equation families
test("quadratic, rational, radical, nested radical", () => {
  ok(sameRoots(roots(S("2x^2 + 3x - 2 = 0")), [0.5, -2]));
  const r = S("1/x + 1/2 = 1"); ok(passed(r)); ok(sameRoots(roots(r), [2]));
  const n = S("x/(x-1) = 1/(x-1)"); ok(noSol(n)); ok(rejectedValues(n).some((v) => near(v, 1)));
  ok(sameRoots(roots(S("sqrt(x+5) - sqrt(x) = 1")), [4]));
  const nest = S("sqrt(1 + sqrt(x)) = 2"); ok(passed(nest)); ok(sameRoots(roots(nest), [9]));
  const cr = S("cbrt(x - 1) = x - 1"); ok(passed(cr)); ok(sameRoots(roots(cr), [0, 1, 2]));
  ok(noSol(S("sqrt(x) = -1")));
});
test("exponential and logarithmic", () => {
  ok(sameRoots(roots(S("4^x - 3*2^x + 2 = 0")), [0, 1]));
  ok(sameRoots(roots(S("3^(2x-1) = 27")), [2]));
  const m = S("2^x = 3^(x-1)"); ok(passed(m)); ok(sameRoots(roots(m), [Math.log(3) / (Math.log(3) - Math.log(2))]));
  const l = S("log_2(x) + log_2(x - 2) = 3"); ok(passed(l)); ok(sameRoots(roots(l), [4])); ok(rejectedValues(l).some((v) => near(v, -2)));
  ok(sameRoots(roots(S("e^(2x) - 5e^x + 6 = 0")), [Math.log(2), Math.log(3)]));
  ok(noSol(S("2^x = -3")));
});
test("Lambert W: x e^x = 1 is W(1)", () => {
  const r = S("x e^x = 1");
  ok(passed(r));
  const a = r.answers[0];
  eq(toText(a.closedForm), "W(1)");
  close(parseFloat(a.approx.value), 0.5671432904097838, 1e-15);
  ok(a.approx.value.startsWith("0.567143290409783873"), "18 digits of the omega constant");
  const w = lambertWBig("-0.34657359027997265470861606072908828403775006718", -1, 25);
  ok(w.certified && w.value.startsWith("-1.386294361119890618834"), "W-1(-ln2/2) = -2 ln 2");
});
test("hyperbolic and transcendental numerics", () => {
  ok(sameRoots(roots(S("cosh(x) = 2")), [Math.acosh(2), -Math.acosh(2)]));
  ok(sameRoots(roots(S("sinh(x) = 1")), [Math.asinh(1)]));
  const c = S("x = cos(x)"); ok(passed(c)); ok(sameRoots(roots(c), [0.7390851332151607], 1e-14));
  const e = S("e^x = 3 - x"); ok(passed(e)); ok(sameRoots(roots(e), [0.792059968430677], 1e-12));
});
test("degree 5: certified approximation + exact Sturm count", () => {
  const r = S("x^5 - x - 1 = 0");
  ok(passed(r));
  eq(r.solutionStatus, "approximate");
  const a = r.answers[0];
  ok(a.approx.value.startsWith("1.167303978261418684"), "18 digits");
  ok(r.verification.checks.some((c) => c.name === "completeness" && /exactly 1 distinct real root/.test(c.detail)));
});

// ---------------------------------------------------------------- trigonometric
function inFamilies(r, t) {
  return r.answers.some((a) => {
    if (a.kind !== "general") return false;
    for (let k = -6; k <= 6; k++) if (Math.abs(evalC(a.tree, { k }, "real").re - t) < 1e-9) return true;
    return false;
  });
}
test("trig: general solutions with integer k", () => {
  const r = S("sin(x) = 1/2");
  ok(passed(r));
  ok(inFamilies(r, Math.PI / 6) && inFamilies(r, 5 * Math.PI / 6) && inFamilies(r, Math.PI / 6 + 2 * Math.PI));
  ok(!inFamilies(r, -Math.PI / 6));
  ok(r.answers.every((a) => a.param === "k"));
  const t = S("tan(x) = 1"); eq(t.answers.length, 1); ok(inFamilies(t, Math.PI / 4 + Math.PI));
  ok(noSol(S("sin(x) = 2")));
});
test("trig: quadratic in sin, multiple angles, products, R-form", () => {
  const q = S("2sin(x)^2 - sin(x) - 1 = 0");
  ok(passed(q));
  for (const t of [Math.PI / 2, 7 * Math.PI / 6, -Math.PI / 6]) ok(inFamilies(q, t), "contains " + t);
  ok(!inFamilies(q, 0));
  const m = S("sin(2x) = sin(x)");
  for (const t of [0, Math.PI, Math.PI / 3, -Math.PI / 3]) ok(inFamilies(m, t));
  ok(!inFamilies(m, Math.PI / 2));
  const rf = S("sin(x) + cos(x) = 1");
  for (const t of [0, Math.PI / 2, 2 * Math.PI]) ok(inFamilies(rf, t));
  ok(!inFamilies(rf, Math.PI));
  const p = S("sin(x) cos(x) = 0");
  for (const t of [0, Math.PI / 2, Math.PI, 3 * Math.PI / 2]) ok(inFamilies(p, t));
  const ma = S("cos(3x) = 0");
  for (const t of [Math.PI / 6, Math.PI / 2, 5 * Math.PI / 6]) ok(inFamilies(ma, t));
});
test("trig: principal solutions with options.interval", () => {
  const r = S("sin(x) = 1/2", { interval: [0, 2 * Math.PI] });
  ok(passed(r));
  ok(sameRoots(roots(r), [Math.PI / 6, 5 * Math.PI / 6]));
  const c = S("cos(2x) = 1", { interval: [0, 7] });
  ok(sameRoots(roots(c), [0, Math.PI, 2 * Math.PI]));
  // the float 2 * Math.PI is slightly below 2pi, so 2pi is correctly excluded (exact edge comparison)
  ok(sameRoots(roots(S("sin(x) = 0", { interval: [0, 2 * Math.PI] })), [0, Math.PI]));
  const q = S("x^2 = 2", { interval: [0, 5] }); ok(passed(q)); ok(sameRoots(roots(q), [Math.SQRT2]));
});

// ---------------------------------------------------------------- inequalities
test("(x-1)^2 (x+2) > 0", () => {
  const r = S("(x-1)^2 (x+2) > 0");
  ok(passed(r));
  ok(sameSet(r, "x", (t) => (Math.abs(t - 1) < 1e-6 ? null : (t - 1) ** 2 * (t + 2) > 0)));
  ok(truth(setAns(r).tree, { x: 1 }) === false, "x = 1 excluded");
  eq(setAns(r).interval.length, 2);
  ok(setAns(r).interval.every((iv) => iv.loOpen && iv.hiOpen));
});
test("1/(x-1) < 1/(x+1) -> -1 < x < 1", () => {
  const r = S("1/(x-1) < 1/(x+1)");
  ok(passed(r));
  ok(sameSet(r, "x", (t) => (Math.abs(t - 1) < 1e-9 || Math.abs(t + 1) < 1e-9 ? null : t > -1 && t < 1)));
  eq(toText(setAns(r).tree), "-1 < x < 1");
});
test("(x+1)/(x-1) > 2 -> 1 < x < 3 (oracle)", () => {
  const r = S("(x+1)/(x-1) > 2");
  ok(passed(r));
  eq(toText(setAns(r).tree), "1 < x < 3");
});
test("inequalities: abs, radical, exp/log, compound, chained, closed ends", () => {
  ok(sameSet(S("|x - 1| < 3"), "x", (t) => Math.abs(t - 1) < 3));
  const rad = S("sqrt(x) > x - 2"); ok(passed(rad)); ok(sameSet(rad, "x", (t) => (t < 0 ? false : Math.sqrt(t) > t - 2)));
  eq(toText(setAns(rad).tree), "0 <= x < 4");
  eq(toText(setAns(S("e^x > 2")).tree), "ln(2) < x");
  const ln = S("ln(x) < 1"); ok(sameSet(ln, "x", (t) => t > 0 && t < Math.E));
  const ch = S("-1 < 2x+1 <= 5"); ok(passed(ch)); eq(toText(setAns(ch).tree), "-1 < x <= 2");
  const cmp = S("x^2 < 4 and x > 0"); ok(sameSet(cmp, "x", (t) => t * t < 4 && t > 0));
  const or = S("x < -1 or x > 2"); ok(sameSet(or, "x", (t) => t < -1 || t > 2));
  const cl = S("(x-1)/(x+2) >= 0"); ok(sameSet(cl, "x", (t) => (Math.abs(t + 2) < 1e-9 ? null : (t - 1) / (t + 2) >= 0)));
  ok(setAns(cl).interval.some((iv) => !iv.loOpen), "closed at x = 1");
  const none = S("x^2 + 1 < 0"); eq(setAns(none).tree, X.FALSE); ok(noSol(none));
  eq(setAns(S("(x-1)^2 >= 0")).tree, X.TRUE);
  eq(toText(setAns(S("x != 3")).tree), "x != 3");
});
test("inequality with a Lambert-W endpoint: 2^x > x^2", () => {
  const r = S("2^x > x^2");
  ok(passed(r));
  ok(sameSet(r, "x", (t) => (Math.abs(t + 0.766664695962123) < 1e-9 ? null : 2 ** t > t * t)));
  eq(r.solutionStatus, "approximate");
});
test("parametric linear inequality a x > b: sign cases", () => {
  const r = S("a x > b", { variable: "x" });
  ok(passed(r));
  ok(r.answers.some((a) => a.condition && /a > 0/.test(toText(a.condition))));
});

// ---------------------------------------------------------------- systems
test("x^2 + y^2 = 5, x y = 2 -> (1,2),(2,1),(-1,-2),(-2,-1) (oracle)", () => {
  const r = S("x^2+y^2=5, x y = 2");
  ok(passed(r));
  const sols = r.answers.filter((a) => a.kind === "solution").map((a) => a.values.map(([, t]) => toText(t)).join(",")).sort();
  eq(sols.join(" "), "-1,-2 -2,-1 1,2 2,1");
});
test("3x3 nonlinear system via Groebner basis", () => {
  const r = S("x + y + z = 6, x y + y z + z x = 11, x y z = 6");
  ok(passed(r));
  eq(r.method, "solve.polysys");
  const sols = r.answers.filter((a) => a.kind === "solution").map((a) => a.values.map(([, t]) => toText(t)).join(",")).sort();
  eq(sols.join(" "), "1,2,3 1,3,2 2,1,3 2,3,1 3,1,2 3,2,1");
  ok(r.steps.some((s) => s.rule === "solve.polysys.groebner"));
});
test("linear systems: unique, inconsistent, underdetermined", () => {
  const u = S("2x + y = 5, x - y = 1");
  ok(passed(u));
  eq(u.answers[0].values.map(([k, t]) => k + "=" + toText(t)).join(","), "x=2,y=1");
  ok(u.verification.checks.some((c) => c.name === "cross-check" && c.passed));
  const n = S("x + y = 2, 2x + 2y = 5");
  ok(noSol(n)); ok(passed(n)); eq(n.answers[0].kind, "none");
  const f = S("x + y + z = 1, x - y = 2");
  ok(passed(f));
  eq(f.answers[0].kind, "family");
  eq(f.answers[0].params.join(","), "t1");
  // the bench corpus lists (1, 1, 3) for x + y + z = 6, x - y = 0, 2x + z = 5, but 1 + 1 + 3 = 5: inconsistent
  ok(noSol(S("x + y + z = 6, x - y = 0, 2x + z = 5")));
});
test("nonlinear systems: real filtering, substitution, no solution", () => {
  const r = S("x^2 + y^2 = 25, y = x + 1");
  eq(r.answers.filter((a) => a.kind === "solution").length, 2);
  const c = S("x^2 + y^2 = -1, x = y"); ok(noSol(c));
  const i = S("x^2 + y^2 = 1, x^2 + y^2 = 4"); ok(noSol(i));
  const e = S("y = e^x, y = 2"); ok(passed(e)); eq(toText(e.answers[0].values.find(([k]) => k === "x")[1]), "ln(2)");
});
test("Groebner basis: reduced lex basis of a known ideal", () => {
  const vars = ["x", "y"];
  const F = ["x^2 + y^2 - 5", "x y - 2"].map((s) => GPoly.fromMPoly(P.fromTree(parse(s), vars), vars));
  const g = groebner(F).basis;
  const last = g[g.length - 1];
  ok(last._lead.e[0] === 0, "last element is univariate in y");
  eq(toText(P.toTree(P.fromTree(last.toTree(vars), vars))), "y^4 - 5y^2 + 4");
  ok(g.some((p) => p._lead.e[0] === 1 && p._lead.e[1] === 0), "x appears linearly (shape lemma)");
});

// ---------------------------------------------------------------- integers, congruences, extrema
test("congruence mod(3x, 7) = 2 over the integers -> x = 3 + 7k", () => {
  const tree = X.eq(X.fn("mod", X.mul(X.num(3), X.sym("x")), X.num(7)), X.num(2));
  const r = S(tree, { integers: true });
  ok(passed(r));
  eq(toText(r.answers[0].tree), "7k + 3");
  const real = S(tree);
  ok(passed(real));
  eq(real.answers[0].kind, "general");
});
test("linear Diophantine 3x + 5y = 7 and an unsolvable one", () => {
  const r = S("3x + 5y = 7", { integers: true });
  ok(passed(r));
  eq(r.answers[0].kind, "family");
  const [[, xt], [, yt]] = r.answers[0].values;
  for (let t = -3; t <= 3; t++) eq(3 * evalC(xt, { t }).re + 5 * evalC(yt, { t }).re, 7);
  const n = S("4x + 6y = 7", { integers: true });
  ok(noSol(n));
});
test("CRT: x = 2 (mod 3), x = 3 (mod 5) -> 8 + 15k", () => {
  const md = (m, r) => X.eq(X.fn("mod", X.sym("x"), X.num(m)), X.num(r));
  const r = S(X.system(md(3, 2), md(5, 3)), { integers: true });
  ok(passed(r));
  eq(toText(r.answers[0].tree), "15k + 8");
});
test("integer mode keeps integer roots only", () => {
  const r = S("2x^2 - 3x - 2 = 0", { integers: true });
  ok(passed(r));
  ok(sameRoots(roots(r), [2]));
  ok(rejectedValues(r).some((v) => near(v, -0.5)));
});
test("extrema of x^3 - 3x: local max 2 at -1, local min -2 at 1, no global extrema", () => {
  const r = S(parse("x^3 - 3x"), { goal: "extrema" });
  ok(passed(r));
  const mx = r.answers.find((a) => a.type === "max"), mn = r.answers.find((a) => a.type === "min");
  eq(toText(mx.tree), "2"); eq(toText(mx.at[0][1]), "-1");
  eq(toText(mn.tree), "-2"); eq(toText(mn.at[0][1]), "1");
  ok(r.answers.some((a) => a.kind === "none" && /unbounded/.test(a.label)));
});
test("global extrema on a closed interval and on the line", () => {
  const r = S(parse("x^3 - 3x"), { goal: "maximize", interval: [0, 3] });
  ok(passed(r));
  const g = r.answers.find((a) => a.global);
  eq(toText(g.tree), "18"); eq(toText(g.at[0][1]), "3");
  const q = S(parse("-(x - 2)^2 + 5"), { goal: "maximize" });
  ok(passed(q));
  const gq = q.answers.find((a) => a.global);
  eq(toText(gq.tree), "5");
});

// ---------------------------------------------------------------- property tests
test("property: polynomials built from known rational roots return exactly those roots with multiplicities", () => {
  const R = rng(20260925);
  for (let trial = 0; trial < 25; trial++) {
    const k = R.int(1, 4);
    const want = [];
    let tree = X.num(R.pick([1, 2, -3]));
    for (let i = 0; i < k; i++) {
      const p = R.int(-6, 6), q = R.pick([1, 1, 2, 3]);
      const m = R.pick([1, 1, 1, 2, 3]);
      if (want.some((w) => w.v === p / q)) continue;
      want.push({ v: p / q, m });
      tree = X.mul(tree, X.pow(X.sub(X.mul(X.num(q), X.sym("x")), X.num(p)), X.num(m)));
    }
    const r = S(X.eq(tree, X.ZERO));
    ok(passed(r), `verified trial ${trial}`);
    const got = r.answers.filter((a) => a.kind === "exact");
    eq(got.length, want.length, `root count trial ${trial} (${toText(tree)})`);
    for (const w of want) {
      const a = got.find((g) => near(evalC(g.tree, {}).re, w.v));
      ok(a, `root ${w.v} found`);
      eq(a.multiplicity || 1, w.m, `multiplicity of ${w.v}`);
    }
  }
});
test("property: random 3x3 linear systems with a known solution", () => {
  const R = rng(777);
  for (let trial = 0; trial < 15; trial++) {
    const sol = [R.int(-5, 5), R.int(-5, 5), R.int(-5, 5)];
    const vars = ["x", "y", "z"];
    let A;
    do { A = [0, 1, 2].map(() => [0, 1, 2].map(() => R.int(-4, 4))); } while (Math.abs(det3(A)) < 1);
    const eqs = A.map((row) => X.eq(X.add(...row.map((c, j) => X.mul(X.num(c), X.sym(vars[j])))), X.num(row.reduce((s, c, j) => s + c * sol[j], 0))));
    const r = S(X.system(...eqs));
    ok(passed(r), `verified ${trial}`);
    const vals = r.answers[0].values;
    vals.forEach(([k, t]) => eq(evalC(t, {}).re, sol[vars.indexOf(k)], `${k} in trial ${trial}`));
  }
});
function det3(A) { return A[0][0] * (A[1][1] * A[2][2] - A[1][2] * A[2][1]) - A[0][1] * (A[1][0] * A[2][2] - A[1][2] * A[2][0]) + A[0][2] * (A[1][0] * A[2][1] - A[1][1] * A[2][0]); }
test("property: random quadratic inequalities agree with brute-force sampling", () => {
  const R = rng(4242);
  const ops = ["<", "<=", ">", ">="];
  for (let trial = 0; trial < 25; trial++) {
    const a = R.pick([-3, -2, -1, 1, 2, 3]), b = R.int(-6, 6), c = R.int(-8, 8);
    const op = R.pick(ops);
    const tree = X.rel(op, X.add(X.mul(X.num(a), X.pow(X.sym("x"), X.num(2))), X.mul(X.num(b), X.sym("x")), X.num(c)), X.ZERO);
    const r = S(tree);
    ok(passed(r), `verified ${toText(tree)}`);
    const f = (t) => a * t * t + b * t + c;
    const holds = (t) => (op === "<" ? f(t) < 0 : op === "<=" ? f(t) <= 0 : op === ">" ? f(t) > 0 : f(t) >= 0);
    // skip sample points too close to a root (floating point decides the boundary there)
    ok(sameSet(r, "x", (t) => (Math.abs(f(t)) < 1e-6 ? null : holds(t)), -15, 15), `set of ${toText(tree)}`);
  }
});
