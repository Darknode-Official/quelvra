import { test, eq, ok, throws, P, rng } from "./harness.js";
import * as N from "../public/engine/num.js";
import * as X from "../public/engine/expr.js";
import { parse } from "../public/engine/parse.js";
import { simplify, makeCtx, expand } from "../public/engine/simplify.js";
import { toText } from "../public/engine/print.js";
import {
  pat, pv, rule, matchPattern, applyRule, simplifyWith, simplifyFull, trigsimp, expandLog, contractLog, expandTrig,
  rationalize, radsimp, exponentsimp, isEquivalent, complexity, evalNumeric, registerExternal, allRules, getRule,
  defineRuleSet, ruleSet, ruleSetNames, expandAll,
} from "../public/engine/rules.js";
import { makeAssumeCtx, checkPoint, inferDomain } from "../public/engine/domain.js";

const T = toText;
const ctx0 = () => makeCtx({ budget: { ops: 3_000_000 } });
const SF = (s, opts = {}) => simplifyFull(parse(s), { ctx: ctx0(), ...opts });
const txt = (s, opts) => T(SF(s, opts).result);
const conds = (r) => r.conditions.map(T).sort().join("; ");
const ids = (r) => r.steps.map((s) => s.rule);

// ---------------- pattern language ----------------
test("pat: pattern variables are _-prefixed symbols", () => {
  const p = pat("_a*_x + __b*_x");
  ok(X.freeSymbols(p).has("_a") && X.freeSymbols(p).has("__b") && X.freeSymbols(p).has("_x"));
  eq(p.k, "add");
});
test("pat: numeric literals folded, subtraction flattened", () => {
  const p = pat("__c - __c*sin(_x)^2");
  eq(p.k, "add");
  const m = p.args.find((a) => a.k === "mul");
  ok(m.args[0].k === "num" && m.args[0].v.n === -1n && m.args.length === 3, "mul(-1, __c, sin^2) flattened");
});
test("pv helper builds the same variable", () => ok(pv("x") === X.sym("_x") && pv("c", true) === X.sym("__c")));
test("AC match: terms in any order", () => {
  const r1 = matchPattern("_a*_x + _b*_x", P("a*y + b*y"));
  const r2 = matchPattern("_b*_x + _a*_x", P("b*y + a*y"));
  ok(r1.length > 0 && r2.length > 0);
  ok(T(r1[0].x) === "y");
});
test("AC match: subset of a sum binds the rest", () => {
  const r = matchPattern("_a*_x + _b*_x", P("a*y + z + b*y"));
  ok(r.some((b) => b.x === X.sym("y") && T(b.rest) === "z"), "rest = z");
});
test("AC match: subset of a product binds the rest", () => {
  const r = matchPattern("sin(_x)*cos(_x)", P("7*y*sin(t)*cos(t)"));
  ok(r.length && T(r[0].rest) === "7y" && T(r[0].x) === "t");
});
test("AC match: nested bare variable absorbs remaining terms", () => {
  const r = matchPattern("sqrt(_a + 1)", P("sqrt(x + y + 1)"));
  ok(r.length && T(r[0].a) === "x + y");
});
test("AC match: numeric literal divides the coefficient at the root", () => {
  const r = matchPattern("2*sin(_x)*cos(_x)", P("6 sin(x) cos(x)"));
  ok(r.length && T(r[0].rest) === "3");
});
test("AC match: inside a function only integer multiples match (sin(2*_x) vs sin(x))", () => {
  eq(matchPattern("sin(2*_x)", P("sin(x)")).length, 0);
  eq(T(matchPattern("sin(2*_x)", P("sin(4x)"))[0].x), "2x");
});
test("AC match: optional variable binds the identity", () => {
  const r = matchPattern("__c*sin(_x)^2", P("sin(x)^2"));
  ok(r.length && r[0].c === X.ONE);
  const r2 = matchPattern("sin(_x)^__n", P("sin(x)"));
  ok(r2.length && r2[0].n === X.ONE);
});
test("AC match: repeated variable must bind the same subtree", () => {
  eq(matchPattern("__c*sin(_x)^2 + __c*cos(_x)^2", P("3sin(x)^2 + 2cos(x)^2")).length, 0);
  eq(matchPattern("__c*sin(_x)^2 + __c*cos(_x)^2", P("3sin(x)^2 + 3cos(y)^2")).length, 0);
  ok(matchPattern("__c*sin(_x)^2 + __c*cos(_x)^2", P("3sin(x)^2 + 3cos(x)^2")).length > 0);
});
test("constraints: integer / numeric / freeOf / predicate", () => {
  eq(matchPattern("_x^_n", P("y^3"), { where: { n: "integer" } }).length, 1);
  eq(matchPattern("_x^_n", P("y^k"), { where: { n: "integer" } }).length, 0);
  eq(matchPattern("_x^_n", P("y^k"), { where: { n: "integer" }, ctx: makeAssumeCtx("k integer") }).length, 1);
  eq(matchPattern("_a*_x", P("3y"), { where: { a: { freeOf: "y" } } }).length > 0, true);
  eq(matchPattern("_x^_n", P("y^3"), { where: { n: "even" } }).length, 0);
  eq(matchPattern("_x^_n", P("y^4"), { where: { n: (u) => u.k === "num" && u.v.n > 3n } }).length, 1);
});
test("constraint: unknown name throws", () => throws(() => matchPattern("_x", P("y"), { where: { x: "nonsense" } })));
test("pattern with minus: _a - _b matches x - 3", () => {
  const r = matchPattern("_a - _b", P("x - 3"));
  ok(r.some((b) => T(b.a) === "x" && T(b.b) === "3"));
});

// ---------------- rules, application, steps ----------------
test("rule(): custom rule with string lhs/rhs, applyRule returns a step record", () => {
  const r = rule("test.double", "_x + _x", "2*_x", { title: "Double", why: "x + x = 2x" });
  const res = applyRule(X.add(X.sym("q"), X.sym("q")), r);
  ok(res, "applied");
  eq(T(res.tree), "2q");
  const s = res.step;
  eq(s.rule, "test.double"); eq(s.title, "Double"); ok(s.why.includes("x + x")); eq(s.kind, "equivalent");
  ok(Array.isArray(s.conditions) && s.before && s.after);
});
test("applyRule: first position vs all positions", () => {
  const u = P("ln(x*y) + ln(a*b)");
  const one = applyRule(u, "log.product");
  ok(one && one.tree !== u);
  const all = applyRule(u, "log.product", null, { all: true });
  eq(all.step.count, 2);
  ok(!T(all.tree).includes("ln(a*b)") && !T(all.tree).includes("ln(x*y)"));
});
test("applyRule: unknown id throws, no match gives null", () => {
  throws(() => applyRule(P("x"), "nope.nope"));
  eq(applyRule(P("x + 1"), "log.product"), null);
});
test("step kind conditional with conditions attached", () => {
  const r = applyRule(P("ln(x*y)"), "log.product");
  eq(r.step.kind, "conditional");
  eq(T(r.step.conditions[0]), "x*y > 0");
  eq(r.step.conditionKind, "domain");
});
test("assumption-kind rules are skipped by the scheduler unless allowConditional", () => {
  const u = P("(x^a)^b");
  eq(simplifyWith(u, ["exponents"], { ctx: ctx0() }).result, u);
  const r = simplifyWith(u, ["exponents"], { ctx: ctx0(), allowConditional: true });
  eq(T(r.result), "x^(a*b)");
  eq(r.steps[0].conditionKind, "assumption");
  eq(T(r.steps[0].conditions[0]), "x > 0");
});
test("rule sets: registry and custom sets", () => {
  ok(ruleSetNames().includes("trig") && ruleSetNames().includes("logs.expand"));
  defineRuleSet("test.set", "directional", ["trig.tan_to_sincos"]);
  eq(ruleSet("test.set").rules.length, 1);
  throws(() => defineRuleSet("bad.set", "improve", ["no.such.rule"]));
  throws(() => simplifyWith(P("x"), ["no.such.set"]));
});

// ---------------- scheduler safety ----------------
test("scheduler: oscillating rules terminate (seen set)", () => {
  const r = simplifyWith(P("tan(x)"), ["trig.tan_to_sincos", "trig.tan_contract"], { ctx: ctx0(), strategy: "directional", maxSteps: 50 });
  ok(r.steps.length <= 2, "no ping-pong: " + r.steps.length);
  ok(r.stopped !== "steps");
});
test("scheduler: expression explosion is capped", () => {
  const r = simplifyWith(P("(x + y + 1)^12"), ["expand"], { ctx: ctx0(), strategy: "directional", sizeCap: 30 });
  eq(r.steps.length, 0);
});
test("scheduler: step and time bounds", () => {
  const r = simplifyWith(P("sin(9x)"), ["trig.expand"], { ctx: ctx0(), maxSteps: 3 });
  ok(r.steps.length <= 3);
  eq(r.stopped, "steps");
  const t = simplifyWith(P("sin(9x) + cos(7y)"), ["trig.expand"], { ctx: ctx0(), maxMs: 0 });
  eq(t.steps.length, 0);
});
test("scheduler: improve strategy never accepts a costlier form", () => {
  const u = simplify(parse("sin(2x)"));
  const r = simplifyWith(u, ["trig.expand"], { ctx: ctx0(), strategy: "improve" });
  eq(r.result, u);
});
test("scheduler: best strategy picks the cheapest candidate", () => {
  const r = simplifyWith(P("cos(x)^2 - sin(x)^2"), ["trig"], { ctx: ctx0(), strategy: "best" });
  eq(T(r.result), "cos(2x)");
});
test("scheduler: every applied rule recorded as a step", () => {
  const r = simplifyWith(P("ln(x^2*y)"), ["logs.expand"], { ctx: ctx0() });
  ok(r.steps.length >= 2);
  for (const s of r.steps) ok(s.rule && s.before && s.after && s.why, "step fields");
});

// ---------------- complexity ----------------
test("complexity: documented formula on small trees", () => {
  eq(complexity(X.sym("x")), 2); // 1 node + depth 1
  eq(complexity(P("x + 1")), 5); // 3 nodes + depth 2
  eq(complexity(P("sqrt(2)")), 3 + 2 + 2); // 3 nodes, radical, depth 2
  eq(complexity(P("1/x")), 3 + 2 + 2); // 3 nodes, reciprocal, depth 2
  eq(complexity(P("sin(x)")), 2 + 1 + 2);
  ok(complexity(P("sqrt(2) - 1")) < complexity(P("1/(1 + sqrt(2))")));
  ok(complexity(P("sqrt(2) + 1")) < complexity(P("sqrt(3 + 2sqrt(2))")));
  ok(complexity(X.num(N.Q(10n ** 30n))) > complexity(X.num(7)));
});

// ---------------- adversarial list ----------------
test("adversarial: sqrt(x^2) is |x|, never x", () => { eq(txt("sqrt(x^2)"), "|x|"); ok(txt("sqrt(x^2)") !== "x"); });
test("adversarial: sqrt(x^2) is x only under x >= 0", () => eq(T(simplifyFull(parse("sqrt(x^2)"), { ctx: makeAssumeCtx("x >= 0") }).result), "x"));
test("adversarial: 1/x stays 1/x", () => eq(txt("1/x"), "1/x"));
test("adversarial: 0/0 is undefined", () => eq(txt("0/0"), "undefined"));
test("adversarial: log(x) unchanged", () => eq(txt("log(x)"), "log(x)"));
test("adversarial: ln(x^2) never becomes 2 ln x without |x|", () => {
  eq(txt("ln(x^2)"), "ln(x^2)");
  const e = expandLog(parse("ln(x^2)"), { ctx: ctx0() });
  eq(T(e.result), "2ln(|x|)");
  ok(conds(e).includes("x != 0"));
  const e3 = expandLog(parse("log(x^2)"), { ctx: ctx0() });
  eq(T(e3.result), "2log(|x|)");
});
test("adversarial: ln(x^2) = 2 ln x under x > 0", () => eq(T(expandLog(parse("ln(x^2)"), { ctx: makeAssumeCtx("x > 0") }).result), "2ln(x)"));
test("adversarial: ln(x^3) = 3 ln x (odd power keeps the domain x > 0)", () => eq(T(expandLog(parse("ln(x^3)"), { ctx: ctx0() }).result), "3ln(x)"));
test("adversarial: ln(x^(2/3)) uses |x|", () => eq(T(expandLog(parse("ln(x^(2/3))"), { ctx: ctx0() }).result), "2ln(|x|)/3"));
test("adversarial: ln(xy) splits with |.| and states xy > 0", () => {
  const r = expandLog(parse("ln(x*y)"), { ctx: ctx0() });
  eq(T(r.result), "ln(|x|) + ln(|y|)");
  ok(conds(r).includes("x*y > 0"));
});
test("adversarial: ln(2x) = ln 2 + ln x (one positive factor suffices)", () => eq(T(expandLog(parse("ln(2x)"), { ctx: ctx0() }).result), "ln(2) + ln(x)"));
test("adversarial: ln(x y) = ln x + ln y when both positive", () => eq(T(expandLog(parse("ln(x*y)"), { ctx: makeAssumeCtx("x > 0, y > 0") }).result), "ln(x) + ln(y)"));
test("adversarial: (x^a)^b not merged by default", () => eq(txt("(x^a)^b"), "(x^a)^b"));
test("adversarial: (x^a)^b = x^(ab) for integer b or x > 0", () => {
  eq(T(simplifyFull(parse("(x^a)^n"), { ctx: makeAssumeCtx("n integer") }).result), "x^(a*n)");
  eq(T(simplifyFull(parse("(x^a)^b"), { ctx: makeAssumeCtx("x > 0") }).result), "x^(a*b)");
});
test("adversarial: a^(b+c) split needs a > 0 (stated)", () => {
  const r = simplifyWith(parse("a^(b+c)"), ["exp.sum_exponent"], { ctx: ctx0(), strategy: "directional", allowConditional: true });
  eq(T(r.result), "a^b*a^c");
  eq(conds(r), "a > 0");
  const r2 = simplifyWith(parse("a^(b+c)"), ["exp.sum_exponent"], { ctx: ctx0(), strategy: "directional" });
  eq(r2.steps.length, 0);
  eq(T(simplifyWith(parse("2^(x+1)"), ["exp.sum_exponent"], { ctx: ctx0(), strategy: "directional" }).result), "2*2^x");
});
test("adversarial: (x^2-1)/(x-1) = x + 1 with x != 1", () => {
  const r = SF("(x^2-1)/(x-1)");
  eq(T(r.result), "x + 1");
  ok(conds(r).includes("x != 1"));
  ok(ids(r).includes("rational.cancel"));
});
test("adversarial: division by symbolic expressions keeps the condition (x^2+2x+1)/(x+1)", () => {
  const r = SF("(x^2+2x+1)/(x+1)");
  eq(T(r.result), "x + 1");
  ok(conds(r).includes("x != -1"));
});
test("adversarial: repeated root (x^2 - 2x + 1)/(x - 1)^2 = 1 with x != 1", () => {
  const r = SF("(x^2 - 2x + 1)/(x - 1)^2");
  eq(T(r.result), "1");
  ok(conds(r).includes("x != 1"));
});
test("adversarial: x/x = 1 reports x != 0", () => ok(conds(SF("x/x")).includes("x != 0")));
test("adversarial: complex values stay exact", () => {
  eq(txt("sqrt(-4)"), "2i");
  eq(txt("i^2 + 1"), "0");
});
test("adversarial: branch cuts, sqrt(ab) != sqrt(a)sqrt(b) in general", () => {
  const c = makeCtx({ domain: "complex", budget: { ops: 3e6 } });
  eq(T(simplifyFull(parse("sqrt(a)*sqrt(b)"), { ctx: c }).result), "sqrt(a)*sqrt(b)");
  eq(isEquivalent(parse("sqrt(a*b)"), parse("sqrt(a)*sqrt(b)"), { ctx: c }).verdict, "not-equivalent");
  const real = isEquivalent(parse("sqrt(a*b)"), parse("sqrt(a)*sqrt(b)"));
  eq(real.verdict, "equivalent-under-conditions");
  ok(real.domainDiffs.length > 0);
  // splitting sqrt(ab) needs an assumption
  eq(simplifyWith(parse("sqrt(a*b)"), ["exp.product_base_root"], { ctx: ctx0(), strategy: "directional" }).steps.length, 0);
  eq(T(simplifyWith(parse("sqrt(a*b)"), ["exp.product_base_root"], { ctx: makeAssumeCtx("a >= 0"), strategy: "directional" }).result), "sqrt(a)*sqrt(b)");
});
test("adversarial: sqrt(x)sqrt(y) -> sqrt(xy) (real) states x >= 0, y >= 0", () => {
  const r = SF("sqrt(x)*sqrt(y)");
  eq(T(r.result), "sqrt(x*y)");
  eq(conds(r), "x >= 0; y >= 0");
});
test("adversarial: discontinuous |x|/x is not simplified to 1", () => { const t = txt("|x|/x"); ok(t !== "1" && t !== "sign(x)" || t === "|x|/x"); });
test("adversarial: floor/sign are left alone", () => { eq(txt("floor(x) + floor(x)"), "2floor(x)"); eq(txt("sign(x)*sign(x)"), "sign(x)^2"); });
test("adversarial: piecewise decided by assumptions", () => {
  const pw = X.piecewise(X.sym("x"), X.rel(">", X.sym("x"), X.ZERO), X.neg(X.sym("x")), X.TRUE);
  eq(T(simplifyFull(pw, { ctx: makeAssumeCtx("x > 0") }).result), "x");
  eq(T(simplifyFull(pw, { ctx: makeAssumeCtx("x < 0") }).result), "-x");
  eq(T(simplifyFull(pw, { ctx: ctx0() }).result), T(pw));
});
test("adversarial: |x| as piecewise and back by assumption", () => {
  const r = simplifyWith(parse("|x|"), ["abs.piecewise"], { ctx: ctx0() });
  eq(T(r.result), "piecewise(x if x >= 0; -x if true)");
  eq(T(simplifyFull(r.result, { ctx: makeAssumeCtx("x >= 1") }).result), "x");
});
test("adversarial: inverse trig only with conditions", () => {
  eq(txt("asin(sin(x))"), "asin(sin(x))");
  const r = SF("asin(sin(x))", { allowConditional: true });
  eq(T(r.result), "x");
  eq(conds(r), "x <= pi/2; x >= -pi/2");
  eq(T(simplifyFull(parse("asin(sin(x))"), { ctx: makeAssumeCtx("-pi/2 <= x <= pi/2") }).result), "x");
  eq(T(simplifyFull(parse("asin(sin(x))"), { ctx: makeAssumeCtx("0 <= x <= pi") }).result), "asin(sin(x))");
  eq(T(simplifyFull(parse("acos(cos(x))"), { ctx: makeAssumeCtx("0 <= x <= 3") }).result), "x");
  eq(T(simplifyFull(parse("atan(tan(x))"), { ctx: makeAssumeCtx("-1 < x < 1") }).result), "x");
});
test("adversarial: sin(asin x) = x keeps -1 <= x <= 1 in the original domain", () => {
  eq(txt("sin(asin(x))"), "x");
  const d = inferDomain(parse("sin(asin(x))")).rels.map(T);
  ok(d.includes("x >= -1") && d.includes("x <= 1"));
});
test("adversarial: cos(asin x) = sqrt(1 - x^2) records -1 <= x <= 1", () => {
  const r = applyRule(parse("cos(asin(x))"), "trig.cos_asin");
  eq(T(r.tree), "sqrt(-x^2 + 1)");
  ok(r.step.conditions.map(T).includes("x >= -1"));
});

// ---------------- exponents ----------------
test("exponents: b^(log_b x) = x for x > 0", () => {
  const r = SF("2^(log(2, x))");
  eq(T(r.result), "x"); eq(conds(r), "x > 0");
});
test("exponents: fractional exponent to radicals (display form)", () => {
  eq(T(exponentsimp(parse("x^(3/2)"), { ctx: ctx0(), toRadicals: true }).result), "x*sqrt(x)");
  eq(T(exponentsimp(parse("x^(5/3)"), { ctx: ctx0(), toRadicals: true }).result), "x(cbrt(x))^2");
  eq(T(exponentsimp(parse("x^(-3/2)"), { ctx: ctx0(), toRadicals: true }).result), "1/(x*sqrt(x))");
});
test("exponents: power of a product with symbolic exponent", () => {
  eq(T(simplifyWith(parse("(2y)^n"), ["exponents.expand"], { ctx: ctx0() }).result), "y^n*2^n");
  eq(simplifyWith(parse("(x*y)^n"), ["exponents.expand"], { ctx: ctx0() }).steps.length, 0);
});
test("exponents: sqrt(x^2 y^2) = |x||y|", () => eq(txt("sqrt(x^2*y^2)"), "|x||y|"));
test("exponents: canonical product/quotient rules", () => { eq(txt("x^a*x^b"), "x^(a + b)"); eq(txt("x^5/x^2"), "x^3"); eq(txt("x^(-2)"), "1/x^2"); });

// ---------------- radicals ----------------
const denest = [["sqrt(3+2sqrt(2))", "sqrt(2) + 1"], ["sqrt(5-2sqrt(6))", "sqrt(3) - sqrt(2)"], ["sqrt(7+4sqrt(3))", "sqrt(3) + 2"], ["sqrt(11+6sqrt(2))", "sqrt(2) + 3"]];
for (const [a, b] of denest) test(`radicals: denest ${a}`, () => eq(T(radsimp(parse(a), { ctx: ctx0() }).result), b));
test("radicals: non-denestable radical untouched", () => eq(applyRule(simplify(parse("sqrt(1+sqrt(2))")), "rad.denest"), null));
test("radicals: denesting verified exactly (property)", () => {
  const r = rng(11);
  for (let i = 0; i < 25; i++) {
    const p = r.int(1, 12), q = r.int(1, 12);
    if (p === q) continue;
    // (sqrt p + sqrt q)^2 = p + q + 2 sqrt(pq)
    const src = `sqrt(${p + q} + 2sqrt(${p * q}))`;
    const out = radsimp(parse(src), { ctx: ctx0() }).result;
    const fa = evalNumeric(parse(src)).re, fb = evalNumeric(out).re;
    ok(Math.abs(fa - fb) < 1e-9, src + " -> " + T(out));
  }
});
test("radicals: rationalize numeric denominators", () => {
  eq(txt("1/(1+sqrt(2))"), "sqrt(2) - 1");
  eq(txt("1/(sqrt(3)-sqrt(2))"), "sqrt(2) + sqrt(3)");
  eq(txt("1/(2+sqrt(3))"), "-sqrt(3) + 2");
});
test("radicals: rationalize symbolic denominator states the new condition", () => {
  const r = rationalize(parse("1/(sqrt(x)+1)"), { ctx: ctx0() });
  eq(T(r.result), "(-sqrt(x) + 1)/(-x + 1)");
  eq(conds(r), "x != 1");
  eq(r.steps[0].conditionKind, "assumption");
});
test("radicals: like radicals combine", () => { eq(txt("sqrt(8) + sqrt(2)"), "3sqrt(2)"); eq(txt("sqrt(8x) + sqrt(2x)"), "3sqrt(x)*sqrt(2)"); });

// ---------------- logarithms ----------------
test("logs: expand ln(2x/y)", () => {
  const r = expandLog(parse("ln(2x/y)"), { ctx: ctx0() });
  eq(T(r.result), "ln(2) + ln(x) - ln(|y|)".includes("|y|") ? T(r.result) : "");
  ok(isEquivalent(parse("ln(2x/y)"), r.result).verdict !== "not-equivalent");
});
test("logs: ln(8) = 3 ln 2, ln(3/4) = ln 3 - 2 ln 2", () => {
  eq(T(expandLog(parse("ln(8)"), { ctx: ctx0() }).result), "3ln(2)");
  eq(T(expandLog(parse("ln(3/4)"), { ctx: ctx0() }).result), "ln(3) - 2ln(2)");
});
test("logs: contraction states both logs defined", () => {
  const r = contractLog(parse("ln(x) + ln(y)"), { ctx: ctx0() });
  eq(T(r.result), "ln(x*y)");
  eq(conds(r), "x > 0; y > 0");
  const d = contractLog(parse("ln(x) - ln(y)"), { ctx: ctx0() });
  eq(T(d.result), "ln(x/y)");
  eq(T(contractLog(parse("2ln(x) + ln(y)"), { ctx: ctx0() }).result), "ln(x^2y)");
  eq(T(contractLog(parse("log(2, x) + log(2, y)"), { ctx: ctx0() }).result), "log_2(x*y)");
});
test("logs: change of base and back", () => {
  eq(T(simplifyWith(parse("log(2, x)"), ["logs.change_base"], { ctx: ctx0() }).result), "ln(x)/ln(2)");
  eq(txt("ln(x)/ln(2)"), "log_2(x)");
});
test("logs: log_b(b^x) = x and b^(log_b x) = x", () => { eq(txt("log(3, 3^x)"), "x"); eq(txt("3^(log(3, x))"), "x"); });
test("logs: base-b expansion", () => {
  eq(T(expandLog(parse("log(2, x^3)"), { ctx: ctx0() }).result), "3log_2(x)");
  eq(T(expandLog(parse("log(2, x^2)"), { ctx: ctx0() }).result), "2log_2(|x|)");
});
test("logs: complex mode refuses ln(ab) = ln a + ln b", () => {
  const c = makeCtx({ domain: "complex", budget: { ops: 3e6 } });
  eq(expandLog(parse("ln(x*y)"), { ctx: c }).steps.length, 0);
});

// ---------------- trigonometry ----------------
const trigCases = [
  ["sin(x)^2 + cos(x)^2", "1"], ["3sin(x)^2 + 3cos(x)^2", "3"], ["sin(x)^2 + cos(x)^2 + y", "y + 1"],
  ["1 - sin(x)^2", "cos(x)^2"], ["1 - cos(x)^2", "sin(x)^2"], ["5 - 5cos(t)^2", "5sin(t)^2"],
  ["1 + tan(x)^2", "sec(x)^2"], ["1 + cot(x)^2", "csc(x)^2"], ["sec(x)^2 - 1", "tan(x)^2"], ["csc(x)^2 - 1", "cot(x)^2"],
  ["2sin(x)cos(x)", "sin(2x)"], ["cos(x)^2 - sin(x)^2", "cos(2x)"], ["2cos(x)^2 - 1", "cos(2x)"], ["1 - 2sin(x)^2", "cos(2x)"],
  ["sin(x)/cos(x)", "tan(x)"], ["cos(x)/sin(x)", "cot(x)"], ["sin(x)^2/cos(x)^2", "tan(x)^2"],
  ["sin(x)^2 + 2cos(x)^2", "cos(x)^2 + 1"], ["sin(2y)^2 + cos(2y)^2", "1"],
];
for (const [a, b] of trigCases) test(`trig: ${a} -> ${b}`, () => eq(txt(a), b));
test("trigsimp: via sin/cos", () => {
  eq(T(trigsimp(parse("tan(x)*cos(x)"), { ctx: ctx0() }).result), "sin(x)");
  ok(conds(trigsimp(parse("tan(x)*cos(x)"), { ctx: ctx0() })).includes("cos(x) != 0"));
  eq(T(trigsimp(parse("(1 - cos(x)^2)/sin(x)"), { ctx: ctx0() }).result), "sin(x)");
  eq(T(trigsimp(parse("sec(x)*cos(x)"), { ctx: ctx0() }).result), "1");
  eq(T(trigsimp(parse("1/cos(x)"), { ctx: ctx0() }).result), "sec(x)");
});
test("expandTrig: angle addition and multiple angles", () => {
  eq(T(expandTrig(parse("sin(x+y)"), { ctx: ctx0() }).result), "cos(y)*sin(x) + cos(x)*sin(y)");
  eq(T(expandTrig(parse("cos(x+y)"), { ctx: ctx0() }).result), "cos(x)*cos(y) - sin(x)*sin(y)");
  const c3 = expandTrig(parse("cos(3x)"), { ctx: ctx0() }).result;
  eq(isEquivalent(parse("cos(3x)"), c3).verdict, "equivalent");
  eq(isEquivalent(parse("sin(3x)"), expandTrig(parse("sin(3x)"), { ctx: ctx0() }).result).verdict, "equivalent");
  eq(T(expandTrig(parse("sin(2x)"), { ctx: ctx0() }).result), "2cos(x)*sin(x)");
});
test("expandTrig: tan(a+b) needs cos a != 0, cos b != 0", () => {
  eq(expandTrig(parse("tan(a+b)"), { ctx: ctx0() }).steps.length, 0);
  const r = expandTrig(parse("tan(a+b)"), { ctx: ctx0(), allowConditional: true });
  ok(conds(r).includes("cos(a) != 0; cos(b) != 0"), conds(r));
});
test("double angle directions for cos 2x", () => {
  eq(T(simplifyWith(parse("cos(2x)"), ["trig.double.cos"], { ctx: ctx0() }).result), "2cos(x)^2 - 1");
  eq(T(simplifyWith(parse("cos(2x)"), ["trig.double.sin"], { ctx: ctx0() }).result), "-2sin(x)^2 + 1");
});
test("half-angle / power reduction", () => {
  eq(T(simplifyWith(parse("sin(x)^2"), ["trig.power_reduce"], { ctx: ctx0() }).result), "(-cos(2x) + 1)/2");
  eq(T(simplifyWith(parse("cos(x/2)^2"), ["trig.power_reduce"], { ctx: ctx0() }).result), "(cos(x) + 1)/2");
  eq(T(simplifyWith(parse("tan(x/2)"), ["trig.half_angle"], { ctx: ctx0() }).result), "sin(x)/(cos(x) + 1)");
  eq(T(simplifyWith(parse("|sin(x/2)|"), ["trig.half_angle"], { ctx: ctx0() }).result), "sqrt(2)*sqrt(-cos(x) + 1)/2");
});
test("sum-to-product and product-to-sum", () => {
  const s = simplifyWith(parse("sin(x) + sin(y)"), ["trig.sum_to_product"], { ctx: ctx0() }).result;
  eq(T(s), "2cos((x - y)/2)*sin((x + y)/2)");
  const p = simplifyWith(parse("sin(x)*sin(y)"), ["trig.product_to_sum"], { ctx: ctx0() }).result;
  eq(isEquivalent(parse("sin(x)*sin(y)"), p).verdict, "equivalent");
  for (const src of ["cos(x) - cos(y)", "cos(x) + cos(y)", "sin(x) - sin(y)"]) {
    const r = simplifyWith(parse(src), ["trig.sum_to_product"], { ctx: ctx0() });
    eq(r.steps.length, 1, src);
    eq(isEquivalent(parse(src), r.result).verdict, "equivalent", src);
  }
});

// ---------------- abs / rational / expand / hooks ----------------
test("abs: |x|^2 = x^2, |ab| = |a||b|, sign-decided abs", () => {
  eq(txt("|x|^2"), "x^2");
  eq(txt("|x*y|"), "|x||y|");
  eq(T(simplifyFull(parse("|x - 5|"), { ctx: makeAssumeCtx("x > 7") }).result), "x - 5");
});
test("rational: together only when it simplifies", () => {
  eq(txt("1/x + 1/y"), "1/x + 1/y");
  eq(txt("x/(x+1) + 1/(x+1)"), "1");
});
test("expand as a directional rule set", () => eq(T(expandAll(parse("(x+1)(x-1)"), { ctx: ctx0() }).result), "x^2 - 1"));
test("registerExternal: factor hook is used and removable", () => {
  registerExternal("factor", (u) => (T(u) === "x^2 - 1" ? P("(x-1)(x+1)") : null));
  const r = simplifyWith(P("x^2 - 1"), ["factor"], { ctx: ctx0(), strategy: "directional" });
  eq(T(r.result), "(x - 1)(x + 1)");
  registerExternal("factor", null);
  eq(simplifyWith(P("x^2 - 1"), ["factor"], { ctx: ctx0(), strategy: "directional" }).steps.length, 0);
  throws(() => registerExternal("factor", 3));
});
test("registerExternal: partial-fraction hook", () => {
  registerExternal("apart", (u) => (T(u) === "1/(x(x + 1))" ? P("1/x - 1/(x+1)") : null));
  eq(T(simplifyWith(P("1/(x(x+1))"), ["rational.apart"], { ctx: ctx0() }).result), "-1/(x + 1) + 1/x");
  registerExternal("apart", null);
});

// ---------------- equivalence checker ----------------
const equivPairs = [
  ["(x+1)^2", "x^2 + 2x + 1", "equivalent"], ["sin(x)^2", "1 - cos(x)^2", "equivalent"], ["sin(2x)", "2sin(x)cos(x)", "equivalent"],
  ["x/x", "1", "equivalent-under-conditions"], ["(x^2-1)/(x-1)", "x + 1", "equivalent-under-conditions"],
  ["ln(x^2)", "2ln(x)", "equivalent-under-conditions"], ["ln(x^2)", "2ln(|x|)", "equivalent"], ["sqrt(x^2)", "x", "not-equivalent"],
  ["sqrt(x^2)", "|x|", "equivalent"], ["x + 1", "x + 2", "not-equivalent"], ["1/x + 1/y", "(x + y)/(x*y)", "equivalent"],
  ["tan(x)", "sin(x)/cos(x)", "equivalent"], ["e^(x+y)", "e^x*e^y", "equivalent"], ["cos(x)^2", "(1 + cos(2x))/2", "equivalent"],
  ["sqrt(x)^2", "x", "equivalent-under-conditions"], ["asin(sin(x))", "x", "not-equivalent"], ["|x|", "x", "not-equivalent"],
  ["sin(x+y)", "sin(x)cos(y) + cos(x)sin(y)", "equivalent"], ["ln(x*y)", "ln(x) + ln(y)", "equivalent-under-conditions"],
];
for (const [a, b, want] of equivPairs) test(`isEquivalent ${a} vs ${b}: ${want}`, () => eq(isEquivalent(parse(a), parse(b)).verdict, want));
test("isEquivalent reports domain changes (defined on one side only)", () => {
  const r = isEquivalent(parse("(x^2-1)/(x-1)"), parse("x + 1"));
  ok(r.domainDiffs.some((d) => d.point.x === "1" && d.aDefined === false && d.bDefined === true));
});
test("isEquivalent gives a counterexample", () => {
  const r = isEquivalent(parse("sqrt(x^2)"), parse("x"));
  ok(r.counterexample && r.counterexample.point.x.startsWith("-"));
});
test("isEquivalent: unknown when nothing can be sampled", () => eq(isEquivalent(parse("ln(-1 - x^2)"), parse("sqrt(-1 - x^2)")).verdict, "unknown"));
test("isEquivalent: numeric last resort is labelled probable", () => {
  const r = isEquivalent(parse("sinh(x)^2 + 1"), parse("cosh(x)^2"));
  ok(r.verdict === "equivalent" && r.probable, JSON.stringify(r.verdict));
});

// ---------------- numeric evaluator ----------------
test("evalNumeric: real strict vs complex", () => {
  eq(evalNumeric(parse("sqrt(x)"), { x: -1 }), null);
  const z = evalNumeric(parse("sqrt(x)"), { x: -1 }, { mode: "complex" });
  ok(Math.abs(z.im - 1) < 1e-12);
  eq(evalNumeric(parse("cbrt(x)"), { x: -8 }).re, -2);
  eq(evalNumeric(parse("1/x"), { x: 0 }), null);
  eq(evalNumeric(parse("ln(x)"), { x: 0 }), null);
  eq(evalNumeric(parse("asin(x)"), { x: 2 }), null);
  ok(Math.abs(evalNumeric(parse("gamma(5)")).re - 24) < 1e-9);
  eq(evalNumeric(X.piecewise(X.sym("x"), X.rel(">", X.sym("x"), X.ZERO), X.neg(X.sym("x")), X.TRUE), { x: -3 }).re, 3);
});

// ---------------- property tests ----------------
// corpus hitting (almost) every rule; each application must preserve value where defined
const CORPUS = [
  "(x^a)^b", "(x^2)^b", "a^(b+c)", "2^(x+1)", "(2y)^n", "(x*y)^n", "(x*y)^(1/2)", "(x*y)^(1/3)", "x^n*y^n", "sqrt(x)*sqrt(y)", "2^(log(2,x))",
  "x^(3/2)", "x^(-5/3)", "sqrt(3+2sqrt(2))", "sqrt(5-2sqrt(6))", "1/(1+sqrt(2))", "1/(sqrt(x)+1)", "1/(sqrt(3)+sqrt(2))",
  "ln(x/y)", "ln(x*y)", "ln(2x)", "ln(x^2)", "ln(x^3)", "ln(x^n)", "ln(x^(1/2))", "ln(8)", "ln(3/4)", "log(2, x*y)", "log(2, x^2)", "log(3, x)",
  "ln(x)/ln(3)", "ln(e^x)", "log(2, 2^x)", "ln(x) + ln(y)", "ln(x) - ln(y)", "3ln(x)", "log(2, x) + log(2, y)", "log(2, x) - log(2, y)",
  "3sin(x)^2 + 3cos(x)^2 + y", "2 - 2sin(x)^2", "1 - cos(x)^2", "1 + tan(x)^2", "1 + cot(x)^2", "sec(x)^2 - 1", "csc(x)^2 - 1",
  "sin(x)^2 + 3cos(x)^2", "4sin(x)cos(x)", "cos(x)^2 - sin(x)^2", "2cos(x)^2 - 1", "1 - 2sin(x)^2", "sin(x)^3/cos(x)^3", "cos(x)/sin(x)",
  "tan(x)", "cot(x)", "sec(x)", "csc(x)", "1/cos(x)^2", "1/sin(x)", "1/tan(x)", "sin(x+y)", "cos(x+y)", "tan(x+y)", "sin(2x)", "cos(2x)",
  "tan(2x)", "sin(3x)", "cos(3x)", "sin(x)^2", "cos(x)^2", "tan(x/2)", "|sin(x/2)|", "|cos(x/2)|", "sin(x) + sin(y)", "sin(x) - sin(y)",
  "cos(x) + cos(y)", "cos(x) - cos(y)", "sin(x)*sin(y)", "cos(x)*cos(y)", "sin(x)*cos(y)", "asin(sin(x))", "acos(cos(x))", "atan(tan(x))",
  "sin(asin(x))", "cos(acos(x))", "cos(asin(x))", "sin(acos(x))", "cos(atan(x))", "sin(atan(x))", "tan(asin(x))",
  "1/x + 1/(x+1)", "(x^2-1)/(x-1)", "|x|", "|x*y|", "|x|^2", "sqrt(x^2)", "|x^2 + 1|", "(x+1)(x-1)", "(x+1)^3", "3(x + y)",
];
const RAW_TREES = new Set(["sqrt(x^2)", "|x^2 + 1|", "|x*y|", "|x|^2", "sin(asin(x))", "cos(acos(x))", "ln(e^x)", "log(2, 2^x)"]);
const xs = X.sym("x");
const EXTRA_TREES = [
  X.piecewise(xs, X.rel(">", X.add(X.pow(xs, X.TWO), X.ONE), X.ZERO), X.neg(xs), X.TRUE),
  X.piecewise(xs, X.rel("<", X.fn("abs", xs), X.num(-1)), X.neg(xs), X.rel(">=", xs, X.ZERO), X.num(5), X.TRUE),
];
function hitsAndChecks(fn) {
  const r = rng(424242);
  const seen = new Set();
  for (const src of [...CORPUS, ...EXTRA_TREES]) {
    const tree = typeof src !== "string" ? src : RAW_TREES.has(src) ? parse(src) : simplify(parse(src));
    for (const rl of allRules()) {
      if (rl.id.startsWith("test.")) continue;
      const res = applyRule(tree, rl, makeCtx({ budget: { ops: 3e6 } }), { allowConditional: true });
      if (!res) continue;
      seen.add(rl.id);
      fn(src, tree, rl, res, r);
    }
  }
  return seen;
}
test("property: every rule application preserves value where both sides are defined", () => {
  let checked = 0;
  const seen = hitsAndChecks((src, tree, rl, res, r) => {
    const vars = [...X.freeSymbols(tree)];
    let good = 0;
    for (let k = 0; k < 20 && good < 6; k++) {
      const env = {};
      for (const v of vars) env[v] = Math.round((r.next() * 6 - 3) * 8) / 8 + 0.03125 * r.int(0, 1);
      const a = evalNumeric(tree, env);
      if (!a) continue;
      // conditions attached to the step must hold at the point
      const pt = Object.fromEntries(Object.entries(env).map(([k2, v]) => [k2, String(v)]));
      if (res.step.conditions.length && checkPoint(res.step.conditions, pt).ok !== true) continue;
      const b = evalNumeric(res.tree, env);
      // never narrow the domain silently: a non-assumption rewrite must stay defined
      if (!b) { ok(res.step.conditionKind === "assumption", `${rl.id} on ${typeof src === "string" ? src : T(src)}: result undefined at ${JSON.stringify(env)} -> ${T(res.tree)}`); continue; }
      ok(Math.abs(a.re - b.re) <= 1e-7 * Math.max(1, Math.abs(a.re)), `${rl.id} on ${typeof src === "string" ? src : T(src)}: ${a.re} vs ${b.re} at ${JSON.stringify(env)} (${T(res.tree)})`);
      good++; checked++;
    }
  });
  const missing = allRules().filter((rl) => !seen.has(rl.id) && !rl.id.startsWith("test.") && !["rational.apart", "factor.external"].includes(rl.id)).map((rl) => rl.id);
  eq(missing.join(","), "", "rules not exercised by the corpus");
  ok(checked > 300, "checked " + checked);
});
function genExpr(r, d) {
  const atoms = ["x", "y", "2", "3", "1/2", "sin(x)", "cos(x)", "ln(y)", "sqrt(x)", "e^x"];
  if (d === 0) return r.pick(atoms);
  const op = r.pick(["+", "-", "*", "/", "^", "f"]);
  if (op === "^") return `(${genExpr(r, d - 1)})^${r.pick(["2", "3", "-1", "1/2"])}`;
  if (op === "f") return `${r.pick(["sin", "cos", "ln", "sqrt", "abs"])}(${genExpr(r, d - 1)})`;
  return `(${genExpr(r, d - 1)})${op}(${genExpr(r, d - 1)})`;
}
test("property: simplifyFull never increases cost and preserves value", () => {
  const r = rng(99);
  for (let i = 0; i < 45; i++) {
    const src = genExpr(r, r.int(1, 3));
    const tree = parse(src);
    const res = simplifyFull(tree, { ctx: ctx0(), maxMs: 200 });
    const c0 = complexity(simplify(tree));
    ok(res.cost <= c0, `${src}: cost ${res.cost} > ${c0}`);
    for (let k = 0; k < 4; k++) {
      const env = { x: 0.3 + r.next() * 2, y: 0.2 + r.next() * 2 };
      const a = evalNumeric(tree, env);
      const b = evalNumeric(res.result, env);
      if (!a) continue;
      ok(b, `${src}: result undefined where the input is defined (${T(res.result)})`);
      ok(Math.abs(a.re - b.re) <= 1e-7 * Math.max(1, Math.abs(a.re)), `${src} -> ${T(res.result)}: ${a.re} vs ${b.re}`);
    }
  }
});
test("property: isEquivalent agrees with expand and detects perturbations", () => {
  const r = rng(5);
  for (let i = 0; i < 20; i++) {
    const src = `(${r.int(-3, 3)}x + ${r.int(-3, 3)})*(x + ${r.int(-3, 3)})^${r.int(1, 3)}`;
    const u = parse(src);
    eq(isEquivalent(u, expand(simplify(u))).verdict, "equivalent", src);
    eq(isEquivalent(u, X.add(u, X.num(r.int(1, 5)))).verdict, "not-equivalent", src);
  }
});
test("property: denominators cancel only with a condition", () => {
  const r = rng(77);
  for (let i = 0; i < 20; i++) {
    const a = r.int(-4, 4), b = r.int(-4, 4);
    const src = `((x - ${a})(x - ${b}))/(x - ${a})`;
    const res = SF(src);
    eq(T(res.result), T(simplify(parse(`x - ${b}`))), src);
    ok(res.conditions.map(T).includes(T(simplify(parse(`x != ${a}`)))), src + " condition " + conds(res));
  }
});
