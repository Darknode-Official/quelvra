import { test, eq, ok, rng } from "./harness.js";
import * as X from "../public/engine/expr.js";
import { parse } from "../public/engine/parse.js";
import { toText } from "../public/engine/print.js";
import { evalNumeric } from "../public/engine/rules.js";
import {
  inferDomain, domainConditions, equationConditions, checkPoint, normalizeCond, normalizeConditions, decideRel,
  parseAssumptions, parseAssumptionsDetailed, deriveTags, makeAssumeCtx, signUnder, safeSimplify, simplifyUnder,
  tightenConditions, constSign, rangeOf,
} from "../public/engine/domain.js";

const T = toText;
const dom = (s) => inferDomain(parse(s)).rels.map(T).join("; ");
const nc = (s, a = "") => normalizeCond(parse(s), makeAssumeCtx(a)).map(T).join("; ");
const su = (s, a = "") => { const ctx = makeAssumeCtx(a); return signUnder(safeSimplify(parse(s), ctx), ctx); };
const under = (s, a) => T(simplifyUnder(parse(s), a).result);
const tags = (a, name) => [...(parseAssumptions(a).get(name) || [])].sort().join(",");

// ---------------- inferDomain: one test per condition type ----------------
test("domain: denominators are nonzero", () => {
  eq(dom("1/(x-1)"), "x != 1");
  eq(dom("1/(x*y)"), "x != 0; y != 0");
  eq(dom("x/(x^2-1)"), "x^2 != 1");
  eq(dom("1/|x|"), "x != 0");
  eq(dom("1/x^2"), "x != 0");
});
test("domain: even roots need nonnegative radicands, positive in a denominator", () => {
  eq(dom("sqrt(x-3)"), "x >= 3");
  eq(dom("1/sqrt(x)"), "x > 0");
  eq(dom("x^(1/4)"), "x >= 0");
  eq(dom("cbrt(x)"), "");
  eq(dom("sqrt(x^2)"), "");
  eq(dom("sqrt(x^2+1)"), "");
});
test("domain: symbolic exponents", () => {
  eq(dom("x^y"), "x > 0");
  eq(dom("(-2)^x"), "isInteger(x)");
  eq(dom("0^x"), "x > 0");
  eq(dom("2^x"), "");
  eq(dom("e^x"), "");
});
test("domain: logarithms", () => {
  eq(dom("ln(x)"), "x > 0");
  eq(dom("log(x)"), "x > 0");
  eq(dom("log(b, x)"), "x > 0; b > 0; b != 1");
  eq(dom("ln(x^2)"), "x != 0");
  eq(dom("ln(|x|)"), "x != 0");
});
test("domain: inverse trig and hyperbolic", () => {
  eq(dom("asin(x)"), "x >= -1; x <= 1");
  eq(dom("acos(2x)"), "x >= -1/2; x <= 1/2");
  eq(dom("asec(x)"), "|x| >= 1");
  eq(dom("acosh(x)"), "x >= 1");
  eq(dom("atanh(x)"), "x > -1; x < 1");
  eq(dom("atan(x)"), "");
  eq(dom("asinh(x)"), "");
});
test("domain: tan/sec need cos != 0, cot/csc need sin != 0", () => {
  eq(dom("tan(x)"), "cos(x) != 0");
  eq(dom("sec(x)"), "cos(x) != 0");
  eq(dom("cot(x)"), "sin(x) != 0");
  eq(dom("csc(x)"), "sin(x) != 0");
  eq(dom("sin(x) + cos(x)"), "");
});
test("domain: factorial, gamma, mod", () => {
  eq(dom("x!"), "not (isInteger(x) and x < 0)");
  eq(dom("gamma(x)"), "not (isInteger(x) and x <= 0)");
  eq(dom("mod(x, y)"), "y != 0");
});
test("domain: records carry reasons and the subexpression", () => {
  const r = inferDomain(parse("ln(x-1)"));
  eq(r.conditions.length, 1);
  ok(/logarithm|ln/i.test(r.conditions[0].reason), r.conditions[0].reason);
  eq(T(r.conditions[0].sub), "x - 1");
  eq(r.empty, false);
  eq(domainConditions(parse("1/x")).map(T).join(), "x != 0");
});
test("domain: empty domains are detected", () => {
  ok(inferDomain(parse("acosh(x) + atanh(x)")).empty);
  ok(inferDomain(parse("sqrt(-1 - x^2)")).empty);
  ok(inferDomain(parse("ln(-2)")).empty);
  eq(dom("asin(x) + acosh(x)"), "x <= 1; x >= 1");
});
test("domain: bound variables are not constrained", () => {
  eq(dom("sum(1/k, k, 1, n)"), "");
});
test("domain: complex domain drops the real-only conditions", () => {
  eq(inferDomain(parse("sqrt(x)"), { domain: "complex" }).rels.length, 0);
  eq(inferDomain(parse("1/x"), { domain: "complex" }).rels.map(T).join(), "x != 0");
});

// ---------------- normalization ----------------
test("normalize: linear conditions are solved", () => {
  eq(nc("x - 1 != 0"), "x != 1");
  eq(nc("2x + 4 >= 0"), "x >= -2");
  eq(nc("-x - 3 < 0"), "x > -3");
  eq(nc("3 - x > 0"), "x < 3");
});
test("normalize: products split for != 0", () => {
  eq(nc("x*y != 0"), "x != 0; y != 0");
  eq(nc("(x-1)*(x+2) != 0"), "x != 1; x != -2");
});
test("normalize: abs, even and odd-negative powers", () => {
  eq(nc("|x| > 0"), "x != 0");
  eq(nc("abs(x-2) >= 0"), "");
  eq(nc("x^2 > 0"), "x != 0");
  eq(nc("x^2 + 1 > 0"), "");
  eq(nc("1/y > 0"), "y > 0");
});
test("normalize: bounded functions and constants", () => {
  eq(nc("sin(x) <= 1"), "");
  eq(nc("cos(x) >= -1"), "");
  eq(nc("exp(x) > 0"), "");
  eq(nc("3 > 2"), "");
  eq(nc("1 > 2"), "false");
  eq(nc("pi > 3"), "");
});
test("normalize: decided by assumptions", () => {
  eq(nc("x > 0", "x > 1"), "");
  eq(nc("x < 0", "x > 1"), "false");
  eq(nc("x - 5 > 0", "x > 7"), "");
  eq(nc("x != 0", "x > 0"), "");
  eq(normalizeConditions([parse("x > 0"), parse("x < 0")], makeAssumeCtx("x > 1")), null);
});
test("tighten: redundant bounds merge", () => {
  const recs = (ss) => ss.map((s) => ({ rel: parse(s), reason: "r" }));
  eq(tightenConditions(recs(["x > 0", "x > 2"])).map((c) => T(c.rel)).join("; "), "x > 2");
  eq(tightenConditions(recs(["x >= 1", "x != 1"])).map((c) => T(c.rel)).join("; "), "x > 1");
  eq(tightenConditions(recs(["x >= 1", "x != -3"])).map((c) => T(c.rel)).join("; "), "x >= 1");
  eq(tightenConditions(recs(["x != 5", "x >= 1"])).map((c) => T(c.rel)).join("; "), "x != 5; x >= 1");
  ok(tightenConditions(recs(["x > 1", "x < 0"])).some((c) => c.rel.k === "bool"));
});

// ---------------- checkPoint ----------------
test("checkPoint: exact decisions", () => {
  const c = inferDomain(parse("sqrt(x) + 1/(x-4)"));
  eq(checkPoint(c, { x: 1 }).ok, true);
  eq(checkPoint(c, { x: 4 }).ok, false);
  eq(checkPoint(c, { x: -1 }).ok, false);
  eq(checkPoint(c, { x: "9/4" }).method, "exact");
  eq(checkPoint([parse("x^2 != 4")], { x: 2 }).ok, false);
  eq(checkPoint([X.fn("isInteger", X.sym("n"))], { n: "3/2" }).ok, false);
  eq(checkPoint([X.fn("isInteger", X.sym("n"))], { n: 6 }).ok, true);
  eq(checkPoint(inferDomain(parse("x!")), { x: -3 }).ok, false);
  eq(checkPoint(inferDomain(parse("x!")), { x: "-5/2" }).ok, true);
});
test("checkPoint: numeric high-precision fallback says so", () => {
  const c = [parse("x - sqrt(2) > 0")];
  const a = checkPoint(c, { x: "7/5" }), b = checkPoint(c, { x: "3/2" });
  eq(a.ok, false); eq(b.ok, true);
  eq(a.method, "numeric"); eq(a.results[0].method, "numeric-high-precision");
  ok(a.note && /numerical/.test(a.note));
  eq(checkPoint(c, { x: "1.414" }).ok, false);
  eq(checkPoint(c, { x: "1.415" }).ok, true);
  eq(checkPoint([parse("pi - 314159/100000 > 0")], {}).ok, true);
  eq(checkPoint([parse("pi - 314160/100000 > 0")], {}).ok, false);
});
test("checkPoint: undecided when variables remain", () => {
  const r = checkPoint([parse("x + y > 0")], { x: 1 });
  eq(r.ok, null); eq(r.undecided.length, 1);
});
test("checkPoint: extraneous roots are rejected", () => {
  const cases = [
    ["sqrt(x+2) = x", [[-1, false], [2, true]]],
    ["ln(x) + ln(x-2) = ln(3)", [[-1, false], [3, true]]],
    ["sqrt(x-3) = 0", [[1, false], [3, true]]],
    ["1/(x-1) = 2", [[1, false], ["3/2", true]]],
    ["sqrt(2x+3) = x", [[-1, false], [3, true]]],
    ["|x| = x - 2", [[1, false]]],
  ];
  for (const [s, pts] of cases) {
    const c = equationConditions(parse(s));
    for (const [x, want] of pts) eq(checkPoint(c, { x }).ok, want, s + " at x = " + x);
  }
  eq(equationConditions(parse("sqrt(x+2) = x")).rels.map(T).join(), "x >= 0");
  eq(equationConditions(parse("ln(x) + ln(x-2) = ln(3)")).rels.map(T).join(), "x > 2");
});

// ---------------- assumptions ----------------
test("assumptions: inequality forms", () => {
  eq(tags("x > 0", "x"), "nonnegative,nonzero,positive,real");
  eq(tags("x >= 0", "x"), "nonnegative,real");
  eq(tags("y < 0", "y"), "negative,nonpositive,nonzero,real");
  eq(tags("a != 0", "a"), "nonzero,real");
  eq(tags("0 < x", "x"), "nonnegative,nonzero,positive,real");
});
test("assumptions: integer forms", () => {
  eq(tags("n integer", "n"), "integer,rational,real");
  eq(tags("n is an even integer", "n"), "even,integer,rational,real");
  eq(tags("k in Z", "k"), "integer,rational,real");
  eq(tags("x real", "x"), "real");
  eq(tags("z positive", "z"), "nonnegative,nonzero,positive,real");
});
test("assumptions: lists, chains and unparsed parts", () => {
  const r = parseAssumptionsDetailed("x >= 0, y < 0");
  ok(r.assume.has("x") && r.assume.has("y"));
  const c = parseAssumptionsDetailed("-pi/2 <= x <= pi/2");
  const b = c.bounds.get("x");
  eq(T(b.lo), "-pi/2"); eq(T(b.hi), "pi/2"); eq(b.loOpen, false); eq(b.hiOpen, false);
  eq(parseAssumptionsDetailed("p prime").unparsed.join(), "p prime");
  eq(parseAssumptionsDetailed("x > 1").bounds.get("x").loOpen, true);
});
test("assumptions: deriveTags closes the tag set", () => {
  const d = (a) => [...deriveTags(new Set(a))].sort().join(",");
  eq(d(["positive"]), "nonnegative,nonzero,positive,real");
  eq(d(["even"]), "even,integer,rational,real");
  eq(d(["negative", "integer"]), "integer,negative,nonpositive,nonzero,rational,real");
});

// ---------------- signUnder / decideRel / ranges ----------------
test("signUnder", () => {
  eq(su("x", "x > 0"), 1);
  eq(su("-x", "x > 0"), -1);
  eq(su("x^2"), "nn");
  eq(su("x^2 + 1"), 1);
  eq(su("x - 5", "x > 7"), 1);
  eq(su("x*y", "x > 0, y < 0"), -1);
  eq(su("x", "x >= 0"), "nn");
  eq(su("x + y", "x > 0, y > 0"), 1);
  eq(su("sin(x) + 2"), 1);
  eq(su("cos(x) - 3"), -1);
  eq(su("x"), null);
  eq(su("x - 1", "0 <= x <= 1"), "np");
});
test("decideRel", () => {
  eq(decideRel(parse("x > 0"), makeAssumeCtx("x > 1")), true);
  eq(decideRel(parse("x < 0"), makeAssumeCtx("x > 1")), false);
  eq(decideRel(parse("x > 2"), makeAssumeCtx("x > 1")), null);
});
test("constSign and rangeOf", () => {
  eq(constSign(parse("sqrt(2) - 7/5")), 1);
  eq(constSign(parse("pi - 22/7")), -1);
  eq(constSign(parse("e - 2718281828/1000000000")), 1);
  const r = rangeOf(safeSimplify(parse("sin(x)^2 + 1")), makeAssumeCtx(""));
  eq(T(X.num(r.lo)), "1"); eq(T(X.num(r.hi)), "2");
});

// ---------------- simplifyUnder ----------------
test("simplifyUnder: assumptions unlock rewrites", () => {
  eq(under("sqrt(x^2)", "x > 0"), "x");
  eq(under("sqrt(x^2)", ""), "|x|");
  eq(under("|x|", "x < 0"), "-x");
  eq(under("|x-5|", "x > 7"), "x - 5");
  eq(under("asin(sin(x))", "-pi/2 <= x <= pi/2"), "x");
  eq(under("asin(sin(x))", ""), "asin(sin(x))");
  eq(under("(x^a)^b", "x > 0"), "x^(a*b)");
  eq(under("(x^a)^b", ""), "(x^a)^b");
  eq(under("sqrt(x^2*y^2)", "x > 0, y < 0"), "-x*y");
});
test("simplifyUnder: piecewise decided by an assumption", () => {
  const pw = X.piecewise(X.sym("x"), X.rel(">", X.sym("x"), X.ZERO), X.neg(X.sym("x")), X.TRUE);
  eq(T(simplifyUnder(pw, "x > 3").result), "x");
  eq(T(simplifyUnder(pw, "x < -1").result), "-x");
  ok(simplifyUnder(pw, "").result.k === "piecewise");
});
test("simplifyUnder: returns the assumption context", () => {
  const r = simplifyUnder(parse("x"), "x > 0");
  ok(r.ctx.assume.get("x").has("positive"));
});

// ---------------- property: domain conditions match real evaluability ----------------
// Polynomials with small integer coefficients evaluated at dyadic points k/4 are exact in doubles,
// so a finite real value must coincide with all domain conditions holding.
test("property: conditions hold exactly when the real value is finite", () => {
  const R = rng(20260925);
  const poly = () => {
    const deg = R.int(1, 2), cs = [];
    for (let i = 0; i <= deg; i++) cs.push(R.int(-3, 3));
    if (cs[deg] === 0) cs[deg] = R.pick([1, -1, 2]);
    return cs.map((c, i) => "(" + c + ")" + (i === 0 ? "" : i === 1 ? "*x" : "*x^" + i)).join(" + ");
  };
  const wrap = (p) => R.pick([
    () => "sqrt(" + p + ")", () => "ln(" + p + ")", () => "1/(" + p + ")", () => "asin(" + p + ")",
    () => "acos(" + p + ")", () => "atanh(" + p + ")", () => "acosh(" + p + ")", () => "(" + p + ")^(1/4)",
    () => "log(2, " + p + ")", () => "1/sqrt(" + p + ")",
  ])();
  let checked = 0, defined = 0;
  for (let n = 0; n < 60; n++) {
    const src = R.next() < 0.5 ? wrap(poly()) : wrap(poly()) + R.pick([" + ", " * "]) + wrap(poly());
    const tree = parse(src);
    const d = inferDomain(tree);
    for (let k = -12; k <= 12; k++) {
      const x = k / 4;
      const v = evalNumeric(tree, { x }, { mode: "real" });
      const finite = !!v && Number.isFinite(v.re) && Math.abs(v.im || 0) < 1e-12;
      const r = checkPoint(d, { x: k + "/4" });
      eq(r.ok, finite, src + " at x = " + k + "/4");
      eq(r.method, "exact", src);
      checked++; if (finite) defined++;
    }
  }
  ok(checked === 60 * 25 && defined > 100 && defined < checked - 100, "mix " + defined + "/" + checked);
});
test("safeSimplify absorbs the foundation stack overflow on (-x)^(1/2)", () => {
  const r = safeSimplify(parse("(-x)^(1/2)"));
  ok(r === null || r.k === "pow");
  eq(dom("sqrt(-x)"), "x <= 0");
});
