import { test, eq, ok, throws, T, P, rng } from "./harness.js";
import * as N from "../public/engine/num.js";
import * as X from "../public/engine/expr.js";
import { parse, parseDetailed } from "../public/engine/parse.js";
import { simplify, expand, together, makeCtx } from "../public/engine/simplify.js";
import { toText, toLatex } from "../public/engine/print.js";

const cases = [
  ["1/3+1/3+1/3", "1"], ["x + 2x", "3x"], ["x+y+x", "2x + y"], ["x - y", "x - y"],
  ["2(x+y)", "2(x + y)"], ["(x^2)^3", "x^6"], ["sqrt(x^2)", "|x|"], ["x/x", "1"],
  ["sqrt(8)", "2sqrt(2)"], ["sqrt(72)", "6sqrt(2)"], ["1/sqrt(2)", "sqrt(2)/2"], ["sqrt(-4)", "2i"],
  ["(-8)^(1/3)", "-2"], ["sin(pi/6)", "1/2"], ["cos(pi/4)", "sqrt(2)/2"], ["tan(pi/3)", "sqrt(3)"],
  ["sin(-x)", "-sin(x)"], ["cos(-x)", "cos(x)"], ["ln(e^2)", "2"], ["e^(ln(x))", "x"], ["log_2(8)", "3"],
  ["log(1000)", "3"], ["|-3|", "3"], ["|x^2|", "x^2"], ["5!", "120"], ["0^0", "undefined"], ["1/0", "undefined"],
  ["x*x*x", "x^3"], ["x^(1/2)*x^(1/2)", "x"], ["sqrt(2)*sqrt(3)", "sqrt(6)"], ["sqrt(2)*sqrt(2)", "2"],
  ["i^2", "-1"], ["i^3", "-i"], ["(2x)^2", "4x^2"], ["sqrt(4x)", "2sqrt(x)"], ["0.1+0.2", "3/10"],
  ["2^10", "1024"], ["(x^3)^(1/3)", "x"], ["(x^4)^(1/2)", "x^2"], ["(x^6)^(1/4)", "|x|^(3/2)"], ["x^(-2)", "1/x^2"],
  ["3/(2x)", "3/(2x)"], ["-x^2", "-x^2"], ["sin^-1(1/2)", "pi/6"], ["30°", "pi/6"], ["binomial(10,3)", "120"],
  ["gcd(12,18)", "6"], ["sin(pi)", "0"], ["cos(pi)", "-1"], ["sin(7pi/6)", "-1/2"], ["tan(pi/2)", "undefined"],
  ["ln(1)", "0"], ["ln(0)", "undefined"], ["ln(-1)", "undefined"], ["sqrt(1/2)", "sqrt(2)/2"], ["8^(2/3)", "4"],
  ["(1/4)^(-1/2)", "2"], ["27^(-1/3)", "1/3"], ["x^0", "1"], ["0*x", "0"], ["oo - oo", "undefined"],
  ["asin(sqrt(2)/2)", "pi/4"], ["acos(-1/2)", "2pi/3"], ["atan(sqrt(3))", "pi/3"],
];
for (const [src, want] of cases) test(`simplify ${src}`, () => eq(T(src), want, src));

test("x/x records the condition x != 0", () => {
  const ctx = makeCtx({ conditions: [] });
  eq(toText(simplify(parse("x/x"), ctx)), "1");
  ok(ctx.conditions.some((c) => toText(c.node) === "x" && c.rel === "!=0"));
});
test("sqrt(x^2) is not x (adversarial)", () => ok(T("sqrt(x^2)") !== "x"));
test("(x^2)^(1/2) with x > 0 is x", () => {
  const ctx = makeCtx({ assume: new Map([["x", new Set(["positive"])]]) });
  eq(toText(simplify(parse("(x^2)^(1/2)"), ctx)), "x");
});
test("complex domain keeps sqrt(x^2)", () => {
  const ctx = makeCtx({ domain: "complex" });
  ok(toText(simplify(parse("sqrt(x^2)"), ctx)) !== "x");
});
test("expand (x+1)^3", () => eq(toText(expand(parse("(x+1)^3"))), "x^3 + 3x^2 + 3x + 1"));
test("expand (a+b)(a-b)", () => eq(toText(expand(parse("(a+b)(a-b)"))), "a^2 - b^2"));
test("together 1/x + 1/(x+1)", () => eq(toText(together(parse("1/x + 1/(x+1)"))), "(2x + 1)/(x(x + 1))"));

// parser
const parses = [
  ["2x", "2x"], ["2 x", "2x"], ["2*x", "2x"], ["2·x", "2x"], ["2×x", "2x"], ["x^2", "x^2"], ["x**2", "x^2"], ["x²", "x^2"],
  ["x^{2}", "x^2"], ["\\sqrt{x}", "sqrt(x)"], ["√x", "sqrt(x)"], ["x^(1/2)", "sqrt(x)"], ["sin x", "sin(x)"], ["\\sin x", "sin(x)"],
  ["sin^2 x", "sin(x)^2"], ["\\frac{a}{b}", "a/b"], ["|x - 3|", "|x - 3|"], ["π", "pi"], ["3 ≤ x", "3 <= x"],
  ["x ≠ 2", "x != 2"], ["2(x+1)", "2(x + 1)"], ["(x+1)(x-1)", "(x - 1)(x + 1)"], ["\\sqrt[3]{x}", "cbrt(x)"],
  ["log_{10}(100)", "2"], ["\\log_2 8", "3"], ["arcsin(1)", "pi/2"], ["e^{i pi}", "-1"],
];
for (const [src, want] of parses) test(`parse ${src}`, () => eq(T(src), want, src));
test("parse 1/2x warns", () => {
  const r = parseDetailed("1/2x");
  eq(toText(simplify(r.node)), "x/2");
  ok(r.warnings.length > 0);
});
test("parse error has position and hint", () => {
  try { parse("(x+1"); ok(false, "should throw"); } catch (e) { ok(e.pos >= 0 && e.hint, "pos/hint"); }
});
test("parse integral with bounds", () => {
  const u = parse("\\int_0^1 x^2 \\, dx");
  eq(u.k, "integral"); eq(u.args.length, 4);
});
test("parse derivative", () => { const u = parse("d/dx (x^3 + 1)"); eq(u.k, "deriv"); eq(u.args[1].name, "x"); });
test("parse limit one-sided", () => { const u = parse("lim_(x->0^+) 1/x"); eq(u.k, "limit"); eq(u.dir, "+"); });
test("parse limit plain", () => { const u = parse("lim x->0 sin(x)/x"); eq(u.k, "limit"); eq(toText(simplify(u.args[0])), "sin(x)/x"); });
test("parse system", () => eq(parse("2x+y=5, x-y=1").k, "system"));
test("parse matrix", () => { const u = parse("[[1,2],[3,4]]"); eq(u.k, "matrix"); eq(u.args.length, 2); });
test("parse chained inequality", () => eq(T("3 < x <= 5"), "3 < x <= 5"));
test("parse sum", () => eq(parse("sum_(i=1)^(n) i^2").k, "sum"));
test("parse sum binds i (not imaginary)", () => ok(X.hasSym(parse("sum_(i=1)^(10) i").args[0], "i")));
test("latex output", () => eq(toLatex(P("x^2/2 + sqrt(x)")), "\\frac{x^{2}}{2} + \\sqrt{x}"));

// hash-consing
test("hash-consing gives identity", () => ok(parse("x^2 + 1") === parse("x^2+1")));
test("canonical forms coincide", () => ok(P("x + 2x - 3") === P("-3 + 3x")));

// number tower
test("rational arithmetic exact", () => eq(N.toString(N.add(N.Q(1, 3), N.Q(1, 6))), "1/2"));
test("big integers", () => eq(T("2^200 - 2^200 + 1"), "1"));
test("decimal expansion", () => eq(N.toDecimalString(N.Q(1, 7), 10), "0.1428571429"));
test("iroot exact", () => { const [r, ex] = N.iroot(10n ** 40n, 2); ok(ex && r === 10n ** 20n); });
test("zero denominator throws", () => throws(() => N.Q(1, 0)));

// property: printing then re-parsing is the identity on canonical forms
test("property: print/parse round trip", () => {
  const r = rng(7);
  const atoms = ["x", "y", "2", "3", "1/2", "pi", "sqrt(2)", "sin(x)", "e^x", "ln(y)"];
  const gen = (d) => {
    if (d === 0) return r.pick(atoms);
    const op = r.pick(["+", "-", "*", "/", "^"]);
    if (op === "^") return `(${gen(d - 1)})^${r.pick(["2", "3", "-1", "1/2"])}`;
    return `(${gen(d - 1)})${op}(${gen(d - 1)})`;
  };
  for (let i = 0; i < 300; i++) {
    const src = gen(r.int(1, 3));
    const a = P(src);
    const b = P(toText(a));
    if (a !== b) throw new Error(`round trip failed for ${src}: ${toText(a)} -> ${toText(b)}`);
  }
});
