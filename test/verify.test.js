import { test, eq, ok } from "./harness.js";
import * as X from "../public/engine/expr.js";
import { parse } from "../public/engine/parse.js";
import { simplify } from "../public/engine/simplify.js";
import { diff } from "../public/engine/calc/diff.js";
import { verifySolution, equivalent, verifyAntiderivative, verifySolutionSet, evalReal, evalC } from "../public/engine/verify.js";

const P = (s) => simplify(parse(s));
const vs = (eqn, x, v) => verifySolution(parse(eqn), new Map([[x, P(v)]])).status;

test("x=2 solves 2x+3=7 exactly", () => eq(vs("2x+3=7", "x", "2"), "verified-exact"));
test("x=3 fails 2x+3=7", () => eq(vs("2x+3=7", "x", "3"), "failed"));
test("quadratic root with surd", () => eq(vs("x^2-2=0", "x", "sqrt(2)"), "verified-exact"));
test("extraneous root of sqrt eq rejected", () => ok(["failed", "rejected-domain"].includes(vs("sqrt(x+2)=x", "x", "-1"))));
test("x=2 is valid for sqrt(x+2)=x", () => eq(vs("sqrt(x+2)=x", "x", "2"), "verified-exact"));
test("division by zero candidate rejected", () => eq(vs("x/(x-1) = 1/(x-1)", "x", "1"), "rejected-domain"));
test("log of negative rejected", () => eq(vs("ln(x)+ln(x-2)=ln(3)", "x", "-1"), "rejected-domain"));
test("log candidate accepted", () => ok(vs("ln(x)+ln(x-2)=ln(3)", "x", "3").startsWith("verified")));
test("complex root rejected in real domain", () => eq(vs("x^2+1=0", "x", "i"), "rejected-domain"));
test("complex root verified in complex domain", () => ok(verifySolution(parse("x^2+1=0"), new Map([["x", X.I]]), { domain: "complex" }).status.startsWith("verified")));
test("system solution", () => eq(verifySolution(parse("2x+y=5, x-y=1"), new Map([["x", P("2")], ["y", P("1")]])).status, "verified-exact"));
test("transcendental numeric root", () => eq(verifySolution(parse("x=cos(x)"), new Map([["x", X.num(0.7390851332151607.toString().replace(".", "") * 1, 10 ** 16)]])).status, "verified-numeric"));
test("equivalent: (x+1)^2 vs x^2+2x+1", () => ok(equivalent(parse("(x+1)^2"), parse("x^2+2x+1")).status.startsWith("equivalent")));
test("equivalent catches (x+1)^2 vs x^2+1", () => eq(equivalent(parse("(x+1)^2"), parse("x^2+1")).status, "different"));
test("equivalent sin^2+cos^2 = 1", () => ok(equivalent(parse("sin(x)^2+cos(x)^2"), parse("1")).status.startsWith("equivalent")));
test("antiderivative check (numeric, independent)", () => eq(verifyAntiderivative(parse("x^3/3 + sin(x)"), parse("x^2+cos(x)"), "x").status, "verified-numeric"));
test("antiderivative check with diff", () => ok(verifyAntiderivative(parse("x ln(x) - x"), parse("ln(x)"), "x", { diffFn: diff }).status.startsWith("verified")));
test("wrong antiderivative caught", () => eq(verifyAntiderivative(parse("x^3"), parse("x^2"), "x").status, "failed"));
test("inequality set check", () => {
  const r = verifySolutionSet(parse("x^2-4>0"), "x", (v) => v < -2 || v > 2, { boundaries: [-2, 2] });
  eq(r.status, "verified-numeric");
});
test("inequality wrong set caught", () => eq(verifySolutionSet(parse("x^2-4>0"), "x", (v) => v > 2, { boundaries: [-2, 2] }).status, "failed"));
test("evaluator real cube root of negative", () => ok(Math.abs(evalReal(parse("(-8)^(1/3)"), {}) + 2) < 1e-12));
test("evaluator sqrt negative undefined in real", () => ok(Number.isNaN(evalReal(parse("sqrt(x)"), { x: -1 }))));
test("evaluator complex sqrt(-1)", () => { const c = evalC(parse("sqrt(x)"), { x: -1 }, "complex"); ok(Math.abs(c.im - 1) < 1e-12); });
test("evaluator gamma(5)=24", () => ok(Math.abs(evalReal(parse("gamma(5)"), {}) - 24) < 1e-9));
