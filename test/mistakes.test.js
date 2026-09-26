import { test, eq, ok } from "./harness.js";
import { checkLines } from "../public/engine/mistakes.js";

const verdict = (ls) => checkLines(ls).verdict;
const diag = (ls) => (checkLines(ls).firstMistake?.diagnosis || []).map((d) => d.id);

test("correct linear working", () => eq(verdict(["2x + 3 = 7", "2x = 4", "x = 2"]), "all-correct"));
test("wrong subtraction", () => eq(verdict(["2x + 3 = 7", "2x = 10", "x = 5"]), "mistake"));
test("first mistake located", () => eq(checkLines(["2x + 3 = 7", "2x = 4", "x = 3"]).firstMistake.from, 2));
test("move without sign change diagnosed", () => ok(diag(["2x + 3 = 7", "2x = 10"]).includes("move-no-sign-change")));
test("divide one term diagnosed", () => ok(diag(["2x + 4 = 10", "x + 4 = 5"]).includes("divide-one-term")));
test("square of sum diagnosed", () => ok(diag(["(x+1)^2", "x^2+1"]).includes("square-of-sum")));
test("expression expansion correct", () => eq(verdict(["(x+1)^2", "x^2+2x+1"]), "all-correct"));
test("distribute first only diagnosed", () => ok(diag(["3(x+2)", "3x+2"]).includes("distribute-first-only")));
test("sign distribute diagnosed", () => ok(diag(["5-(x-2)", "5-x-2"]).includes("sign-distribute")));
test("root of sum diagnosed", () => ok(diag(["sqrt(x^2+9)", "x+3"]).includes("root-of-sum")));
test("log of sum diagnosed", () => ok(diag(["ln(x+1)", "ln(x)+ln(1)"]).includes("log-of-sum")));
test("power of power diagnosed", () => ok(diag(["(x^2)^3", "x^5"]).includes("power-of-product-add")));
test("inequality flip missing", () => {
  const r = checkLines(["-2x < 6", "x < -3"]);
  eq(r.verdict, "mistake");
  ok(r.firstMistake.diagnosis.some((d) => d.id === "no-flip"));
});
test("inequality correct flip", () => eq(verdict(["-2x < 6", "x > -3"]), "all-correct"));
test("squaring both sides is conditional, not wrong", () => {
  const r = checkLines(["sqrt(x+2) = x", "x+2 = x^2"]);
  eq(r.transitions[0].status, "ok-conditional");
});
test("dividing by x loses a solution", () => {
  const r = checkLines(["x^2 = 3x", "x = 3"]);
  eq(r.firstMistake.kind, "lost-solutions");
});
test("quadratic factoring correct", () => eq(verdict(["x^2-5x+6=0", "(x-2)(x-3)=0"]), "all-correct"));
test("multivariable solved-for", () => eq(verdict(["2x + y = 5", "y = 5 - 2x"]), "all-correct"));
test("parse error reported", () => eq(checkLines(["2x+3=7", "2x = (4"]).transitions[0].kind, "parse-error"));
test("trig identity step", () => eq(verdict(["sin(x)^2 + cos(x)^2 + x", "1 + x"]), "all-correct"));
