// Regressions for gaps found while widening recognition (congruences, greetings, simplify, vectors).
import { test, eq, ok } from "./harness.js";
import { solve } from "../public/engine/quelvra.js";
import { simplify } from "../public/engine/simplify.js";
import { parse } from "../public/engine/parse.js";
import { toText } from "../public/engine/print.js";

const run = (s) => solve(s, { timeLimit: 6000 });
const ans = (s) => { const r = run(s); ok(r.ok && r.verification.status === "passed", `${s}: not verified`); return r.answers.filter((a) => a.tree).map((a) => toText(a.tree)).join("; "); };
const S = (s) => toText(simplify(parse(s)));

test("congruence notation is solved over the integers", () => {
  eq(ans("3x ≡ 2 (mod 7)"), "7k + 3");
  eq(ans("3x = 2 (mod 7)"), "7k + 3");
  eq(ans("3x = 2 mod 7"), "7k + 3");
  eq(ans("4x ≡ 2 (mod 6)"), "3k + 2");
  eq(ans("x ≡ 2 (mod 3); x ≡ 3 (mod 5)"), "15k + 8");
  const r = run("2x ≡ 1 (mod 4)");
  ok(r.noSolution, "2x = 1 (mod 4) has no solution");
  // the remainder function written as a call stays a real equation
  eq(ans("mod(3x, 7) = 2"), "(7k + 2)/3");
});
test("greetings are refused, not read as products", () => {
  for (const s of ["hi", "hey!", "ok", "thanks", "hello"]) ok(!run(s).ok, s);
  eq(ans("x^2 - 4 = 0"), "-2; 2");
});
test("scaled sums cancel only when terms cancel", () => {
  eq(S("x+1-(x+1)"), "0");
  eq(S("a-(a-b)"), "b");
  eq(S("3(x+y)-3y+1"), "3x + 1");
  eq(S("6(x-3)+9"), "6(x - 3) + 9");
  eq(S("x+2(y+1)"), "x + 2(y + 1)");
});
test("simplify of a constant evaluates and rationalises", () => {
  eq(ans("simplify(1/(1+sqrt(2)))"), "sqrt(2) - 1");
  eq(ans("rationalize 1/(1+sqrt(2))"), "sqrt(2) - 1");
  eq(ans("simplify 1/(sqrt(2)+sqrt(3))"), "sqrt(3) - sqrt(2)");
  eq(ans("simplify(2/4)"), "1/2");
});
test("dot and cross products", () => {
  eq(ans("dot product of [1,2,3] and [4,5,6]"), "32");
  eq(ans("cross([1,2,3],[4,5,6])"), "[-3, 6, -3]");
  eq(ans("cross product of [1,0,0] and [0,1,0]"), "[0, 0, 1]");
  eq(ans("cross([a,b,c],[1,0,0])"), "[0, c, -b]");
  ok(!run("dot([1,2],[3,4,5])").ok || run("dot([1,2],[3,4,5])").answers.every((a) => !a.tree), "length mismatch refused");
});
