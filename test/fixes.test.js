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

test("standard deviation and variance give sample and population, labelled", () => {
  const r = run("standard deviation of 2, 4, 4, 4, 5, 5, 7, 9");
  ok(r.verification.status === "passed");
  eq(r.answers.map((a) => a.label + " = " + toText(a.tree)).join("; "), "Sample standard deviation (divide by n - 1) = 4sqrt(14)/7; Population standard deviation (divide by n) = 2");
  eq(run("variance of 1, 2, 3, 4").answers.map((a) => toText(a.tree)).join("; "), "5/3; 5/4");
});
test("complex numbers print real part first", () => {
  eq(ans("(3+4i)(1-2i)"), "11 - 2i");
  eq(ans("(2+i)/(1-i)"), "1/2 + 3i/2");
  eq(ans("i*(2+i)"), "-1 + 2i");
});
test("finite series without the words arithmetic or geometric", () => {
  eq(ans("sum of the first 10 terms of 2, 6, 18, ..."), "59048");
  eq(ans("sum of first 20 terms of 3, 7, 11, ..."), "820");
  ok(!run("sum of the first 5 terms of 1, 2, 5, ...").ok, "neither arithmetic nor geometric: refused");
});
test("graph edges with a space-separated weight", () => {
  const r = run("shortest path from A to D in graph A-B 1, B-D 2, A-C 4, C-D 1");
  ok(r.verification.status === "passed");
  ok(/distance = 3/.test(r.answers.map((a) => a.label + " = " + (a.tree ? toText(a.tree) : a.text)).join("; ")), "distance 3");
});
test("logic and set requests use the advanced discrete engine", () => {
  const labels = (s) => run(s).answers.map((a) => a.label);
  ok(labels("is p or not p a tautology").includes("classification"));
  ok(labels("{1, 2, 3} union {3, 4, 5}").includes("cardinality"));
});
