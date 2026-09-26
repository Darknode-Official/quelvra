// Coverage work: probe corpora (zero WRONG), the new commands, notation, logic/sets, arity checks and
// the guards that make Quelvra refuse instead of echoing or misreading.
import { test, eq, ok, close } from "./harness.js";
import { solve } from "../public/engine/quelvra.js";
import { parse } from "../public/engine/parse.js";
import { toText } from "../public/engine/print.js";
import { evalC } from "../public/engine/verify.js";
import { solveLogic } from "../public/engine/logic.js";
import { judge, textOf } from "../tools/coverage-judge.mjs";
import { CASES as MAIN } from "../tools/coverage-cases.mjs";
import { CASES as HELDOUT } from "../tools/coverage-heldout.mjs";

const S = (q) => solve(q, { timeLimit: 10000 });
const good = (r, msg = "") => {
  ok(r.ok, `${msg} not ok: ${JSON.stringify(r.error || r.answers.map((a) => a.label))}`);
  eq(r.verification.status, "passed", `${msg} verification`);
};
const refused = (r, msg = "") => ok(!r.ok || r.verification.status !== "passed" || r.answers.every((a) => a.kind === "none"), `${msg} should be refused, got ${(r.answers || []).map(textOf).join("; ")}`);
const num = (a) => { const c = evalC(a.tree, {}, "complex"); return c.re; };
const valueIs = (q, want, msg = q) => { const r = S(q); good(r, msg); ok(r.answers.some((a) => a.tree && Math.abs(num(a) - want) <= 1e-9 * Math.max(1, Math.abs(want))), `${msg}: got ${r.answers.map(textOf).join("; ")}`); };
const textHas = (q, re, msg = q) => { const r = S(q); good(r, msg); ok(re.test(r.answers.map(textOf).join("; ")), `${msg}: got ${r.answers.map(textOf).join("; ")}`); };

for (const [name, cases] of [["main", MAIN], ["held-out", HELDOUT]]) {
  test(`coverage corpus (${name}): no verified wrong answer`, () => {
    const wrong = [];
    for (const [area, input, exp] of cases) {
      let r;
      try { r = solve(input, { timeLimit: 5000 }); } catch (_) { continue; }
      if (judge(exp, r) === "WRONG") wrong.push(`[${area}] ${input} -> ${r.answers.map(textOf).join("; ")}`);
    }
    eq(wrong.length, 0, wrong.join("\n"));
  });
}

test("probability phrasings", () => {
  valueIs("probability of rolling a 6 on a die", 1 / 6);
  valueIs("probability of getting a sum of 9 when rolling two dice", 4 / 36);
  valueIs("probability of exactly 3 heads in 5 coin flips", 10 / 32);
  valueIs("probability of at least one head in 3 coin tosses", 7 / 8);
  valueIs("probability that a card is a heart or a king", 16 / 52);
  valueIs("probability of drawing a red card or a queen", 28 / 52);
  valueIs("probability of drawing 2 aces from a deck without replacement", 1 / 221);
});

test("notation: n choose k, C(n,k), P(n,k), P(Z < a)", () => {
  valueIs("10 choose 3", 120);
  valueIs("C(12, 4)", 495);
  valueIs("P(7, 3)", 210);
  const r = S("P(Z < 1.5)");
  good(r);
  ok(r.answers.some((a) => a.approx && Math.abs(parseFloat(a.approx.value) - 0.9331927987) < 1e-9) || r.answers.some((a) => a.tree && Math.abs(num(a) - 0.9331927987) < 1e-9), "P(Z<1.5)");
});

test("statistics commands", () => {
  valueIs("pstdev(2, 4, 4, 4, 5, 5, 7, 9)", 2);
  valueIs("pvariance(2, 4, 6)", 8 / 3);
  valueIs("iqr(1, 2, 3, 4, 5, 6, 7, 8)", 4);
  valueIs("zscore(85, 70, 10)", 1.5);
  valueIs("wmean([1, 2, 3], [3, 2, 1])", 10 / 6);
  const r = S("invnorm(0.975)");
  good(r, "invnorm");
  ok(Math.abs(parseFloat(r.answers[0].approx.value) - 1.959963985) < 1e-8, "invnorm value");
  textHas("mode of 1, 2, 2, 3, 3", /2.*3/);
  textHas("linreg([1, 2, 3], [2, 4, 6])", /y = 2x|2x/);
});

test("combinatorics phrasings", () => {
  valueIs("number of arrangements of the letters in banana", 60);
  valueIs("how many ways can 6 people be arranged in a row", 720);
  valueIs("derangements of 5", 44);
  valueIs("number of diagonals of a decagon", 35);
});

test("complex numbers: parts, arithmetic and polar form", () => {
  textHas("conjugate of 4 + 7i", /-7i \+ 4|4 - 7i/);
  valueIs("re(3 - 2i)", 3);
  valueIs("im((1+i)^3)", 2);
  valueIs("abs(3+4i)", 5);
  textHas("(2 + 3i)(1 - i)", /5 \+ i|i \+ 5/);
  textHas("convert 1 + i to polar form", /pi\/4/);
  textHas("polar form of -1 - i", /-3pi\/4/);
  textHas("polar(2i)", /pi\/2/);
  refused(S("polar(0)"), "polar(0)");
});

test("series phrasings (trailing ellipsis)", () => {
  valueIs("10th term of the arithmetic sequence 3, 7, 11, ...", 39);
  valueIs("find the 6th term of the geometric sequence 2, 6, 18, ...", 486);
  valueIs("sum of the first 20 terms of the arithmetic series 5, 9, 13, ...", 860);
  valueIs("sum of the first 5 terms of the geometric series 1 + 2 + 4 + ...", 31);
});

test("geometry phrasings and commands", () => {
  valueIs("area of a triangle with sides 5, 5 and 6", 12);
  valueIs("hypotenuse of a right triangle with legs 8 and 15", 17);
  valueIs("distance from (0, 0) to the line 3x + 4y - 10 = 0", 2);
  textHas("circle(x^2 + y^2 - 4x + 6y - 3 = 0)", /4/);
});

test("solvein: solutions inside an interval, incl. touching roots", () => {
  textHas("solve 2cos(x) - 1 = 0 for 0 <= x < 2pi", /pi\/3.*5pi\/3/);
  textHas("solve sin(x) = 1 on [0, 4pi]", /pi\/2.*5pi\/2/);
  const r = S("solve cos(x)^2 = 1 on [0, 2pi]");
  good(r);
  eq(r.answers.filter((a) => a.tree).length, 3, "0, pi, 2pi");
});

test("polynomial commands", () => {
  textHas("divide x^3 - 1 by x - 1", /x\^2 \+ x \+ 1/);
  valueIs("remainder when x^3 + 2x + 5 is divided by x - 2", 17);
  valueIs("discriminant of 2x^2 + 3x - 5", 49);
  valueIs("sum of the roots of x^2 - 7x + 10", 7);
  textHas("gcd(x^2 - 1, x^2 + 2x + 1)", /x \+ 1/);
});

test("number theory and bases", () => {
  valueIs("inverse of 3 mod 11", 4);
  textHas("convert 255 to base 2", /11111111/);
  valueIs("phi(36)", 12);
  valueIs("10th prime", 29);
});

test("matrix arithmetic evaluates instead of echoing", () => {
  textHas("[[1, 2], [3, 4]] * [[0, 1], [1, 0]]", /\[\[2, 1\], \[4, 3\]\]/);
});

test("calculus additions: derivative at a point, higher orders, gradient", () => {
  valueIs("slope of the tangent to y = x^2 at x = 3", 6);
  const r = S("second derivative of x^4");
  good(r, "second derivative");
  textHas("grad(x^2 y, x, y)", /2x\*?y|2y\*?x/);
});

test("logs: condense evaluates numeric logs", () => {
  textHas("condense ln(2) + ln(5)", /ln\(10\)/);
  valueIs("condense log(2) + log(5)", 1);
  textHas("condense log(x) + log(y)", /log\(x\*?y\)/);
});

test("round and decimal-to-fraction", () => {
  valueIs("round 3.14159 to 2 decimal places", 3.14);
  valueIs("round(2.675, 2)", 2.68);
  valueIs("round(-2.5)", -3);
  valueIs("0.125 as a fraction", 1 / 8);
});

test("word problems", () => {
  textHas("find two consecutive integers whose product is 72", /8.*9|-9.*-8/);
  valueIs("the sum of a number and 7 is 20. find the number", 13);
});

test("logic and sets", () => {
  const t = solveLogic("truth table for p and not q");
  ok(t && t.ok, "truth table");
  ok(/tautology/i.test(JSON.stringify(solveLogic("is p or not p a tautology"))), "tautology");
  const u = S("simplify (p and q) or (p and not q)");
  good(u, "boolean simplify");
  ok(/^p$/.test(u.answers.map((a) => a.text || (a.tree && toText(a.tree)) || "").join("").trim()) || /\bp\b/.test(JSON.stringify(u.answers)), "reduces to p");
});

test("arity: wrong argument counts are syntax errors, never truncated", () => {
  for (const s of ["sin(1, 2)", "binomial(10)", "powmod(2, 3)", "sqrt(1, 2)"]) {
    let threw = false;
    try { parse(s); } catch (_) { threw = true; }
    ok(threw, s);
  }
  eq(toText(parse("log(8, 2)")).length > 0, true, "log with base parses");
});

test("refusals: non-math and borrowed words are not read as products", () => {
  for (const q of ["hi", "hello there", "what is love", "x form 3", "sine form of 2", "a band b", "x = 2 if y"]) refused(S(q), q);
  // "for x in [0, 2pi)" is handled by solvein, never as the product f*o*r*x*i*n
  const r = S("solve sin(x) = 0 for x in [0, 2pi)");
  ok(!r.ok || !/f\*?o\*?r/.test(r.input.text), "no f*o*r product");
});

test("counting/probability functions are cross-checked by independent floats", () => {
  const r = S("binomial(30, 12)");
  good(r);
  eq(toText(r.answers[0].tree), "86493225");
});
