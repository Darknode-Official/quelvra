import { test, eq, ok } from "./harness.js";
import { translate, wordsToNumbers } from "../public/engine/language.js";
import { parse } from "../public/engine/parse.js";

const cases = [
  ["what is 15% of 80", "percent-of"], ["derivative of x^3 + 2x", "derivative"], ["find the derivative of sin(x) with respect to x", "derivative"],
  ["second derivative of x^4", "derivative"], ["integral of x^2 from 0 to 3", "integral-def"], ["integrate e^x", "integrate"],
  ["limit of sin(x)/x as x approaches 0", "limit"], ["limit of 1/x as x approaches 0 from the right", "limit"], ["limit of 1/x as x goes to infinity", "limit"],
  ["a number plus 7 is 19", "number-plus"], ["twice a number minus 3 is 11", "k-times-number"], ["3 times a number is 27", "k-times-number"],
  ["the sum of two numbers is 20 and their difference is 4", "sum-difference"], ["the sum of three consecutive integers is 72", "consecutive"],
  ["what is the square root of 144", "evaluate"], ["what is five squared plus three", "evaluate"], ["solve x^2 - 5x + 6 = 0", "solve"],
  ["solve a x + b = c for x", "solve-for"], ["simplify (x^2-1)/(x-1)", "simplify"], ["factor x^2 - 9", "simplify"], ["gcd of 12 and 18", "gcd"],
  ["is 97 prime", "is-prime"], ["mean of 3, 5, 7, 9", "mean"], ["what is the simple interest on $1000 at 5% per year for 3 years", "simple-interest"],
  ["find the prime factorization of 360", "prime-factor"], ["2x+3=11", "math"],
];
for (const [s, pat] of cases) test(`language: ${s}`, () => {
  const r = translate(s);
  ok(r.ok, `not understood: ${s} (${r.reason})`);
  eq(r.pattern, pat, s);
  parse(r.math); // must be parseable
});
test("refuses nonsense", () => ok(!translate("tell me a story about dragons").ok));
test("refuses vague", () => ok(!translate("what is the meaning of life").ok));
test("number words", () => eq(wordsToNumbers("three hundred and twenty five"), "325"));
test("fraction words", () => eq(wordsToNumbers("two thirds of x"), "(2/3) of x"));
test("sum-difference yields system", () => eq(parse(translate("the sum of two numbers is 20 and their difference is 4").math).k, "system"));
// conventions are stated, never silent
const hasNote = (s, re) => { const r = translate(s); ok(r.ok, s); ok((r.notes || []).some((n) => re.test(n)), `${s}: notes ${JSON.stringify(r.notes)}`); return r; };
test("log without a base says base 10", () => { const r = hasNote("the log of 100", /base 10/); eq(r.math, "log 100"); });
test("area under a curve says signed area", () => { const r = hasNote("area under y = x^2 from 0 to 2", /signed/); eq(r.math, "integrate(x^2, x, 0, 2)"); });
test("taylor series states default centre and order", () => { const r = hasNote("taylor series of sin(x)", /order 5/i); eq(r.math, "taylor(sin(x), x, 0, 5)"); });
test("f(x) = expr passes expr and x", () => eq(translate("find the domain of f(x) = sqrt(x - 1)").math, "domain(sqrt(x - 1), x)"));
test("variable choice skips e and pi", () => eq(translate("find the critical points of e^t - pi t").math, "critical(e^t - pi t, t)"));
test("maximize uses the optimize call form", () => eq(translate("maximize x(10 - x)").math, "maximize(x(10 - x), x)"));
test("volume about the y-axis is not guessed", () => ok(!translate("volume of y = x^2 from 0 to 1 rotated about the y-axis").ok || !/volume\(/.test(translate("volume of y = x^2 from 0 to 1 rotated about the y-axis").math)));
test("mixed travel units are not guessed", () => ok(!/^\d/.test(translate("how long does it take to travel 300 km at 60 mph").math || "")));
test("factorial is not sentence punctuation", () => eq(translate("5!").math, "5!"));
