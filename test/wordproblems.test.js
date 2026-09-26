// Word problems (engine/language-words.js): the three corpora must have zero WRONG answers, plus
// unit tests for the grammar, each category's translation and the refusals that keep it honest.
import { test, eq, ok } from "./harness.js";
import { solve } from "../public/engine/quelvra.js";
import { translate, wordsToNumbers } from "../public/engine/language.js";
import { _internal } from "../public/engine/language-words.js";
import { judge, shownNumbers } from "./wordproblems.judge.js";
import { CASES } from "./wordproblems.corpus.js";
import { HELDOUT, HELDOUT_FRESH } from "./wordproblems.heldout.js";

const S = (q) => solve(q, { timeLimit: 5000 });
const run = (cases) => {
  const tally = { ok: 0, incomplete: 0, refused: 0, WRONG: 0 }, wrong = [];
  for (const [cat, input, exp] of cases) {
    let r, v;
    try { r = S(input); v = judge(exp, r); } catch (e) { v = "refused"; }
    tally[v]++;
    if (v === "WRONG") wrong.push(`[${cat}] ${input} -> ${JSON.stringify(shownNumbers(r).nums)}`);
  }
  return { tally, wrong };
};

// minimum ok counts are floors a little under today's numbers, so a regression shows up
for (const [name, cases, floor] of [["main", CASES, 260], ["held-out", HELDOUT, 76], ["fresh", HELDOUT_FRESH, 30]]) {
  test(`word problems (${name}): zero WRONG, at least ${floor} answered`, () => {
    const { tally, wrong } = run(cases);
    eq(wrong.length, 0, `WRONG answers:\n  ${wrong.join("\n  ")}`);
    ok(tally.ok >= floor, `only ${tally.ok}/${cases.length} ok (${JSON.stringify(tally)})`);
  });
}
test("word problems: the main corpus is big enough and covers every category", () => {
  ok(CASES.length >= 150, `${CASES.length} cases`);
  const cats = new Set(CASES.map((c) => c[0]));
  for (const c of ["age", "mixture", "work", "distance", "percent", "interest", "consecutive", "geometry", "probability", "unit-rate", "ratio", "number", "system", "angles"]) ok(cats.has(c), c);
});

// ---------------------------------------------------------------- the grammar
const X = [_internal.noun("a number", "x"), _internal.noun("the number", "x")];
const readEq = (s) => _internal.readEquation(_internal.normaliseWords(s, wordsToNumbers), X, ["x"]);
test("word grammar: sums, products and 'more than' read as written", () => {
  eq(readEq("a number plus twice the number is 21").text, "x + 2x = 21");
  eq(readEq("5 more than twice a number is 17").text, "2x + 5 = 17");
  eq(readEq("3 less than a number is 10").text, "x - 3 = 10");
});
test("word grammar: 'less than' is not read backwards", () => {
  // "3 less than x" is x - 3, never 3 - x
  const e = readEq("3 less than a number is 10");
  ok(e && !e.ambiguous && /x - 3/.test(e.text), JSON.stringify(e));
});
test("word grammar: normalisation of money, percent and number words", () => {
  eq(_internal.normaliseWords("A $1,200 loan at five percent", wordsToNumbers), "a 1200 dollars loan at 5%");
  // "the larger one" keeps its pronoun
  ok(/larger one/.test(_internal.normaliseWords("Find the larger one.", wordsToNumbers)));
});

// ---------------------------------------------------------------- one translation per category
const tr = (s) => translate(s);
const cases = [
  ["Maria is 4 years older than her brother Tom. The sum of their ages is 30. How old is Tom?", "word-age", "m = t + 4, m + t = 30"],
  ["How many liters of water must be added to 10 liters of a 40% salt solution to get a 25% salt solution?", "word-mixture", null],
  ["Pipe A can fill a tank in 6 hours and pipe B can fill it in 3 hours. How long will it take both pipes together to fill the tank?", "word-work", "1/6 + 1/3 = 1/t"],
  ["A cyclist rides at 15 miles per hour for 3 hours. How far does she ride?", "word-distance", "15*3"],
  ["A shirt costs $40 and is on sale for 25% off. What is the sale price?", "word-percent", null],
  ["Find the compound interest on $1000 at 10% for 2 years.", "word-interest", null],
  ["The sum of three consecutive odd integers is 57. What are the integers?", "word-consecutive", "a + b + c = 57, b = a + 2, c = a + 4"],
  ["The width of a rectangle is 4 less than its length. The area is 60. Find the length.", "word-geometry", "l*(l - 4) = 60, l > 0, l - 4 > 0"],
  ["A bag contains 3 red and 7 blue marbles. Two marbles are drawn without replacement. What is the probability both are red?", "word-probability", "binomial(3, 2)/binomial(10, 2)"],
  ["6 apples cost $3. How much do 10 apples cost?", "word-rate", "3/6*10"],
  ["The ratio of cats to dogs at a shelter is 3:4. If there are 12 cats, how many dogs are there?", "word-ratio", "12*4/3"],
  ["Adult tickets cost $8 and child tickets cost $5. 100 tickets were sold for a total of $650. How many adult tickets were sold?", "word-system", "a + c = 100, 8a + 5c = 650"],
  ["Two angles are supplementary. One angle is 40 degrees less than the other. Find the larger angle.", "word-angles", "x + y = 180, x = y - 40"],
];
for (const [q, pat, math] of cases) test(`word translate: ${q.slice(0, 60)}`, () => {
  const t = tr(q);
  ok(t.ok, `${q}: ${t.reason}`);
  eq(t.pattern, pat);
  if (math) eq(t.math, math);
});
test("word problems: compound interest 'on' P asks for A - P, not the amount (the old WRONG answer)", () => {
  const r = S("Find the compound interest on $1000 at 10% for 2 years.");
  eq(judge(210, r), "ok");
});
test("word problems: 'two numbers in the ratio 2:5' puts the larger share on the larger number (was a WRONG answer)", () => {
  eq(judge(60, S("Two numbers are in the ratio 2:5. Their sum is 84. What is the larger number?")), "ok");
  eq(judge({ nums: [30, 42] }, S("Two numbers are in the ratio 5:7 and their difference is 12. Find the numbers.")), "ok");
});
test("word problems: widening pass, one translation per new family", () => {
  const w = [
    ["A and B together can finish a job in 4 days. A alone can finish it in 6 days. How many days will B take alone?", "word-work", "1/6 + 1/t = 1/4"],
    ["A $200 coat is discounted by 20% and then by a further 10%. What is the final price?", "word-percent", "200*(1 - 20/100)*(1 - 10/100)"],
    ["What principal will amount to $1320 in 2 years at 5% simple interest?", "word-interest", "P*(1 + 5/100*2) = 1320"],
    ["Two cars start from towns 300 km apart and drive toward each other at 70 km/h and 80 km/h. After how many hours do they meet?", "word-distance", "(70 + 80)t = 300"],
    ["A boat's speed in still water is 12 km/h and the current is 3 km/h. How long will it take to travel 45 km upstream?", "word-distance", "45/(12 - 3)"],
    ["15 liters of a 40% solution are mixed with 25 liters of a 20% solution. What is the concentration of the mixture?", "word-mixture", "(15*40 + 25*20)/(15 + 25)"],
    ["The sum of the digits of a two-digit number is 9. If the digits are reversed, the new number is 27 more than the original number. Find the number.", "word-digits", "t + u = 9, 10u + t = 10t + u + 27, n = 10t + u"],
    ["Divide 200 in the ratio 1:3. What is the smaller part?", "word-ratio", "200*1/(1 + 3)"],
  ];
  for (const [q, pat, math] of w) { const t = tr(q); ok(t.ok, `${q}: ${t.reason}`); eq(t.pattern, pat); eq(t.math, math); }
});
test("word problems: a system names the unknown that the question asks for", () => {
  const t = tr("A farmer has chickens and pigs. There are 20 heads and 56 legs. How many pigs are there?");
  ok(/\(the question asks for y\)/.test(t.interpretation), t.interpretation);
  eq(judge(8, S("A farmer has chickens and pigs. There are 20 heads and 56 legs. How many pigs are there?")), "ok");
});

// ---------------------------------------------------------------- refusals: never guess
const refuses = [
  // the text does not determine the answer
  "John is 5 years older than Mary. How old is John?",
  "A rectangle has a perimeter of 30. What is its area?",
  "A shirt costs $30. What is the sale price?",
  "Two angles are complementary. Find the larger angle.",
  "A train travels 200 miles. How fast is it going?",
  // parity and integrality: 2a + 2 = 52 gives a = 25, which is not even
  "The sum of two consecutive even integers is 52. Find the integers.",
  "The sum of two consecutive integers is 40. Find the integers.",
  // a colour that is not in the bag
  "A bag contains 3 red and 5 blue marbles. What is the probability of drawing a purple marble?",
  // units that do not agree
  "A car travels 120 miles in 2 hours. What is its speed in km/h?",
  "How many liters of a 20% solution must be added to 10 gallons of a 50% solution to get a 30% solution?",
  // a target percentage outside the two components cannot be mixed
  "How many liters of a 20% solution must be mixed with 10 liters of a 30% solution to get a 50% solution?",
  // an unknown sentence anywhere refuses the whole problem
  "Tom is twice as old as Ann. Ann likes pizza. How old is Tom?",
  // the question does not name either unknown
  "Adult tickets cost $8 and child tickets cost $5. 100 tickets were sold for a total of $650. How many seats are there?",
  // the stated direction contradicts the numbers
  "The price rose from $80 to $60. What is the percent increase?",
  // the equations solve, but the solution makes no sense for the story (found by adversarial probing)
  "Pipe A fills a tank in 6 hours. Pipe B empties it in 4 hours. How long will it take both pipes together to fill the tank?",
  "A shirt costs $40 and is on sale for 125% off. What is the sale price?",
  "A farmer has chickens and cows. There are 20 heads and 30 legs. How many cows are there?",
  "Two angles are complementary. One is 100 degrees more than the other. Find the smaller angle.",
  "An angle is 100 more than its complement. Find the angle.",
  "Divide 50 in the ratio 0:5.",
  "A boat goes 30 miles downstream in 2 hours and 30 miles upstream in 1 hours. What is the speed of the boat in still water?",
  "The ratio of boys to girls in a club is 2:3. There are 31 members in total. How many girls are there?",
  "A number is chosen at random from 1 to 20. What is the probability that it is a multiple of 0?",
  "Adult tickets cost $8 and child tickets cost $5. 100 tickets were sold for a total of $651. How many adult tickets were sold?",
  "Kate is twice as old as Ben. Five years ago Kate was three times as old as Ben. Ten years ago Ben was 1. How old is Kate?",
  // work: the question's verb and the job must match (the older template answered these before the widening pass)
  "Pipe A fills a tank in 3 hours and pipe B empties it in 6 hours. How long will it take both pipes together to empty the tank?",
  "Pipe A fills a tank in 3 hours and pipe B fills it in 6 hours. How long will it take both pipes together to empty the tank?",
  "A can paint a house in 6 days and B can paint a fence in 3 days. How long will they take together?",
  "Pipe A fills a tank in 3 hours and pipe B fills half the tank in 6 hours. How long will it take both pipes together?",
  "Pipe A can fill a tank in 3 hours and pipe B can fill it in 6 hours. If both are open, how long will it take to fill a quarter of the tank?",
  "A and B together finish a job in 6 days. A alone takes 4 days. How long does B take alone?",
  // percent, distance, mixture, digits, ratio: facts missing, contradictory or impossible
  "A price is increased by 10% and then decreased by 10%. What is the final price?",
  "A shopkeeper buys a chair for $120 and marks it up by 25%. He then gives a 10% discount. What is the selling price?",
  "Two cars start from towns 300 km apart and drive in the same direction at 70 km/h and 80 km/h. When do they meet?",
  "Two cars start from the same place at 60 km/h and 40 km/h. After how many hours will they be 100 km apart?",
  "Two cars leave the same town in opposite directions, one at 60 km/h and the other 2 hours later at 80 km/h. After how many hours will they be 300 km apart?",
  "A boat's speed in still water is 3 km/h and the current is 12 km/h. How long will it take to travel 45 km upstream?",
  "A train leaves a station at 90 km/h. Three hours later a train leaves the same station on the same track at 60 km/h. How many hours after the second train leaves will it catch the first?",
  "How many liters of water must be added to 30 liters of a 20% sugar solution to make it a 25% solution?",
  "15 liters of a 40% acid solution are mixed with 25 liters of a 20% salt solution. What is the concentration of the mixture?",
  "The sum of the digits of a two-digit number is 10. If the digits are reversed, the new number is 27 more than the original number. Find the number.",
  "The tens digit of a two-digit number is twice the units digit. The sum of the digits is 12. Find the units digit.",
  "Share 85 sweets between Tom and Ann in the ratio 3:4. How many does Ann get?",
  "The first number and the second number are in the ratio 2:5. Their difference is 21. Find the first number.",
];
for (const q of refuses) test(`word refuses: ${q.slice(0, 70)}`, () => {
  const r = S(q);
  // "no solution" is an honest verdict too (an angle 100 more than its complement does not exist)
  ok(!r.ok || r.verification.status !== "passed" || r.noSolution || !(r.answers || []).some((a) => a.kind !== "none"), `answered: ${JSON.stringify(shownNumbers(r).nums)} via ${r.input && r.input.interpretation}`);
});
