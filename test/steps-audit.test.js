// Step explanations for 41 common problems (linear, quadratic, systems, derivatives, integrals,
// limits, log / exponent equations). The answers are frozen: step work must never change them.
// The rest checks that the steps read like a textbook: in order, nothing missing, plain wording.
import { test, eq, ok } from "./harness.js";
import { solve } from "../public/engine/quelvra.js";
import { explain } from "../public/engine/explain.js";
import { stepsToText } from "../public/engine/steps.js";
import { toText } from "../public/engine/print.js";
import { textOf } from "../tools/coverage-judge.mjs";

const AUDIT = [
  ["2x + 3 = 11", "x = 4"],
  ["5x - 7 = 3x + 9", "x = 8"],
  ["3(x - 2) = 2x + 5", "x = 11"],
  ["x/4 + 2 = 5", "x = 12"],
  ["7 - 2x = 15", "x = -4"],
  ["x^2 - 5x + 6 = 0", "x = 2; x = 3"],
  ["x^2 + 7x + 12 = 0", "x = -4; x = -3"],
  ["2x^2 - 8 = 0", "x = -2; x = 2"],
  ["x^2 = 4x", "x = 0; x = 4"],
  ["6x^2 + x - 2 = 0", "x = -2/3; x = 1/2"],
  ["x^2 + 4x + 1 = 0", "x = (-2sqrt(3) - 4)/2; x = (2sqrt(3) - 4)/2"],
  ["2x^2 - 3x - 4 = 0", "x = (-sqrt(41) + 3)/4; x = (sqrt(41) + 3)/4"],
  ["x^2 + x + 1 = 0", "No real solution"],
  ["x^2 - 6x + 9 = 0", "x = 3"],
  ["2x + y = 5, x - y = 1", "x = 2, y = 1"],
  ["3x + 2y = 12, x - y = -1", "x = 2, y = 3"],
  ["x + y = 10, x - y = 2", "x = 6, y = 4"],
  ["derivative of sin(x^2)", "2x*cos(x^2)"],
  ["derivative of (3x + 1)^5", "15(3x + 1)^4"],
  ["derivative of x^2 sin(x)", "x^2cos(x) + 2x*sin(x)"],
  ["derivative of x e^x", "x*e^x + e^x"],
  ["derivative of ln(x^2 + 1)", "2x/(x^2 + 1)"],
  ["derivative of e^(3x) cos(x)", "3e^(3x)*cos(x) - e^(3x)*sin(x)"],
  ["derivative of x^3 - 4x + 7", "3x^2 - 4"],
  ["integrate x^2", "x^3/3"],
  ["integrate 3x^2 + 2x", "x^3 + x^2"],
  ["integrate sin(x)", "-cos(x)"],
  ["integrate e^(2x)", "e^(2x)/2"],
  ["integrate 1/x", "ln(|x|)"],
  ["integral of x^2 from 0 to 3", "9"],
  ["integrate x cos(x)", "x*sin(x) + cos(x)"],
  ["limit of sin(x)/x as x approaches 0", "1"],
  ["limit of (x^2 - 4)/(x - 2) as x approaches 2", "4"],
  ["limit of (3x^2 + 1)/(x^2 - 2) as x goes to infinity", "3"],
  ["limit of (1 - cos(x))/x^2 as x approaches 0", "1/2"],
  ["2^x = 32", "x = 5"],
  ["3^(x + 1) = 81", "x = 3"],
  ["log(x) = 2", "x = 100"],
  ["ln(x) + ln(2) = 3", "x = e^(-(ln(2) - 3))"],
  ["log_2(x) + log_2(x - 2) = 3", "x = 4"],
  ["e^(2x) = 7", "x = ln(7)/2"],
];
const memo = new Map();
const run = (q) => {
  if (!memo.has(q)) { const r = solve(q, { timeLimit: 8000 }); memo.set(q, { r, steps: explain(r, "steps").steps }); }
  return memo.get(q);
};
const flat = (ss) => ss.flatMap((s) => [s, ...flat(s.sub || [])]);
const txt = (q) => stepsToText(run(q).steps);

test("step audit: the 41 answers are unchanged and verified", () => {
  for (const [q, want] of AUDIT) {
    const { r } = run(q);
    eq((r.answers || []).map(textOf).join("; "), want, q);
    eq(r.verification && r.verification.status, "passed", q);
  }
});
test("step audit: every problem shows steps, and no step repeats its input unchanged", () => {
  for (const [q] of AUDIT) {
    const { steps } = run(q);
    ok(steps.length > 0, `${q}: no steps`);
    for (const s of flat(steps)) ok(!(s.before && s.after && s.kind !== "note" && toText(s.before) === toText(s.after)), `${q}: trivial step ${s.title}`);
    ok(!/Zassenhaus|F\(\d+\) F =/.test(txt(q)), `${q}: jargon or garbled text`);
  }
});

// ---------------------------------------------------------------- linear
test("steps: a linear equation collects terms, then divides", () => {
  const t = txt("5x - 7 = 3x + 9");
  ok(/Get the x terms on one side and the numbers on the other: 5x - 7 = 3x \+ 9  ->  2x = 16/.test(t), t);
  ok(/Subtract 3x from both sides and add 7 to both sides/.test(t), t);
  ok(/Divide both sides by 2: 2x = 16  ->  x = 8/.test(t), t);
  ok(!/Move everything to one side/.test(t), t);
});
test("steps: brackets are expanded first; x/4 is undone by multiplying", () => {
  ok(/Expand and simplify each side: 3\(x - 2\) = 2x \+ 5  ->  3x - 6 = 2x \+ 5/.test(txt("3(x - 2) = 2x + 5")));
  ok(/Multiply both sides by 4: x\/4 = 3  ->  x = 12/.test(txt("x/4 + 2 = 5")));
});

// ---------------------------------------------------------------- quadratics
test("steps: nothing to move when the right side is already 0", () => {
  ok(!/Move everything/.test(txt("x^2 - 5x + 6 = 0")));
  ok(/Subtract 4x from both sides, so the right side is 0/.test(txt("x^2 = 4x")));
});
test("steps: factors are solved in the order they are written, including a bare x", () => {
  const titles = flat(run("x^2 - 5x + 6 = 0").steps).map((s) => s.title);
  ok(titles.indexOf("Solve x - 2 = 0") < titles.indexOf("Solve x - 3 = 0"), titles.join(" | "));
  const t = txt("x^2 = 4x");
  ok(/The factor x gives x = 0/.test(t) && t.indexOf("x = 0") < t.indexOf("Solve x - 4 = 0"), t);
  ok(/Subtract 2 from both sides, then divide by 3/.test(txt("6x^2 + x - 2 = 0")));
});
test("steps: the quadratic formula shows the numbers substituted", () => {
  ok(/\(-4 \+- sqrt\(12\)\) \/ 2/.test(txt("x^2 + 4x + 1 = 0")));
  ok(/\(3 \+- sqrt\(41\)\) \/ 4/.test(txt("2x^2 - 3x - 4 = 0")));
});

// ---------------------------------------------------------------- systems
test("steps: a linear system names its columns and reads the answer back as equations", () => {
  const t = txt("2x + y = 5, x - y = 1");
  ok(/coefficients of x, y/.test(t), t);
  ok(/Read off the solution: .*  ->  x = 2, y = 1/.test(t), t);
});

// ---------------------------------------------------------------- derivatives
test("steps: the outer rule comes first and the inner derivatives are its sub-steps", () => {
  const { steps } = run("derivative of sin(x^2)");
  eq(steps.length, 1);
  eq(steps[0].rule, "diff.sin-chain");
  eq(steps[0].sub[0].rule, "diff.power");
  const p = run("derivative of x^2 sin(x)").steps[0];
  eq(p.rule, "diff.product");
  ok(/f = x\^2 and g = sin\(x\)/.test(p.why), p.why);
  eq(p.sub.map((s) => s.rule).join(","), "diff.power,diff.sin");
  eq(run("derivative of x^3 - 4x + 7").steps[0].sub.map((s) => toText(s.before)).join(" | "), "d/dx (x^3) | d/dx (-4x)");
});

// ---------------------------------------------------------------- integrals
test("steps: term by term lists the terms in written order, each nested", () => {
  const top = run("integrate 3x^2 + 2x").steps[0];
  eq(top.title, "Integrate term by term");
  ok(toText(top.sub[0].before).includes("3x^2") && toText(top.sub[1].before).includes("2x"), top.sub.map((s) => toText(s.before)).join(" | "));
  const parts = run("integrate x cos(x)").steps[0];
  eq(parts.rule, "int.parts");
  ok(/du = dx and v = sin\(x\)/.test(parts.why), parts.why);
  eq(parts.sub.length, 2);
});
test("steps: a definite integral says F(b) - F(a) in words", () => {
  ok(/F\(3\) = 9 and F\(0\) = 0, so the integral is 9 - 0/.test(txt("integral of x^2 from 0 to 3")));
});

// ---------------------------------------------------------------- limits
test("steps: limits show the textbook route", () => {
  const f = txt("limit of (x^2 - 4)/(x - 2) as x approaches 2");
  ok(/gives 0\/0/.test(f) && /Factor the top and the bottom/.test(f) && /Cancel the common factor: .*  ->  lim x->2 \(x \+ 2\)/.test(f) && /Substitute x = 2: lim x->2 \(x \+ 2\)  ->  4/.test(f), f);
  const l = txt("limit of sin(x)/x as x approaches 0");
  ok(/Apply L'Hopital's rule: lim x->0 \(sin\(x\)\/x\)  ->  lim x->0 \(cos\(x\)\)/.test(l), l);
  const h = txt("limit of (1 - cos(x))/x^2 as x approaches 0");
  ok(/Still 0\/0/.test(h) && /Apply L'Hopital's rule again/.test(h), h);
  ok(/Divide the top and the bottom by x\^2/.test(txt("limit of (3x^2 + 1)/(x^2 - 2) as x goes to infinity")));
});
test("steps: a limit whose value the textbook route does not reach gets no made-up steps", () => {
  const { steps } = run("limit of x^x as x approaches 0");
  for (const s of flat(steps)) ok(!/lim\.(factor|lhopital)/.test(s.rule), s.title);
});

// ---------------------------------------------------------------- logs and exponents
test("steps: exponential and log equations skip the pointless move and keep the base", () => {
  const e = txt("2^x = 32");
  ok(!/Move everything/.test(e) && /Take logarithms: 2\^x = 32  ->  x = 5/.test(e), e);
  ok(/Get the term with x on its own: ln\(x\) \+ ln\(2\) = 3  ->  ln\(x\) =/.test(txt("ln(x) + ln(2) = 3")));
  const b = txt("log_2(x) + log_2(x - 2) = 3");
  ok(/Combine the logarithms: .*  ->  log_2\(x\(x - 2\)\) = 3/.test(b), b);
  ok(/log_2\(A\) = c means A = 2\^c, and 2\^3 = 8/.test(b), b);
  ok(/Expand and collect like terms: x\(x - 2\) - 8 = 0  ->  x\^2 - 2x - 8 = 0/.test(b), b);
  ok(/here 10\^2 = 100/.test(txt("log(x) = 2")));
});
