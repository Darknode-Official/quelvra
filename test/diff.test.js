import { test, eq, ok, P, rng } from "./harness.js";
import * as X from "../public/engine/expr.js";
import { parse } from "../public/engine/parse.js";
import { simplify, expand } from "../public/engine/simplify.js";
import { toText } from "../public/engine/print.js";
import { diff, diffSteps, implicitDiff, gradient, hessian, jacobian } from "../public/engine/calc/diff.js";

const D = (s, v = "x", order = 1) => toText(diff(parse(s), v, { order }));
const cases = [
  ["x^3", "3x^2"], ["5", "0"], ["x", "1"], ["3x^2 + 2x + 1", "6x + 2"], ["sin(x)", "cos(x)"], ["cos(x)", "-sin(x)"],
  ["e^x", "e^x"], ["e^(2x)", "2e^(2x)"], ["ln(x)", "1/x"], ["sqrt(x)", "1/(2sqrt(x))"], ["1/x", "-1/x^2"],
  ["x sin(x)", "x*cos(x) + sin(x)"], ["tan(x)", "sec(x)^2"], ["2^x", "ln(2)*2^x"], ["log_2(x)", "1/(x*ln(2))"],
  ["atan(x)", "1/(x^2 + 1)"], ["asin(x)", "1/sqrt(-x^2 + 1)"], ["sin(x^2)", "2x*cos(x^2)"], ["(x^2+1)^5", "10x(x^2 + 1)^4"],
  ["sinh(x)", "cosh(x)"], ["cosh(x)", "sinh(x)"], ["|x|", "x/|x|"], ["ln(sin(x))", "cos(x)/sin(x)"],
];
for (const [src, want] of cases) test(`d/dx ${src}`, () => eq(D(src), want, src));
test("second derivative of x^4", () => eq(D("x^4", "x", 2), "12x^2"));
test("third derivative of sin", () => eq(D("sin(x)", "x", 3), "-cos(x)"));
test("partial derivative treats y as constant", () => eq(D("x^2 y + y^3", "x"), "2x*y"));
test("x^x logarithmic", () => eq(D("x^x"), "x^x(ln(x) + 1)"));
test("implicit circle", () => eq(toText(implicitDiff(parse("x^2 + y^2 = 25"), "x", "y")), "-x/y"));
test("gradient", () => eq(toText(gradient(parse("x^2 + x y"), [X.sym("x"), X.sym("y")])), "[2x + y, x]"));
test("hessian", () => eq(toText(hessian(parse("x^2 y"), [X.sym("x"), X.sym("y")])), "[[2y, 2x], [2x, 0]]"));
test("jacobian", () => eq(toText(jacobian([parse("x y"), parse("x + y")], [X.sym("x"), X.sym("y")])), "[[y, x], [1, 1]]"));
test("steps recorded", () => {
  const r = diffSteps(parse("sin(x^2)"), "x");
  const all = (ss) => ss.flatMap((s) => [s, ...all(s.sub || [])]);
  ok(all(r.steps).some((s) => s.rule === "diff.sin-chain"), "chain step");
  ok(all(r.steps).some((s) => s.rule.startsWith("diff.power")), "power step");
  // the rule that was applied last comes first; the inner derivative is its sub-step
  eq(r.steps.length, 1);
  eq(r.steps[0].rule, "diff.sin-chain");
  eq(r.steps[0].sub[0].rule, "diff.power");
});
test("abs derivative records condition", () => {
  const r = diffSteps(parse("|x|"), "x");
  ok(r.conditions.some((c) => c.rel === "!=0"));
});

// property: derivative agrees with a central difference at random points
const ev = (u, x) => {
  const go = (w) => {
    switch (w.k) {
      case "num": return Number(w.v.n) / Number(w.v.d);
      case "sym": return w.name === "x" ? x : NaN;
      case "const": return { pi: Math.PI, e: Math.E }[w.name] ?? NaN;
      case "add": return w.args.reduce((s, a) => s + go(a), 0);
      case "mul": return w.args.reduce((s, a) => s * go(a), 1);
      case "pow": return Math.pow(go(w.args[0]), go(w.args[1]));
      case "fn": {
        const a = w.args.map(go);
        const f = { sin: Math.sin, cos: Math.cos, tan: Math.tan, ln: Math.log, abs: Math.abs, atan: Math.atan, sec: (t) => 1 / Math.cos(t), sinh: Math.sinh, cosh: Math.cosh, asin: Math.asin, exp: Math.exp }[w.name];
        return f ? f(...a) : NaN;
      }
      default: return NaN;
    }
  };
  return go(u);
};
test("property: derivative matches finite difference", () => {
  const r = rng(99);
  const atoms = ["x", "x^2", "sin(x)", "cos(x)", "e^x", "ln(x)", "sqrt(x)", "3", "atan(x)", "1/x"];
  const gen = (dd) => {
    if (dd === 0) return r.pick(atoms);
    const op = r.pick(["+", "*", "/", "comp"]);
    if (op === "comp") return `${r.pick(["sin", "cos", "e^", "ln", "sqrt"])}(${gen(dd - 1)})`.replace("e^(", "e^(");
    return `(${gen(dd - 1)})${op}(${gen(dd - 1)})`;
  };
  let checked = 0;
  for (let i = 0; i < 300; i++) {
    const src = gen(r.int(1, 3));
    const u = simplify(parse(src));
    const du = diff(u, "x");
    const x0 = 0.3 + r.next() * 1.4;
    const h = 1e-6;
    const fd = (ev(u, x0 + h) - ev(u, x0 - h)) / (2 * h);
    const an = ev(du, x0);
    if (!isFinite(fd) || !isFinite(an) || Math.abs(fd) > 1e6) continue;
    checked++;
    if (Math.abs(fd - an) > 1e-4 * Math.max(1, Math.abs(an))) throw new Error(`d/dx ${src} = ${toText(du)}: ${an} vs finite difference ${fd} at x=${x0}`);
  }
  ok(checked > 150, "enough points checked: " + checked);
});
