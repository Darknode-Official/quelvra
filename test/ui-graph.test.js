import { test, eq, ok, close } from "./harness.js";
import * as X from "../public/engine/expr.js";
import { parse } from "../public/engine/parse.js";
import {
  compile, niceTicks, sampleFunction, implicitCurve, inequalityGrid, sampleParametric, samplePolar, classifyPlot, gamma,
} from "../public/graph.js";

const f1 = (src, v = "x") => compile(parse(src), [v]);

test("compile polynomials, trig, constants", () => {
  eq(f1("x^2+1")(3), 10);
  close(f1("sin(pi/2)")(0), 1);
  close(f1("e^x")(1), Math.E);
  close(f1("ln(x)")(Math.E), 1);
  close(f1("log_2(x)")(8), 3);
  close(f1("log(x)")(1000), 3);
  close(f1("|x - 5|")(2), 3);
  close(f1("sqrt(x)")(9), 3);
  ok(Number.isNaN(f1("sqrt(x)")(-1)), "sqrt of negative is NaN");
});
test("compile odd real roots of negatives", () => {
  close(compile(parse("(-8)^(1/3)"), [])(), -2);
  close(f1("x^(2/3)")(-8), 4);
  close(f1("cbrt(x)")(-27), -3);
});
test("compile factorial / gamma", () => {
  eq(f1("x!")(5), 120);
  close(gamma(0.5), Math.sqrt(Math.PI), 1e-10);
});
test("compile piecewise", () => {
  const x = X.sym("x");
  const pw = X.piecewise([X.neg(x), X.rel("<", x, X.ZERO)], [x, X.TRUE]);
  const f = compile(pw, ["x"]);
  eq(f(-3), 3);
  eq(f(4), 4);
});
test("compile multiple variables and unknown symbols", () => {
  const f = compile(parse("a sin(b x)"), ["x", "a", "b"]);
  close(f(Math.PI / 4, 2, 2), 2);
  ok(Number.isNaN(compile(parse("x + q"), ["x"])(1)), "unknown symbol gives NaN");
});
test("compile finite sum", () => {
  eq(compile(parse("sum_(k=1)^(10) k"), [])(), 55);
});

test("niceTicks", () => {
  const t = niceTicks(-10, 10, 8);
  eq(t.step, 2);
  ok(t.ticks.includes(0) && t.ticks[0] >= -10 && t.ticks[t.ticks.length - 1] <= 10);
  const s = niceTicks(0, 0.003, 5).step;
  close(s, 0.0005, 1e-12);
  eq(niceTicks(5, 5).ticks.length, 0);
});

function noCrossing(segs, isBad) {
  for (const s of segs) for (let i = 1; i < s.length; i++) if (isBad(s[i - 1], s[i])) return [s[i - 1], s[i]];
  return null;
}
const opts = { ymin: -10, ymax: 10 };

test("sampler: tan(x) never joins across a pole", () => {
  const segs = sampleFunction(Math.tan, -10, 10, opts);
  const bad = noCrossing(segs, (a, b) => Math.floor(a[0] / Math.PI - 0.5) !== Math.floor(b[0] / Math.PI - 0.5));
  ok(!bad, "segment crosses a tan pole: " + JSON.stringify(bad));
  ok(segs.length >= 6, "one branch per period, got " + segs.length);
  // branches reach well outside the viewport so lines touch the edges
  ok(segs.some((s) => s.some((p) => p[1] > 10)) && segs.some((s) => s.some((p) => p[1] < -10)));
});
test("sampler: tan(x) via compiled tree", () => {
  const segs = sampleFunction(f1("tan(x)"), -10, 10, opts);
  ok(!noCrossing(segs, (a, b) => Math.floor(a[0] / Math.PI - 0.5) !== Math.floor(b[0] / Math.PI - 0.5)));
});
test("sampler: 1/x never joins across 0", () => {
  for (const [a, b] of [[-10, 10], [-9.37, 10.11], [-1, 3]]) {
    const segs = sampleFunction((x) => 1 / x, a, b, opts);
    ok(!noCrossing(segs, (p, q) => p[0] < 0 && q[0] > 0), `1/x crossing on [${a}, ${b}]`);
    ok(!noCrossing(segs, (p, q) => p[0] <= 0 && q[0] >= 0), "no segment touching both sides");
  }
});
test("sampler: known poles split the domain", () => {
  const segs = sampleFunction((x) => 1 / (x - 1.2345), -10, 10, { ...opts, poles: [1.2345] });
  ok(!noCrossing(segs, (p, q) => p[0] < 1.2345 && q[0] > 1.2345));
});
test("sampler: floor(x) steps are not joined", () => {
  const segs = sampleFunction(Math.floor, -10, 10, opts);
  const bad = noCrossing(segs, (a, b) => Math.abs(a[1] - b[1]) >= 0.5);
  ok(!bad, "floor joined across a step: " + JSON.stringify(bad));
  ok(segs.length >= 19, "about one segment per step, got " + segs.length);
  const segs2 = sampleFunction(f1("floor(x)"), -7.3, 8.9, opts);
  ok(!noCrossing(segs2, (a, b) => Math.abs(a[1] - b[1]) >= 0.5));
});
test("sampler: continuous functions stay in one piece", () => {
  eq(sampleFunction(Math.sin, -10, 10, opts).length, 1);
  eq(sampleFunction(f1("x^3 - 4x"), -10, 10, opts).length, 1);
  eq(sampleFunction(Math.cbrt, -10, 10, opts).length, 1);
  eq(sampleFunction((x) => Math.atan(50 * x), -10, 10, opts).length, 1);
  eq(sampleFunction(Math.abs, -10, 10, opts).length, 1);
});
test("sampler: domain edges (sqrt, ln) are approached", () => {
  const segs = sampleFunction(Math.sqrt, -10, 10, opts);
  eq(segs.length, 1);
  ok(segs[0][0][0] < 0.01, "sqrt starts near 0, got " + segs[0][0][0]);
});

test("implicit circle x^2 + y^2 = 4", () => {
  const t = parse("x^2 + y^2 = 4");
  const G = compile(X.sub(t.args[0], t.args[1]), ["x", "y"]);
  const lines = implicitCurve(G, -5, 5, -5, 5, { nx: 80, ny: 80 });
  ok(lines.length > 50, "enough segments: " + lines.length);
  for (const l of lines) {
    ok(Math.abs(Math.hypot(l[0], l[1]) - 2) < 0.05 && Math.abs(Math.hypot(l[2], l[3]) - 2) < 0.05, "endpoint off circle " + l);
  }
});
test("implicit 1/x - y skips the pole at x = 0", () => {
  const G = (x, y) => 1 / x - y;
  const lines = implicitCurve(G, -5, 5, -5, 5, { nx: 81, ny: 81 });
  ok(lines.length > 10);
  ok(!lines.some((l) => (l[0] < 0 && l[2] > 0) || (l[0] > 0 && l[2] < 0)), "a segment crosses x = 0");
  ok(!lines.some((l) => Math.abs(l[0]) < 0.05 && Math.abs(l[1]) < 4), "no vertical line along x = 0");
});
test("inequality grid y > x^2", () => {
  const m = inequalityGrid((x, y) => y - x * x, ">", -2, 2, -2, 2, 4, 4);
  eq(m.length, 16);
  // cell (1, 3): centre x = -0.5, y = 1.5 -> inside; cell (0, 0): x = -1.5, y = -1.5 -> outside
  eq(m[3 * 4 + 1], 1);
  eq(m[0], 0);
});
test("parametric and polar", () => {
  const segs = sampleParametric(Math.cos, Math.sin, 0, 2 * Math.PI, { n: 200 });
  eq(segs.length, 1);
  ok(segs[0].every((p) => Math.abs(Math.hypot(p[0], p[1]) - 1) < 1e-9));
  const pol = samplePolar(() => 3, 0, 2 * Math.PI, { n: 100 });
  ok(pol[0].every((p) => Math.abs(Math.hypot(p[0], p[1]) - 3) < 1e-9));
  const br = sampleParametric((t) => t, (t) => 1 / t, -1, 1, { n: 100, maxJump: 5 });
  ok(br.length >= 2, "breaks at the pole");
});

test("classifyPlot", () => {
  const a = classifyPlot(parse("y = a sin(b x)"));
  eq(a.type, "function");
  eq(a.var, "x");
  eq(a.params.join(","), "a,b");
  eq(classifyPlot(parse("x^2+y^2=1")).type, "implicit");
  const i = classifyPlot(parse("y > x^2"));
  eq(i.type, "inequality");
  eq(i.conds[0].op, ">");
  const p = classifyPlot(parse("r = 1 + cos(theta)"));
  eq(p.type, "polar");
  eq(p.params.length, 0);
  eq(classifyPlot(parse("x^2 - 4")).type, "function");
  eq(classifyPlot(parse("(cos(t), sin(t))")).type, "parametric");
  eq(classifyPlot(parse("(1, 2), (3, 4)")).type, "points");
  eq(classifyPlot(X.set(X.tuple(X.ONE, X.TWO), X.tuple(X.TWO, X.ONE))).points.length, 2);
  eq(classifyPlot(parse("x^2 = 4")).type, "multi");
  eq(classifyPlot(parse("x + y = 3, x - y = 1")).type, "multi");
  eq(classifyPlot(parse("d/dx x^2")).type, "none");
  eq(classifyPlot(parse("t^2")).var, "t");
});
