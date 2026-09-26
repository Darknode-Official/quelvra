import { test, eq, ok, close } from "./harness.js";
import { parse } from "../public/engine/parse.js";
import { toText } from "../public/engine/print.js";
import { equivalent } from "../public/engine/verify.js";
import { solve } from "../public/engine/quelvra.js";
import { runAnalysis, analysisCommands } from "../public/engine/strategies/analysis.js";

// Call form through solve(); fall back to the module runner if the parser does not route the name.
function A(name, ...args) {
  const r = solve(`${name}(${args.join(", ")})`, { timeLimit: 15000 });
  if (r.classification && r.classification.command === name) return r;
  return runAnalysis(name, args, { timeLimit: 15000 });
}
const txt = (a) => (a.tree ? toText(a.tree) : a.approx ? a.approx.value : "");
const lab = (r, label) => r.answers.filter((a) => a.label === label || (a.label || "").startsWith(label));
const good = (r, msg = "") => {
  ok(r.ok, `${msg} not ok: ${JSON.stringify(r.answers.map((a) => a.label))} ${JSON.stringify(r.attempts || r.error || "")}`);
  eq(r.verification.status, "passed", `${msg} verification`);
};
const refused = (r, msg = "") => ok(!r.ok, `${msg} should be refused, got ${r.answers.map((a) => `${a.label}: ${txt(a)}`).join("; ")}`);
const same = (got, want, msg) => {
  const e = equivalent(got, parse(want));
  ok(e.status.startsWith("equivalent"), `${msg}: got ${toText(got)}, expected ${want}`);
};
const setIs = (r, want, msg) => { good(r, msg); eq(toText(r.answers[0].tree), want, msg); };

test("analysisCommands lists every command", () => {
  for (const n of ["domain", "range", "zeros", "intercepts", "asymptotes", "extrema", "inflection", "monotonic", "tangent", "normal", "inverse",
    "completesquare", "apart", "identity", "line", "slope", "distance", "midpoint", "arclength", "areabetween", "volume", "avgvalue", "critical"]) ok(analysisCommands.includes(n), n);
});

// ---------------------------------------------------------------- domain
test("domain: rational with even root", () => setIs(A("domain", "sqrt(x-1)/(x-3)", "x"), "1 <= x < 3 or 3 < x", "sqrt(x-1)/(x-3)"));
test("domain: log", () => {
  setIs(A("domain", "ln(x)", "x"), "0 < x", "ln x");
  setIs(A("domain", "ln(x^2-4)", "x"), "x < -2 or 2 < x", "ln(x^2-4)");
});
test("domain: even roots", () => {
  setIs(A("domain", "sqrt(x^2-5x+6)", "x"), "x <= 2 or 3 <= x", "sqrt quadratic");
  setIs(A("domain", "(4-x)^(1/4)", "x"), "x <= 4", "fourth root");
  setIs(A("domain", "sqrt(-x^2)", "x"), "x = 0", "single point");
});
test("domain: odd root is all reals, tan excludes a family", () => {
  const r = A("domain", "x^(1/3)", "x"); good(r); eq(r.answers[0].tree.k, "bool");
  const t = A("domain", "tan(x)", "x"); good(t); eq(toText(t.answers[0].tree), "x != k*pi + pi/2");
});
test("domain: refuses what it cannot decide", () => {
  refused(A("domain", "(-2)^x", "x"), "(-2)^x");
  refused(A("domain", "x + y", "x"), "second variable");
});

// ---------------------------------------------------------------- range
test("range: parabola, rational, trig", () => {
  setIs(A("range", "x^2", "x"), "0 <= y", "x^2");
  setIs(A("range", "1/x", "x"), "y != 0", "1/x");
  setIs(A("range", "sin(x)", "x"), "-1 <= y <= 1", "sin");
  setIs(A("range", "x/(x^2+1)", "x"), "-1/2 <= y <= 1/2", "x/(x^2+1)");
  setIs(A("range", "x^2/(x^2+1)", "x"), "0 <= y < 1", "sup not attained");
});
test("range: hole removes a value, exp/log", () => {
  setIs(A("range", "(x^2-1)/(x-1)", "x"), "y != 2", "hole at x = 1");
  setIs(A("range", "e^x", "x"), "0 < y", "e^x");
  setIs(A("range", "x e^(-x)", "x"), "y <= 1/e", "x e^-x");
  setIs(A("range", "x+1/x", "x"), "y <= -2 or 2 <= y", "x + 1/x");
});
test("range on an interval", () => setIs(A("range", "x^3-3x", "x", "-2", "2"), "-2 <= y <= 2", "cubic on [-2, 2]"));
test("range: refuses infinitely many critical points without an interval", () => refused(A("range", "x+sin(x)", "x")));

// ---------------------------------------------------------------- zeros / intercepts
test("zeros", () => {
  const r = A("zeros", "x^3-x", "x"); good(r);
  eq(r.answers.map(txt).join(","), "-1,0,1");
  const s = A("zeros", "sin(x)", "x"); good(s); eq(txt(s.answers[0]), "k*pi");
  const n = A("zeros", "x^2+1", "x"); good(n); eq(n.answers[0].kind, "none");
});
test("intercepts", () => {
  const r = A("intercepts", "x^2-4", "x"); good(r);
  eq(lab(r, "y-intercept").map(txt).join(), "(0, -4)");
  eq(lab(r, "x-intercept").map(txt).join(" "), "(-2, 0) (2, 0)");
  const h = A("intercepts", "1/x", "x"); good(h); eq(h.answers[0].kind, "none");
});

// ---------------------------------------------------------------- asymptotes
test("asymptotes: vertical, horizontal, oblique", () => {
  const r = A("asymptotes", "(2x^2+1)/(x^2-4)", "x"); good(r);
  eq(lab(r, "Vertical asymptote").map(txt).join(" "), "x = -2 x = 2");
  eq(lab(r, "Horizontal asymptote").map(txt).join(), "y = 2");
  const o = A("asymptotes", "(x^2+1)/x", "x"); good(o);
  eq(lab(o, "Oblique asymptote").map(txt).join(), "y = x");
  const s = A("asymptotes", "sqrt(x^2+1)", "x"); good(s);
  eq(lab(s, "Oblique asymptote").map(txt).join(" "), "y = x y = -x");
  const a = A("asymptotes", "atan(x)", "x"); good(a);
  eq(lab(a, "Horizontal asymptote").length, 2);
});
test("asymptotes: a removable discontinuity is NOT an asymptote", () => {
  const r = A("asymptotes", "(x^2-1)/(x-1)", "x"); good(r);
  eq(lab(r, "Vertical asymptote").length, 0, "no vertical asymptote at the hole");
  eq(lab(r, "Oblique asymptote").length, 0, "the graph is the line itself");
  ok(r.rejected.some((j) => /removable/.test(j.reason)), "hole reported as rejected");
  const s = A("asymptotes", "sin(x)/x", "x"); good(s);
  eq(lab(s, "Vertical asymptote").length, 0, "sin(x)/x has no vertical asymptote");
  eq(lab(s, "Horizontal asymptote").map(txt).join(), "y = 0");
});
test("asymptotes: periodic family and none", () => {
  const t = A("asymptotes", "tan(x)", "x"); good(t);
  eq(t.answers.map(txt).join(), "x = k*pi + pi/2");
  const p = A("asymptotes", "x^2", "x"); good(p); eq(p.answers[0].kind, "none");
  const l = A("asymptotes", "ln(x)", "x"); good(l); eq(l.answers.map(txt).join(), "x = 0");
});

// ---------------------------------------------------------------- critical / extrema / inflection / monotonic
test("x^3 has no extremum (critical point is not an extremum)", () => {
  const r = A("extrema", "x^3", "x"); good(r);
  eq(r.answers.length, 1); eq(r.answers[0].kind, "none");
  const c = A("critical", "x^3", "x"); good(c); eq(c.answers.map(txt).join(), "0");
});
test("extrema: local and absolute", () => {
  const r = A("extrema", "x^3-3x", "x"); good(r);
  eq(lab(r, "Local maximum").map(txt).join(), "(-1, 2)");
  eq(lab(r, "Local minimum").map(txt).join(), "(1, -2)");
  const c = A("extrema", "x^4-2x^2", "x", "-2", "2"); good(c);
  eq(lab(c, "Absolute maximum (endpoint)").map(txt).join(" "), "(-2, 8) (2, 8)");
  eq(lab(c, "Local and absolute minimum").map(txt).join(" "), "(-1, -1) (1, -1)");
  const e = A("extrema", "x^3", "x", "-1", "2"); good(e);
  eq(lab(e, "Absolute maximum (endpoint)").map(txt).join(), "(2, 8)");
  eq(lab(e, "Absolute minimum (endpoint)").map(txt).join(), "(-1, -1)");
});
test("extrema: non-differentiable minima, exp, periodic", () => {
  const a = A("extrema", "abs(x)", "x"); good(a); eq(a.answers.map(txt).join(), "(0, 0)");
  const b = A("extrema", "x^(2/3)", "x"); good(b); eq(b.answers.map(txt).join(), "(0, 0)");
  const c = A("extrema", "x e^(-x)", "x"); good(c); same(c.answers[0].tree, "(1, 1/e)", "x e^-x");
  const s = A("extrema", "sin(x)", "x"); good(s);
  eq(lab(s, "Local and absolute maximum").map(txt).join(), "(2k*pi + pi/2, 1)");
});
test("critical points: f' undefined vs f' = 0, periodic families merged", () => {
  const a = A("critical", "abs(x)", "x"); good(a); eq(a.answers[0].label, "Critical point (f' undefined)");
  const s = A("critical", "sin(x)", "x"); good(s); eq(s.answers.map(txt).join(), "k*pi + pi/2");
});
test("inflection", () => {
  const r = A("inflection", "x^3", "x"); good(r); eq(r.answers.map(txt).join(), "(0, 0)");
  const q = A("inflection", "x^4", "x"); good(q); eq(q.answers[0].kind, "none");
  const c = A("inflection", "x^(1/3)", "x"); good(c); eq(c.answers.map(txt).join(), "(0, 0)");
  const s = A("inflection", "sin(x)", "x"); good(s); eq(s.answers.map(txt).join(), "(k*pi, 0)");
  const h = A("inflection", "1/x", "x"); good(h); eq(h.answers[0].kind, "none");
});
test("monotonic", () => {
  const r = A("monotonic", "x^3-3x", "x"); good(r);
  eq(txt(lab(r, "Increasing")[0]), "x < -1 or 1 < x");
  eq(txt(lab(r, "Decreasing")[0]), "-1 < x < 1");
  eq(txt(lab(r, "Concave up")[0]), "0 < x");
  const h = A("monotonic", "1/x", "x"); good(h);
  eq(lab(h, "Increasing")[0].interval.length, 0);
  eq(txt(lab(h, "Decreasing")[0]), "x < 0 or 0 < x");
});

// ---------------------------------------------------------------- tangent / normal
test("tangent and normal", () => {
  const r = A("tangent", "x^2", "x", "3"); good(r);
  same(r.answers[0].tree.args[1], "6x - 9", "tangent");
  eq(txt(r.answers.find((a) => a.label === "Slope")), "6");
  const n = A("normal", "x^2", "x", "1"); good(n);
  same(n.answers[0].tree.args[1], "-(x-1)/2 + 1", "normal");
  const v = A("normal", "x^2", "x", "0"); good(v); eq(txt(v.answers[0]), "x = 0");
});
test("x^(1/3) has a vertical tangent at 0, not a slope", () => {
  const r = A("tangent", "x^(1/3)", "x", "0"); good(r);
  eq(txt(r.answers[0]), "x = 0");
  ok(/vertical/i.test(r.answers[0].label));
  ok(!r.answers.some((a) => a.label === "Slope" && a.tree), "no numeric slope");
});
test("tangent: corner and outside the domain", () => {
  const c = A("tangent", "abs(x)", "x", "0"); good(c); eq(c.answers[0].kind, "none");
  refused(A("tangent", "ln(x)", "x", "0"), "ln at 0");
});

// ---------------------------------------------------------------- inverse
test("inverse functions", () => {
  const a = A("inverse", "2x+3", "x"); good(a); same(a.answers[0].tree, "(x-3)/2", "linear");
  const e = A("inverse", "e^x", "x"); good(e); eq(txt(e.answers[0]), "ln(x)"); eq(txt(lab(e, "Domain of the inverse")[0]), "0 < x");
  const q = A("inverse", "x^2", "x"); good(q); eq(txt(q.answers[0]), "sqrt(x)");
  ok(/restricted to 0 <= x/.test(q.answers[0].label), "domain note");
  const m = A("inverse", "(x+1)/(x-2)", "x"); good(m); same(m.answers[0].tree, "(2x+1)/(x-1)", "mobius");
  const s = A("inverse", "sin(x)", "x"); good(s); eq(txt(s.answers[0]), "asin(x)");
});

// ---------------------------------------------------------------- algebra
test("completesquare", () => {
  const r = A("completesquare", "2x^2+8x+3", "x"); good(r);
  eq(txt(r.answers[0]), "2(x + 2)^2 - 5"); eq(txt(lab(r, "Vertex")[0]), "(-2, -5)");
  refused(A("completesquare", "x^3", "x"));
});
test("apart", () => {
  const r = A("apart", "1/(x^2-1)", "x"); good(r); same(r.answers[0].tree, "1/(2(x-1)) - 1/(2(x+1))", "apart");
  refused(A("apart", "sin(x)/(x-1)", "x"));
});

// ---------------------------------------------------------------- identity
test("sin^2 + cos^2 = 1 is an identity", () => {
  const r = A("identity", "sin(x)^2+cos(x)^2 = 1"); good(r);
  eq(r.answers[0].tree.k, "bool"); ok(r.answers[0].tree.v === true); eq(r.conditions.length, 0);
});
test("(x^2-1)/(x-1) = x+1 is an identity only for x != 1", () => {
  const r = A("identity", "(x^2-1)/(x-1) = x+1"); good(r);
  ok(r.answers[0].tree.v === true);
  eq(r.conditions.map(toText).join(), "x != 1");
  ok(/x != 1/.test(r.answers[0].label));
});
test("trig identity false at isolated points (domains differ) carries its conditions", () => {
  const r = A("identity", "sin(x)/tan(x) = cos(x)"); good(r);
  ok(r.conditions.map(toText).includes("tan(x) != 0"), "tan(x) != 0");
  ok(r.conditions.map(toText).includes("cos(x) != 0"), "cos(x) != 0");
  const c = A("identity", "cot(x)*tan(x) = 1"); good(c); ok(c.conditions.length >= 1);
});
test("an equation true only at isolated points is not an identity", () => {
  const r = A("identity", "sin(2x) = 2sin(x)"); good(r);
  ok(r.answers[0].tree.v === false); ok(r.answers[0].counterexample && r.answers[0].counterexample.x, "counterexample x");
  const s = A("identity", "sqrt(x^2) = x"); good(s); ok(s.answers[0].tree.v === false);
  const t = A("identity", "x = x + 10^(-20)"); good(t); ok(t.answers[0].tree.v === false, "tiny difference found exactly");
});
test("identity: two-argument form, more trig", () => {
  const r = A("identity", "cos(2x)", "1-2sin(x)^2"); good(r); ok(r.answers[0].tree.v === true);
  const s = A("identity", "1/(1-cos(x)) + 1/(1+cos(x)) = 2/sin(x)^2"); good(s); ok(s.answers[0].tree.v === true);
});
test("identity: refuses when neither proof nor counterexample", () => refused(A("identity", "ln(x^2) = 2ln(x)")));

// ---------------------------------------------------------------- analytic geometry
test("line, slope, distance, midpoint", () => {
  const r = A("line", "1", "2", "3", "8"); good(r); eq(txt(r.answers[0]), "y = 3x - 1");
  const v = A("line", "2", "1", "2", "5"); good(v); eq(txt(v.answers[0]), "x = 2"); ok(/vertical/i.test(v.answers[0].label));
  refused(A("line", "1", "1", "1", "1"), "same point");
  const s = A("slope", "1", "2", "3", "8"); good(s); eq(txt(s.answers[0]), "3");
  const sv = A("slope", "2", "1", "2", "5"); good(sv); eq(sv.answers[0].kind, "none");
  const d = A("distance", "0", "0", "1", "1"); good(d); eq(txt(d.answers[0]), "sqrt(2)");
  const d2 = A("distance", "(1,2)", "(4,6)"); good(d2); eq(txt(d2.answers[0]), "5");
  const m = A("midpoint", "1", "2", "3", "8"); good(m); eq(txt(m.answers[0]), "(2, 5)");
});

// ---------------------------------------------------------------- integral applications
test("arclength", () => {
  const r = A("arclength", "sqrt(1-x^2)", "x", "-1", "1"); good(r); eq(txt(r.answers[0]), "pi");
  const p = A("arclength", "x^(3/2)", "x", "0", "4"); good(p); same(p.answers[0].tree, "(80sqrt(10) - 8)/27", "x^(3/2)");
  const s = A("arclength", "sin(x)", "x", "0", "pi"); good(s);
  close(parseFloat(s.answers[0].approx.value), 3.820197789027712, 1e-10, "sin arclength");
});
test("areabetween with and without bounds", () => {
  const r = A("areabetween", "x", "x^2", "x"); good(r); eq(txt(r.answers[0]), "1/6");
  const q = A("areabetween", "x^2", "x+2", "x"); good(q); eq(txt(q.answers[0]), "9/2");
  const c = A("areabetween", "x^3", "x", "x"); good(c); eq(txt(c.answers[0]), "1/2");
  const t = A("areabetween", "sin(x)", "cos(x)", "x", "0", "pi"); good(t); eq(txt(t.answers[0]), "2sqrt(2)");
  const n = A("areabetween", "cos(x)", "x", "x", "0", "1"); good(n);
  close(parseFloat(n.answers[0].approx.value), 0.4595062390, 1e-8, "numeric crossing");
  refused(A("areabetween", "e^x", "x", "x"), "no enclosed region");
  refused(A("areabetween", "1/x", "0", "x", "-1", "1"), "singular");
});
test("volume and average value", () => {
  const v = A("volume", "sqrt(x)", "x", "0", "4"); good(v); eq(txt(v.answers[0]), "8pi");
  const c = A("volume", "x", "x", "0", "1"); good(c); eq(txt(c.answers[0]), "pi/3");
  const a = A("avgvalue", "sin(x)", "x", "0", "pi"); good(a); eq(txt(a.answers[0]), "2/pi");
  refused(A("avgvalue", "1/x", "x", "-1", "1"), "divergent");
});

// ---------------------------------------------------------------- verification policy
test("every answered command reports a passed verification and steps", () => {
  for (const [n, args] of [["domain", ["ln(x)", "x"]], ["extrema", ["x^2", "x"]], ["identity", ["sin(x)^2+cos(x)^2 = 1"]], ["areabetween", ["x", "x^2", "x"]]]) {
    const r = runAnalysis(n, args);
    good(r, n);
    ok(r.steps.length > 0, `${n} steps`);
    ok(r.verification.checks.length > 0, `${n} checks`);
  }
});
