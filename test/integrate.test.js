import { test, eq, ok, close, rng } from "./harness.js";
import * as X from "../public/engine/expr.js";
import { parse } from "../public/engine/parse.js";
import { simplify } from "../public/engine/simplify.js";
import { toText } from "../public/engine/print.js";
import { diff } from "../public/engine/calc/diff.js";
import { evalReal, equivalent } from "../public/engine/verify.js";
import { integrate } from "../public/engine/calc/integrate.js";
import { definiteIntegral } from "../public/engine/calc/int-definite.js";
import { integrateRationalQ } from "../public/engine/calc/int-rational.js";
import { lim } from "../public/engine/calc/int-limit.js";
import { checkAntiderivative, evalD, SiD, CiD, EiD, erfiD, FresnelSD, FresnelCD, liD } from "../public/engine/calc/int-util.js";
import * as P from "../public/engine/poly.js";
import { StepLog } from "../public/engine/steps.js";
import { solve } from "../public/engine/quelvra.js";
import { CORPUS } from "./bench/corpus.js";

const x = X.sym("x");
const OO = X.OO, NOO = X.mul(X.NEG_ONE, X.OO);
const S = (s) => simplify(parse(s));
const B = (s) => (s === "oo" ? OO : s === "-oo" ? NOO : S(s));

// independent test: G - f's known antiderivative-free check. F' = f at many points by central differences
// (the harness's own, not the integrator's), with F required to be defined where f is.
function derivMatches(F, f, pts = [-2.7, -1.3, -0.45, 0.35, 0.8, 1.6, 2.4, 3.3, 5.1]) {
  let n = 0;
  for (const p of pts) {
    const fv = evalD(f, { x: p });
    if (!Number.isFinite(fv)) continue;
    const h = 1e-5 * Math.max(1, Math.abs(p));
    const Fp = evalD(F, { x: p + h }), Fm = evalD(F, { x: p - h });
    if (!Number.isFinite(Fp) || !Number.isFinite(Fm)) {
      // allow isolated points only
      if (Number.isFinite(evalD(F, { x: p + 1e-3 })) && Number.isFinite(evalD(F, { x: p - 1e-3 }))) continue;
      return false;
    }
    if (Math.abs((Fp - Fm) / (2 * h) - fv) > 1e-5 * Math.max(1, Math.abs(fv))) return false;
    n++;
  }
  return n >= 3;
}
const I = (s, opts) => integrate(S(s), x, opts);
function anti(src, check) {
  test(`indefinite ${src}`, () => {
    const f = S(src);
    const r = integrate(f, x);
    ok(derivMatches(r.F, f), `derivative of ${toText(r.F)} is not ${src}`);
    if (check) check(r);
  });
}
function codeOf(fn) { try { fn(); } catch (e) { return e.code || "CRASH:" + e.message; } return "OK"; }

// ---------------------------------------------------------------- required indefinite integrals
anti("1/(x^3+1)", (r) => ok(/atan/.test(toText(r.F)) && /ln\(\|x \+ 1\|\)/.test(toText(r.F)), toText(r.F)));
anti("1/(x^4+1)", (r) => ok(!/i\b/.test(toText(r.F)) && /atan/.test(toText(r.F)), "real logs and atans only"));
anti("x^3 e^(x^2)", (r) => eq(toText(r.F), "e^(x^2)(x^2/2 - 1/2)"));
anti("e^x sin(x)", (r) => eq(r.method, "int.parts"));
anti("sec(x)^3", (r) => eq(toText(r.F), "sec(x)*tan(x)/2 + ln(|sec(x) + tan(x)|)/2"));
anti("sqrt(x^2+1)", (r) => eq(toText(r.F), "x*sqrt(x^2 + 1)/2 + ln(|x + sqrt(x^2 + 1)|)/2"));
anti("1/(x sqrt(x^2-1))");
anti("1/(2+cos(x))", (r) => eq(r.method, "int.weierstrass"));
anti("ln(x)/x", (r) => eq(toText(r.F), "ln(x)^2/2"));
test("tan x = -ln|cos x|", () => eq(toText(I("tan(x)").F), "-ln(|cos(x)|)"));
test("1/x = ln|x| (abs in the real domain)", () => eq(toText(I("1/x").F), "ln(|x|)"));
test("1/(x - 3) = ln|x - 3|", () => eq(toText(I("1/(x-3)").F), "ln(|x - 3|)"));
test("e^(x^2) is recognised as non-elementary (erfi)", () => {
  const r = I("e^(x^2)");
  eq(toText(r.F), "sqrt(pi)*erfi(x)/2");
  ok(r.special && r.nonelementary, "flagged non-elementary with a proof");
});
test("sin(x)/x -> Si, e^x/x -> Ei, 1/ln x -> li, e^(-x^2) -> erf, sin(x^2) -> Fresnel", () => {
  eq(toText(I("sin(x)/x").F), "Si(x)");
  eq(toText(I("e^x/x").F), "Ei(x)");
  eq(toText(I("1/ln(x)").F), "li(x)");
  eq(toText(I("e^(-x^2)").F), "sqrt(pi)*erf(x)/2");
  ok(/FresnelS/.test(toText(I("sin(x^2)").F)));
});
test("Risch: e^x/(x^2+1) proven non-elementary, x^x honestly unsupported", () => {
  eq(codeOf(() => I("e^x/(x^2+1)")), "NONELEMENTARY");
  eq(codeOf(() => I("x^x")), "UNSUPPORTED");
});
test("non-elementary sub-integrals never make an elementary sum non-elementary", () => {
  // each term alone needs Ei/erf-type functions; the sum is d/dx [e^x atan(x^3)]
  const c = codeOf(() => I("3x^2 e^x/(x^6+1) + e^x atan(x^3)"));
  ok(c === "OK" || c === "UNSUPPORTED", c);
  const r = I("2x e^(x^2) cos(e^(x^2))");
  eq(toText(r.F), "sin(e^(x^2))");
});

// more layers
const more = ["x^2", "cos(x)", "e^(3x)", "x e^x", "2x cos(x^2)", "1/(x^2+1)", "1/(x^2-1)", "ln(x)", "sin(x)^2", "sqrt(1-x^2)", "1/sqrt(1-x^2)",
  "cos(x)^4", "sin(x)^3 cos(x)^2", "tan(x)^3", "tan(x)^2 sec(x)^3", "csc(x)", "1/(1+sin(x))", "sin(3x) cos(5x)", "x^2 sqrt(x^2+1)", "x^2 sqrt(4-x^2)",
  "1/(x^2 sqrt(x^2+1))", "sqrt(x^2+2x+5)", "sqrt(x^2-1)", "x ln(x)", "x^2 e^(-x)", "atan(x)", "x atan(x)", "asin(x)", "ln(x)^2", "x^3 ln(x)^2",
  "e^(2x) cos(3x)", "1/(x^3-3x+1)", "1/(x^4-2)", "(x^5+1)/((x^2+1)^2 (x-1)^3)", "1/(x^6+1)", "x/(x^4+2x^2+2)", "sinh(x)^2", "1/cosh(x)",
  "6x^2/(4x^6+1)", "(2x+1)/(x^2 (x+1)^2+1)", "x^2 e^(-x^2)", "sqrt(x) e^x", "sin(ln(x))", "1/(x ln(x))", "3^x", "log_2(x)", "e^x/(e^x+1)",
  "1/(1+e^x)", "x/sqrt(x+1)", "1/(sqrt(x) + 1)", "cos(x)/(1 + sin(x)^2)"];
for (const s of more) anti(s);

// ---------------------------------------------------------------- rational engine directly
test("rational: Hermite + Rothstein-Trager, real forms", () => {
  for (const [n, d] of [["1", "x^3+2"], ["1", "x^4+x^2+1"], ["x^2", "(x^2+1)^3"], ["1", "x^5+x+1"]]) {
    const pn = P.fromTree(S(n), "x"), pd = P.fromTree(S(d), "x");
    const F = integrateRationalQ(pn, pd, x, null);
    ok(F && derivMatches(F, S(`(${n})/(${d})`)), `${n}/(${d})`);
  }
});

// ---------------------------------------------------------------- steps
test("steps use the documented rule ids", () => {
  const log = new StepLog();
  integrate(S("x e^(x^2) + 1/(x^2+1) + sec(x)^3"), x, { steps: log });
  const ids = new Set();
  const walk = (ss) => { for (const s of ss) { ids.add(s.rule); if (s.sub) walk(s.sub); } };
  walk(log.steps);
  for (const id of ids) ok(/^int\.(table|linear|poly|usub|parts|partial|trig|trigsub|weierstrass|euler|risch|special|ftc|improper)$/.test(id), id);
  ok(ids.has("int.linear"), "linearity recorded");
});

// ---------------------------------------------------------------- special-function evaluators
test("special-function evaluators", () => {
  close(SiD(1), 0.9460830703671830, 1e-12);
  close(SiD(20), 1.5482417010434398, 1e-11);
  close(CiD(1), 0.3374039229009681, 1e-12);
  close(EiD(1), 1.8951178163559368, 1e-12);
  close(EiD(-1), -0.21938393439552029, 1e-12);
  close(erfiD(1), 1.6504257587975429, 1e-12);
  close(FresnelSD(1), 0.43825914739035476, 1e-12);
  close(FresnelCD(1), 0.7798934003768228, 1e-12);
  close(liD(2), 1.0451637801174928, 1e-12);
});

// ---------------------------------------------------------------- limits for the definite module
test("limits with special functions", () => {
  eq(toText(lim(X.fn("Si", x), x, OO, "").v), "pi/2");
  eq(toText(lim(S("sqrt(pi) erf(x)/2"), x, OO, "").v), "sqrt(pi)/2");
  eq(lim(X.fn("Ci", x), x, X.ZERO, "+").s, -1);
  eq(lim(S("-cos(x)"), x, OO, "").k, "dne");
});

// ---------------------------------------------------------------- definite / improper
const DI = (f, a, b, opts) => definiteIntegral(S(f), x, B(a), B(b), opts);
function exact(f, a, b, want, opts) {
  test(`definite int_${a}^${b} ${f} = ${want}`, () => {
    const r = DI(f, a, b, opts);
    eq(r.status, "exact", `${f}: ${r.reason || ""}`);
    const e = equivalent(r.value, S(want));
    ok(e.status.startsWith("equivalent"), `got ${toText(r.value)}`);
  });
}
function diverges(f, a, b) {
  test(`definite int_${a}^${b} ${f} diverges`, () => {
    const r = DI(f, a, b);
    eq(r.status, "diverges");
    ok(r.reason && r.reason.length > 20, "has a reason");
  });
}
exact("1/(2+cos(x))", "0", "2*pi", "2pi/sqrt(3)");
diverges("1/x^2", "-1", "1");
exact("e^(-x^2)", "0", "oo", "sqrt(pi)/2");
exact("sin(x)/x", "0", "oo", "pi/2");
exact("ln(x)", "0", "1", "-1");
exact("1/(1+x^2)", "0", "oo", "pi/2");
exact("1/sqrt(x)", "0", "1", "2");
test("int_0^1 x^x ~ 0.7834305107 (numeric, no exact tree)", () => {
  const r = DI("x^x", "0", "1");
  eq(r.status, "approx");
  close(r.value, 0.78343051071213440705, 1e-10);
});
exact("1/(5-4cos(x))", "0", "2*pi", "2pi/3");
exact("1/(1+x^2)", "-oo", "oo", "pi");
exact("e^(-x^2)", "-oo", "oo", "sqrt(pi)");
exact("1/(x^3+1)", "0", "oo", "2pi/(3sqrt(3))");
exact("x^2 e^(-x)", "0", "oo", "2");
exact("1/sqrt(1-x^2)", "-1", "1", "pi");
exact("1/(x^2-1)", "2", "3", "ln(3/2)/2");
exact("1/(x ln(x)^2)", "2", "oo", "1/ln(2)");
exact("abs(x)", "-1", "2", "5/2");
exact("1/x^(1/3)", "-1", "1", "0");
exact("x^2", "1", "0", "-1/3");
diverges("1/x", "-1", "1");
diverges("tan(x)", "-3", "0"); // limit at -pi/2 needs the mirrored retry (simplifier recursion)
diverges("1/x", "1", "oo");
diverges("sin(x)", "0", "oo");
diverges("tan(x)", "0", "pi");
diverges("sec(x)^2", "0", "pi");
diverges("1/(x^2-1)", "0", "2");
diverges("x/(1+x^2)", "-oo", "oo");
diverges("1/(x ln(x))", "2", "oo");
exact("1/x", "-1", "2", "ln(2)", { pv: true });
exact("x/(1+x^2)", "-oo", "oo", "0", { pv: true });
test("integrand not real on the interval", () => eq(codeOf(() => DI("sqrt(x)", "-1", "1")), "NOTREAL"));
test("symbolic upper limit: int_0^t cos = sin t", () => {
  const r = definiteIntegral(S("cos(x)"), x, X.ZERO, X.sym("t"));
  eq(toText(r.value), "sin(t)");
});
test("symbolic limit with a break point is refused, not guessed", () => {
  eq(codeOf(() => definiteIntegral(S("1/x"), x, X.num(-1), X.sym("t"))), "UNSUPPORTED");
});

// ---------------------------------------------------------------- solver strategy (answer shapes)
test("strategy: antiderivative answer shape", () => {
  const r = solve("int x e^x dx");
  eq(r.answers[0].kind, "exact");
  eq(r.answers[0].constant, true);
  eq(r.verification.status, "passed");
});
test("strategy: divergence answer shape", () => {
  const r = solve("int_1^oo 1/x dx");
  eq(r.answers[0].kind, "none");
  eq(r.answers[0].label, "The integral diverges");
  ok(r.answers[0].reason);
  eq(r.solutionStatus, "exact");
});
test("strategy: definite value with approximation, cross-checked", () => {
  const r = solve("int_0^oo e^(-x^2) dx");
  eq(toText(r.answers[0].tree), "sqrt(pi)/2");
  ok(r.answers.some((a) => a.kind === "approx"));
  eq(r.verification.status, "passed");
});
test("strategy: non-elementary antiderivative", () => {
  const r = solve("int e^x/(x^2+1) dx");
  eq(r.answers[0].kind, "none");
  ok(/elementary/i.test(r.answers[0].label));
});
test("strategy: numeric fallback is an Approx record, never a tree", () => {
  const r = solve("int_0^1 x^x dx");
  eq(r.solutionStatus, "approximate");
  ok(r.answers.every((a) => a.kind === "approx" && !a.tree));
});

// ---------------------------------------------------------------- benchmark corpus entries
const P0 = (s) => simplify(parse(s));
for (const [cat, q, exp] of CORPUS.filter((c) => c[0] === "int")) {
  test(`corpus: ${q}`, () => {
    const r = solve(q);
    ok(r.ok, `not ok: ${(r.answers || []).map((a) => a.label || a.kind).join("; ")}`);
    eq(r.verification.status, "passed", "verified");
    if (exp.anti) {
      const F = r.answers[0].tree, G = P0(exp.anti);
      const d = [0.3, 0.7, 1.3, 0.55, 0.9].map((t) => evalReal(F, { x: t }) - evalReal(G, { x: t })).filter(Number.isFinite);
      ok(d.length >= 3 && d.every((v) => Math.abs(v - d[0]) < 1e-8 * Math.max(1, Math.abs(d[0]))), `got ${toText(F)}`);
    } else if (exp.value !== undefined) {
      ok(equivalent(r.answers[0].tree, P0(exp.value)).status.startsWith("equivalent"), `got ${toText(r.answers[0].tree)}`);
    } else if (exp.approx !== undefined) {
      const a = r.answers.find((z) => z.approx);
      close(Number(a.approx.value), exp.approx, exp.tol || 1e-8);
    }
    void cat;
  });
}

// ---------------------------------------------------------------- robustness
test("simplifier recursion on sin(-x - 2) does not crash the integrator", () => {
  const c = codeOf(() => I("e^(-x/2) cos(x+2) - e^(-x/2) sin(x+2)/2"));
  ok(c === "OK" || c === "UNSUPPORTED", c);
});

// ---------------------------------------------------------------- property test
// Random elementary F; f = simplify(F'); integrate(f) must either fail honestly or return G with
// G - F locally constant (checked independently of the integrator's own verification).
test("property: integrate(diff(F)) is F + C or an honest failure; zero wrong answers", () => {
  const R = rng(20260925);
  const K = () => X.num(R.pick([1, 2, 3, -1, -2, 5]), R.pick([1, 1, 1, 2, 3]));
  const gen = (d) => {
    if (d === 0) return R.pick([() => x, () => X.add(x, X.num(R.int(1, 3))), () => X.mul(K(), x), () => X.pow(x, X.num(R.int(2, 3)))])();
    const a = gen(d - 1);
    switch (R.int(0, 9)) {
      case 0: return X.add(a, gen(d - 1));
      case 1: return X.mul(a, gen(d - 1));
      case 2: return X.fn("sin", a);
      case 3: return X.fn("cos", a);
      case 4: return X.exp(a);
      case 5: return X.fn("ln", X.add(X.pow(a, X.TWO), X.ONE));
      case 6: return X.fn("atan", a);
      case 7: return X.sqrt(X.add(X.pow(a, X.TWO), X.num(R.int(1, 4))));
      case 8: return X.mul(K(), a);
      default: return X.pow(a, X.num(R.int(2, 3)));
    }
  };
  let okN = 0, honest = 0, wrong = 0, total = 0;
  const bad = [];
  while (total < 300) {
    const F = simplify(gen(R.int(1, 2)));
    let f;
    try { f = simplify(diff(F, x)); } catch (_) { continue; }
    if (X.freeOf(f, x)) continue;
    total++;
    let G;
    try { G = integrate(f, x, { timeLimit: 3000 }).F; } catch (e) {
      ok(["UNSUPPORTED", "BUDGET", "TIMEOUT", "NONELEMENTARY"].includes(e.code), `crash on ${toText(f)}: ${e.message}`);
      if (e.code === "NONELEMENTARY") { wrong++; bad.push(`claimed non-elementary: ${toText(f)}`); } else honest++;
      continue;
    }
    let tested = 0, mism = 0;
    for (let k = 0; k < 60 && tested < 12; k++) {
      const p = -4 + 8 * ((k * 0.6180339887) % 1);
      const d1 = evalD(G, { x: p }) - evalD(F, { x: p }), d2 = evalD(G, { x: p + 0.01 }) - evalD(F, { x: p + 0.01 });
      if (!Number.isFinite(d1) || !Number.isFinite(d2)) continue;
      tested++;
      if (Math.abs(d1 - d2) > 1e-6 * Math.max(1, Math.abs(d1))) mism++;
    }
    if (mism) { wrong++; bad.push(`${toText(f)} => ${toText(G)}`); } else okN++;
  }
  console.log(`   property test: ${okN}/${total} integrated (${(100 * okN / total).toFixed(1)}%), ${honest} honest failures, ${wrong} wrong`);
  eq(wrong, 0, bad.join("; "));
});

void checkAntiderivative;
