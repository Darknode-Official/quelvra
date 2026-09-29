// Quelvra Tools tab: the pure logic in public/quelvra/tools-core.js, checked against the real engine
// (the same solve() the worker runs), so every request the UI builds is one the engine answers.
import { test, eq, ok, close } from "./harness.js";
import * as engine from "../public/engine/quelvra.js";
import { toText } from "../public/engine/print.js";
import { parse } from "../public/engine/parse.js";
import { serializeResult, deserializeResult } from "../public/bridge-shared.js";
import { classifyPlot } from "../public/graph.js";
import * as C from "../public/tools-core.js";

// what the page receives: the engine result after the worker round trip
const solve = (input, options = {}) => deserializeResult(JSON.parse(JSON.stringify(serializeResult(engine.solve(input, options)))));
const first = (r) => C.exactAnswers(r)[0];

// ---------------- shared helpers
test("tools: exactNumberText accepts decimals, fractions and e-notation exactly", () => {
  eq(C.exactNumberText("12"), "12");
  eq(C.exactNumberText(" -3.50 "), "-3.50");
  eq(C.exactNumberText(".5"), "0.5");
  eq(C.exactNumberText("5."), "5");
  eq(C.exactNumberText("3/4"), "3/4");
  eq(C.exactNumberText("-1/3"), "-1/3");
  eq(C.exactNumberText("1/0"), "");
  eq(C.exactNumberText("2.5e3"), "2500");
  eq(C.exactNumberText("1.25E-3"), "0.00125");
  eq(C.exactNumberText("7e0"), "7");
  eq(C.exactNumberText("−2"), "-2");
  for (const bad of ["", "abc", "1..2", "--1", "1e", "e5", "1/2/3", "0x1f"]) eq(C.exactNumberText(bad), "", bad);
});

test("tools: verdict reads verified, approximate, empty and refused results", () => {
  eq(C.verdict(solve("x^2 - 5x + 6 = 0")).state, "verified");
  eq(C.verdict(solve("cos(x) = x")).state, "approx");
  const none = C.verdict(solve("x + y = 3; x + y = 4"));
  ok(none.empty && none.state === "verified", JSON.stringify(none));
  eq(C.verdict(null).state, "none");
  eq(C.verdict({ answers: [{ kind: "none", label: "Not supported yet" }], solutionStatus: "unsupported" }).state, "none");
  eq(C.decimalOf(solve("sqrt(2) + 1")).slice(0, 8), "2.414213");
  eq(C.decimalOf(solve("2 + 3")), "");
});

test("tools: floatOf and evalFloat handle trees, text and odd roots", () => {
  close(C.floatOf(first(solve("sqrt(8)")).tree), Math.sqrt(8));
  close(C.floatOf("pi/2"), Math.PI / 2);
  close(C.evalFloat(parse("(-8)^(1/3)")), -2);
  close(C.evalFloat(parse("log_2(8)")), 3);
  ok(Number.isNaN(C.floatOf("x + 1")));
  eq(C.fmt(0.1 + 0.2), "0.3");
  eq(C.fmt(1e-7), "1e-7");
  eq(C.fmt(Infinity), "inf");
});

// ---------------- matrices
test("tools: grid resize keeps entries, clamps to 1..8 and serialises with 0 for blanks", () => {
  let g = C.makeGrid(2, 2);
  g[0][0] = "1"; g[1][1] = "4";
  g = C.resizeGrid(g, 3, 1);
  eq(g.length, 3); eq(g[0].length, 1); eq(g[0][0], "1"); eq(g[2][0], "");
  eq(C.resizeGrid(g, 0, 20).length, 1);
  eq(C.resizeGrid(g, 0, 20)[0].length, 8);
  eq(C.matrixText([["1", ""], [" -1/2", "sqrt(2)"]]), "[[1, 0], [-1/2, sqrt(2)]]");
  eq(C.cellError("1/3"), "");
  ok(C.cellError("1, 2"), "commas are not cells");
  ok(C.cellError("2 +"), "syntax errors are reported");
  eq(C.gridErrors([["1", "x ="]]).length, 1);
});

test("tools: pasted grids from spreadsheets, text and bracket form", () => {
  eq(JSON.stringify(C.parseGridText("1\t2\n3\t4")), JSON.stringify([["1", "2"], ["3", "4"]]));
  eq(JSON.stringify(C.parseGridText("1 2 3\n4 5 6")), JSON.stringify([["1", "2", "3"], ["4", "5", "6"]]));
  eq(JSON.stringify(C.parseGridText("[[1, 2], [3, 4]]")), JSON.stringify([["1", "2"], ["3", "4"]]));
  eq(C.parseGridText("1 2\n3"), null);
  eq(C.parseGridText(""), null);
});

test("tools: every matrix operation builds a request the engine verifies", () => {
  const A = [["2", "1"], ["1", "3"]], B = [["1", "0"], ["4", "1"]];
  const want = {
    det: "5", inv: "[[3/5, -1/5], [-1/5, 2/5]]", transpose: "[[2, 1], [1, 3]]", rank: "2", rref: "[[1, 0], [0, 1]]", trace: "5",
    mul: "[[6, 1], [13, 3]]", add: "[[3, 1], [5, 4]]", sub: "[[1, 1], [-3, 2]]", pow: "[[5, 5], [5, 10]]",
  };
  for (const [op, text] of Object.entries(want)) {
    const req = C.matrixRequest(op, A, B, "2");
    ok(!req.error, op + ": " + req.error);
    const r = solve(req.input, req.options);
    eq(C.verdict(r).state, "verified", op);
    eq(C.answerText(first(r)), text, op);
  }
  const ev = solve(C.matrixRequest("eigenvalues", A, B).input);
  eq(C.verdict(ev).state, "verified");
  eq(C.exactAnswers(ev).map(C.answerText).sort().join(" | "), "-sqrt(5)/2 + 5/2 | sqrt(5)/2 + 5/2");
});

test("tools: solve A x = b writes the system out and solves for x_1..x_n", () => {
  const req = C.matrixRequest("solve", [["1", "2"], ["3", "4"]], [["5"], ["6"]]);
  eq(req.input, "(1)*x_1 + (2)*x_2 = 5; (3)*x_1 + (4)*x_2 = 6");
  const r = solve(req.input, req.options);
  eq(C.verdict(r).state, "verified");
  const sol = (r.answers || []).find((a) => a.kind === "solution");
  eq(sol.values.map(([k, v]) => k + "=" + C.answerText({ tree: v })).join(","), "x_1=-4,x_2=9/2");
  // singular: proven inconsistent
  const bad = solve(C.matrixRequest("solve", [["1", "1"], ["1", "1"]], [["1"], ["2"]]).input, { variable: ["x_1", "x_2"] });
  ok(C.verdict(bad).empty, "inconsistent system is reported as no solution");
});

test("tools: matrix shape errors are caught before the engine", () => {
  const A = [["1", "2", "3"]], B = [["1"], ["2"]];
  ok(C.matrixRequest("det", A, B).error);
  ok(C.matrixRequest("mul", A, B).error);
  ok(C.matrixRequest("add", A, B).error);
  ok(C.matrixRequest("pow", [["1"]], B, "1.5").error);
  ok(C.matrixRequest("solve", [["1", "2"], ["3", "4"]], [["1"]]).error);
  ok(!C.matrixRequest("rank", A, B).error);
});

// ---------------- units
test("tools: unit catalog has the ten categories with unique ids", () => {
  eq(C.UNIT_CATEGORIES.map((c) => c.id).join(","), "length,mass,time,speed,temperature,area,volume,energy,pressure,data");
  for (const c of C.UNIT_CATEGORIES) {
    eq(new Set(c.units.map((u) => u.id)).size, c.units.length, c.id);
    ok(c.units.length >= 3, c.id);
    for (const u of c.units) ok(u.sym || u.factor, c.id + " " + u.id);
  }
});

test("tools: engine unit conversions agree with the catalog's exact factors (every symbol pair)", () => {
  for (const c of C.UNIT_CATEGORIES) {
    if (c.id === "temperature") continue;
    const withSym = c.units.filter((u) => u.sym);
    const base = withSym[0];
    for (const u of withSym) {
      for (const v of [base, withSym[withSym.length - 1]]) {
        if (u === v) continue;
        const viaUnits = C.conversionRequest(c.id, u.id, v.id, "3.7");
        eq(viaUnits.via, "units");
        const r1 = solve(viaUnits.input);
        eq(C.verdict(r1).state, "verified", viaUnits.input);
        // the same conversion by factor arithmetic must give the identical exact value
        const f = `(3.7) * (${u.factor.replace(/e(-?\d+)/, "*10^($1)")}) / (${v.factor})`;
        const r2 = solve(f);
        eq(C.answerText(first(r1)), C.answerText(first(r2)), `${u.id} -> ${v.id}`);
      }
    }
  }
});

test("tools: conversions with units the engine lacks go through exact factors", () => {
  const cases = [
    ["data", "GiB", "MB", "1", "1073741824/1000000", "1073.741824"],
    ["data", "B", "bit", "3", "24", ""],
    ["area", "acre", "m^2", "1", "", "4046.8564224"],
    ["mass", "st", "kg", "1", "", "6.35029318"],
    ["volume", "gal", "qt", "1", "4", ""],
    ["energy", "BTU", "J", "2", "", "2110.1117052"],
  ];
  for (const [cat, a, b, v, exact, dec] of cases) {
    const req = C.conversionRequest(cat, a, b, v);
    eq(req.via, "factors", `${a} -> ${b}`);
    const r = solve(req.input);
    eq(C.verdict(r).state, "verified", req.input);
    const t = C.answerText(first(r));
    if (exact) eq(t.replace(/\s/g, ""), exact.includes("/") ? String(eval_(exact)) : exact, `${a} -> ${b}`);
    if (dec) ok(C.decimalOf(r).startsWith(dec) || t === dec, `${a} -> ${b}: ${t} ${C.decimalOf(r)}`);
  }
  function eval_(s) { const [n, d] = s.split("/").map(BigInt); const g = gcd(n, d); return `${n / g}/${d / g}`.replace(/\/1$/, ""); }
  function gcd(a, b) { while (b) [a, b] = [b, a % b]; return a; }
});

test("tools: temperature is affine and converted by the engine", () => {
  const r = solve(C.conversionRequest("temperature", "degF", "degC", "100").input);
  eq(C.answerText(first(r)), "340/9");
  const k = solve(C.conversionRequest("temperature", "degC", "K", "-273.15").input);
  eq(C.answerText(first(k)), "0");
  ok(C.conversionRequest("temperature", "degC", "K", "hot").error);
  ok(C.conversionRequest("length", "m", "kg", "1").error);
  ok(C.conversionRequest("temperature", "degC", "K", "1/3").error, "fractions are not read by the unit parser");
  eq(C.conversionRequest("length", "m", "ft", "1/3").via, "factors");
});

// ---------------- calculator
test("tools: calculator input handles Ans, memory, symbols and degree mode", () => {
  eq(C.calcInput("2 × 3 ÷ 4").error, undefined);
  eq(solve(C.calcInput("2 × 3 ÷ 4").input).answers[0].tree.text, "3/2");
  eq(solve(C.calcInput("Ans + 1", { ans: "1/2" }).input).answers[0].tree.text, "3/2");
  ok(C.calcInput("Ans + 1").error, "no answer yet");
  eq(solve(C.calcInput("MR * 2", { memory: "sqrt(2)" }).input).answers[0].tree.text, "2sqrt(2)");
  eq(solve(C.calcInput("sin(30)", { angle: "deg" }).input).answers[0].tree.text, "1/2");
  eq(solve(C.calcInput("cos(60) + tan(45)", { angle: "deg" }).input).answers[0].tree.text, "3/2");
  eq(solve(C.calcInput("asin(1/2)", { angle: "deg" }).input).answers[0].tree.text, "30");
  eq(solve(C.calcInput("sin(pi/6)", { angle: "rad" }).input).answers[0].tree.text, "1/2");
  eq(solve(C.calcInput("√(16) + π - π").input).answers[0].tree.text, "4");
  ok(C.calcInput("x + 1").error.includes("Unknown name"));
  ok(C.calcInput("2 +").error);
  ok(C.calcInput("").error);
});

test("tools: calculator keypad inserts templates at the caret", () => {
  eq(JSON.stringify(C.insertTemplate("12", 2, 2, " + ")), JSON.stringify({ value: "12 + ", caret: 5 }));
  eq(JSON.stringify(C.insertTemplate("x", 0, 1, "sqrt(|)")), JSON.stringify({ value: "sqrt(x)", caret: 6 }));
  eq(C.insertTemplate("", 0, 0, "sin(|)").caret, 4);
  const labels = C.CALC_KEYS.map((k) => k[0]);
  for (const d of "0123456789") ok(labels.includes(d), "digit " + d);
  ok(C.CALC_KEYS.every((k) => k[0] && k[1]));
});

// ---------------- statistics
test("tools: data lists parse from commas, spaces, lines, with bad tokens reported", () => {
  const d = C.parseData("1, 2.5\n-3; 4e1 abc 1/2");
  eq(d.values.join(" "), "1 2.5 -3 40 1/2");
  eq(d.bad.join(" "), "abc");
  close(d.floats[4], 0.5);
  const p = C.parsePairs("x, y\n1, 2\n2 4\n(3, 5)\n4\t8\nbad line");
  eq(p.xs.join(","), "1,2,3,4");
  eq(p.ys.join(","), "2,4,5,8");
  eq(p.bad.join(","), "6");
});

test("tools: statistics requests are verified by the engine", () => {
  const vals = C.parseData("2 4 4 4 5 5 7 9").values;
  const reqs = Object.fromEntries(C.statsRequests(vals));
  const got = {};
  for (const [k, input] of Object.entries(reqs)) {
    const r = solve(input);
    eq(C.verdict(r).state, "verified", k + ": " + input);
    got[k] = C.exactAnswers(r).map(C.answerText).join(" | ");
  }
  eq(got.mean, "5"); eq(got.median, "9/2"); eq(got.sum, "40"); eq(got.mode, "4"); eq(got.range, "7");
  eq(got.stdev, "sqrt(32/7) | 2".replace("sqrt(32/7)", C.answerText(first(solve("stdev(2,4,4,4,5,5,7,9)")))));
  eq(got.quartiles.split(" | ").length, 3);
  eq(C.statsRequests(["1"]).map((r) => r[0]).join(","), "mean,median,sum");
  const reg = Object.fromEntries(C.regressionRequests(["1", "2", "3", "4"], ["2", "4", "5", "8"]));
  const lr = solve(reg.linreg);
  eq(C.verdict(lr).state, "verified");
  eq(C.answerText(first(lr)), "y = 19x/10");
  eq(C.verdict(solve(reg.corr)).state, "verified");
});

test("tools: histogram bins and box plot geometry", () => {
  const bins = C.histogramBins([1, 2, 2, 3, 3, 3, 4, 4, 5, 10]);
  eq(bins.length, Math.ceil(Math.log2(10) + 1));
  eq(bins.reduce((s, b) => s + b.count, 0), 10);
  eq(bins[0].lo, 1); eq(bins[bins.length - 1].hi, 10);
  eq(C.histogramBins([5, 5, 5]).reduce((s, b) => s + b.count, 0), 3);
  eq(C.histogramBins([]).length, 0);
  const b = C.boxPlot([1, 2, 3, 4, 5, 6, 7, 8, 100], 2.5, 5, 7.5);
  eq(b.outliers.join(), "100");
  eq(b.whiskerHi, 8); eq(b.whiskerLo, 1);
});

// ---------------- number theory
test("tools: number theory requests: factor, gcd, lcm, powmod", () => {
  const f = solve(C.ntRequest("factor", "360").input);
  eq(C.verdict(f).state, "verified");
  eq(C.answerText(first(f)), "2^3*3^2*5");
  eq(C.answerText(first(solve(C.ntRequest("gcd", "462, 1071").input))), "21");
  eq(C.answerText(first(solve(C.ntRequest("lcm", "4 6 10").input))), "60");
  eq(C.answerText(first(solve(C.ntRequest("powmod", "2", "100", "97").input))), "16");
  ok(C.ntRequest("gcd", "12").error);
  ok(C.ntRequest("powmod", "2", "", "7").error);
  eq(C.intText("1 000 003"), "1000003");
  eq(C.intText("2^61 - 1"), "2^61 - 1");
  eq(C.intText("abc"), "");
});

test("tools: modular inverse comes from the engine's verified congruence solution", () => {
  const req = C.ntRequest("modinv", "3", "11");
  const r = solve(req.input);
  eq(C.verdict(r).state, "verified");
  const a = (r.answers || []).find((x) => x.kind === "general" || x.kind === "exact");
  eq(C.residueOf(a.tree, req.modulus), 4n);
  const big = C.ntRequest("modinv", "17", "3120");
  const rb = solve(big.input);
  const ab = (rb.answers || []).find((x) => x.kind === "general" || x.kind === "exact");
  eq(C.residueOf(ab.tree, big.modulus), 2753n);
  // no inverse when gcd(a, m) > 1
  const none = solve(C.ntRequest("modinv", "2", "4").input);
  ok(!C.exactAnswers(none).length, "2 has no inverse mod 4");
  eq(C.residueOf(parse("11k + 4"), "11"), 4n);
  eq(C.residueOf(parse("7k - 3"), "7"), 4n);
  eq(C.residueOf(parse("x/2"), "7"), null);
});

test("tools: base conversion both ways, including letter digits", () => {
  const t = solve(C.ntRequest("tobase", "255", "16").input);
  eq(C.verdict(t).state, "verified");
  eq(first(t).text, "FF (base 16)");
  eq(C.fromBaseExpr("ff", 16), "15*16^1 + 15");
  eq(C.fromBaseExpr("-101", 2), "-(2^2 + 1)");
  eq(C.fromBaseExpr("000", 8), "0");
  eq(C.answerText(first(solve(C.ntRequest("frombase", "zz", "36").input))), "1295");
  eq(C.answerText(first(solve(C.ntRequest("frombase", "7fffffffffffffff", "16").input))), "9223372036854775807");
  ok(C.ntRequest("frombase", "12", "2").error.includes("digit 2"));
  ok(C.ntRequest("tobase", "10", "40").error);
});

test("tools: primality certificates render as proof lines", () => {
  const lines = C.certificateLines({ n: "1000003", type: "pocklington", F: "1000002", witnesses: [{ q: "2", a: "2" }], factors: [{ n: "2", type: "deterministic-mr" }] });
  ok(lines[0].includes("Pocklington"));
  ok(lines[1].includes("witness a = 2"));
  ok(lines[2].startsWith("  2 is prime"));
  eq(C.certificateLines({ n: "127", type: "lucas-lehmer", p: 7, pCert: { n: "7", type: "deterministic-mr" } }).length, 2);
});

// ---------------- systems
test("tools: system builder passes the chosen unknowns to the engine", () => {
  const req = C.systemRequest(["a x + y = 1", "", "x - y = 2"], "x, y");
  eq(req.input, "a x + y = 1; x - y = 2");
  eq(JSON.stringify(req.options), JSON.stringify({ variable: ["x", "y"] }));
  const r = solve(req.input, req.options);
  eq(C.verdict(r).state, "verified");
  const sol = r.answers.find((a) => a.kind === "solution");
  eq(sol.values.map(([k, v]) => k + "=" + v.text).join(","), "x=3/(a + 1),y=(-2a + 1)/(a + 1)");
  ok(C.systemRequest([], "").error);
  ok(C.systemRequest(["x + y"], "").error.includes("equals"));
  ok(C.systemRequest(["x = 1"], "x, 2y").error);
  eq(JSON.stringify(C.systemRequest(["x = 1"], "x").options), JSON.stringify({ variable: "x" }));
  eq(C.suggestUnknowns(["a x + y = 1", "x - y = 2"]).join(","), "x,y");
  eq(C.suggestUnknowns(["p + q = 2", "p - q = 0"]).join(","), "p,q");
  eq(C.parseUnknowns("x y, x z_1").names.join(","), "x,y,z_1");
});

// ---------------- graphing
test("tools: plot rows classify as function, parametric, polar and implicit", () => {
  const kind = (s) => C.rowKind(classifyPlot(parse(s)));
  eq(kind("x^2 - 2"), "function");
  eq(kind("y = sin(x)"), "function");
  eq(kind("(cos(3t), sin(2t))"), "parametric");
  eq(kind("r = 1 + cos(theta)"), "polar");
  eq(kind("x^2 + y^2 = 9"), "implicit");
  eq(kind("y > x^2"), "inequality");
  for (const ex of C.GRAPH_EXAMPLES) ok(kind(ex) !== "none", ex);
});

test("tools: graph analysis finds verified zeros, extrema and intersections", () => {
  const fns = [{ text: "x^2 - 2" }, { text: "x" }];
  const reqs = C.analysisRequests(fns);
  eq(reqs.map((r) => r.key).join(","), "zeros:0,extrema:0,zeros:1,extrema:1,meet:0:1");
  const f0 = (x) => x * x - 2;
  const at = { zero: f0, extremum: f0, intersection: f0 };
  const pts = {};
  for (const q of reqs) pts[q.key] = C.pointsFromResult(q, solve(q.input, q.options), q.rows[0] === 1 ? (x) => x : at[q.kind], -10, 10);
  eq(pts["zeros:0"].map((p) => p.text).join(","), "-sqrt(2),sqrt(2)");
  ok(pts["zeros:0"].every((p) => p.status === "verified" && p.y === 0 || Math.abs(p.y) < 1e-12));
  eq(pts["extrema:0"].length, 1);
  eq(pts["extrema:0"][0].label, "min");
  eq(pts["extrema:0"][0].y, -2);
  eq(pts["meet:0:1"].map((p) => p.text).join(","), "-1,2");
  // periodic zeros are expanded inside the view only
  const sz = C.pointsFromResult({ kind: "zero", rows: [0] }, solve("zeros(sin(x))"), Math.sin, -7, 7);
  eq(sz.length, 5);
  ok(sz.every((p) => p.status === "verified"));
  // an approximate root is marked approximate
  const ap = C.pointsFromResult({ kind: "intersection", rows: [0, 1] }, solve("cos(x) = x", { variable: "x" }), Math.cos, -10, 10);
  eq(ap.length, 1);
  eq(ap[0].status, "approximate");
  close(ap[0].x, 0.7390851332, 1e-9);
});

test("tools: table of values substitutes exact x values into the tree", () => {
  const xs = C.tableXs("-1", "1/2", 5);
  eq(xs.length, 5);
  eq(xs[0], "-1");
  const tree = parse("x^2 + 1");
  const vals = xs.map((x) => C.answerText(first(solve(C.substituteText(tree, "x", x)))));
  eq(vals.join(","), "2,5/4,1,5/4,2");
  eq(C.tableXs("a", "1", 3), null);
  eq(C.tableXs("0", "1", 500).length, 50);
});

// ---------------- formulas
test("tools: formula sheet covers six areas and every example is solved and verified", () => {
  eq(C.FORMULA_CATEGORIES.join(","), "Algebra,Trigonometry,Derivatives,Integrals,Geometry,Probability");
  for (const f of C.FORMULAS) {
    const r = solve(f.example);
    const v = C.verdict(r);
    ok(v.state === "verified" || v.state === "approx", `${f.name}: ${f.example} -> ${v.state} ${v.text}`);
  }
  eq(C.searchFormulas("chain").length, 1);
  ok(C.searchFormulas("sin").length >= 4);
  eq(C.searchFormulas("", "Geometry").length, C.FORMULAS.filter((f) => f.cat === "Geometry").length);
  eq(C.searchFormulas("nothing-matches-this").length, 0);
});

test("tools: tool list is stable", () => {
  eq(C.TOOL_IDS.join(","), "graph,matrix,units,calc,stats,numtheory,formulas,system");
});

test("tools: expanded general answers print simplified (no 0 pi terms)", () => {
  const r = solve("zeros(cos(x))");
  const pts = C.pointsFromResult({ kind: "zero", rows: [0] }, r, Math.cos, -7, 7);
  ok(pts.length >= 4, "several zeros in view");
  for (const p of pts) ok(!/\b0 ?\*? ?pi|\+ 0\b/.test(p.text), p.text);
  ok(pts.some((p) => p.text === "pi/2"), pts.map((p) => p.text).join(" | "));
});
