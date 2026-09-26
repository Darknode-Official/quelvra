// Quelvra web interface: pure-module tests (MathML renderer, serialisation, stub engine, storage fallback).
import { test, eq, ok } from "./harness.js";
import * as X from "../public/engine/expr.js";
import { parse } from "../public/engine/parse.js";
import { simplify } from "../public/engine/simplify.js";
import { toText } from "../public/engine/print.js";
import { toMathML, mathmlBody, mathmlFromText, changedIds } from "../public/mathml.js";
import { serializeResult, deserializeResult, treeToJSON, treeFromJSON } from "../public/bridge-shared.js";
import * as engine from "../public/engine/quelvra.js";
import * as store from "../public/storage.js";
import { readFileSync, readdirSync } from "node:fs";
import { dirname, join } from "node:path";
import { fileURLToPath } from "node:url";

const M = (src, simp = true) => mathmlBody(simp ? simplify(parse(src)) : parse(src));
const has = (s, frag, msg) => ok(s.includes(frag), `${msg || ""} expected ${JSON.stringify(frag)} in ${s}`);
const lacks = (s, frag, msg) => ok(!s.includes(frag), `${msg || ""} did not expect ${JSON.stringify(frag)} in ${s}`);
// strip tags: the visible character sequence
const flat = (s) => s.replace(/<[^>]+>/g, "").replace(/[\u2061\u2062]/g, "").replace(/&lt;/g, "<").replace(/&gt;/g, ">").replace(/&amp;/g, "&");

// crude well-formedness check: every opening tag is closed in order
function balanced(xml) {
  const stack = [];
  const re = /<\/?([a-z]+)[^>]*?(\/?)>/g;
  let m;
  while ((m = re.exec(xml))) {
    if (m[0].startsWith("</")) { if (stack.pop() !== m[1]) return false; }
    else if (!m[2]) stack.push(m[1]);
  }
  return stack.length === 0;
}

test("mathml: wrapper and namespace", () => {
  const s = toMathML(parse("x+1"));
  ok(s.startsWith('<math xmlns="http://www.w3.org/1998/Math/MathML" display="block">'), s);
  ok(s.endsWith("</math>"));
  has(toMathML(parse("x"), { display: false }), 'display="inline"');
});

test("mathml: sums print highest degree first with subtraction", () => {
  const s = M("3 + x^2 - 2x");
  eq(flat(s), "x2−2x+3"); // x^2 - 2x + 3 (invisible times not shown by flat? it is a char)
});

test("mathml: fractions from negative powers and rational coefficients", () => {
  has(M("1/x"), "<mfrac>");
  has(M("x/2"), "<mfrac>");
  has(M("3/(2x)"), "<mfrac>");
  const s = M("-x/3");
  has(s, "−");
  has(s, "<mfrac>");
  has(mathmlBody(X.num(-3, 4)), "<mfrac><mrow><mn>3</mn></mrow><mrow><mn>4</mn></mrow></mfrac>");
});

test("mathml: radicals", () => {
  has(M("sqrt(x)"), "<msqrt>");
  has(M("cbrt(x)"), "<mroot>");
  has(M("root(x, 5)", false), "<mroot>");
  has(M("2sqrt(2)"), "<msqrt><mn>2</mn></msqrt>");
});

test("mathml: powers and subscripts", () => {
  has(M("x^3"), "<msup><mrow><mi>x</mi></mrow><mrow><mn>3</mn></mrow></msup>");
  has(M("(x+1)^2"), "<mo>(</mo>");
  has(mathmlBody(X.sym("x_1")), "<msub><mi>x</mi><mn>1</mn></msub>");
  has(M("e^x"), "<msup><mrow><mi>e</mi></mrow>");
});

test("mathml: functions, abs, factorial, log base", () => {
  const s = M("sin(x)", false);
  has(s, '<mi mathvariant="normal">sin</mi>');
  has(s, "⁡");
  has(M("|x - 1|", false), "<mo>|</mo>");
  has(M("n!", false), "<mo>!</mo>");
  has(M("log_2(x)", false), "<msub><mrow><mi>log</mi></mrow><mrow><mn>2</mn></mrow></msub>");
  has(M("asin(x)", false), "arcsin");
  has(mathmlBody(X.fn("floor", X.sym("x"))), "⌊");
});

test("mathml: relations and chained inequalities", () => {
  has(M("x <= 3", false), "≤");
  has(M("x != 3", false), "≠");
  has(M("x < 3", false), "&lt;");
  eq(flat(M("1 < x < 3", false)), "1<x<3");
});

test("mathml: systems, matrices, vectors", () => {
  const sys = M("x + y = 3; x - y = 1", false);
  has(sys, "<mtable");
  has(sys, "<mo stretchy=\"true\">{</mo>");
  const m = M("[[1, 2], [3, 4]]", false);
  has(m, "<mtable");
  eq((m.match(/<mtr>/g) || []).length, 2);
  has(m, "<mo>[</mo>");
  const v = mathmlBody(X.vector(X.ONE, X.TWO, X.num(3)));
  eq((v.match(/<mtr>/g) || []).length, 3);
});

test("mathml: sets, intervals, piecewise", () => {
  has(mathmlBody(X.set(X.ONE, X.TWO)), "<mo>{</mo>");
  has(mathmlBody(X.set()), "∅");
  const iv = mathmlBody(X.interval(X.ZERO, X.OO, true, true));
  has(iv, "<mo>(</mo>");
  has(iv, "∞");
  const pw = mathmlBody(X.piecewise([X.sym("x"), X.rel(">", X.sym("x"), X.ZERO)], [X.neg(X.sym("x")), X.TRUE]));
  has(pw, "<mtable");
  has(pw, "otherwise");
  has(pw, "if");
});

test("mathml: calculus notation", () => {
  const d = M("diff(x^2, x)", false);
  has(d, "<mfrac><mrow><mi mathvariant=\"normal\">d</mi></mrow>");
  const d2 = mathmlBody(X.deriv(X.pow(X.sym("x"), X.num(3)), X.sym("x"), 2));
  has(d2, "<msup><mrow><mi mathvariant=\"normal\">d</mi></mrow><mrow><mn>2</mn></mrow></msup>");
  const i = M("integrate(x, x, 0, 1)", false);
  has(i, "<msubsup><mo>∫</mo>");
  has(M("integrate(x, x)", false), "<mo>∫</mo>");
  const l = M("limit(sin(x)/x, x, 0)", false);
  has(l, "<munder><mi mathvariant=\"normal\">lim</mi>");
  has(l, "→");
  has(mathmlBody(X.limit(X.sym("x"), X.sym("x"), X.ZERO, "+")), "<msup>");
  const s = M("sum(1/k^2, k, 1, oo)", false);
  has(s, "<munderover><mo largeop=\"true\" movablelimits=\"false\">∑</mo>");
  has(mathmlBody(X.product(X.sym("k"), X.sym("k"), X.ONE, X.sym("n"))), "∏");
});

test("mathml: constants, greek, units", () => {
  has(M("pi", false), "π");
  has(M("oo", false), "∞");
  has(M("i", false), "<mi>i</mi>");
  has(mathmlBody(X.sym("theta")), "θ");
  has(mathmlBody(X.sym("Delta")), "Δ");
  has(mathmlBody(X.mul(X.num(5), X.unit("km"))), 'class="unit"');
  has(mathmlBody(X.UNDEF), "undefined");
});

test("mathml: escapes and well-formed output over many inputs", () => {
  const srcs = ["x^2 - 5x + 6 = 0", "sqrt(x+3) = x - 3", "(x-1)/(x+2) > 0", "diff(x^2 sin(x), x)", "integrate(x e^x, x)",
    "limit(sin(x)/x, x, 0)", "sum(1/k^2, k, 1, oo)", "[[1,2],[3,4]]", "{1,2}", "|2x-1| >= 3", "x+y=10; x-y=2", "5!", "log_3(81)",
    "2^x = 32", "sin(x)^2 + cos(x)^2", "-x^2 + 3x - 1/2", "a < b", "x_1 + x_2", "f(x) = x^2"];
  for (const s of srcs) {
    for (const simp of [false, true]) {
      let t = parse(s);
      if (simp) { try { t = simplify(t); } catch (_) { continue; } }
      const ml = toMathML(t);
      ok(balanced(ml), "unbalanced markup for " + s + ": " + ml);
      ok(!/<[a-z]+[^>]*<|>[^<]*[<](?![a-z\/])/i.test(ml), "raw < in text for " + s);
    }
  }
});

test("mathml: mathmlFromText reports errors without throwing", () => {
  const good = mathmlFromText("x + 1");
  ok(good.ok && good.mathml.includes("<math"));
  const bad = mathmlFromText("(x + 1");
  ok(!bad.ok);
  ok(typeof bad.error.message === "string" && bad.error.message.length > 0);
  ok(typeof bad.error.pos === "number");
  const empty = mathmlFromText("");
  ok(!empty.ok);
});

test("mathml: highlight wraps changed subtrees", () => {
  const before = simplify(parse("2x + 4 = 10"));
  const after = simplify(parse("2x = 6"));
  const ids = changedIds(before, after);
  ok(ids.size > 0);
  ok(!ids.has(X.sym("x").id), "x is unchanged and must not be highlighted");
  const ml = mathmlBody(after, { highlight: ids });
  has(ml, '<mrow class="changed">');
  has(flat(ml.match(/<mrow class="changed">.*?<\/mrow>/)[0]), "6");
  eq(changedIds(before, before).size, 0);
});

test("serialise: tree JSON round trip is identity (hash-consed)", () => {
  const srcs = ["x^2 - 5x + 6 = 0", "[[1,2],[3,4]]", "integrate(x, x, 0, 1)", "1 < x <= 3", "{1, 2}", "sum(k, k, 1, n)"];
  for (const s of srcs) {
    const t = parse(s);
    const back = treeFromJSON(JSON.parse(JSON.stringify(treeToJSON(t))));
    ok(back === t, "round trip for " + s);
  }
  const iv = X.interval(X.ZERO, X.ONE, true, false);
  ok(treeFromJSON(treeToJSON(iv)) === iv);
  ok(treeFromJSON(treeToJSON(X.TRUE)) === X.TRUE);
  const lim = X.limit(X.recip(X.sym("x")), X.sym("x"), X.ZERO, "+");
  ok(treeFromJSON(treeToJSON(lim)) === lim);
  ok(treeFromJSON(treeToJSON(X.num(-7, 3))) === X.num(-7, 3));
});

test("serialise: result objects survive structured clone and rebuild trees", () => {
  const r = engine.solve("(x^2 - 1)/(x - 1)", { domain: "real", digits: 15 });
  const wire = serializeResult(r);
  const cloned = structuredClone(wire); // what postMessage does
  const back = deserializeResult(cloned);
  const a = back.answers[0].tree;
  ok(a.$tree === 1 && typeof a.text === "string" && typeof a.latex === "string");
  ok(a.node === r.answers[0].tree, "rebuilt node is the same hash-consed tree");
  eq(a.text, toText(r.answers[0].tree));
  ok(back.input.tree.node === r.input.tree);
  // bigints and functions are removed from the wire format
  const w2 = serializeResult({ big: 10n, f: () => 1, q: { n: 1n, d: 2n } });
  eq(w2.big, "10");
  ok(!("f" in w2));
  eq(w2.q, "1/2");
});

test("engine returns a contract-shaped result", () => {
  const r = engine.solve("sqrt(8) + 1/2", { digits: 30 });
  for (const k of ["ok", "input", "recognition", "classification", "answers", "solutionStatus", "verification", "steps", "conditions", "rejected", "attempts", "graph", "ms"])
    ok(k in r, "missing " + k);
  eq(r.solutionStatus, "exact");
  eq(r.verification.status, "passed");
  eq(toText(r.answers[0].tree), "2sqrt(2) + 1/2");
  const c = engine.solve("x/x");
  ok(c.conditions.length === 1 && toText(c.conditions[0]) === "x != 0");
});

test("checkWork flags the first wrong line", () => {
  const r = engine.checkWork(["2(x + 3) = 14", "2x + 6 = 14", "2x = 8", "x = 5"]);
  eq(r.lines.map((l) => l.status).join(","), "start,ok,ok,mistake");
  eq(r.firstMistake, 3);
  const s = engine.checkWork(["(x+1)^2", "x^2 + 2x + 1", "x^2 + 2x + 2"]);
  eq(s.lines.map((l) => l.status).join(","), "start,ok,mistake");
  eq(engine.checkWork(["x +", "x"]).lines[0].status, "syntax");
});

test("storage works without IndexedDB (memory fallback)", async () => {
  ok(!(await store.isPersistent()));
  const rec = await store.addHistory({ input: "x+1", answer: "x + 1" });
  ok(rec.id);
  await store.setPref("mode", "steps");
  eq(await store.getPref("mode", "answer"), "steps");
  const list = await store.listHistory();
  ok(list.some((h) => h.input === "x+1"));
  await store.del("history", rec.id);
  ok(!(await store.listHistory()).some((h) => h.id === rec.id));
  const dump = await store.exportAll();
  eq(dump.format, "quelvra-export");
  eq(Object.keys(dump.stores).length, 7);
});

// ---------- static checks over the shipped files ----------
const ROOT = join(dirname(fileURLToPath(import.meta.url)), "../public");
const shipped = () => {
  const out = [];
  for (const f of readdirSync(ROOT)) if (/\.(js|html|css|webmanifest|svg)$/.test(f)) out.push(join(ROOT, f));
  out.push(join(ROOT, "engine/quelvra.js"));
  return out;
};

test("static: no emojis, no eval/new Function, no remote URLs in UI files", () => {
  const emoji = /[\u{1F300}-\u{1FAFF}\u{2600}-\u{27BF}\u{1F000}-\u{1F2FF}\u{FE0F}]/u;
  for (const f of shipped()) {
    const s = readFileSync(f, "utf8");
    ok(!emoji.test(s), "emoji in " + f);
    ok(!/\beval\s*\(|new\s+Function\s*\(/.test(s), "eval in " + f);
    const urls = (s.match(/https?:\/\/[^\s"'`)<]+/g) || []).filter((u) => !/^https?:\/\/(www\.w3\.org|darknode\.ai)/.test(u));
    ok(!urls.length, "remote URL in " + f + ": " + urls.join(", "));
  }
});

test("static: licensing guard is the first script in index.html", () => {
  const html = readFileSync(join(ROOT, "index.html"), "utf8");
  const first = html.indexOf("<script");
  ok(html.slice(first).startsWith('<script>!function(){var a=["darknode.ai","www.darknode.ai","darknode-official.github.io","quelvra.onrender.com","localhost","127.0.0.1"]'));
  ok(!/firebase|botpress|gstatic|googleapis/i.test(html), "index.html must not load darknode auth scripts");
});

test("static: service worker precaches every shipped file", () => {
  const sw = readFileSync(join(ROOT, "sw.js"), "utf8");
  for (const f of readdirSync(ROOT)) {
    if (f === "sw.js" || !/\.(js|html|css|webmanifest|svg)$/.test(f)) continue;
    ok(sw.includes(`"${f}"`), "sw.js FILES is missing " + f);
  }
  for (const f of ["num.js", "expr.js", "parse.js", "print.js", "simplify.js", "quelvra.js"]) ok(sw.includes(`"engine/${f}"`), "missing engine/" + f);
});

test("mathml: changedIds marks a new node assembled from reused parts", () => {
  const before = parse("sqrt(x) = x - 2"), after = parse("x = (x - 2)^2");
  const ids = changedIds(before, after);
  ok(ids.has(after.args[1].id), "(x - 2)^2 is new");
  ok(!ids.has(after.id), "the equation itself is not wholly new");
  ok(!ids.has(X.sym("x").id));
});

test("static: Tools tab, panel and icons are wired", () => {
  const html = readFileSync(join(ROOT, "index.html"), "utf8");
  for (const id of ["tab-tools", "panel-tools", "tool-nav", "tool-host"]) ok(html.includes(`id="${id}"`), "index.html is missing #" + id);
  ok(/<button[^>]*id="tab-tools"[^>]*aria-controls="panel-tools"/.test(html), "tools tab controls its panel");
  ok(/<section id="panel-tools" role="tabpanel" aria-labelledby="tab-tools" hidden>/.test(html), "tools panel starts hidden");
  const tools = readFileSync(join(ROOT, "tools.js"), "utf8");
  const used = [...tools.matchAll(/icon\("([a-z-]+)"\)|: "([a-z-]+)"(?=[,}])/g)].map((m) => m[1] || m[2]);
  const icons = new Set([...html.matchAll(/<symbol id="i-([a-z-]+)"/g)].map((m) => m[1]));
  for (const name of ["swap", "tools", "t-graph", "t-matrix", "t-stats", "t-hash", "t-system", "keys", "book", "check", "alert", "dash", "x", "plus", "down", "copy", "enter", "chev"]) ok(icons.has(name), "missing SVG symbol i-" + name);
  for (const m of tools.matchAll(/icon\("([a-z-]+)"\)/g)) ok(icons.has(m[1]), "tools.js uses an undefined icon " + m[1]);
  void used;
  const app = readFileSync(join(ROOT, "app.js"), "utf8");
  ok(app.includes('import("./tools.js")'), "tools load lazily from app.js");
  ok(/const TABS = \["solve", "check", "tools"\]/.test(app));
});

test("static: tools modules import only local files and the engine stays untouched by them", () => {
  for (const f of ["tools.js", "tools-core.js"]) {
    const src = readFileSync(join(ROOT, f), "utf8");
    for (const m of src.matchAll(/^import .* from "([^"]+)";$/gm)) ok(m[1].startsWith("./"), `${f} imports ${m[1]}`);
    ok(!/fetch\(|XMLHttpRequest|WebSocket|localStorage\.setItem/.test(src), f + " must not use the network or raw storage");
  }
  const core = readFileSync(join(ROOT, "tools-core.js"), "utf8");
  ok(!/document\.|window\./.test(core), "tools-core.js stays DOM-free so Node can test it");
});

test("worker: batch and prove-prime requests are exposed through the tools lane", () => {
  const w = readFileSync(join(ROOT, "worker.js"), "utf8");
  ok(/"batch"/.test(w) && /"prove-prime"/.test(w), "worker handles batch and prove-prime");
  const b = readFileSync(join(ROOT, "bridge.js"), "utf8");
  ok(/new Lane\("tools"/.test(b), "tools run on their own lane so they never cancel Solve");
  for (const fn of ["tool", "toolBatch", "provePrime", "cancelTools"]) ok(new RegExp(`export const ${fn} =`).test(b), "bridge exports " + fn);
});
