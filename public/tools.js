// Quelvra Tools tab: graphing, matrices, units, calculator, statistics, number theory, formulas and
// equation systems. Plain ES module, no dependencies. Every answer comes from the engine in the
// worker (bridge.js Tools lane), so it carries the engine's own verification; this file only
// builds requests (tools-core.js) and draws. Plots and charts use doubles and say so.

import * as bridge from "./bridge.js";
import * as X from "./engine/expr.js";
import { createGraph, classifyPlot, compile, niceTicks } from "./graph.js";
import * as C from "./tools-core.js";

let ctx = null;          // { h, icon, mathEl, toast, copyText, loadProblem, store }
const built = new Map(); // tool id -> { el, onShow?, onHide? }
let current = "";

const SVGNS = "http://www.w3.org/2000/svg";
const debounce = (fn, ms) => { let t = 0; return (...a) => { clearTimeout(t); t = setTimeout(() => fn(...a), ms); }; };
const put = (el, ...kids) => el.replaceChildren(...kids.flat().filter(Boolean));
let uidSeq = 0;
const uid = (p) => `${p}-${++uidSeq}`;

// ------------------------------------------------------------------ shared pieces
function badge(v) {
  const { h, icon } = ctx;
  const map = { verified: ["check", "st-ok"], exact: ["check", "st-ok"], approx: ["alert", "st-warn"], partial: ["alert", "st-warn"], none: ["dash", "st-mut"] };
  const [ic, cls] = map[v.state] || map.none;
  return h("span", { class: "tl-badge " + cls }, icon(ic), v.text);
}
function field(label, input, hint) {
  const { h } = ctx;
  const id = input.id || (input.id = uid("tf"));
  return h("div", { class: "tl-field" }, h("label", { for: id, class: "ctl-label" }, label), input, hint ? h("span", { class: "tiny muted" }, hint) : null);
}
function textInput(attrs = {}) {
  const { h } = ctx;
  const el = h("input", { type: "text", class: "field mono", spellcheck: "false", autocomplete: "off", autocapitalize: "off", ...attrs });
  if (attrs.value != null) el.value = attrs.value;
  return el;
}
function select(options, value, attrs = {}) {
  const { h } = ctx;
  const el = h("select", { class: "field select", ...attrs }, options.map(([v, t]) => h("option", { value: v }, t)));
  if (value != null) el.value = value;
  return el;
}
function seg(name, legend, options, value, onChange) {
  const { h } = ctx;
  const fs = h("fieldset", { class: "seg" }, h("legend", { class: "ctl-label" }, legend));
  const n = uid(name);
  for (const [v, t] of options) {
    const inp = h("input", { type: "radio", name: n, value: v });
    inp.checked = v === value;
    inp.addEventListener("change", () => { if (inp.checked) onChange(v); });
    fs.append(h("label", null, inp, h("span", null, t)));
  }
  return fs;
}
function btn(label, onclick, { cls = "btn small", icon: ic, aria, title } = {}) {
  const { h, icon } = ctx;
  return h("button", { type: "button", class: cls, onclick, "aria-label": aria, title }, ic ? icon(ic) : null, label);
}
// A status line with a Cancel button while a job runs. run(promiseFactory) resolves to the value or null.
function jobStatus(out) {
  const { h, icon } = ctx;
  const text = h("span", { class: "tl-status-t" });
  const cancel = h("button", { type: "button", class: "btn small ghost", hidden: true, onclick: () => bridge.cancelTools() }, icon("x"), "Cancel");
  const el = h("div", { class: "tl-status", role: "status", "aria-live": "polite" }, text, cancel);
  let seq = 0;
  async function run(factory, busyText = "Computing") {
    const my = ++seq;
    text.className = "tl-status-t";
    text.textContent = busyText + "...";
    cancel.hidden = false;
    try {
      const out = await factory((stage) => { if (my === seq) text.textContent = String(stage || busyText).replace(/^./, (c) => c.toUpperCase()) + "..."; });
      if (my !== seq) return null;
      text.textContent = "";
      return out;
    } catch (err) {
      if (my !== seq) return null;
      text.className = "tl-status-t err-msg";
      text.textContent = err && err.code === "CANCELLED" ? "Cancelled." : (err && err.message) || "Could not compute this";
      if (out) out.replaceChildren();
      return null;
    } finally {
      if (my === seq) cancel.hidden = true;
    }
  }
  const error = (msg) => { seq++; cancel.hidden = true; text.className = "tl-status-t err-msg"; text.textContent = msg; if (out) out.replaceChildren(); };
  const clear = () => { text.className = "tl-status-t"; text.textContent = ""; };
  return { el, run, error, clear };
}
const solveJob = (input, options) => (progress) => bridge.tool(input, { mode: "answer", domain: "real", digits: 15, ...(options || {}) }, { onProgress: progress });
const batchJob = (items) => (progress) => bridge.toolBatch(items.map((it) => (typeof it === "string" ? { input: it } : it)), { mode: "answer", domain: "real", digits: 15 }, { onProgress: progress });

// One result: exact answers (MathML), decimals and the verification badge.
function resultView(r, { label = "Result", unit = "", keepCase = false } = {}) {
  const { h, mathEl } = ctx;
  const v = C.verdict(r);
  const box = h("div", { class: "tl-result" });
  const head = h("div", { class: "tl-result-head" }, h("span", { class: "ctl-label" + (keepCase ? " tl-case" : "") }, label), badge(v));
  box.append(head);
  const ex = C.exactAnswers(r);
  if (!ex.length) { box.append(h("p", { class: "muted", style: "margin:0" }, v.text)); return box; }
  const approxAns = (r.answers || []).some((a) => a && a.kind === "approx" && a.approx);
  for (const a of ex) {
    const row = h("div", { class: "tl-ans" });
    if (a.label && ex.length > 1) row.append(h("span", { class: "tl-ans-l" }, a.label));
    if (a.tree) row.append(h("span", { class: "tl-ans-m" }, mathEl(a.tree, { label: a.label || label }), unit ? h("span", { class: "ans-unit" }, unit) : null));
    else row.append(h("span", { class: "tl-ans-m mono" }, a.text || ""));
    if (a.approx && a.approx.value) row.append(h("span", { class: "tl-dec mono" }, "≈ " + a.approx.value));
    else if (a.tree && !approxAns) {
      const f = C.floatOf(a.tree);
      if (Number.isFinite(f) && !/^-?\d+$/.test(C.answerText(a))) row.append(h("span", { class: "tl-dec mono" }, "≈ " + C.fmt(f, 12)));
    }
    box.append(row);
  }
  const shown = ex.some((a) => a.approx && a.approx.value);
  const dec = shown ? [] : (r.answers || []).filter((a) => a && a.kind === "approx" && a.approx);
  for (const a of dec) box.append(h("div", { class: "tl-dec mono" }, "≈ " + a.approx.value + (unit ? " " + unit : "")));
  const first = ex[0];
  if (first && first.tree && first.tree.text) box.append(h("div", { class: "ans-tools" }, btn("Copy", () => ctx.copyText(first.tree.text + (unit ? " " + unit : ""), "answer"), { icon: "copy", aria: "Copy " + label + " as text" })));
  return box;
}
function card(title, ...kids) {
  const { h } = ctx;
  const id = uid("tlh");
  return h("section", { class: "card tl-card", "aria-labelledby": id }, h("h2", { id }, title), ...kids);
}
function download(name, href) {
  const a = ctx.h("a", { href, download: name });
  document.body.append(a); a.click(); a.remove();
}
function svgEl(tag, attrs = {}, ...kids) {
  const el = document.createElementNS(SVGNS, tag);
  for (const [k, v] of Object.entries(attrs)) if (v !== null && v !== undefined) el.setAttribute(k, String(v));
  for (const k of kids) if (k) el.append(k instanceof Node ? k : document.createTextNode(String(k)));
  return el;
}

// ------------------------------------------------------------------ 1. graphing calculator
function buildGraph() {
  const { h, icon } = ctx;
  const rowsBox = h("ol", { class: "tl-rows" });
  const status = jobStatus();
  const graphHost = h("div", { class: "tl-graph-host" });
  const traceSel = select([], "", { "aria-label": "Curve to trace" });
  const analysisList = h("ul", { class: "tl-points" });
  const analysisNote = h("p", { class: "tiny muted", style: "margin:4px 0 0" });
  const opts = { zeros: true, extrema: true, inter: true };
  let graph = null, rows = [], plotted = [], analysis = null, lastKey = "";
  let squareView = true; // the starting curves and the examples open on equal axis scales

  function addRow(text = "") {
    const input = textInput({ value: text, placeholder: "sin(x), x^2 + y^2 = 9, (cos(t), sin(t)), r = 2cos(theta)" });
    const sw = h("span", { class: "tl-swatch", "aria-hidden": "true" });
    const kind = h("span", { class: "tl-kind tiny muted" });
    const err = h("div", { class: "tl-row-err tiny", "aria-live": "polite" });
    const del = btn("", () => { if (rows.length > 1) { rows = rows.filter((r) => r !== row); li.remove(); } else input.value = ""; renumber(); replot(); }, { cls: "btn ghost icon-only", icon: "x" });
    const li = h("li", { class: "tl-row" }, sw, input, del, h("div", { class: "tl-row-meta" }, kind, err));
    const row = { li, input, sw, kind, err, del, node: null, cls: null };
    input.addEventListener("input", () => replotSoon());
    input.addEventListener("keydown", (e) => { if (e.key === "Enter") { e.preventDefault(); const r = addRow(); li.after(r.li); rows.splice(rows.indexOf(row) + 1, 0, r); renumber(); r.input.focus(); } });
    rows.push(row);
    return row;
  }
  function renumber() {
    rows.forEach((r, i) => { r.input.setAttribute("aria-label", `Curve ${i + 1}`); r.del.setAttribute("aria-label", `Remove curve ${i + 1}`); });
  }

  const KIND_TEXT = { function: "y = f(x)", "function-other": "function", parametric: "parametric", polar: "polar", implicit: "implicit", inequality: "region", points: "points" };
  async function replot() {
    const seqRows = rows.slice();
    await Promise.all(seqRows.map(async (r) => {
      const text = r.input.value.trim();
      r.node = null; r.cls = null;
      if (!text) { r.kind.textContent = ""; r.err.textContent = ""; return; }
      try {
        const p = await bridge.preview(text);
        const node = p.tree && p.tree.node;
        if (!node) throw { message: "This cannot be plotted" };
        const cls = classifyPlot(node);
        if (cls.type === "none") throw { message: "Cannot plot this: " + (cls.reason || "not a curve") };
        if (cls.type === "multi") throw { message: "Enter one curve per row" };
        r.node = node; r.cls = cls;
        r.kind.textContent = KIND_TEXT[C.rowKind(cls)] || cls.type;
        r.err.textContent = "";
      } catch (e) {
        if (e && e.code === "CANCELLED") return;
        r.kind.textContent = "";
        r.err.textContent = (e && e.message) || "Cannot read this";
      }
    }));
    plotted = rows.filter((r) => r.node);
    rows.forEach((r) => { r.sw.style.background = ""; r.sw.classList.add("off"); });
    plotted.forEach((r, k) => { r.sw.classList.remove("off"); r.sw.style.background = `var(--plot-${(k % 4) + 1})`; });
    if (!graph) return;
    graph.set({ exprs: plotted.map((r) => r.node), marks: [] });
    // shapes (circles, parametric and polar curves) need equal axis scales to look right
    if (squareView || plotted.some((r) => r.cls.type !== "function" && r.cls.type !== "points")) {
      squareView = false;
      const c = graph.canvas, aspect = c && c.clientWidth ? c.clientHeight / c.clientWidth : 0.6;
      graph.setView({ xmin: -8, xmax: 8, ymin: -8 * aspect, ymax: 8 * aspect });
    }
    // trace choices: the y = f(x) rows, in plotting order
    const fnRows = plotted.filter((r) => r.cls.type === "function");
    traceSel.replaceChildren(...fnRows.map((r, i) => h("option", { value: String(i) }, r.input.value.trim())));
    traceSel.disabled = !fnRows.length;
    graph.setTrace(0);
    analyse();
  }
  const replotSoon = debounce(replot, 320);

  // zeros, extrema and intersections from the engine
  async function analyse() {
    const fns = plotted.filter((r) => r.cls.type === "function" && r.cls.var === "x" && !r.cls.params.length)
      .map((r) => ({ row: r, text: C.substituteText(r.cls.expr, "x", "x") || r.input.value.trim() }));
    const skipped = plotted.filter((r) => r.cls.type === "function" && r.cls.params.length).length;
    analysisNote.textContent = skipped ? "Curves with sliders are not analysed; set the parameters to numbers to analyse them." : "";
    const reqs = C.analysisRequests(fns).filter((q) => (q.kind === "zero" && opts.zeros) || (q.kind === "extremum" && opts.extrema) || (q.kind === "intersection" && opts.inter));
    const key = JSON.stringify(reqs.map((q) => [q.key, q.input]));
    if (key === lastKey && analysis) { analysis.fns = fns; showPoints(); return; }
    lastKey = key;
    analysis = null;
    if (!reqs.length) { analysisList.replaceChildren(); graph.set({ exprs: plotted.map((r) => r.node), marks: [] }); return; }
    const out = await status.run(batchJob(reqs), "Finding zeros, extrema and intersections");
    if (!out || key !== lastKey) return;
    analysis = { reqs, fns, out };
    showPoints();
  }
  let shownView = "";
  function showPoints(force = true) {
    if (!analysis || !graph) return;
    const v = graph.view;
    const vk = [v.xmin, v.xmax, v.ymin, v.ymax].join(",");
    if (!force && vk === shownView) return;
    shownView = vk;
    const all = [];
    analysis.reqs.forEach((q, i) => {
      const item = analysis.out[i];
      if (!item || !item.ok) return;
      const fr = analysis.fns[q.rows[0]].row;
      const f = compile(fr.cls.expr, ["x"]);
      for (const p of C.pointsFromResult(q, item.result, f, v.xmin, v.xmax)) all.push({ ...p, y: p.kind === "zero" ? 0 : p.y, q });
    });
    // one marker per place (an intersection that is also a zero is listed twice but drawn once)
    const marks = [];
    for (const p of all) if (!marks.some((m) => Math.abs(m.x - p.x) < 1e-9 && Math.abs(m.y - p.y) < 1e-9)) marks.push({ x: p.x, y: p.y, label: p.label, kind: p.kind === "extremum" ? "extremum" : "point", approx: p.status !== "verified" });
    graph.set({ exprs: plotted.map((r) => r.node), marks });
    graph.setView(v);
    const num = (i) => rows.indexOf(analysis.fns[i].row) + 1;
    const name = (q) => (q.kind === "intersection" ? `Curves ${num(q.rows[0])} and ${num(q.rows[1])} meet` : q.kind === "zero" ? `Zero of curve ${num(q.rows[0])}` : `Extremum of curve ${num(q.rows[0])}`);
    analysisList.replaceChildren(...all.slice(0, 60).map((p) => h("li", null,
      h("span", { class: "tl-pt-k" }, p.label === "max" ? `Local maximum of curve ${num(p.q.rows[0])}` : p.label === "min" ? `Local minimum of curve ${num(p.q.rows[0])}` : name(p.q)),
      h("span", { class: "mono" }, p.kind === "extremum" || p.text.startsWith("≈") ? p.text.replace(/^≈ /, "x ≈ ") : "x = " + p.text),
      p.kind !== "extremum" ? h("span", { class: "mono muted" }, `(${C.fmt(p.x)}, ${C.fmt(p.y)})`) : null,
      badge(p.status === "verified" ? { state: "verified", text: "Exact, verified" } : { state: "approx", text: "Approximate" }))));
    if (!all.length) analysisList.replaceChildren(h("li", { class: "muted" }, "No zeros, extrema or intersections in view."));
  }

  // table of values
  const tStart = textInput({ value: "-2", inputmode: "decimal" }), tStep = textInput({ value: "1", inputmode: "decimal" }), tCount = textInput({ value: "5", inputmode: "numeric" });
  const tFn = select([], "", {});
  const tOut = h("div", { class: "tbl-wrap" });
  const tStatus = jobStatus(tOut);
  async function makeTable() {
    const fnRows = plotted.filter((r) => r.cls.type === "function");
    const r = fnRows[Number(tFn.value) || 0];
    if (!r) { tStatus.error("Plot a y = f(x) curve first"); return; }
    const xs = C.tableXs(tStart.value, tStep.value, tCount.value);
    if (!xs) { tStatus.error("Start and step must be numbers"); return; }
    const items = [...xs.map((x) => ({ input: x })), ...xs.map((x) => ({ input: C.substituteText(r.cls.expr, r.cls.var, x) || "undefined" }))];
    const out = await tStatus.run(batchJob(items), "Evaluating");
    if (!out) return;
    const n = xs.length;
    const cell = (it) => {
      if (!it || !it.ok) return h("td", { class: "muted" }, "undefined");
      const a = C.exactAnswers(it.result)[0];
      return h("td", null, a ? h("span", { class: "mono" }, C.answerText(a)) : h("span", { class: "muted" }, "undefined"), a && a.approx ? h("span", { class: "tl-dec mono" }, " ≈ " + a.approx.value) : (C.decimalOf(it.result) ? h("span", { class: "tl-dec mono" }, " ≈ " + C.decimalOf(it.result)) : null));
    };
    tOut.replaceChildren(h("table", { class: "att" },
      h("caption", { class: "sr-only" }, "Table of values for " + r.input.value.trim()),
      h("thead", null, h("tr", null, h("th", { scope: "col" }, r.cls.var), h("th", { scope: "col" }, r.input.value.trim()))),
      h("tbody", null, xs.map((_, i) => h("tr", null, cell(out[i]), cell(out[n + i]))))));
  }

  const checks = h("div", { class: "tl-inline" }, ...[["zeros", "Zeros"], ["extrema", "Extrema"], ["inter", "Intersections"]].map(([k, t]) => {
    const c = h("input", { type: "checkbox" });
    c.checked = opts[k];
    c.addEventListener("change", () => { opts[k] = c.checked; lastKey = ""; analyse(); });
    return h("label", { class: "tl-check" }, c, t);
  }));

  const el = h("div", { class: "tl-tool" },
    card("Curves",
      h("p", { class: "tiny muted", style: "margin:0 0 8px" }, "One curve per row: y = f(x), an implicit equation in x and y, a parametric pair (x(t), y(t)), a polar curve r = f(theta), or an inequality. Letters other than x, y, t, theta and r become sliders."),
      rowsBox,
      h("div", { class: "cw-actions" },
        btn("Add curve", () => { const r = addRow(); rowsBox.append(r.li); renumber(); r.input.focus(); }, { icon: "plus" }),
        btn("Load examples", () => { squareView = true; rows = []; rowsBox.replaceChildren(); for (const ex of ["x^2 - 2", "x", "(cos(3t), sin(2t))", "r = 1 + cos(theta)", "x^2 + y^2 = 9"]) rowsBox.append(addRow(ex).li); renumber(); replot(); }, { cls: "btn small ghost" }))),
    h("section", { class: "card graph-card tl-card", "aria-label": "Graph" },
      h("div", { class: "tl-graph-bar" },
        field("Trace", traceSel),
        h("div", { class: "tl-inline" },
          btn("PNG", () => { if (graph) download("quelvra-graph.png", graph.toPNG()); }, { icon: "down", aria: "Export the graph as PNG" }),
          btn("SVG", () => { if (!graph) return; const url = URL.createObjectURL(new Blob([graph.toSVG()], { type: "image/svg+xml" })); download("quelvra-graph.svg", url); setTimeout(() => URL.revokeObjectURL(url), 1000); }, { icon: "down", aria: "Export the graph as SVG" }))),
      graphHost),
    card("Zeros, extrema and intersections", checks, status.el, analysisList, analysisNote,
      h("p", { class: "tiny muted", style: "margin:6px 0 0" }, "Found by the engine for the y = f(x) curves in view. Exact values are verified by substitution; approximate ones are numeric roots with a checked residual.")),
    card("Table of values",
      h("div", { class: "tl-form" }, field("Curve", tFn), field("Start", tStart), field("Step", tStep), field("Rows", tCount), h("div", { class: "tl-field tl-go" }, btn("Make table", makeTable, { cls: "btn primary" }))),
      tStatus.el, tOut));
  traceSel.addEventListener("change", () => graph && graph.setTrace(Number(traceSel.value) || 0));

  for (const ex of ["x^2 - 2", "x"]) rowsBox.append(addRow(ex).li);
  renumber();
  const syncTableFns = () => { const fnRows = plotted.filter((r) => r.cls.type === "function"); tFn.replaceChildren(...fnRows.map((r, i) => h("option", { value: String(i) }, r.input.value.trim()))); };
  const onViewChange = debounce(() => showPoints(false), 160);
  return {
    el,
    onShow() {
      if (!graph) {
        graph = createGraph(graphHost, { trace: true, onView: () => onViewChange() });
        replot().then(syncTableFns);
      } else graph.redraw();
    },
    afterPlot: syncTableFns,
    get graph() { return graph; },
    replot: () => replot().then(syncTableFns),
    redraw: () => graph && graph.redraw(),
  };
}

// ------------------------------------------------------------------ 2. matrix calculator
function matrixEditor(name, grid, onChange) {
  const { h } = ctx;
  const table = h("div", { class: "tl-grid", role: "group", "aria-label": `Matrix ${name} entries` });
  const dims = h("span", { class: "mono tiny muted", "aria-live": "polite" });
  const ed = { grid, name };
  function draw(focus) {
    const [r, c] = [ed.grid.length, ed.grid[0].length];
    table.style.gridTemplateColumns = `repeat(${c}, minmax(3.2em, 1fr))`;
    table.replaceChildren(...ed.grid.flatMap((row, i) => row.map((v, j) => {
      const inp = h("input", { type: "text", class: "field mono tl-cell", inputmode: "decimal", spellcheck: "false", autocomplete: "off", "aria-label": `${name} row ${i + 1} column ${j + 1}`, dataset: { r: i, c: j } });
      inp.value = v;
      inp.addEventListener("input", () => { ed.grid[i][j] = inp.value; inp.classList.toggle("bad", !!C.cellError(inp.value)); onChange(); });
      inp.addEventListener("paste", (e) => {
        const text = (e.clipboardData || window.clipboardData)?.getData("text") || "";
        const g = /[\t\n,\s]/.test(text.trim()) ? C.parseGridText(text) : null;
        if (!g) return;
        e.preventDefault();
        ed.grid = C.resizeGrid(g, g.length, g[0].length);
        draw(); onChange();
      });
      inp.addEventListener("keydown", (e) => {
        const move = { ArrowUp: [-1, 0], ArrowDown: [1, 0], Enter: [1, 0] }[e.key];
        if (!move) return;
        const t = table.querySelector(`[data-r="${i + move[0]}"][data-c="${j + move[1]}"]`);
        if (t) { e.preventDefault(); t.focus(); t.select(); }
      });
      return inp;
    })));
    dims.textContent = `${r} x ${c}`;
    if (focus) table.querySelector("input")?.focus();
  }
  const resize = (dr, dc) => { ed.grid = C.resizeGrid(ed.grid, ed.grid.length + dr, ed.grid[0].length + dc); draw(); onChange(); };
  const id = uid("mx");
  ed.el = h("div", { class: "tl-mx", role: "group", "aria-labelledby": id },
    h("div", { class: "tl-mx-head" }, h("span", { id, class: "tl-mx-name" }, name), dims,
      h("span", { class: "tl-inline tl-mx-size" },
        btn("Row", () => resize(-1, 0), { cls: "btn small ghost", icon: "dash", aria: `Remove a row from ${name}` }),
        btn("Row", () => resize(1, 0), { cls: "btn small ghost", icon: "plus", aria: `Add a row to ${name}` }),
        btn("Col", () => resize(0, -1), { cls: "btn small ghost", icon: "dash", aria: `Remove a column from ${name}` }),
        btn("Col", () => resize(0, 1), { cls: "btn small ghost", icon: "plus", aria: `Add a column to ${name}` }))),
    table);
  ed.set = (g) => { ed.grid = C.resizeGrid(g, g.length, g[0].length); draw(); onChange(); };
  draw();
  return ed;
}
function buildMatrix() {
  const { h } = ctx;
  const out = h("div", { class: "tl-out" });
  const status = jobStatus(out);
  const errs = h("p", { class: "err-msg tiny", "aria-live": "polite", style: "margin:0" });
  const validate = () => { const e = [...C.gridErrors(A.grid).map((x) => ({ ...x, m: "A" })), ...C.gridErrors(B.grid).map((x) => ({ ...x, m: "B" }))]; errs.textContent = e.length ? `${e[0].m} row ${e[0].row + 1} column ${e[0].col + 1}: ${e[0].message}` : ""; return !e.length; };
  const A = matrixEditor("A", [["2", "1"], ["1", "3"]], validate);
  const B = matrixEditor("B", [["1", "0"], ["4", "1"]], validate);
  const power = textInput({ value: "2", inputmode: "numeric", class: "field mono tl-pow" });
  async function run(op, title) {
    if (!validate()) return;
    const req = C.matrixRequest(op, A.grid, B.grid, power.value);
    if (req.error) { status.error(req.error); return; }
    const r = await status.run(solveJob(req.input, req.options), title);
    if (!r) return;
    const box = h("div", { class: "tl-result" });
    if (op === "solve") {
      const v = C.verdict(r);
      box.append(h("div", { class: "tl-result-head" }, h("span", { class: "ctl-label" }, title), badge(v)));
      const sols = (r.answers || []).filter((a) => a && (a.kind === "solution" || a.kind === "family"));
      if (!sols.length) box.append(h("p", { class: "muted", style: "margin:0" }, v.text));
      for (const s of sols) {
        if (s.kind === "family") box.append(h("p", { class: "tiny muted", style: "margin:0" }, s.label || "Infinitely many solutions"));
        box.append(h("div", { class: "tl-ans tl-sol" }, (s.values || []).map(([k, val]) => h("span", { class: "tl-ans-m" }, ctx.mathEl(val.node ? X.eq(X.sym(k), val.node) : `${k} = ${val.text}`, { label: k })))));
      }
    } else {
      box.append(resultView(r, { label: title }));
      const a = C.exactAnswers(r)[0];
      const g = a && a.tree && /^\s*\[\s*\[/.test(a.tree.text || "") ? C.parseGridText(a.tree.text) : null;
      if (g) box.append(h("div", { class: "ans-tools" }, btn("Use as A", () => A.set(g), { cls: "btn small ghost" }), btn("Use as B", () => B.set(g), { cls: "btn small ghost" })));
    }
    put(out, box);
  }
  const ops = h("div", { class: "tl-ops", role: "group", "aria-label": "Matrix operations" },
    ...C.MATRIX_OPS.filter(([op]) => op !== "pow").map(([op, title, kind]) => btn(kind === "Ab" ? "Solve Ax = b" : kind === "AB" ? { mul: "A x B", add: "A + B", sub: "A - B" }[op] : title, () => run(op, title), { cls: "btn small", aria: title + (kind === "Ab" ? ", with b the first column of B" : "") })),
    h("span", { class: "tl-inline tl-powgrp" }, btn("A^n", () => run("pow", "A to the power " + power.value.trim()), { cls: "btn small", aria: "A to the power n" }), h("label", { class: "sr-only", for: power.id || (power.id = uid("pw")) }, "Power n"), power));
  const el = h("div", { class: "tl-tool" },
    card("Matrices",
      h("p", { class: "tiny muted", style: "margin:0 0 8px" }, "Entries can be integers, fractions, decimals, roots or letters. Empty cells are 0. Paste rows from a spreadsheet into any cell. For Ax = b, b is the first column of B."),
      h("div", { class: "tl-mx-pair" }, A.el, B.el), errs, ops, status.el),
    card("Result", out));
  return { el };
}

// ------------------------------------------------------------------ 3. unit converter
function buildUnits() {
  const { h, icon } = ctx;
  const out = h("div", { class: "tl-out", "aria-live": "polite" });
  const status = jobStatus(out);
  const cat = select(C.UNIT_CATEGORIES.map((c) => [c.id, c.label]), "length");
  const value = textInput({ value: "1", inputmode: "decimal" });
  const from = select([], ""), to = select([], "");
  const fillUnits = (keep) => {
    const c = C.unitCategory(cat.value);
    const opts = c.units.map((u) => h("option", { value: u.id }, `${u.label} (${u.id})`));
    from.replaceChildren(...opts.map((o) => o.cloneNode(true)));
    to.replaceChildren(...opts);
    if (!keep) { from.value = c.units[c.id === "temperature" ? 0 : Math.min(2, c.units.length - 1)].id; to.value = c.units[c.id === "temperature" ? 1 : c.units.length - 1].id; }
  };
  async function convert() {
    const req = C.conversionRequest(cat.value, from.value, to.value, value.value);
    if (req.error) { status.error(req.error); put(out, ); return; }
    const r = await status.run(solveJob(req.input), "Converting");
    if (!r) return;
    const u = C.findUnit(cat.value, to.value);
    put(out, resultView(r, { label: `${req.value} ${from.value} in ${to.value}`, unit: u.id, keepCase: true }),
      h("p", { class: "tiny muted", style: "margin:6px 0 0" }, req.via === "units" ? "Converted by the engine's unit system with exact SI definitions." : `Converted with exact factors (1 ${from.value} = ${C.findUnit(cat.value, from.value).factor} ${C.unitCategory(cat.value).base}), evaluated exactly by the engine.`));
  }
  const soon = debounce(convert, 250);
  cat.addEventListener("change", () => { fillUnits(false); soon(); });
  for (const e of [from, to]) e.addEventListener("change", soon);
  value.addEventListener("input", soon);
  value.addEventListener("keydown", (e) => { if (e.key === "Enter") { e.preventDefault(); convert(); } });
  const swap = h("button", { type: "button", class: "btn tl-swap", "aria-label": "Swap the units", title: "Swap the units", onclick: () => { const a = from.value; from.value = to.value; to.value = a; convert(); } }, icon("swap"));
  fillUnits(false);
  const el = h("div", { class: "tl-tool" },
    card("Unit converter",
      h("div", { class: "tl-form" }, field("Category", cat), field("Value", value)),
      h("div", { class: "tl-form tl-units" }, field("From", from), swap, field("To", to)),
      status.el),
    card("Result", out));
  return { el, onShow: () => { if (!out.childNodes.length) convert(); } };
}

// ------------------------------------------------------------------ 4. scientific calculator
function buildCalc() {
  const { h, store } = ctx;
  const st = { angle: "rad", ans: "", memory: "", history: [] };
  const inp = textInput({ placeholder: "2 sin(30) + sqrt(2)", class: "field mono tl-calc-in" });
  const out = h("div", { class: "tl-calc-out", "aria-live": "polite" });
  const memEl = h("span", { class: "tiny muted mono tl-mem" });
  const status = jobStatus(out);
  const histList = h("ol", { class: "tl-hist" });
  const showMem = () => { memEl.textContent = st.memory ? "M = " + st.memory : "Memory empty"; };
  const insert = (tpl) => {
    const s = inp.selectionStart ?? inp.value.length, e = inp.selectionEnd ?? inp.value.length;
    const r = C.insertTemplate(inp.value, s, e, tpl);
    inp.value = r.value;
    inp.focus();
    inp.setSelectionRange(r.caret, r.caret);
  };
  async function evaluate(src = inp.value) {
    const req = C.calcInput(src, st);
    if (req.error) { status.error(req.error); return null; }
    const r = await status.run(solveJob(req.input), "Evaluating");
    if (!r) return null;
    const a = C.exactAnswers(r)[0];
    put(out, resultView(r, { label: src.trim() + (st.angle === "deg" && /\b(a?sin|a?cos|a?tan)\b/.test(src) ? " (degrees)" : ""), keepCase: true }));
    if (a && a.tree && a.tree.text) {
      st.ans = a.tree.text;
      st.history.unshift({ q: src.trim(), a: a.tree.text, d: C.decimalOf(r), angle: st.angle });
      st.history = st.history.slice(0, 50);
      store.setPref("calcHistory", st.history);
      renderHist();
    }
    return a && a.tree ? a.tree.text : null;
  }
  async function memOp(op) {
    if (op === "MC") { st.memory = ""; showMem(); return; }
    if (op === "MR") { if (!st.memory) { status.error("Memory is empty"); return; } insert("MR"); return; }
    const val = inp.value.trim() ? await evaluate() : st.ans;
    if (!val) { status.error("Evaluate something first"); return; }
    if (op === "MS" || !st.memory) { st.memory = op === "M-" ? `-(${val})` : val; }
    else {
      const r = await status.run(solveJob(`(${st.memory}) ${op === "M+" ? "+" : "-"} (${val})`), "Updating memory");
      const a = r && C.exactAnswers(r)[0];
      if (!a || !a.tree) return;
      st.memory = a.tree.text;
    }
    if (op === "M-" && st.memory.startsWith("-(")) {
      const r = await status.run(solveJob(st.memory), "Updating memory");
      const a = r && C.exactAnswers(r)[0];
      if (a && a.tree) st.memory = a.tree.text;
    }
    showMem();
    store.setPref("calcMemory", st.memory);
  }
  function renderHist() {
    histList.replaceChildren(...st.history.map((e) => h("li", null, h("button", { type: "button", class: "hist-load", onclick: () => { inp.value = e.q; inp.focus(); } },
      h("span", { class: "hist-q" }, e.q + (e.angle === "deg" ? "  [deg]" : "")), h("span", { class: "hist-a" }, "= " + e.a + (e.d ? "  ≈ " + e.d : ""))))));
    if (!st.history.length) histList.replaceChildren(h("li", { class: "muted tiny" }, "No calculations yet."));
  }
  inp.addEventListener("keydown", (e) => { if (e.key === "Enter") { e.preventDefault(); evaluate(); } else if (e.key === "Escape" && inp.value) { e.preventDefault(); e.stopPropagation(); inp.value = ""; } });
  const keys = h("div", { class: "tl-keys", role: "group", "aria-label": "Calculator keys" },
    ...C.CALC_KEYS.map(([label, ins, aria, kind]) => h("button", { type: "button", class: "tl-key" + (kind ? " " + kind : ""), "aria-label": aria || label, onclick: () => (ins === "=" ? evaluate() : insert(ins)) }, label)));
  const edit = h("div", { class: "tl-inline" },
    btn("Clear", () => { inp.value = ""; put(out, ); status.clear(); inp.focus(); }, { cls: "btn small", aria: "Clear the expression" }),
    btn("Del", () => { const s = inp.selectionStart ?? inp.value.length, e = inp.selectionEnd ?? s; if (s !== e) inp.value = inp.value.slice(0, s) + inp.value.slice(e); else if (s > 0) { inp.value = inp.value.slice(0, s - 1) + inp.value.slice(s); inp.setSelectionRange(s - 1, s - 1); } inp.focus(); }, { cls: "btn small", aria: "Delete one character" }));
  const mem = h("div", { class: "tl-inline", role: "group", "aria-label": "Memory" },
    ...[["MC", "Clear memory"], ["MR", "Recall memory"], ["M+", "Add to memory"], ["M-", "Subtract from memory"], ["MS", "Store in memory"]].map(([k, a]) => btn(k, () => memOp(k), { cls: "btn small ghost", aria: a })), memEl);
  const angle = seg("angle", "Angles", [["rad", "Radians"], ["deg", "Degrees"]], "rad", (v) => { st.angle = v; store.setPref("calcAngle", v); });
  const el = h("div", { class: "tl-tool tl-calc" },
    card("Scientific calculator",
      field("Expression", inp, "Enter evaluates. Ans is the last answer, MR the memory. Results are exact where possible, with a decimal."),
      h("div", { class: "tl-calc-bar" }, angle, edit),
      keys, mem, status.el, out),
    card("History", histList, h("div", { class: "ans-tools", style: "margin-top:8px" }, btn("Clear history", () => { st.history = []; store.setPref("calcHistory", []); renderHist(); }, { cls: "btn small ghost danger" }))));
  (async () => {
    try {
      st.history = (await store.getPref("calcHistory", [])) || [];
      st.memory = (await store.getPref("calcMemory", "")) || "";
      const a = await store.getPref("calcAngle", "rad");
      if (a === "deg") { st.angle = "deg"; angle.querySelector('input[value="deg"]').checked = true; }
    } catch (_) { /* storage unavailable: start empty */ }
    renderHist(); showMem();
  })();
  renderHist(); showMem();
  return { el, onShow: (focus) => { if (focus) inp.focus({ preventScroll: true }); } };
}

// ------------------------------------------------------------------ 5. statistics
const LABELS = { mean: "Mean", median: "Median", sum: "Sum", mode: "Mode", stdev: "Standard deviation", range: "Range", quartiles: "Quartiles", iqr: "Interquartile range" };
function chartFrame(w, hgt, label) {
  return svgEl("svg", { viewBox: `0 0 ${w} ${hgt}`, class: "tl-chart", role: "img", "aria-label": label, preserveAspectRatio: "xMidYMid meet" });
}
function xAxis(svg, x0, x1, px, y, w) {
  const t = niceTicks(x0, x1, Math.max(3, Math.round(w / 70)));
  svg.append(svgEl("line", { x1: px(x0), x2: px(x1), y1: y, y2: y, class: "tl-axis" }));
  for (const v of t.ticks) svg.append(svgEl("line", { x1: px(v), x2: px(v), y1: y, y2: y + 4, class: "tl-axis" }), svgEl("text", { x: px(v), y: y + 16, class: "tl-tick", "text-anchor": "middle" }, C.fmt(v, 4)));
}
function histogramSVG(nums) {
  const bins = C.histogramBins(nums);
  const W = 520, H = 220, L = 34, B = 26, T = 8;
  const svg = chartFrame(W, H, "Histogram: " + bins.map((b) => `${C.fmt(b.lo, 4)} to ${C.fmt(b.hi, 4)}: ${b.count}`).join("; "));
  if (!bins.length) return svg;
  const max = Math.max(...bins.map((b) => b.count));
  const lo = bins[0].lo, hi = bins[bins.length - 1].hi;
  const px = (x) => L + ((x - lo) / (hi - lo)) * (W - L - 10), py = (c) => H - B - (c / max) * (H - B - T);
  for (const b of bins) {
    const x = px(b.lo), w = Math.max(1, px(b.hi) - px(b.lo) - 1);
    svg.append(svgEl("rect", { x, y: py(b.count), width: w, height: H - B - py(b.count), class: "tl-bar" }, svgEl("title", {}, `${C.fmt(b.lo, 4)} to ${C.fmt(b.hi, 4)}: ${b.count}`)));
  }
  const yt = niceTicks(0, max, 4);
  for (const v of yt.ticks) if (Number.isInteger(v)) svg.append(svgEl("text", { x: L - 6, y: py(v) + 4, class: "tl-tick", "text-anchor": "end" }, v));
  xAxis(svg, lo, hi, px, H - B, W);
  return svg;
}
function boxSVG(nums, q) {
  const bp = C.boxPlot(nums, q[0], q[1], q[2]);
  const W = 520, H = 96, L = 14, R = 14;
  const lo = Math.min(bp.min, bp.whiskerLo), hi = Math.max(bp.max, bp.whiskerHi);
  const span = hi - lo || 1;
  const px = (x) => L + ((x - lo) / span) * (W - L - R);
  const svg = chartFrame(W, H, `Box plot: whiskers ${C.fmt(bp.whiskerLo)} and ${C.fmt(bp.whiskerHi)}, quartiles ${C.fmt(bp.q1)}, ${C.fmt(bp.q2)}, ${C.fmt(bp.q3)}` + (bp.outliers.length ? `, outliers ${bp.outliers.map((v) => C.fmt(v)).join(", ")}` : ""));
  const y = 34, hh = 30;
  svg.append(
    svgEl("line", { x1: px(bp.whiskerLo), x2: px(bp.q1), y1: y, y2: y, class: "tl-axis" }),
    svgEl("line", { x1: px(bp.q3), x2: px(bp.whiskerHi), y1: y, y2: y, class: "tl-axis" }),
    svgEl("line", { x1: px(bp.whiskerLo), x2: px(bp.whiskerLo), y1: y - 9, y2: y + 9, class: "tl-axis" }),
    svgEl("line", { x1: px(bp.whiskerHi), x2: px(bp.whiskerHi), y1: y - 9, y2: y + 9, class: "tl-axis" }),
    svgEl("rect", { x: px(bp.q1), y: y - hh / 2, width: Math.max(1, px(bp.q3) - px(bp.q1)), height: hh, class: "tl-box" }),
    svgEl("line", { x1: px(bp.q2), x2: px(bp.q2), y1: y - hh / 2, y2: y + hh / 2, class: "tl-median" }));
  for (const o of bp.outliers) svg.append(svgEl("circle", { cx: px(o), cy: y, r: 3.5, class: "tl-dot hollow" }));
  xAxis(svg, lo, hi, px, 70, W);
  return svg;
}
function scatterSVG(xs, ys, slope, intercept) {
  const W = 520, H = 280, L = 40, B = 26, T = 10, R = 12;
  const pad = (a, b) => { const s = b - a || 1; return [a - s * 0.08, b + s * 0.08]; };
  const [x0, x1] = pad(Math.min(...xs), Math.max(...xs)), [y0, y1] = pad(Math.min(...ys), Math.max(...ys));
  const px = (x) => L + ((x - x0) / (x1 - x0)) * (W - L - R), py = (y) => H - B - ((y - y0) / (y1 - y0)) * (H - B - T);
  const svg = chartFrame(W, H, `Scatter plot of ${xs.length} points` + (Number.isFinite(slope) ? ` with the line y = ${C.fmt(slope)} x ${intercept < 0 ? "-" : "+"} ${C.fmt(Math.abs(intercept))}` : ""));
  const yt = niceTicks(y0, y1, 5);
  for (const v of yt.ticks) svg.append(svgEl("line", { x1: L, x2: W - R, y1: py(v), y2: py(v), class: "tl-gridline" }), svgEl("text", { x: L - 6, y: py(v) + 4, class: "tl-tick", "text-anchor": "end" }, C.fmt(v, 4)));
  if (Number.isFinite(slope) && Number.isFinite(intercept)) svg.append(svgEl("line", { x1: px(x0), y1: py(slope * x0 + intercept), x2: px(x1), y2: py(slope * x1 + intercept), class: "tl-fit" }));
  xs.forEach((x, i) => svg.append(svgEl("circle", { cx: px(x), cy: py(ys[i]), r: 4, class: "tl-dot" }, svgEl("title", {}, `(${C.fmt(x)}, ${C.fmt(ys[i])})`))));
  xAxis(svg, x0, x1, px, H - B, W);
  svg.style.overflow = "hidden";
  return svg;
}
function buildStats() {
  const { h } = ctx;
  let mode = "one";
  const data = h("textarea", { class: "field mono tl-data", rows: "5", spellcheck: "false" });
  data.value = "12, 15, 11, 18, 15, 20, 14, 15, 22, 13, 16, 19, 30";
  const pairs = h("textarea", { class: "field mono tl-data", rows: "6", spellcheck: "false" });
  pairs.value = "1, 2.1\n2, 3.9\n3, 6.2\n4, 7.8\n5, 10.1\n6, 12.2";
  const out = h("div", { class: "tl-out" });
  const status = jobStatus(out);
  const dataField = field("Data", data, "Numbers separated by commas, spaces or new lines. Paste a spreadsheet column.");
  const pairField = field("x, y pairs", pairs, "One pair per line: x, y");
  pairField.hidden = true;
  async function compute() {
    if (mode === "one") {
      const d = C.parseData(data.value);
      if (d.bad.length) { status.error(`Not a number: ${d.bad.slice(0, 3).join(", ")}`); return; }
      if (!d.values.length) { status.error("Enter some numbers"); return; }
      const reqs = C.statsRequests(d.values);
      const res = await status.run(batchJob(reqs.map(([, input]) => input)), `Computing ${reqs.length} statistics`);
      if (!res) return;
      const byKey = Object.fromEntries(reqs.map(([k], i) => [k, res[i]]));
      const rows = [];
      const sorted = d.values.map((v, i) => [v, d.floats[i]]).sort((a, b) => a[1] - b[1]);
      rows.push(h("tr", null, h("th", { scope: "row" }, "Count n"), h("td", { class: "mono" }, String(d.values.length)), h("td", null, badge({ state: "exact", text: "Counted" }))));
      rows.push(h("tr", null, h("th", { scope: "row" }, "Minimum, maximum"), h("td", { class: "mono" }, `${sorted[0][0]}, ${sorted[sorted.length - 1][0]}`), h("td", null, badge({ state: "exact", text: "From data" }))));
      for (const [k] of reqs) {
        const it = byKey[k];
        if (!it || !it.ok) { rows.push(h("tr", null, h("th", { scope: "row" }, LABELS[k]), h("td", { colspan: "2", class: "muted" }, (it && it.error && it.error.message) || "Not available"))); continue; }
        const ans = C.exactAnswers(it.result);
        const v = C.verdict(it.result);
        if (!ans.length) { rows.push(h("tr", null, h("th", { scope: "row" }, LABELS[k]), h("td", { class: "muted" }, v.text), h("td", null, badge(v)))); continue; }
        ans.forEach((a, i) => {
          const name = ans.length < 2 ? LABELS[k] : k === "stdev" ? (/sample/i.test(a.label || "") ? "Sample SD (n - 1)" : "Population SD (n)") : k === "quartiles" ? String(a.label || `Q${i + 1}`).replace(/\s*\(.*$/, "") : `${LABELS[k]} ${i + 1}`;
          const f = a.tree ? C.floatOf(a.tree) : NaN;
          const dec = a.approx ? a.approx.value : Number.isFinite(f) && !Number.isInteger(f) ? C.fmt(f, 10) : "";
          rows.push(h("tr", null,
            h("th", { scope: "row" }, name),
            h("td", null, a.tree ? ctx.mathEl(a.tree, { label: name }) : a.text, dec ? h("div", { class: "mono muted tiny tl-nowrap" }, "≈ " + dec) : null),
            h("td", null, badge(v))));
        });
      }
      const qs = byKey.quartiles && byKey.quartiles.ok ? C.exactAnswers(byKey.quartiles.result).map((a) => C.floatOf(a.tree)) : null;
      put(out, 
        card("Summary", h("div", { class: "tbl-wrap" }, h("table", { class: "att tl-stats" }, h("caption", { class: "sr-only" }, "Summary statistics"),
          h("thead", null, h("tr", null, h("th", { scope: "col" }, "Statistic"), h("th", { scope: "col" }, "Value"), h("th", { scope: "col" }, "Check"))),
          h("tbody", null, rows))),
          h("p", { class: "tiny muted", style: "margin:6px 0 0" }, "Quartiles use the median-of-halves method (the median is excluded from both halves when n is odd).")),
        card("Histogram", histogramSVG(d.floats), h("p", { class: "tiny muted", style: "margin:4px 0 0" }, "Bins by Sturges' rule; drawn from decimal values.")),
        qs && qs.length === 3 && qs.every(Number.isFinite) ? card("Box plot", boxSVG(d.floats, qs), h("p", { class: "tiny muted", style: "margin:4px 0 0" }, "Box from Q1 to Q3 with the median; whiskers reach the furthest points within 1.5 IQR; hollow dots are outliers.")) : null);
    } else {
      const p = C.parsePairs(pairs.value);
      if (p.bad.length) { status.error(`Line ${p.bad[0]} is not an x, y pair`); return; }
      if (p.xs.length < 2) { status.error("Enter at least two pairs"); return; }
      const reqs = C.regressionRequests(p.xs, p.ys);
      const res = await status.run(batchJob(reqs.map(([, i]) => i)), "Fitting the least-squares line");
      if (!res) return;
      const [lr, cr] = res;
      const blocks = [];
      if (lr && lr.ok) blocks.push(resultView(lr.result, { label: "Least-squares line" }));
      else blocks.push(h("p", { class: "err-msg" }, (lr && lr.error && lr.error.message) || "No line"));
      if (cr && cr.ok) blocks.push(resultView(cr.result, { label: "Correlation r" }));
      const ans = lr && lr.ok ? C.exactAnswers(lr.result) : [];
      const slope = ans[1] ? C.floatOf(ans[1].tree) : NaN, icpt = ans[2] ? C.floatOf(ans[2].tree) : NaN;
      put(out, card("Regression", ...blocks), card("Scatter plot", scatterSVG(p.xs.map((v) => C.floatOf(v)), p.ys.map((v) => C.floatOf(v)), slope, icpt)));
    }
  }
  for (const t of [data, pairs]) t.addEventListener("keydown", (e) => { if (e.key === "Enter" && (e.ctrlKey || e.metaKey)) { e.preventDefault(); compute(); } });
  const modeSeg = seg("stmode", "Data", [["one", "One variable"], ["two", "x, y pairs"]], "one", (v) => { mode = v; dataField.hidden = v !== "one"; pairField.hidden = v === "one"; put(out, ); status.clear(); });
  const el = h("div", { class: "tl-tool" },
    card("Statistics", modeSeg, dataField, pairField, h("div", { class: "cw-actions" }, btn("Compute", compute, { cls: "btn primary" }), h("span", { class: "tiny muted" }, "Ctrl+Enter also computes.")), status.el),
    out);
  return { el };
}

// ------------------------------------------------------------------ 6. number theory
function buildNumberTheory() {
  const { h } = ctx;
  let op = "factor";
  const out = h("div", { class: "tl-out" });
  const status = jobStatus(out);
  const a = textInput({ value: "360", inputmode: "numeric" }), b = textInput({ inputmode: "numeric" }), c = textInput({ inputmode: "numeric" });
  const fa = field("n", a), fb = field("", b), fc = field("", c);
  const LAYOUT = {
    factor: ["n", null, null, "360", "Prime factorisation; the factors are multiplied back and each is checked prime."],
    prime: ["n", null, null, "2^61 - 1", "A proof of primality with a certificate that is re-checked independently, or a factor."],
    gcd: ["Numbers (two or more)", null, null, "84, 126, 210", "Greatest common divisor and least common multiple."],
    modinv: ["a", "Modulus m", null, "17", "The x with a x = 1 (mod m), from the engine's verified congruence solver."],
    powmod: ["Base a", "Exponent e", "Modulus m", "3", "a^e mod m, computed exactly."],
    base: ["Digits", "From base", "To base", "255", "Any base from 2 to 36; letters are digits above 9."],
  };
  const DEF_B = { modinv: "3120", powmod: "1000000", base: "10" }, DEF_C = { powmod: "1000000007", base: "16" };
  const help = h("p", { class: "tiny muted", style: "margin:4px 0 0" });
  function layout() {
    const [la, lb, lc, va, hp] = LAYOUT[op];
    fa.querySelector("label").textContent = la; a.value = va;
    fb.hidden = !lb; fc.hidden = !lc;
    if (lb) { fb.querySelector("label").textContent = lb; b.value = DEF_B[op] || ""; }
    if (lc) { fc.querySelector("label").textContent = lc; c.value = DEF_C[op] || ""; }
    help.textContent = hp;
    put(out, ); status.clear();
  }
  async function run() {
    if (op === "prime") {
      const n = C.intText(a.value);
      if (!n) { status.error("Enter a whole number"); return; }
      const r = await status.run((p) => bridge.provePrime(n, { onProgress: p }), "Proving");
      if (!r) return;
      const lines = C.certificateLines(r.certificate);
      const verdictText = r.status === "prime" ? `${r.n} is prime` : r.status === "composite" ? `${r.n} is not prime` : `${r.n} is probably prime, but no proof was found`;
      const v = r.status === "unknown" ? { state: "partial", text: "Not proven" } : r.checked === true ? { state: "verified", text: r.status === "prime" ? "Certificate re-checked" : "Factor checked by division" } : { state: "exact", text: "Decided by a deterministic test" };
      put(out, h("div", { class: "tl-result" },
        h("div", { class: "tl-result-head" }, h("span", { class: "ctl-label" }, "Primality"), badge(v)),
        h("p", { class: "tl-big" }, verdictText),
        r.factor ? h("p", { class: "mono", style: "margin:0" }, `${r.n} = ${r.factor} x ${(BigInt(r.n) / BigInt(r.factor)).toString()}`) : null,
        r.witness && !r.factor ? h("p", { class: "tiny muted" }, `Miller-Rabin witness ${r.witness} shows it is composite.`) : null,
        h("p", { class: "tiny muted", style: "margin:4px 0" }, "Method: " + r.method),
        lines.length && r.status === "prime" ? h("details", { class: "disc", open: true }, h("summary", null, ctx.icon("chev"), "Certificate"), h("pre", { class: "tl-cert mono" }, lines.join("\n"))) : null));
      return;
    }
    if (op === "gcd") {
      const g = C.ntRequest("gcd", a.value), l = C.ntRequest("lcm", a.value);
      if (g.error) { status.error(g.error); return; }
      const res = await status.run(batchJob([g.input, l.input]), "Computing");
      if (!res) return;
      put(out, ...res.map((it, i) => (it.ok ? resultView(it.result, { label: i ? "Least common multiple" : "Greatest common divisor" }) : h("p", { class: "err-msg" }, it.error.message))));
      return;
    }
    if (op === "base") {
      const from = Number(b.value), to = Number(c.value);
      if (!(to >= 2 && to <= 36)) { status.error("The target base must be from 2 to 36"); return; }
      let dec = a.value.trim();
      if (from !== 10) {
        const req = C.ntRequest("frombase", a.value, String(from));
        if (req.error) { status.error(req.error); return; }
        const r = await status.run(solveJob(req.input), "Reading the digits");
        const ans = r && C.exactAnswers(r)[0];
        if (!ans) return;
        dec = ans.tree.text;
      } else if (!/^-?\d+$/.test(dec)) { status.error("Base 10 digits are 0 to 9"); return; }
      if (to === 10) { put(out, h("div", { class: "tl-result" }, h("div", { class: "tl-result-head" }, h("span", { class: "ctl-label" }, `${a.value.trim()} in base ${from} is, in base 10`), badge({ state: "verified", text: "Verified" })), h("p", { class: "tl-big mono" }, dec))); return; }
      const req = C.ntRequest("tobase", dec, String(to));
      if (req.error) { status.error(req.error); return; }
      const r = await status.run(solveJob(req.input), "Converting");
      if (!r) return;
      put(out, resultView(r, { label: `${a.value.trim()} (base ${from}) in base ${to}` }), from !== 10 ? h("p", { class: "tiny muted" }, `In base 10: ${dec}`) : null);
      return;
    }
    const req = C.ntRequest(op, a.value, b.value, c.value);
    if (req.error) { status.error(req.error); return; }
    const r = await status.run(solveJob(req.input), "Computing");
    if (!r) return;
    if (op === "modinv") {
      const ans = (r.answers || []).find((x) => x && (x.kind === "general" || x.kind === "exact") && x.tree);
      const res = ans ? C.residueOf(ans.tree, req.modulus) : null;
      if (res === null) { put(out, h("div", { class: "tl-result" }, h("div", { class: "tl-result-head" }, h("span", { class: "ctl-label" }, "Modular inverse"), badge(C.verdict(r))), h("p", { class: "tl-big" }, `${C.intText(a.value)} has no inverse modulo ${req.modulus}: they share a common factor.`))); return; }
      put(out, h("div", { class: "tl-result" },
        h("div", { class: "tl-result-head" }, h("span", { class: "ctl-label" }, "Modular inverse"), badge(C.verdict(r))),
        h("p", { class: "tl-big mono" }, `${C.intText(a.value)}^(-1) = ${res} (mod ${req.modulus})`),
        h("p", { class: "tiny muted" }, `Every solution of ${C.intText(a.value)} x = 1 (mod ${req.modulus}): x = ${ans.tree.text}`)));
      return;
    }
    put(out, resultView(r, { label: op === "factor" ? "Prime factorisation" : "a^e mod m" }));
  }
  const opSeg = seg("ntop", "Operation", [["factor", "Factorise"], ["prime", "Primality"], ["gcd", "GCD and LCM"], ["modinv", "Inverse mod m"], ["powmod", "Power mod m"], ["base", "Bases"]], op, (v) => { op = v; layout(); });
  for (const i of [a, b, c]) i.addEventListener("keydown", (e) => { if (e.key === "Enter") { e.preventDefault(); run(); } });
  layout();
  const el = h("div", { class: "tl-tool" },
    card("Number theory", opSeg, h("div", { class: "tl-form" }, fa, fb, fc, h("div", { class: "tl-field tl-go" }, btn("Compute", run, { cls: "btn primary" }))), help, status.el),
    card("Result", out));
  return { el };
}

// ------------------------------------------------------------------ 7. formula sheet
function buildFormulas() {
  const { h, icon } = ctx;
  const q = h("input", { type: "search", class: "field", placeholder: "Search formulas", autocomplete: "off" });
  const cat = select([["", "All areas"], ...C.FORMULA_CATEGORIES.map((c) => [c, c])], "");
  const list = h("div", { class: "tl-formulas" });
  const count = h("p", { class: "tiny muted", role: "status", style: "margin:0" });
  function render() {
    const found = C.searchFormulas(q.value, cat.value);
    count.textContent = `${found.length} formula${found.length === 1 ? "" : "s"}`;
    const groups = new Map();
    for (const f of found) { if (!groups.has(f.cat)) groups.set(f.cat, []); groups.get(f.cat).push(f); }
    list.replaceChildren(...[...groups].map(([c, fs]) => h("section", { class: "tl-fgroup", "aria-label": c }, h("h3", null, c),
      h("ul", null, fs.map((f) => h("li", { class: "tl-formula" },
        h("div", { class: "tl-f-name" }, f.name),
        h("code", { class: "tl-f-eq mono" }, f.formula),
        h("button", { type: "button", class: "btn small tl-f-try", "aria-label": `Solve the example for ${f.name}: ${f.example}`, onclick: () => ctx.loadProblem(f.example, true) }, h("span", { class: "mono" }, f.example), icon("enter"))))))));
    if (!found.length) list.replaceChildren(h("p", { class: "muted" }, "No formula matches."));
  }
  q.addEventListener("input", debounce(render, 120));
  cat.addEventListener("change", render);
  render();
  const el = h("div", { class: "tl-tool" }, card("Formula sheet",
    h("div", { class: "tl-form" }, field("Search", q), field("Area", cat)), count,
    h("p", { class: "tiny muted", style: "margin:4px 0 8px" }, "Each example button opens the problem in Solve and runs it."), list));
  return { el, onShow: (focus) => { if (focus) q.focus({ preventScroll: true }); } };
}

// ------------------------------------------------------------------ 8. equation system builder
function buildSystem() {
  const { h } = ctx;
  const lines = h("ol", { class: "cw-lines" });
  const unknowns = textInput({ placeholder: "x, y" });
  const out = h("div", { class: "tl-out" });
  const status = jobStatus(out);
  function line(v = "") {
    const input = textInput({ value: v });
    const li = h("li", { class: "cw-line" }, h("span", { class: "cw-n", "aria-hidden": "true" }), input,
      h("button", { type: "button", class: "btn ghost", onclick: () => { if (lines.children.length > 1) { li.remove(); renum(); } else input.value = ""; } }, ctx.icon("x")));
    input.addEventListener("keydown", (e) => {
      if (e.key !== "Enter") return;
      e.preventDefault();
      if (e.ctrlKey || e.metaKey) { solve(); return; }
      const n = line(); li.after(n); renum(); n.querySelector("input").focus();
    });
    return li;
  }
  function renum() {
    [...lines.children].forEach((li, i) => {
      li.querySelector(".cw-n").textContent = String(i + 1);
      li.querySelector("input").setAttribute("aria-label", `Equation ${i + 1}`);
      li.querySelector(".btn").setAttribute("aria-label", `Remove equation ${i + 1}`);
    });
  }
  const texts = () => [...lines.querySelectorAll("input")].map((i) => i.value);
  const detect = () => { const u = C.suggestUnknowns(texts()); unknowns.value = u.join(", "); return u; };
  async function solve() {
    if (!unknowns.value.trim()) detect();
    const req = C.systemRequest(texts(), unknowns.value);
    if (req.error) { status.error(req.error); return; }
    const r = await status.run(solveJob(req.input, req.options), "Solving");
    if (!r) return;
    const v = C.verdict(r);
    const box = h("div", { class: "tl-result" }, h("div", { class: "tl-result-head" }, h("span", { class: "ctl-label" }, "Solutions"), badge(v)));
    const sols = (r.answers || []).filter((a) => a && a.kind !== "none");
    if (!sols.length) box.append(h("p", { class: "tl-big" }, v.text));
    for (const s of sols) {
      if (s.values) {
        if (s.kind === "family") box.append(h("p", { class: "tiny muted", style: "margin:0" }, (s.label || "Infinitely many solutions") + (s.params && s.params.length ? `; ${s.params.join(", ")} can be any number` : "")));
        box.append(h("div", { class: "tl-ans tl-sol" }, s.values.map(([k, val]) => h("span", { class: "tl-ans-m" }, ctx.mathEl(val.node ? X.eq(X.sym(k), val.node) : `${k} = ${val.text}`, { label: k })))));
      } else if (s.tree) {
        box.append(h("div", { class: "tl-ans" }, h("span", { class: "tl-ans-m" }, ctx.mathEl(s.tree.node && s.label && /^[a-z]\w*$/i.test(s.label) && s.kind !== "set" ? X.eq(X.sym(s.label), s.tree.node) : s.tree, { label: s.label || "Solution" })), s.approx ? h("span", { class: "tl-dec mono" }, "≈ " + s.approx.value) : null));
      } else if (s.approx) box.append(h("div", { class: "tl-dec mono" }, (s.label ? s.label + " ≈ " : "≈ ") + s.approx.value));
    }
    const checks = (r.verification && r.verification.checks) || [];
    const passed = [...new Set(checks.filter((x) => x.passed).map((x) => x.name))];
    if (passed.length) box.append(h("p", { class: "tiny muted", style: "margin:6px 0 0" }, `Checks passed: ${passed.slice(0, 5).join(", ")}.`));
    box.append(h("div", { class: "ans-tools", style: "margin-top:8px" }, btn("Open in Solve for steps", () => ctx.loadProblem(texts().filter((t) => t.trim()).join("; "), true), { cls: "btn small ghost" })));
    put(out, box);
  }
  for (const e of ["2x + 3y - z = 1", "x - y + 2z = 3", "3x + y + z = 6"]) lines.append(line(e));
  renum();
  unknowns.addEventListener("keydown", (e) => { if (e.key === "Enter") { e.preventDefault(); solve(); } });
  const el = h("div", { class: "tl-tool" },
    card("Equation system",
      h("p", { class: "tiny muted", style: "margin:0" }, "One equation per line. Enter adds a line, Ctrl+Enter solves. Letters that are not unknowns are treated as constants."),
      lines,
      h("div", { class: "cw-actions" },
        btn("Add equation", () => { const n = line(); lines.append(n); renum(); n.querySelector("input").focus(); }, { icon: "plus" }),
        btn("Clear", () => { lines.replaceChildren(line(), line()); renum(); unknowns.value = ""; put(out, ); status.clear(); }, { cls: "btn small ghost" })),
      h("div", { class: "tl-form" }, field("Unknowns", unknowns, "Comma separated. Leave empty to use the letters x, y, z found."), h("div", { class: "tl-field tl-go" }, h("div", { class: "tl-inline" }, btn("Detect", () => { detect(); unknowns.focus(); }, { cls: "btn small" }), btn("Solve", solve, { cls: "btn primary" })))),
      status.el),
    card("Result", out));
  return { el };
}

// ------------------------------------------------------------------ navigation
const BUILDERS = { graph: buildGraph, matrix: buildMatrix, units: buildUnits, calc: buildCalc, stats: buildStats, numtheory: buildNumberTheory, formulas: buildFormulas, system: buildSystem };
const TOOL_ICONS = { graph: "t-graph", matrix: "t-matrix", units: "swap", calc: "keys", stats: "t-stats", numtheory: "t-hash", formulas: "book", system: "t-system" };

export function showTool(id, focusTab = false, quiet = false) {
  if (!BUILDERS[id]) id = "graph";
  const host = document.getElementById("tool-host");
  for (const [tid, t] of built) if (tid !== id) t.el.hidden = true;
  if (!built.has(id)) {
    const t = BUILDERS[id]();
    t.el.id = "tool-" + id;
    t.el.setAttribute("role", "tabpanel");
    t.el.setAttribute("aria-labelledby", "tooltab-" + id);
    built.set(id, t);
    host.append(t.el);
  }
  const t = built.get(id);
  t.el.hidden = false;
  current = id;
  for (const b of document.querySelectorAll("#tool-nav [role=tab]")) {
    const on = b.dataset.tool === id;
    b.setAttribute("aria-selected", String(on));
    b.tabIndex = on ? 0 : -1;
    if (on && focusTab) b.focus();
  }
  try { ctx.store.setPref("tool", id); } catch (_) { /* optional */ }
  if (t.onShow) queueMicrotask(() => t.onShow(!focusTab && !quiet));
}
export const currentTool = () => current;
export function redrawTools() { const g = built.get("graph"); if (g && g.redraw) g.redraw(); }

export function initTools(context) {
  ctx = context;
  const { h, icon } = ctx;
  const nav = document.getElementById("tool-nav");
  nav.replaceChildren(...C.TOOLS.map(([id, label]) => h("button", { type: "button", role: "tab", id: "tooltab-" + id, class: "tl-tab", "aria-controls": "tool-" + id, "aria-selected": "false", tabindex: "-1", dataset: { tool: id }, onclick: () => showTool(id) }, icon(TOOL_ICONS[id]), h("span", null, label))));
  nav.addEventListener("keydown", (e) => {
    const ids = C.TOOL_IDS;
    const from = e.target.closest && e.target.closest("[data-tool]");
    const i = ids.indexOf(from ? from.dataset.tool : current);
    const next = { ArrowRight: i + 1, ArrowDown: i + 1, ArrowLeft: i - 1, ArrowUp: i - 1, Home: 0, End: ids.length - 1 }[e.key];
    if (next === undefined) return;
    e.preventDefault();
    showTool(ids[(next + ids.length) % ids.length], true);
  });
}
