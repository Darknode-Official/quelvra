// Quelvra engine entry point.
//
//   solve(input, options)      -> Solver result (CONTRACT.md) plus `explanation` for options.mode
//   checkWork(lines, options)  -> { ok, lines: [{ index, text, status, message, tree, diagnosis }], firstMistake }
//   numeric(input, options)    -> Solver result whose answer is a certified approximation
//
// Every solver family registers itself with the orchestrator when its module loads. A family
// that fails to load is reported in `loadErrors` and simply offers no strategies; it never
// makes the engine guess.

import * as X from "./expr.js";
import { parseDetailed } from "./parse.js";
import { solve as orchestrate, register, toContractVerification } from "./orchestrate.js";
import { explain } from "./explain.js";
import { checkLines } from "./mistakes.js";
import { setApproxHook } from "./strategies/basic.js";
import "./strategies/compute.js";
import { solveResearch } from "./strategies/research.js";
import * as NUM from "./numeric.js";
import * as U from "./units.js";
import { solveLogic } from "./logic.js";
import { translateAdvancedDiscrete } from "./discrete/lang.js";

export const loadErrors = [];
const OPTIONAL = ["./strategies/solve.js", "./strategies/integrate.js", "./strategies/calculus.js", "./strategies/analysis.js"];
// advanced continuous commands (engine/advanced/, strategies/advanced-continuous.js)
OPTIONAL.push("./strategies/advanced-continuous.js");
OPTIONAL.push("./strategies/advanced-discrete.js"); // advanced discrete commands
for (const m of OPTIONAL) {
  try { await import(m); } catch (e) { if (!/Cannot find module|Failed to fetch|ERR_MODULE_NOT_FOUND|404/.test(String(e && (e.code || e.message)))) loadErrors.push({ module: m, message: String(e && e.message) }); }
}

setApproxHook((tree, digits) => {
  try {
    const r = NUM.N(tree, digits);
    return r && r.converged !== false && r.value ? r : null;
  } catch (_) { return null; }
});

export function solve(input, options = {}) {
  const progress = typeof options.onProgress === "function" ? options.onProgress : () => {};
  progress("reading");
  // one equation per line is a system, the same as "; " (the UI does this too)
  const text = typeof input === "string" ? input.split(/\r?\n/).map((l) => l.trim()).filter(Boolean).join("; ") : input;
  // unit conversion requests go straight to the units engine ("5 km/h to m/s")
  if (typeof text === "string") {
    const ut = /^(?:convert\s+)?-?[\d.]+\s*[a-z°]/i.test(text) ? U.normalizeUnitWords(text) : text;
    const m = ut.match(/^(?:convert\s+)?(-?[\d.]+(?:\s*[a-zA-Z°][\w°/^*·.]*)+)\s+(?:to|in|into)\s+([a-zA-Z°][\w°/^*·.]*)$/i);
    if (m) {
      try {
        const r = U.convertText(`${m[1]} to ${m[2]}`);
        if (r && r.value) return unitResult(text, r);
      } catch (e) {
        if (e && e.code === "DIMENSION") return refusal(text, e.message.replace(/^Quelvra: /, ""));
      }
    }
  }
  progress("solving");
  // open problems and bounded explorations ("collatz 27", "goldbach up to 10^6", "riemann hypothesis")
  if (typeof text === "string") {
    const res = solveResearch(text, { onProgress: options.onProgressDetail, timeMs: options.timeLimit });
    if (res) return finishResearch(res, options);
  }
  // propositional logic and finite-set operations ("truth table of p and q", "{1, 2} union {3}");
  // the advanced discrete engine takes the requests it recognises (richer, separately verified answers)
  if (typeof text === "string" && !translateAdvancedDiscrete(text)) {
    const lg = solveLogic(text);
    if (lg) {
      if (lg.verification.status !== "passed") return refusal(text, "Quelvra computed an answer but could not verify it, so it is withheld");
      lg.explanation = explain(lg, options.mode === "answer" ? "answer" : "steps");
      return lg;
    }
  }
  const r = orchestrate(text, options);
  if (options.mode === "numeric") attachNumeric(r, options);
  r.explanation = explain(r, options.mode === "answer" ? "answer" : options.mode === "teach" ? "teach" : "steps");
  progress("done");
  return r;
}

// Research results carry their own solutionStatus: exact (decided by exhaustive computation),
// evidence (verified up to a bound, which is not a proof), open-problem / info (no answer claimed).
function finishResearch(r, options) {
  const v = r.verification || {};
  const solution = { exact: 1, evidence: 1, approximate: 0.95 }[r.solutionStatus] ?? null;
  r.confidence = r.confidence || {
    recognition: 1, classification: 1, solution,
    verification: v.status === "passed" ? 1 : v.status === "failed" ? 0 : null,
  };
  r.explanation = explain(r, options.mode === "answer" ? "answer" : options.mode === "teach" ? "teach" : "steps");
  return r;
}

export function numeric(input, options = {}) {
  return solve(input, { ...options, mode: "numeric" });
}

function attachNumeric(r, options) {
  const digits = Math.max(1, Math.min(1000, Number(options.digits) || 30));
  for (const a of r.answers || []) {
    if (a.tree && !a.approx && X.freeSymbols(a.tree).size === 0 && a.tree !== X.UNDEF) {
      try { const v = NUM.N(a.tree, digits); if (v && v.value) a.approx = v; } catch (_) { /* leave exact only */ }
    }
  }
}

function base(text) {
  return {
    ok: true, input: { text, tree: null, warnings: [] }, recognition: { source: "text", confidence: 1 },
    classification: { kind: "command", family: "units", unknowns: [], goal: "convert", label: "Unit conversion", method: "structural" },
    answers: [], solutionStatus: "exact", verification: { status: "not-applicable", checks: [] }, steps: [], conditions: [], rejected: [], attempts: [], graph: null, ms: 0,
    confidence: { recognition: 1, classification: 1, solution: 1, verification: null },
  };
}
function unitResult(text, r) {
  const out = base(text);
  const unitText = r.unit && r.unit.text ? r.unit.text : r.target || "";
  out.answers = [{ kind: "exact", tree: r.value, label: null, unit: unitText, text: `${r.text || ""}` }];
  const dec = r.decimal ? String(r.decimal).replace(/\s.*$/, "") : "";
  // a terminating value shown with fewer than 12 significant digits is the exact value
  const exactDec = r.repeating === false && /^-?[\d.]+$/.test(dec) && dec.replace(/[-.]/g, "").replace(/^0+/, "").length < 12;
  if (r.decimal) out.answers.push({ kind: "approx", approx: { value: dec, digits: 12, requested: 12, errorBound: exactDec ? "0" : /^-?\d+\.\d+$/.test(dec) ? `5e-${dec.split(".")[1].length + 1}` : null, method: "exact conversion factor", iterations: 0, converged: true }, unit: unitText });
  out.steps = r.steps || [];
  out.verification = toContractVerification([{ status: "verified-exact", checks: [{ kind: "exact-factors", ok: true, detail: "conversion uses exact rational factors between SI definitions" }] }]);
  out.confidence.verification = 1;
  out.explanation = explain(out, "steps");
  return out;
}
function refusal(text, message) {
  const out = base(text);
  out.answers = [{ kind: "none", label: message.replace(/^./, (c) => c.toUpperCase()) + "." }];
  out.solutionStatus = "exact";
  out.refused = true;
  out.explanation = explain(out, "answer");
  return out;
}

// Check-my-work in the UI's shape, backed by the equivalence-based mistake detector.
export function checkWork(lines, options = {}) {
  const src = (lines || []).map((l) => String(l));
  const r = checkLines(src, options);
  const rows = [];
  let firstMistake = -1;
  const byLine = new Map(r.lines.map((l) => [l.line, l]));
  const transitionTo = new Map(r.transitions.map((t) => [t.to, t]));
  src.forEach((text, index) => {
    const info = byLine.get(index + 1);
    const row = { index, text, status: "unknown", message: "", tree: null, diagnosis: [] };
    if (!text.trim()) { row.status = "unknown"; row.message = "Empty line"; rows.push(row); return; }
    if (info && info.error) { row.status = "syntax"; row.message = info.error; rows.push(row); return; }
    try { row.tree = parseDetailed(text).node; } catch (_) { /* reported above */ }
    const t = transitionTo.get(index + 1);
    if (!t) { row.status = "start"; row.message = "Starting point"; }
    else if (t.status === "ok") { row.status = "ok"; row.message = t.message || "Follows from the previous line"; }
    else if (t.status === "ok-conditional") { row.status = "ok"; row.message = t.message; row.warning = true; }
    else if (t.status === "wrong") {
      row.status = "mistake";
      row.message = t.message || "Does not follow from the previous line";
      row.diagnosis = t.diagnosis || [];
      if (row.diagnosis.length) row.message += ` Likely cause: ${row.diagnosis[0].name}. ${row.diagnosis[0].explain}`;
      if (firstMistake < 0) firstMistake = index;
    } else { row.status = "unknown"; row.message = t.message || "Could not check this step"; }
    rows.push(row);
  });
  return { ok: firstMistake < 0, lines: rows, firstMistake };
}

export { register };
