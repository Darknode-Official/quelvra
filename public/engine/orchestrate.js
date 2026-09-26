// Quelvra solver orchestrator.
//
// Pipeline: recognise -> parse -> classify (structural) -> order strategies -> run each under a
// resource budget -> verify every candidate independently against the ORIGINAL problem ->
// cross-check when more than one method succeeds -> assemble the result (CONTRACT.md schema).
//
// Strategies register themselves with `register({ id, kinds, families?, goals?, priority, run })`.
// run(node, card, env) returns a candidate:
//   { answers: [...], steps: [...], conditions: [...], rejected: [...], solutionStatus, verify?: fn, graph? }
// or null when the strategy does not apply after closer inspection. It may throw {code:"BUDGET"|"TIMEOUT"}
// or {code:"UNSUPPORTED", message}. The orchestrator never trusts a strategy's own claim of correctness.

import * as X from "./expr.js";
import { parseDetailed, unknownWords } from "./parse.js";
import { simplify, makeCtx } from "./simplify.js";
import { toText } from "./print.js";
import { classify } from "./identify.js";
import { translate } from "./language.js";
import { StepLog, NO_STEPS } from "./steps.js";

const now = () => (typeof performance !== "undefined" ? performance.now() : Date.now());
const STRATEGIES = [];

export function register(s) {
  if (!s || !s.id || typeof s.run !== "function") throw new Error("strategy needs id and run");
  const i = STRATEGIES.findIndex((t) => t.id === s.id);
  if (i >= 0) STRATEGIES.splice(i, 1);
  STRATEGIES.push({ priority: 50, kinds: [], families: null, goals: null, crossCheck: false, ...s });
}
export const strategies = () => STRATEGIES.slice();

function applicable(card) {
  return STRATEGIES.filter((s) =>
    (!s.kinds.length || s.kinds.includes(card.kind)) &&
    (!s.families || s.families.includes(card.family)) &&
    (!s.goals || s.goals.includes(card.goal)) &&
    (!s.applies || s.applies(card)))
    .sort((a, b) => a.priority - b.priority);
}

export function condNode(c) {
  if (!c) return c;
  if (c.k) return c;
  if (c.rel === "!=0") return X.rel("!=", c.node, X.ZERO);
  if (c.rel === ">=0") return X.rel(">=", c.node, X.ZERO);
  if (c.rel === ">0") return X.rel(">", c.node, X.ZERO);
  return c.node;
}
function dedupeConditions(list) {
  const out = [];
  for (const c of list.map(condNode)) if (c && !out.includes(c)) out.push(c);
  return out;
}

// ---- recognition ----
// Natural language goes through the language engine (which refuses rather than guesses); math
// notation goes straight to the parser. Letter runs that are not math names are never silently
// read as products of variables.
function recognise(input, options) {
  if (input && typeof input === "object" && input.k) return { tree: input, text: toText(input), warnings: [], source: "tree", confidence: 1 };
  const src = String(typeof input === "string" ? input : (input && input.text) || "").trim();
  const source = (input && input.source) || options.source || "text";
  const srcConf = input && typeof input.confidence === "number" ? input.confidence : 1;
  if (!src) return { error: Object.assign(new Error("Nothing to solve: the input is empty."), { pos: 0, hint: "Type an equation or expression." }), text: src, source };
  // greetings and chat are not math, even though "hi" would parse as h*i
  if (/^(?:hi+|hello|hey+|yo|sup|ok(?:ay)?|thanks?(?: you)?|thx|ty|lol|bye|yes|yeah|no+|nope|oh|hm+|help|test(?:ing)?)[\s!?.,]*$/i.test(src)) {
    return { error: Object.assign(new Error(`"${src}" is not a math problem.`), { pos: 0, hint: "Type an equation or expression, for example 2x + 3 = 11, or pick one from Examples." }), text: src, source };
  }
  const t = translate(src);
  if (t.ok && t.pattern !== "math") {
    try {
      const { node, warnings, congruence } = parseDetailed(t.math);
      return { tree: node, text: t.math, original: src, warnings, congruence, source: source === "text" ? "language" : source, confidence: srcConf * t.confidence,
        interpretation: t.interpretation, goal: t.goal, variable: t.variable, domain: t.domain, notes: t.notes || [] };
    } catch (_) { /* fall through */ }
  }
  const words = unknownWords(src);
  // an English stop word ("of", "is", "the") would only parse as a product of letters: never math
  const STOP = /^(of|is|as|by|if|an|the|to|for|in|with|from|over|where|when|find|what|then|that|than|are|was)$/i;
  if (words.length >= 2 || words.some((w) => w.length >= 4 || STOP.test(w))) {
    const e = new Error(`Quelvra does not understand "${words[0]}". ${t.reason || ""}`.trim());
    e.pos = src.indexOf(words[0]); e.hint = "Write the math with symbols (2x + 3 = 11), or use one of the supported phrasings such as \"derivative of x^3\" or \"solve x^2 = 4\". Products of letters need a * or spaces: a*b*c.";
    return { error: e, text: src, source, languageReason: t.reason };
  }
  try {
    const { node, warnings, congruence } = parseDetailed(src);
    const w = [...warnings];
    for (const word of words) w.push(`"${word}" was read as the product ${word.split("").join("*")}.`);
    return { tree: node, text: src, warnings: w, congruence, source, confidence: srcConf * (w.length ? 0.9 : 1) };
  } catch (e) {
    return { error: e, text: src, source, languageReason: t.reason };
  }
}

// ---- main entry ----
export function solve(input, options = {}) {
  const t0 = now();
  const timeLimit = options.timeLimit || 8000;
  const opsLimit = options.ops || 3_000_000;
  const rec = recognise(input, options);
  // "solve z^3 = 1 over the complex numbers": the sentence itself can choose the complex domain
  const domain = options.domain === "complex" || (!options.domain && rec.domain === "complex") ? "complex" : "real";
  const base = {
    ok: false, input: { text: rec.text, tree: rec.tree || null, warnings: rec.warnings || [], interpretation: rec.interpretation || null, original: rec.original || null },
    recognition: { source: rec.source, confidence: rec.error ? 0 : rec.confidence },
    classification: null, answers: [], solutionStatus: "unsolved",
    verification: { status: "not-applicable", checks: [] }, steps: [], conditions: [], rejected: [], attempts: [], graph: null, ms: 0,
    confidence: null,
  };
  if (rec.error) {
    base.error = { message: rec.error.message, pos: rec.error.pos, hint: rec.error.hint, language: rec.languageReason || null };
    base.confidence = { recognition: 0, classification: 0, solution: 0, verification: 0 };
    base.ms = now() - t0;
    return base;
  }
  // congruence notation (3x ≡ 2 (mod 7)) asks for integer solutions unless a domain was chosen
  if (rec.congruence && options.integers === undefined && options.domain !== "complex" && options.domain !== "integer") {
    options = { ...options, integers: true };
    base.input.warnings = [...base.input.warnings, "A congruence is solved over the integers."];
  }
  const tree = rec.tree;
  const card = classify(tree, { variable: options.variable || rec.variable, goal: options.goal || rec.goal || undefined });
  card.domain = domain;
  base.classification = card;
  const strategies = applicable(card);
  if (!strategies.length) {
    base.solutionStatus = "unsupported";
    base.answers = [{ kind: "none", label: `Quelvra recognised this as: ${card.label || card.kind}, but has no method for it yet.` }];
    base.confidence = { recognition: base.recognition.confidence, classification: 1, solution: 0, verification: 0 };
    base.ms = now() - t0;
    return base;
  }

  const deadline = t0 + timeLimit;
  const candidates = [];
  const wantCross = options.crossCheck !== false;
  for (const s of strategies) {
    if (now() > deadline) { base.attempts.push({ strategy: s.id, status: "skipped", reason: "time limit reached", ms: 0 }); continue; }
    if (candidates.length && !(wantCross && s.crossCheck)) { base.attempts.push({ strategy: s.id, status: "skipped", reason: "already solved", ms: 0 }); continue; }
    const ts = now();
    const log = options.steps === false ? NO_STEPS : new StepLog();
    const ctx = makeCtx({ domain, conditions: [], budget: { ops: opsLimit } });
    const env = { ctx, log, domain, deadline, digits: options.digits || 20, options, original: tree, checkTime() { if (now() > deadline) { const e = new Error("time limit"); e.code = "TIMEOUT"; throw e; } } };
    try {
      const c = s.run(tree, card, env);
      const ms = now() - ts;
      if (!c) { base.attempts.push({ strategy: s.id, status: "skipped", reason: "not applicable on closer inspection", ms }); continue; }
      c.strategy = s.id;
      c.steps = c.steps || log.steps;
      c.conditions = dedupeConditions([...(c.conditions || []), ...ctx.conditions]);
      // independent verification
      c.verification = c.verify ? safeVerify(c.verify, c) : { status: "not-applicable", checks: [] };
      base.attempts.push({ strategy: s.id, status: c.verification.status === "failed" ? "failed" : "ok", reason: c.verification.status === "failed" ? "answer failed independent verification" : c.note || "", ms });
      if (c.verification.status === "failed") continue; // never report a failed answer as an answer
      candidates.push(c);
    } catch (e) {
      const ms = now() - ts;
      const reason = e && e.code === "BUDGET" ? "operation budget exhausted" : e && e.code === "TIMEOUT" ? "time limit reached" : e && e.code === "UNSUPPORTED" ? e.message : `internal error: ${e && e.message}`;
      base.attempts.push({ strategy: s.id, status: "failed", reason, ms });
      if (!(e && e.code) && options.debug) throw e;
    }
  }

  if (!candidates.length) {
    base.solutionStatus = base.attempts.some((a) => a.reason && a.reason.startsWith("answer failed")) ? "unsolved" : "unsolved";
    base.answers = [{ kind: "none", label: "No method produced an answer that passed verification. Quelvra does not guess." }];
    base.confidence = { recognition: base.recognition.confidence, classification: 1, solution: 0, verification: 0 };
    base.ms = now() - t0;
    return base;
  }

  const best = candidates[0];
  const out = { ...base, ok: true, answers: best.answers, solutionStatus: best.solutionStatus || "exact", steps: best.steps, conditions: best.conditions,
    rejected: best.rejected || [], graph: best.graph || null, verification: best.verification, method: best.strategy, extra: best.extra || null };
  if (best.noSolution || (best.extra && best.extra.noSolution)) out.noSolution = true;
  // cross-check: another independent method must agree
  if (candidates.length > 1 && best.compare) {
    for (const other of candidates.slice(1)) {
      const agree = best.compare(other);
      out.verification = { ...out.verification, checks: [...out.verification.checks, { name: "cross-check", method: other.strategy, passed: agree, detail: agree ? `agrees with ${other.strategy}` : `DISAGREES with ${other.strategy}` }] };
      if (!agree) out.verification.status = "partial";
    }
  }
  out.confidence = scoreConfidence(out, card);
  out.ms = now() - t0;
  return out;
}

function safeVerify(fn, c) {
  try { return fn(c) || { status: "not-applicable", checks: [] }; }
  catch (e) { return { status: "partial", checks: [{ name: "verification", method: "error", passed: false, detail: `verification crashed: ${e.message}` }] }; }
}

// Four separate confidences, never merged into one number.
function scoreConfidence(r, card) {
  const vs = r.verification.status;
  const solution = r.solutionStatus === "exact" ? 1 : r.solutionStatus === "approximate" ? 0.95 : r.solutionStatus === "partial" ? 0.6 : 0;
  const verification = vs === "passed" ? (r.verification.level === "numeric" ? 0.97 : 1) : vs === "partial" ? 0.6 : vs === "not-applicable" ? null : 0;
  return {
    recognition: r.recognition.confidence,
    classification: card.method === "structural" ? 1 : 0.8,
    solution,
    verification,
  };
}

// Helpers for strategies ---------------------------------------------------------------

// Map verifier results ("verified-exact" etc.) to the contract's verification object.
export function toContractVerification(results) {
  const checks = [];
  let failed = false, partial = false, numeric = false;
  for (const r of results) {
    for (const c of r.checks || []) checks.push({ name: c.kind || c.name, method: c.method || (String(r.status).includes("numeric") ? "numeric" : "exact"), passed: c.ok !== false && c.ok !== null, detail: c.detail || "" });
    if (r.status === "failed") failed = true;
    else if (r.status === "inconclusive") partial = true;
    else if (r.status === "verified-numeric") numeric = true;
  }
  return { status: failed ? "failed" : partial ? "partial" : results.length ? "passed" : "not-applicable", level: numeric ? "numeric" : "exact", checks };
}

export function unsupported(message) { const e = new Error(message); e.code = "UNSUPPORTED"; return e; }
export { simplify };
