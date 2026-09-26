// Quelvra step records.
//
// Every user-visible transformation is recorded as it happens (never reconstructed afterwards):
//   { rule, title, why, before, after, conditions, sub, kind, check? }
// kind: "equivalent" (same solution set / value), "conditional" (valid under `conditions`),
//       "approximation" (numerical), "note" (information, no transformation).

import { toText } from "./print.js";

export function makeStep({ rule, title, why = "", before = null, after = null, conditions = [], sub = [], kind = "equivalent", check = null }) {
  if (!rule) throw new Error("step needs a rule id");
  return { rule, title: title || rule, why, before, after, conditions, sub, kind, check };
}

// A log that engines append to. `group` nests the steps produced inside fn as sub-steps.
export class StepLog {
  constructor() { this.steps = []; this.stack = [this.steps]; }
  get cur() { return this.stack[this.stack.length - 1]; }
  add(step) { const s = step.rule ? makeStep(step) : step; this.cur.push(s); return s; }
  group(head, fn) {
    const s = makeStep({ ...head, sub: [] });
    this.cur.push(s);
    this.stack.push(s.sub);
    try { return fn(s); } finally { this.stack.pop(); }
  }
  get length() { return this.steps.length; }
}

// Null log: same interface, records nothing (used when steps are not requested).
export const NO_STEPS = {
  steps: [],
  add() { return null; },
  group(head, fn) { return fn(null); },
  get length() { return 0; },
};

// Fill "{name}" placeholders in explanation templates with printed trees / values.
export function fill(template, vars) {
  return template.replace(/\{(\w+)\}/g, (m, k) => {
    const v = vars[k];
    if (v === undefined) return m;
    return typeof v === "object" && v && v.k ? toText(v) : String(v);
  });
}

// Merge trivial steps (before === after, or consecutive steps of the same rule) so
// explanations stay short. Operates recursively on sub-steps.
export function compact(steps) {
  const out = [];
  for (const s of steps) {
    if (!s) continue;
    const sub = s.sub && s.sub.length ? compact(s.sub) : [];
    if (s.kind !== "note" && s.before && s.after && s.before === s.after && !sub.length) continue;
    out.push({ ...s, sub });
  }
  return out;
}

// Plain-text rendering of a step list (used by tests and as a fallback in the UI).
export function stepsToText(steps, indent = "") {
  let s = "";
  steps.forEach((st, i) => {
    s += `${indent}${i + 1}. ${st.title}`;
    if (st.before && st.after) s += `: ${toText(st.before)}  ->  ${toText(st.after)}`;
    else if (st.after) s += `: ${toText(st.after)}`;
    s += "\n";
    if (st.why) s += `${indent}   ${st.why}\n`;
    if (st.conditions && st.conditions.length) s += `${indent}   valid when ${st.conditions.map((c) => (c.k ? toText(c) : String(c))).join(", ")}\n`;
    if (st.sub && st.sub.length) s += stepsToText(st.sub, indent + "   ");
  });
  return s;
}
