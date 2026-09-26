// Judge for the word-problem corpus (wordproblems.corpus.js).
// judge(expectation, result) -> "ok" | "incomplete" | "refused" | "WRONG"
//   ok          verified, and the shown numbers are exactly what the question asks for
//   incomplete  verified, every shown number is right but some asked-for value is missing
//   refused     no verified answer
//   WRONG       a verified answer shows a number that is not an answer to the question
//   { refuse: true } marks a trap with no determined answer: refusing is "ok", answering is WRONG
import { evalC } from "../public/engine/verify.js";

const close = (x, y) => Math.abs(x - y) <= 1e-7 * Math.max(1, Math.abs(y));
function numOf(t) {
  if (!t) return null;
  const u = t.k === "eq" ? t.args[1] : t;
  try { const c = evalC(u, {}, "complex"); if (c && Number.isFinite(c.re) && Math.abs(c.im) < 1e-9 * Math.max(1, Math.abs(c.re))) return c.re; } catch (_) {}
  return null;
}
// every number shown, with system answers flattened; exact and approximate forms of one value count once
export function shownNumbers(r) {
  const out = [];
  let system = false;
  // "(the question asks for m)": only that unknown of a system answers the question
  const am = /\(the question asks for ([a-z])\)/.exec((r.input && r.input.interpretation) || "");
  for (const a of r.answers || []) {
    if (a.kind === "none") continue;
    const vs = [];
    if (a.values) { system = true; for (const [k, v] of a.values) if (!am || k === am[1]) vs.push(numOf(v)); }
    else if (a.tree) vs.push(numOf(a.tree));
    else if (a.approx && a.approx.value != null) vs.push(parseFloat(a.approx.value));
    for (const v of vs) {
      if (v === null || !Number.isFinite(v)) return { nums: null, system };
      if (!out.some((w) => close(w, v))) out.push(v);
    }
  }
  return { nums: out, system };
}
export function judge(exp, r) {
  const verified = r.ok && r.verification && r.verification.status === "passed";
  const { nums, system } = shownNumbers(r);
  // a trap: the text does not determine an answer, so the only right response is a refusal
  if (exp && exp.refuse) return !verified || !nums || !nums.length ? "ok" : "WRONG";
  if (!verified || !nums || !nums.length) return "refused";
  if (typeof exp === "number") {
    // one asked-for quantity: a system that does not name the asked unknown may show the others too, a root list may not
    if (system && !/\(the question asks for [a-z]\)/.test((r.input && r.input.interpretation) || "")) return nums.some((v) => close(v, exp)) ? "ok" : "WRONG";
    return nums.every((v) => close(v, exp)) ? "ok" : "WRONG";
  }
  if (exp.nums) {
    if (!nums.every((v) => exp.nums.some((w) => close(v, w)))) return "WRONG";
    return exp.nums.every((w) => nums.some((v) => close(v, w))) ? "ok" : "incomplete";
  }
  throw new Error("unknown expectation");
}
