// Recurrence / generating-function / sequence phrasings -> canonical commands (see sequences.js).

import { callForm, splitTop } from "./lang-util.js";

// subscript notation a_n, a_{n-1}, a_0 -> a(n), a(n-1), a(0)
function subscripts(s) {
  return s
    .replace(/(?<![A-Za-z])([A-Za-z])_\{([^{}]+)\}/g, "$1($2)")
    .replace(/(?<![A-Za-z])([A-Za-z])_\(([^()]+)\)/g, "$1($2)")
    .replace(/(?<![A-Za-z])([A-Za-z])_(\d+|[a-z])\b/g, "$1($2)");
}
// "a(n) = ... with a(0) = 1 and a(1) = 2" -> "a(n) = ..., a(0) = 1, a(1) = 2"
function recurrenceText(s) {
  const t = subscripts(s).replace(/\s+(?:with|where|given(?: that)?|and|for n\s*>=?\s*\d+\s*,?)\s+/gi, ", ").replace(/\s*;\s*/g, ", ");
  const parts = splitTop(t).map((p) => p.trim()).filter(Boolean);
  if (!parts.length || !parts.every((p) => /=/.test(p))) return null;
  return parts.join(", ");
}
const isRecurrence = (s) => /(?<![A-Za-z])([A-Za-z])\((?:[a-z])\s*-\s*\d+\)/.test(s);
function numberList(s) {
  const xs = s.split(/\s*,\s*|\s+/).map((x) => x.trim()).filter((x) => x && x !== "..." && x !== "…");
  return xs.length >= 2 && xs.every((x) => /^-?\d+(?:\/\d+)?$/.test(x)) ? xs : null;
}

export function recogniseSeq(text) {
  const t = text;
  const cf = callForm(t);
  if (cf && ["rsolve", "recsolve", "solverecurrence"].includes(cf.name)) {
    const r = recurrenceText(cf.args.join(", "));
    return r ? { math: `rsolve(${r})`, interpretation: "Solve the recurrence" } : null;
  }
  if (cf && ["genfunc", "generatingfunction", "gf"].includes(cf.name)) {
    const joined = subscripts(cf.args.join(", "));
    if (isRecurrence(joined)) { const r = recurrenceText(joined); return r ? { math: `genfunc(${r})`, interpretation: "Generating function" } : null; }
    return { math: `genfunc(${joined})`, interpretation: "Generating function" };
  }
  if (cf && ["coefficient", "seriescoeff", "coeff"].includes(cf.name) && cf.args.length === 3) return { math: `seriescoeff(${cf.args.join(", ")})`, interpretation: "Series coefficient" };
  if (cf && ["findsequence", "identifysequence", "nextterm"].includes(cf.name)) {
    const xs = numberList(cf.args.join(", "));
    return xs ? { math: `findsequence(${xs.join(", ")})`, interpretation: "Identify the sequence" } : null;
  }
  let m;
  if ((m = t.match(/^(?:solve|find a closed form for|find the closed form of)\s+(?:the\s+)?(?:linear\s+)?recurrence(?:\s+relation)?\s*:?\s*(.+)$/i))) {
    const r = recurrenceText(m[1]);
    return r && isRecurrence(r) ? { math: `rsolve(${r})`, interpretation: "Solve the recurrence" } : null;
  }
  if ((m = t.match(/^(?:find\s+|compute\s+|what is\s+)?(?:the\s+)?(?:ordinary\s+)?generating function\s+(?:of|for)\s+(?:the\s+sequence\s+)?(.+)$/i))) {
    const body = subscripts(m[1]);
    if (isRecurrence(body)) { const r = recurrenceText(body); return r ? { math: `genfunc(${r})`, interpretation: "Generating function" } : null; }
    const e = body.match(/^([A-Za-z])\(([a-z])\)\s*=\s*(.+)$/);
    if (e) return { math: `genfunc(${e[3]}, ${e[2]})`, interpretation: `Generating function of ${e[1]}(${e[2]}) = ${e[3]}` };
    if (/^[^=]+$/.test(body) && /\bn\b/.test(body)) return { math: `genfunc(${body}, n)`, interpretation: "Generating function" };
    return null;
  }
  if ((m = t.match(/^(?:find\s+|compute\s+|what is\s+)?(?:the\s+)?coefficient of\s+([a-z])(?:\s*\^\s*\{?(\d+)\}?)?\s+in\s+(?:the\s+(?:power\s+)?series\s+(?:expansion\s+)?(?:of\s+)?)?(?:the\s+expansion\s+of\s+)?(.+)$/i))) {
    // only rational functions of the variable are claimed; anything else (sin x, e^x, ...) is left
    // to the series strategies
    if (m[3].replace(new RegExp(`(?<![A-Za-z])${m[1]}(?![A-Za-z])`, "g"), "").match(/[A-Za-z]/)) return null;
    return { math: `seriescoeff(${m[3]}, ${m[1]}, ${m[2] || 1})`, interpretation: `Coefficient of ${m[1]}^${m[2] || 1}` };
  }
  if ((m = t.match(/^(?:find\s+|what is\s+|what's\s+|give\s+)?(?:the\s+)?(?:next term|next number|nth term|n-th term|general term|formula|pattern)\s+(?:in|of|for)\s+(?:the\s+)?(?:sequence\s+)?:?\s*(.+)$/i))
    || (m = t.match(/^(?:identify|continue|extend)\s+(?:the\s+)?sequence\s*:?\s*(.+)$/i))
    || (m = t.match(/^what comes next\s*(?:in|:)?\s*(?:the\s+sequence\s*)?:?\s*(.+)$/i))) {
    const xs = numberList(m[1].replace(/,?\s*(?:\.\.\.|…)\s*$/, ""));
    return xs ? { math: `findsequence(${xs.join(", ")})`, interpretation: "Identify the sequence" } : null;
  }
  return null;
}
