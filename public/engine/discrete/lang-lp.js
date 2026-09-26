// Linear programming and game phrasings -> canonical commands (see lp.js).
// A linear-program phrasing is only claimed when every constraint and the objective really are
// linear, so nonlinear constrained optimisation keeps going to the calculus strategies.

import { callForm, splitTop, matchClose } from "./lang-util.js";
import { parseDetailed } from "../parse.js";
import { isLinearProblem } from "./lp.js";

const REL = (s) => s.replace(/≤|=<|⩽/g, "<=").replace(/≥|=>|⩾/g, ">=");
function constraints(s) {
  const raw = splitTop(REL(s), [",", ";", " and "]).map((x) => x.trim()).filter(Boolean);
  const out = []; let pending = [];
  for (const c of raw) {
    if (/^[a-z]\d*$/i.test(c)) { pending.push(c); continue; }
    if (/^(?:(?:[a-z]\d*\s*,?\s*)+\s+)?(?:are\s+|is\s+)?(?:all\s+)?(?:integers?|integral|integer-valued)$/i.test(c)) { pending = []; out.push({ integer: true }); continue; }
    const m = c.match(/^([a-z]\d*)\s*(<=|>=|=)\s*(.+)$/i);
    if (pending.length && m) { for (const v of pending) out.push(`${v} ${m[2]} ${m[3]}`); pending = []; }
    else if (pending.length) return null;
    const ints = c.match(/^(?:([a-z](?:\s*,\s*[a-z])*(?:\s*(?:,\s*)?(?:and\s+)?[a-z])?)\s+)?(?:are\s+|is\s+)?(?:all\s+)?(?:integers?|integral|integer-valued)$/i);
    if (ints) { out.push({ integer: true }); continue; }
    if (!/<=|>=|=/.test(c)) return null;
    out.push(c);
  }
  if (pending.length) return null;
  return out;
}
function objective(s) { return s.replace(/^[a-zA-Z]\s*=\s*/, "").trim(); }
function build(sense, obj, cons, integer) {
  const cs = cons.filter((c) => typeof c === "string");
  const isInt = integer || cons.some((c) => c && c.integer);
  const math = `${isInt ? "intprog" : "linprog"}(${sense === "max" ? "objmax" : "objmin"}(${obj}), ${cs.join(", ")})`;
  try { if (!isLinearProblem(parseDetailed(math).node)) return null; } catch (_) { return null; }
  return { math, interpretation: `${isInt ? "Integer" : "Linear"} program: ${sense === "max" ? "maximise" : "minimise"} ${obj}` };
}

export function recogniseLP(text) {
  let t = text;
  const cf = callForm(t);
  if (cf && ["lp", "linprog", "ilp", "intprog"].includes(cf.name)) {
    const m = cf.args[0] && cf.args[0].match(/^(maximi[sz]e|minimi[sz]e|max|min)\s+(.+)$/i);
    if (!m) return null;
    const cons = constraints(cf.args.slice(1).join(", "));
    if (!cons) return null;
    return build(/^max/i.test(m[1]) ? "max" : "min", objective(m[2]), cons, /^(ilp|intprog)$/.test(cf.name));
  }
  if (cf && ["matrixgame", "zerosum", "game"].includes(cf.name) && cf.args.length === 1 && /^\[\[/.test(cf.args[0])) return { math: `matrixgame(${cf.args[0]})`, interpretation: "Zero-sum matrix game" };
  if (cf && ["nash", "nashequilibria", "bimatrix"].includes(cf.name) && cf.args.length === 2 && cf.args.every((a) => /^\[\[/.test(a))) return { math: `nashequilibria(${cf.args[0]}, ${cf.args[1]})`, interpretation: "Nash equilibria of the bimatrix game" };
  let m;
  let integer = false;
  if ((m = t.match(/^(?:integer (?:linear )?programming|ilp|integer program)\s*:?\s*(.+)$/i))) { integer = true; t = m[1]; }
  if ((m = t.match(/^(maximi[sz]e|minimi[sz]e|max|min)\s+(.+?)\s+(?:subject to|s\.?\s?t\.?|such that|with constraints|given)\s*:?\s*(.+)$/i))) {
    const cons = constraints(m[3]);
    if (!cons) return null;
    return build(/^max/i.test(m[1]) ? "max" : "min", objective(m[2]), cons, integer);
  }
  // games
  if (/\bnash\b/i.test(t)) {
    const ms = matrices(t);
    if (ms.length === 2) return { math: `nashequilibria(${ms[0]}, ${ms[1]})`, interpretation: "Nash equilibria of the bimatrix game" };
    return null;
  }
  if (/\b(?:zero[- ]sum|matrix game|payoff matrix|game)\b/i.test(t) && /\b(?:value|solve|optimal strateg)/i.test(t)) {
    const ms = matrices(t);
    if (ms.length === 1) return { math: `matrixgame(${ms[0]})`, interpretation: "Zero-sum matrix game" };
  }
  return null;
}
function matrices(t) {
  const out = []; let i = 0;
  while ((i = t.indexOf("[[", i)) >= 0) { const j = matchClose(t, i); if (j < 0) break; out.push(t.slice(i, j + 1)); i = j + 1; }
  return out;
}
