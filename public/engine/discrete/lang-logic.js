// Propositional-logic phrasings -> canonical logic commands (see logic.js).

import { callForm, splitTop, lab } from "./lang-util.js";

// ---------------------------------------------------------------- formula text -> canonical call text
const WORD_OPS = { and: "AND", or: "OR", not: "NOT", xor: "XOR", implies: "IMP", iff: "IFF", nand: "NAND", nor: "NOR", true: "1", false: "0" };
function lex(s) {
  const toks = [];
  const re = /\s*(<->|<=>|↔|->|=>|→|&&|\|\||\/\\|\\\/|[&|∧∨¬~!⊕()']|[A-Za-z][A-Za-z0-9_]*|\d+)/y;
  let m; re.lastIndex = 0;
  const src = s.trim();
  while (re.lastIndex < src.length) {
    const at = re.lastIndex;
    m = re.exec(src);
    if (!m || m.index !== at) return null;
    const t = m[1];
    if (/^(<->|<=>|↔)$/.test(t)) toks.push("IFF");
    else if (/^(->|=>|→)$/.test(t)) toks.push("IMP");
    else if (/^(&&|&|∧|\/\\)$/.test(t)) toks.push("AND");
    else if (/^(\|\||\||∨|\\\/)$/.test(t)) toks.push("OR");
    else if (/^[¬~!]$/.test(t)) toks.push("NOT");
    else if (t === "⊕") toks.push("XOR");
    else if (t === "(" || t === ")" || t === "'") toks.push(t);
    else if (/^\d+$/.test(t)) { if (t !== "0" && t !== "1") return null; toks.push(t); }
    else if (WORD_OPS[t.toLowerCase()]) toks.push(WORD_OPS[t.toLowerCase()]);
    else if (/^[A-Za-z]\d*$/.test(t)) toks.push({ v: t });
    else return null; // an unknown word: not a formula
    // skip spaces between tokens handled by the regex
  }
  return toks;
}
// precedence: NOT > AND/NAND > XOR > OR/NOR > IMP (right) > IFF
export function formulaText(s) {
  const toks = lex(s);
  if (!toks || !toks.length) return null;
  let p = 0;
  const peek = () => toks[p];
  function prim() {
    const t = toks[p++];
    if (t === undefined) throw new Error("end");
    let out;
    if (t === "NOT") out = `LNOT(${prim()})`;
    else if (t === "(") { out = iff(); if (toks[p++] !== ")") throw new Error("paren"); }
    else if (t === "1" || t === "0") out = t;
    else if (t && t.v) out = lab(t.v);
    else throw new Error("unexpected");
    while (peek() === "'") { p++; out = `LNOT(${out})`; }
    return out;
  }
  const chain = (next, ops) => () => {
    let v = next();
    while (ops[peek()]) { const op = ops[peek()]; const args = [v]; while (peek() === op.tok) { p++; args.push(next()); } v = `${op.name}(${args.join(", ")})`; }
    return v;
  };
  const and = chain(prim, { AND: { tok: "AND", name: "LAND" }, NAND: { tok: "NAND", name: "LNAND" } });
  const xor = chain(and, { XOR: { tok: "XOR", name: "LXOR" } });
  const or = chain(xor, { OR: { tok: "OR", name: "LOR" }, NOR: { tok: "NOR", name: "LNOR" } });
  function imp() { const v = or(); if (peek() === "IMP") { p++; return `LIMP(${v}, ${imp()})`; } return v; }
  function iff() { let v = imp(); while (peek() === "IFF") { p++; v = `LIFF(${v}, ${imp()})`; } return v; }
  try {
    const out = iff();
    if (p !== toks.length) return null;
    return out;
  } catch (_) { return null; }
}
// a formula must use a connective or be a lone variable, and must not look like arithmetic
const looksLogical = (s) => /\b(?:and|or|not|xor|implies|iff|nand|nor)\b|<->|->|=>|[∧∨¬⊕↔→~&|!]/i.test(s);

// split "F and G" (two formulas joined by a top-level " and ") unambiguously
function splitPair(s, sep) {
  const idx = [];
  let depth = 0;
  for (let i = 0; i < s.length; i++) { if (s[i] === "(") depth++; else if (s[i] === ")") depth--; else if (depth === 0 && s.startsWith(sep, i)) idx.push(i); }
  const ok = [];
  for (const i of idx) { const a = formulaText(s.slice(0, i)), b = formulaText(s.slice(i + sep.length)); if (a && b) ok.push([a, b]); }
  return ok.length === 1 ? ok[0] : null;
}

function minterms(s) {
  const m = s.match(/(?:Σ|sum\s*)?\bm\s*\(([\d,\s]+)\)(?:\s*\+?\s*(?:,\s*)?\bd\s*\(([\d,\s]+)\))?/i);
  if (!m) return null;
  const on = m[1].split(",").map((x) => x.trim()).filter(Boolean);
  const dc = m[2] ? m[2].split(",").map((x) => x.trim()).filter(Boolean) : [];
  return { on, dc };
}
function minsopCall(mt, varsList) {
  const parts = [`mterms(${mt.on.join(", ")})`];
  if (mt.dc.length) parts.push(`dcterms(${mt.dc.join(", ")})`);
  if (varsList) parts.push(`bvars(${varsList.map(lab).join(", ")})`);
  return `minsop(${parts.join(", ")})`;
}

const FRIENDLY = { truthtable: "truthtable", tautology: "istautology", istautology: "istautology", contradiction: "istautology", satisfiable: "issatisfiable", issatisfiable: "issatisfiable", sat: "issatisfiable", logicequiv: "logicequiv", equivalent: "logicequiv", cnf: "cnf", dnf: "dnf", minsop: "minsop", validargument: "validargument", valid: "validargument" };

export function recogniseLogic(text) {
  const cf = callForm(text);
  if (cf && FRIENDLY[cf.name]) {
    const cmd = FRIENDLY[cf.name];
    if (cmd === "minsop") {
      const mt = minterms(text);
      if (mt) return { math: minsopCall(mt, null), interpretation: "Minimal sum of products" };
      const f = cf.args.length === 1 && formulaText(cf.args[0]);
      return f ? { math: `minsop(${f})`, interpretation: "Minimal sum of products" } : null;
    }
    if (cmd === "validargument") {
      const inner = text.slice(text.indexOf("(") + 1, -1);
      const parts = inner.split(/;|\btherefore\b|∴|\|-|⊢/);
      if (parts.length !== 2) return null;
      const prem = splitTop(parts[0]).map(formulaText), c = formulaText(parts[1]);
      if (!c || prem.some((x) => !x)) return null;
      return { math: `validargument(${[...prem, c].join(", ")})`, interpretation: "Is the argument valid?" };
    }
    const fs = cf.args.map(formulaText);
    if (fs.some((x) => !x)) return null;
    if (cmd === "logicequiv" ? fs.length !== 2 : fs.length !== 1) return null;
    return { math: `${cmd}(${fs.join(", ")})`, interpretation: cmd };
  }
  return recogniseLogicWords(text);
}

function recogniseLogicWords(t) {
  let m;
  const one = (cmd, s, interp) => { if (!looksLogical(s) && !/^[A-Za-z]\d*$/.test(s.trim())) return null; const f = formulaText(s); return f ? { math: `${cmd}(${f})`, interpretation: interp } : null; };
  // boolean function minimisation with minterms
  if (/\b(?:minimi[sz]e|simplify|minimal|reduce)\b/i.test(t) && /\bm\s*\(/.test(t) && /(?:boolean|function|sum|Σ|minterm|sop|\bf\s*\()/i.test(t)) {
    const mt = minterms(t);
    if (!mt) return null;
    const v = t.match(/\b[fF]\s*\(\s*([A-Za-z](?:\s*,\s*[A-Za-z])*)\s*\)/);
    return { math: minsopCall(mt, v ? v[1].split(",").map((x) => x.trim()) : null), interpretation: "Minimal sum of products" };
  }
  if ((m = t.match(/^(?:simplify|minimi[sz]e)\s+(?:the\s+)?(?:boolean|logic(?:al)?)\s+(?:expression|function|formula)\s*:?\s*(.+)$/i))) return one("minsop", m[1], "Minimal sum of products");
  // truth table
  if ((m = t.match(/^(?:(?:make|construct|build|write|give|show|find)\s+(?:me\s+)?)?(?:a\s+|the\s+)?truth table\s+(?:of|for)\s*:?\s*(.+)$/i))) return one("truthtable", m[1], "Truth table");
  // normal forms
  if ((m = t.match(/^(?:convert|write|put|express|transform|rewrite)\s+(.+?)\s+(?:to|into|in)\s+(?:the\s+)?(conjunctive|disjunctive)\s+normal\s+form$/i))) return one(m[2].toLowerCase().startsWith("c") ? "cnf" : "dnf", m[1], "Normal form");
  if ((m = t.match(/^(?:(?:find|give|what is)\s+)?(?:the\s+)?(conjunctive|disjunctive|cnf|dnf)(?:\s+normal\s+form)?\s+(?:of|for)\s+(.+)$/i))) return one(/^c/i.test(m[1]) ? "cnf" : "dnf", m[2], "Normal form");
  // tautology / contradiction / satisfiable
  if ((m = t.match(/^(?:is|determine whether|check (?:if|whether))\s+(.+?)\s+(?:is\s+)?(?:a\s+)?(tautology|contradiction|contingency|satisfiable|valid formula)(?:\s*,.*|\s+or\s+.*)?$/i))) {
    const cmd = /satisfiable/i.test(m[2]) ? "issatisfiable" : "istautology";
    return one(cmd, m[1], cmd);
  }
  // equivalence
  if (/\bequivalent\b/i.test(t)) {
    if ((m = t.match(/^(?:is|check (?:if|whether))\s+(.+?)\s+(?:logically\s+)?equivalent\s+to\s+(.+)$/i))) {
      const a = formulaText(m[1]), b = formulaText(m[2]);
      if (a && b && (looksLogical(m[1]) || looksLogical(m[2]))) return { math: `logicequiv(${a}, ${b})`, interpretation: "Are the formulas equivalent?" };
      return null;
    }
    if ((m = t.match(/^(?:are|check (?:if|whether))\s+(.+?)\s+(?:logically\s+)?equivalent$/i))) {
      const pair = splitPair(m[1], " and ");
      if (pair) return { math: `logicequiv(${pair[0]}, ${pair[1]})`, interpretation: "Are the formulas equivalent?" };
    }
    return null;
  }
  // arguments
  if (/\b(?:argument|therefore|premises?|conclusion|∴)\b/i.test(t) && /\bvalid\b/i.test(t)) {
    let prem = null, concl = null;
    if ((m = t.match(/^is\s+(?:the|this)\s+argument\s+(?:valid\s*:?\s*)?(.+?)\s*(?:,\s*)?(?:therefore|∴|hence|so)\s+(.+?)(?:\s+valid)?$/i))) { prem = m[1]; concl = m[2]; }
    else if ((m = t.match(/^premises?\s*:?\s*(.+?)\s*[;.]\s*conclusion\s*:?\s*(.+?)(?:\s*[.;,]\s*(?:is (?:it|the argument) valid))?$/i))) { prem = m[1]; concl = m[2]; }
    if (!prem) return null;
    const ps = splitTop(prem.replace(/,\s*$/, "")).map(formulaText), c = formulaText(concl);
    if (!c || !ps.length || ps.some((x) => !x)) return null;
    return { math: `validargument(${[...ps, c].join(", ")})`, interpretation: "Is the argument valid?" };
  }
  return null;
}
