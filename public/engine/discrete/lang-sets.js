// Set, counting, relation and function phrasings -> canonical commands (see sets.js).

import { callForm, splitTop, matchClose, setText, elemText } from "./lang-util.js";

// ---------------------------------------------------------------- set expressions
const OPWORDS = [
  [/^(?:∪|union|cup|or)\b/i, "SUNION", 1], [/^(?:∩|intersect(?:ion)?|cap)\b/i, "SINTER", 2],
  [/^(?:symmetric difference|symdiff|Δ|⊕|△)/i, "SSYMDIFF", 1], [/^(?:minus|\\|-|−)/, "SMINUS", 1],
  [/^(?:×|x(?=\s*[{(A-Z])|times\b)/, "SCART", 3],
];
function exprTokens(s, defs) {
  const toks = []; let i = 0;
  while (i < s.length) {
    if (/\s/.test(s[i])) { i++; continue; }
    const rest = s.slice(i);
    if (s[i] === "{") { const j = matchClose(s, i); if (j < 0) return null; const st = setText(s.slice(i, j + 1)); if (!st) return null; toks.push({ set: st }); i = j + 1; continue; }
    if (s[i] === "(" || s[i] === ")") { toks.push(s[i]); i++; continue; }
    const op = OPWORDS.find(([re]) => re.test(rest));
    if (op) { toks.push({ op: op[1], prec: op[2] }); i += rest.match(op[0])[0].length; continue; }
    const m = rest.match(/^([A-Z])(?:'|ᶜ|\^c)?(?![a-z])/);
    if (m && defs[m[1]]) { let t = { set: defs[m[1]] }; if (/['ᶜ]|\^c/.test(m[0])) { if (!defs.U) return null; t = { set: `SCOMPL(${defs[m[1]]}, ${defs.U})` }; } toks.push(t); i += m[0].length; continue; }
    return null;
  }
  return toks;
}
function setExpr(s, defs = {}) {
  const toks = exprTokens(s, defs);
  if (!toks || !toks.length) return null;
  let p = 0;
  const prim = () => { const t = toks[p++]; if (!t) throw new Error("end"); if (t === "(") { const v = bin(0); if (toks[p++] !== ")") throw new Error("paren"); return v; } if (t.set) return t.set; throw new Error("unexpected"); };
  function bin(minPrec) {
    let lhs = prim();
    for (;;) {
      const t = toks[p];
      if (!t || !t.op || t.prec < minPrec) return lhs;
      p++;
      const rhs = bin(t.prec + (t.op === "SMINUS" ? 1 : 0));
      lhs = `${t.op}(${lhs}, ${rhs})`;
    }
  }
  try { const v = bin(0); if (p !== toks.length) return null; return v; } catch (_) { return null; }
}
// "A = {..}, B = {..}" definitions anywhere in the text
function definitions(t) {
  const defs = {};
  const re = /\b([A-Z])\s*=\s*\{/g; let m;
  while ((m = re.exec(t))) { const open = m.index + m[0].length - 1; const close = matchClose(t, open); if (close < 0) continue; const st = setText(t.slice(open, close + 1)); if (st) defs[m[1]] = st; }
  return defs;
}

const FRIENDLY_SET = { powerset: "SPOWER", union: "SUNION", intersect: "SINTER", intersection: "SINTER", setminus: "SMINUS", symdiff: "SSYMDIFF", cartesian: "SCART", complement: "SCOMPL", setcalc: null, cardinality: "card" };

export function recogniseSets(text) {
  const t = text;
  const cf = callForm(t);
  if (cf) {
    if (cf.name in FRIENDLY_SET) {
      const sets = cf.args.map((a) => setExpr(a, {}));
      if (sets.some((x) => !x) || !sets.length) return null;
      const op = FRIENDLY_SET[cf.name];
      if (op === "card" || op === null) return sets.length === 1 ? { math: `setcalc(${sets[0]})`, interpretation: "Set calculation" } : null;
      return { math: `setcalc(${op}(${sets.join(", ")}))`, interpretation: "Set calculation" };
    }
    if (cf.name === "relation" || cf.name === "relprops") {
      const r = setText(cf.args[0] || ""), d = cf.args[1] ? setText(cf.args[1]) : null;
      if (!r || (cf.args[1] && !d) || cf.args.length > 2) return null;
      return { math: `relprops(${r}${d ? `, ${d}` : ""})`, interpretation: "Properties of the relation" };
    }
    if (cf.name === "func" || cf.name === "funcprops" || cf.name === "function") {
      const parts = cf.args.map(setText);
      if (!parts.length || parts.some((x) => !x) || parts.length > 3) return null;
      return { math: `funcprops(${parts.join(", ")})`, interpretation: "Properties of the function" };
    }
    if (cf.name === "compose" || cf.name === "fcompose") {
      const parts = cf.args.map(setText);
      if (parts.length !== 2 || parts.some((x) => !x)) return null;
      return { math: `fcompose(${parts.join(", ")})`, interpretation: "Composition f ∘ g" };
    }
  }
  return recogniseCounting(t) || recogniseRelations(t) || recogniseSetWords(t);
}

function recogniseCounting(t) {
  let m;
  if ((m = t.match(/^how many (?:positive )?integers (?:from|between) (\d+) (?:to|and|through) (\d+)(?: inclusive)? are (not )?divisible by ((?:\d+\s*,\s*)*\d+)(?:,)?\s*(or|and|nor)\s*(\d+)$/i))) {
    const ds = [...m[4].split(",").map((x) => x.trim()).filter(Boolean), m[6]];
    const mode = m[3] ? (m[5].toLowerCase() === "and" ? null : 0) : m[5].toLowerCase() === "and" ? 2 : m[5].toLowerCase() === "or" ? 1 : null;
    if (mode === null) return null;
    return { math: `divcount(${m[1]}, ${m[2]}, [${ds.join(", ")}], ${mode})`, interpretation: `Integers from ${m[1]} to ${m[2]} ${m[3] ? "not " : ""}divisible by ${ds.join(", ")}` };
  }
  if ((m = t.match(/^how many (?:positive )?integers (?:from|between) (\d+) (?:to|and|through) (\d+)(?: inclusive)? are (not )?divisible by (\d+)$/i))) {
    return { math: `divcount(${m[1]}, ${m[2]}, [${m[4]}], ${m[3] ? 0 : 1})`, interpretation: "Divisibility count" };
  }
  // |A| = 30, |B| = 25, |A ∩ B| = 10, find |A ∪ B|
  if (/\|\s*[A-E](?:\s*(?:∪|∩|u|n|union|intersect)\s*[A-E])+\s*\|/.test(t) && /(?:find|what is|compute)\s*\|/i.test(t)) {
    const target = t.match(/(?:find|what is|compute)\s*\|\s*([A-E](?:\s*(?:∪|u|union)\s*[A-E])+)\s*\|/i);
    if (!target) return null;
    const names = target[1].split(/\s*(?:∪|u|union)\s*/i).map((x) => x.trim());
    if (new Set(names).size !== names.length) return null;
    const k = names.length;
    const pairs = [];
    const re = /\|\s*([A-E](?:\s*(?:∩|n|intersect)\s*[A-E])*)\s*\|\s*=\s*(\d+)/gi; let mm;
    while ((mm = re.exec(t))) {
      const ns = mm[1].split(/\s*(?:∩|n|intersect)\s*/i).map((x) => x.trim().toUpperCase());
      if (ns.some((x) => !names.includes(x))) return null;
      const mask = ns.reduce((acc, x) => acc | (1 << names.indexOf(x)), 0);
      pairs.push(`[${mask}, ${mm[2]}]`);
    }
    if (pairs.length !== (1 << k) - 1) return null;
    return { math: `unionsize(${k}, ${pairs.join(", ")})`, interpretation: `|${names.join(" ∪ ")}| by inclusion-exclusion` };
  }
  return null;
}

function listAfter(t, re) { const m = t.match(re); if (!m) return null; const i = m.index + m[0].length - 1; const j = matchClose(t, i); return j < 0 ? null : { text: t.slice(i, j + 1), end: j + 1 }; }

function recogniseRelations(t) {
  let m;
  // named relations on a set
  if ((m = t.match(/(?:hasse diagram|partial order|poset|relation)\b.*?\b(divisibility|divides|less than or equal|≤|<=)\b.*?\bon\s+(\{.*\})$/i)) || (m = t.match(/^(?:hasse diagram|draw the hasse diagram)\s+(?:of|for)\s+(?:the\s+)?(divisibility)\s+(?:relation|poset|order)\s+on\s+(\{.*\})$/i))) {
    const d = setText(m[2]); if (!d) return null;
    const rel = /divis|divides/i.test(m[1]) ? "reldivides(1)" : "relleq(1)";
    return { math: `relprops(${rel}, ${d})`, interpretation: "Properties of the relation" };
  }
  if ((m = t.match(/^(?:find\s+)?(?:the\s+)?equivalence classes of (?:the\s+)?(?:relation\s+)?congruen(?:ce|t) mod(?:ulo)?\s*(\d+)\s+on\s+(\{.*\})$/i))) {
    const d = setText(m[2]); if (!d) return null;
    return { math: `relprops(relcongmod(${m[1]}), ${d})`, interpretation: "Congruence classes" };
  }
  // explicit relation R = {...} on {...}
  if (/\brelation\b|\breflexive\b|\bsymmetric\b|\btransitive\b|\bantisymmetric\b|\bpartial order\b|\bequivalence\b/i.test(t) && /\(\s*[^,()]+\s*,\s*[^,()]+\s*\)/.test(t)) {
    const rel = listAfter(t, /(?:\bR\s*=\s*|relation\s+|relation\s+R\s*=\s*)\{/i);
    if (!rel) return null;
    const r = setText(rel.text); if (!r) return null;
    const rest = t.slice(rel.end);
    const dm = listAfter(rest, /\bon\s+(?:the\s+set\s+)?(?:[A-Z]\s*=\s*)?\{/i);
    const d = dm ? setText(dm.text) : null;
    if (dm && !d) return null;
    return { math: `relprops(${r}${d ? `, ${d}` : ""})`, interpretation: "Properties of the relation" };
  }
  // functions given as pairs
  if (/\b(?:injective|surjective|bijective|bijection|one-to-one|onto|one to one)\b/i.test(t)) {
    const fm = listAfter(t, /\bf\s*=\s*\{/);
    if (fm) {
      const f = setText(fm.text); if (!f) return null;
      const rest = t.slice(fm.end);
      const dm = listAfter(rest, /\bfrom\s+\{/i), cm = dm ? listAfter(rest.slice(rest.indexOf(dm.text) + dm.text.length), /\bto\s+\{/i) : null;
      const d = dm ? setText(dm.text) : null, c = cm ? setText(cm.text) : null;
      return { math: `funcprops(${f}${d ? `, ${d}` : ""}${d && c ? `, ${c}` : ""})`, interpretation: "Properties of the function" };
    }
    // formula: f(x) = <expr> ... on {dom} [to {cod}]
    if ((m = t.match(/\bf\s*\(\s*([a-z])\s*\)\s*=\s*(.+?)\s+(?:a\s+)?(?:injective|surjective|bijective|bijection|one-to-one|onto|one to one)\b.*?\bon\s+(\{[^}]*\})(?:\s+to\s+(\{[^}]*\}))?\s*$/i)) || (m = t.match(/\bf\s*\(\s*([a-z])\s*\)\s*=\s*(.+?)\s+on\s+(\{[^}]*\})(?:\s+to\s+(\{[^}]*\}))?\s+(?:injective|surjective|bijective|a bijection|one-to-one|onto)\s*$/i))) {
      const expr = m[2].replace(/\s+mod\s+(\d+)\s*$/i, (_, k) => ` mod ${k}`).replace(/^(.*)\s+mod\s+(\d+)$/i, "mod($1, $2)");
      if (!/^[\w\s+\-*^()/,]+$/.test(expr)) return null;
      const d = setText(m[3]), c = m[4] ? setText(m[4]) : null;
      if (!d) return null;
      return { math: `funcprops(fromformula(${expr}, ${m[1]}), ${d}${c ? `, ${c}` : ""})`, interpretation: "Properties of the function" };
    }
  }
  // composition
  if ((m = t.match(/^(?:compose|composition of|find the composition of|find f ∘ g for|compute f ∘ g for)\s+f\s*=\s*(\{.*\})\s+and\s+g\s*=\s*(\{.*\})$/i))) {
    const f = setText(m[1]), g = setText(m[2]);
    if (!f || !g) return null;
    return { math: `fcompose(${f}, ${g})`, interpretation: "Composition f ∘ g (apply g first)" };
  }
  return null;
}

function recogniseSetWords(t) {
  if (!t.includes("{")) return null;
  const defs = definitions(t);
  let m;
  // strip "let A = ..., B = ...;" and "where A = ..." clauses
  let body = t.replace(/^let\s+.*?;\s*/i, "").replace(/\s+(?:where|with|if)\s+[A-Z]\s*=.*$/i, "").replace(/^(?:find|compute|what is|evaluate|calculate)\s+/i, "").trim();
  if ((m = body.match(/^(?:the\s+)?power ?set of\s+(.+)$/i))) { const s = setExpr(m[1], defs); return s ? { math: `setcalc(SPOWER(${s}))`, interpretation: "Power set" } : null; }
  if ((m = body.match(/^(?:the\s+)?cartesian product of\s+(.+?)\s+and\s+(.+)$/i))) { const a = setExpr(m[1], defs), b = setExpr(m[2], defs); return a && b ? { math: `setcalc(SCART(${a}, ${b}))`, interpretation: "Cartesian product" } : null; }
  if ((m = body.match(/^(?:the\s+)?symmetric difference (?:of|between)\s+(.+?)\s+and\s+(.+)$/i))) { const a = setExpr(m[1], defs), b = setExpr(m[2], defs); return a && b ? { math: `setcalc(SSYMDIFF(${a}, ${b}))`, interpretation: "Symmetric difference" } : null; }
  if ((m = body.match(/^(?:the\s+)?(union|intersection) of\s+(.+?)\s+and\s+(.+)$/i))) { const a = setExpr(m[2], defs), b = setExpr(m[3], defs); return a && b ? { math: `setcalc(${/union/i.test(m[1]) ? "SUNION" : "SINTER"}(${a}, ${b}))`, interpretation: "Set operation" } : null; }
  if ((m = body.match(/^(?:the\s+)?complement of\s+(.+?)\s+(?:in|relative to|with respect to)\s+(?:the universe\s+)?(?:U\s*=\s*)?(.+)$/i))) { const a = setExpr(m[1], defs), b = setExpr(m[2], defs); return a && b ? { math: `setcalc(SCOMPL(${a}, ${b}))`, interpretation: "Complement" } : null; }
  if ((m = body.match(/^(?:the\s+)?(?:cardinality|size|number of elements) of\s+(.+)$/i))) { const a = setExpr(m[1], defs); return a ? { math: `setcalc(${a})`, interpretation: "Cardinality" } : null; }
  // a bare set expression with at least one operator
  const s = setExpr(body, defs);
  if (s && /^S[A-Z]+\(/.test(s)) return { math: `setcalc(${s})`, interpretation: "Set calculation" };
  void splitTop; void elemText;
  return null;
}
