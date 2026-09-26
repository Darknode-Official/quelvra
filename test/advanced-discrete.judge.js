// Judge for the advanced discrete-math probe corpus (advanced-discrete.corpus.json, produced by
// tools/quelvra-adv-discrete-oracle.py from sympy / networkx oracles).
//
// judgeCase(c) -> { cat: "correct" | "refused" | "wrong", why, result }
//   correct : every expectation holds and Quelvra's own verification passed (or a refusal was expected and happened)
//   refused : nothing was answered (the honest outcome when a request is unsupported)
//   wrong   : an answer was shown that is not what the oracle says, or was shown without passing verification
// The checks below are written independently of the engine (their own tiny parsers and evaluators).

import { readFileSync } from "node:fs";
import { dirname, join } from "node:path";
import { fileURLToPath } from "node:url";
import { solve } from "../public/engine/quelvra.js";
import { parse } from "../public/engine/parse.js";
import { toText } from "../public/engine/print.js";
import { equivalent, evalC } from "../public/engine/verify.js";

const dir = dirname(fileURLToPath(import.meta.url));
export const CORPUS = JSON.parse(readFileSync(join(dir, "advanced-discrete.corpus.json"), "utf8"));

const shown = (a) => (a.text != null ? String(a.text) : a.tree ? toText(a.tree) : "");
const norm = (s) => String(s).toLowerCase().replace(/\*\*/g, "^").replace(/[\s*]/g, "");
const findAll = (r, label) => (r.answers || []).filter((a) => a.kind !== "none" && String(a.label || "").trim().toLowerCase() === label.toLowerCase());

// ---- set text: {1, {a, b}, (1, 2)} -> canonical string with sorted members
function setCanon(s) {
  let i = 0;
  const src = String(s).replace(/∅/g, "{}");
  const ws = () => { while (/\s/.test(src[i])) i++; };
  function item() {
    ws();
    if (src[i] === "{" || src[i] === "(") {
      const open = src[i], close = open === "{" ? "}" : ")";
      i++;
      const parts = [];
      ws();
      if (src[i] === close) { i++; return open === "{" ? "{}" : "()"; }
      for (;;) {
        parts.push(item()); ws();
        if (src[i] === ",") { i++; continue; }
        if (src[i] === close) { i++; break; }
        throw new Error(`bad set text at ${i}: ${src}`);
      }
      if (open === "{") return "{" + [...new Set(parts)].sort().join(",") + "}";
      return "(" + parts.join(",") + ")";
    }
    const m = /^[^,{}()]+/.exec(src.slice(i));
    if (!m) throw new Error(`bad set text at ${i}: ${src}`);
    i += m[0].length;
    return m[0].trim().toLowerCase();
  }
  const out = item(); ws();
  if (i !== src.length) throw new Error(`trailing text in set: ${src}`);
  return out;
}

// ---- boolean formula text (∧ ∨ ¬ -> ↔ ⊕, words, & | ~ !, and SOP notation a'b + c)
function logicEval(text, env) {
  const s = String(text).trim();
  if (/^[01]$/.test(s)) return s === "1";
  if (/^[a-z'\s+]+$/i.test(s) && (s.includes("+") || s.includes("'") || /^[a-z]+$/i.test(s.replace(/\s/g, "")))) {
    // SOP: terms joined by +, each a run of letters with optional '
    return s.split("+").some((term) => {
      const lits = term.replace(/\s/g, "").match(/[a-z]'?/gi) || [];
      return lits.every((l) => (l.endsWith("'") ? !env[l[0]] : !!env[l[0]]));
    });
  }
  const toks = s.replace(/<->|↔|<=>/g, " IFF ").replace(/->|→|=>/g, " IMP ").replace(/∧|&&|&/g, " AND ").replace(/∨|\|\||\|/g, " OR ")
    .replace(/¬|~|!/g, " NOT ").replace(/⊕/g, " XOR ").replace(/\(/g, " ( ").replace(/\)/g, " ) ").trim().split(/\s+/)
    .map((t) => ({ and: "AND", or: "OR", not: "NOT", xor: "XOR", implies: "IMP", iff: "IFF", true: "1", false: "0", t: "1", f: "0" }[t.toLowerCase()] || t));
  let p = 0;
  const peek = () => toks[p];
  function prim() {
    const t = toks[p++];
    if (t === "NOT") return !prim();
    if (t === "(") { const v = iff(); if (toks[p++] !== ")") throw new Error("paren"); return v; }
    if (t === "1") return true;
    if (t === "0") return false;
    if (!(t in env)) throw new Error(`unknown variable ${t} in ${s}`);
    return env[t];
  }
  function and() { let v = prim(); while (peek() === "AND") { p++; const w = prim(); v = v && w; } return v; }
  function xor() { let v = and(); while (peek() === "XOR") { p++; v = v !== and(); } return v; }
  function or() { let v = xor(); while (peek() === "OR") { p++; const w = xor(); v = v || w; } return v; }
  function imp() { const v = or(); if (peek() === "IMP") { p++; return !v || imp(); } return v; }
  function iff() { let v = imp(); while (peek() === "IFF") { p++; v = v === imp(); } return v; }
  const v = iff();
  if (p !== toks.length) throw new Error(`trailing tokens in ${s}`);
  return v;
}

function checkOne(e, r) {
  const [kind] = e;
  if (kind === "status") return r.solutionStatus === e[1] ? null : `solutionStatus ${r.solutionStatus}, expected ${e[1]}`;
  if (kind === "refuse") return null;
  const label = e[1];
  let cands = findAll(r, label);
  // an unlabelled single answer (a plain value) is judged on its value
  if (!cands.length && kind === "eq") cands = (r.answers || []).filter((a) => a.kind !== "none" && !a.label);
  if (!cands.length) return `no answer labelled "${label}" (labels: ${(r.answers || []).map((a) => a.label).join(" | ")})`;
  const errs = [];
  for (const a of cands) {
    const err = checkAnswer(e, a);
    if (!err) return null;
    errs.push(err);
  }
  return errs[0];
}
function checkAnswer(e, a) {
  const [kind, label] = e;
  const txt = shown(a);
  switch (kind) {
    case "eq": {
      const want = String(e[2]);
      if (norm(txt) === norm(want)) return null;
      if (a.tree) {
        try {
          const w = parse(want.replace(/\*\*/g, "^"));
          const q = equivalent(a.tree, w);
          if (q.status.startsWith("equivalent")) return null;
        } catch (_) { /* fall through */ }
      }
      return `${label}: got "${txt}", expected "${want}"`;
    }
    case "set": {
      try { return setCanon(txt) === setCanon(e[2]) ? null : `${label}: got ${txt}, expected ${e[2]}`; } catch (err) { return `${label}: ${err.message}`; }
    }
    case "seq": {
      const [, , v, start, terms] = e;
      if (!a.tree) return `${label}: no formula`;
      for (let i = 0; i < terms.length; i++) {
        const c = evalC(a.tree, { [v]: { re: start + i, im: 0 } }, "complex");
        const want = Number(terms[i]);
        if (!c || !Number.isFinite(c.re) || Math.abs(c.re - want) > 1e-7 * Math.max(1, Math.abs(want)) || Math.abs(c.im) > 1e-6 * Math.max(1, Math.abs(want))) return `${label}: term ${start + i} is ${c && c.re}, expected ${want} (${txt})`;
      }
      return null;
    }
    case "path": {
      const [, , edges, directed, s, t, dist] = e;
      const verts = txt.split(/\s*(?:->|→|,)\s*/).map((x) => x.trim()).filter(Boolean);
      if (verts[0] !== String(s) || verts[verts.length - 1] !== String(t)) return `path ${txt} does not run from ${s} to ${t}`;
      let total = 0;
      for (let i = 0; i + 1 < verts.length; i++) {
        const ws = edges.filter(([u, v]) => (String(u) === verts[i] && String(v) === verts[i + 1]) || (!directed && String(v) === verts[i] && String(u) === verts[i + 1])).map((x) => (x.length > 2 ? x[2] : 1));
        if (!ws.length) return `path ${txt} uses a missing edge ${verts[i]}-${verts[i + 1]}`;
        total += Math.min(...ws);
      }
      return total === dist ? null : `path ${txt} has length ${total}, expected ${dist}`;
    }
    case "topo": {
      const [, , edges] = e;
      const order = txt.split(/\s*(?:,|->|→)\s*/).map((x) => x.trim()).filter(Boolean);
      const pos = new Map(order.map((v, i) => [v, i]));
      const vs = new Set(edges.flat().map(String));
      if (pos.size !== vs.size || [...vs].some((v) => !pos.has(v))) return `order ${txt} is not a permutation of the vertices`;
      for (const [u, v] of edges) if (!(pos.get(String(u)) < pos.get(String(v)))) return `order ${txt} puts ${v} before ${u}`;
      return null;
    }
    case "logic": {
      const [, , vars, rows, dc = []] = e;
      for (let i = 0; i < 2 ** vars.length; i++) {
        if (dc.includes(i)) continue;
        const env = {};
        vars.forEach((v, j) => { env[v] = !!((i >> (vars.length - 1 - j)) & 1); });
        let val;
        try { val = logicEval(txt, env); } catch (err) { return `${label}: cannot read "${txt}": ${err.message}`; }
        if (val !== rows.includes(i)) return `${label}: "${txt}" is wrong on row ${i}`;
      }
      return null;
    }
    default: return `unknown expectation ${kind}`;
  }
}

export function judgeCase(c, options = {}) {
  let r;
  try { r = solve(c.input, { timeLimit: options.timeLimit || 20000 }); } catch (err) { return { cat: "wrong", why: `crash: ${err.message}`, result: null }; }
  const answered = r.ok && (r.answers || []).some((a) => a.kind !== "none");
  const wantRefuse = c.expect.some((e) => e[0] === "refuse");
  if (wantRefuse) return answered ? { cat: "wrong", why: `expected a refusal, got ${(r.answers || []).map((a) => `${a.label}: ${shown(a)}`).join("; ")}`, result: r } : { cat: "correct", why: "", result: r };
  if (!answered) return { cat: "refused", why: (r.error && r.error.message) || (r.answers || []).map((a) => a.label).join("; ") + " " + (r.attempts || []).map((a) => `${a.strategy}: ${a.reason}`).join("; "), result: r };
  if (!r.verification || r.verification.status !== "passed") return { cat: "wrong", why: `answer shown without passed verification (${r.verification && r.verification.status})`, result: r };
  for (const e of c.expect) {
    const err = checkOne(e, r);
    if (err) return { cat: "wrong", why: err, result: r };
  }
  return { cat: "correct", why: "", result: r };
}

export function judgeAll(filter = "") {
  const rows = [];
  for (const c of CORPUS) {
    if (filter && c.area !== filter && !c.input.includes(filter)) continue;
    const t0 = Date.now();
    const v = judgeCase(c);
    rows.push({ ...c, ...v, ms: Date.now() - t0 });
  }
  return rows;
}
