// Quelvra propositional logic and finite sets.
//
//   truth table of p and not q          is p or not p a tautology       is p and not p a contradiction
//   simplify not (p and q)              is p -> q equivalent to not p or q
//   {1, 2, 3} union {3, 4}              {1, 2, 3} intersect {2, 3, 4}    {1, 2, 3} minus {2}
//   power set of {a, b, c}              number of subsets of {1, 2, 3, 4}
//
// solveLogic(text) returns a Solver result, or null when the text is not a logic or set request.
// Solver and verifier are separate: the solver evaluates formulas row by row (recursion over the
// syntax tree) and minimises with Quine-McCluskey; the verifier re-parses the printed answer and
// evaluates both sides bit-parallel over all rows at once (one BigInt mask per subformula).

import * as X from "./expr.js";

const OPS = [
  ["<->", "iff"], ["<=>", "iff"], ["↔", "iff"], ["->", "imp"], ["=>", "imp"], ["→", "imp"],
  ["&&", "and"], ["||", "or"], ["∧", "and"], ["∨", "or"], ["&", "and"], ["|", "or"], ["⊕", "xor"],
  ["¬", "not"], ["~", "not"], ["!", "not"], ["(", "("], [")", ")"],
];
const WORDS = { and: "and", or: "or", not: "not", xor: "xor", implies: "imp", iff: "iff", nand: "nand", nor: "nor", true: "T", false: "F", T: "T", F: "F" };
const MAX_VARS = 8;

function tokenize(s) {
  const out = [];
  let i = 0;
  while (i < s.length) {
    if (/\s/.test(s[i])) { i++; continue; }
    const op = OPS.find(([t]) => s.startsWith(t, i));
    if (op) { out.push(op[1]); i += op[0].length; continue; }
    const m = /^[A-Za-z]+/.exec(s.slice(i));
    if (!m) return null;
    const w = m[0];
    if (w === "if" && /^\s*and\s+only\s+if\b/.test(s.slice(i + 2))) { out.push("iff"); i += /^if\s*and\s+only\s+if/.exec(s.slice(i))[0].length; continue; }
    if (WORDS[w] !== undefined || WORDS[w.toLowerCase()] !== undefined && w.length > 1) out.push(WORDS[w] || WORDS[w.toLowerCase()]);
    else if (w.length === 1) out.push({ v: w });
    else return null;
    i += w.length;
  }
  return out;
}
// precedence: not > and/nand > xor > or/nor > imp (right assoc) > iff
function parseFormula(s) {
  const toks = tokenize(s);
  if (!toks || !toks.length) return null;
  let p = 0;
  const peek = () => toks[p];
  const bin = (next, ops) => () => {
    let l = next();
    while (ops.includes(peek())) { const o = toks[p++]; l = { op: o, a: l, b: next() }; }
    return l;
  };
  const atom = () => {
    const t = toks[p++];
    if (t === "not") return { op: "not", a: atom() };
    if (t === "(") { const e = iff(); if (toks[p++] !== ")") throw 0; return e; }
    if (t === "T" || t === "F") return { c: t === "T" };
    if (t && t.v) return { v: t.v };
    throw 0;
  };
  const and = bin(atom, ["and", "nand"]);
  const xor = bin(and, ["xor"]);
  const or = bin(xor, ["or", "nor"]);
  const imp = () => { const l = or(); if (peek() === "imp") { p++; return { op: "imp", a: l, b: imp() }; } return l; };
  const iff = bin(imp, ["iff"]);
  try { const e = iff(); return p === toks.length ? e : null; } catch (_) { return null; }
}
const varsOf = (e, s = new Set()) => { if (e.v) s.add(e.v); if (e.a) varsOf(e.a, s); if (e.b) varsOf(e.b, s); return s; };
const hasOp = (e) => !!e.op;

// solver: row-by-row recursive evaluation
function evalRow(e, env) {
  if (e.c !== undefined) return e.c;
  if (e.v) return env[e.v];
  const a = evalRow(e.a, env);
  if (e.op === "not") return !a;
  const b = evalRow(e.b, env);
  switch (e.op) {
    case "and": return a && b;
    case "or": return a || b;
    case "xor": return a !== b;
    case "imp": return !a || b;
    case "iff": return a === b;
    case "nand": return !(a && b);
    case "nor": return !(a || b);
  }
  return false;
}
const rows = (vars) => Array.from({ length: 1 << vars.length }, (_, r) => Object.fromEntries(vars.map((v, i) => [v, !((r >> (vars.length - 1 - i)) & 1)])));

// verifier: bit-parallel evaluation; bit r of each mask is the value on row r
function evalMask(e, vars) {
  const n = vars.length, R = 1 << n, ALL = (1n << BigInt(R)) - 1n;
  const varMask = (i) => { let m = 0n; for (let r = 0; r < R; r++) if (!((r >> (n - 1 - i)) & 1)) m |= 1n << BigInt(r); return m; };
  const go = (t) => {
    if (t.c !== undefined) return t.c ? ALL : 0n;
    if (t.v) return varMask(vars.indexOf(t.v));
    const a = go(t.a);
    if (t.op === "not") return ALL ^ a;
    const b = go(t.b);
    return { and: a & b, or: a | b, xor: a ^ b, imp: (ALL ^ a) | b, iff: ALL ^ (a ^ b), nand: ALL ^ (a & b), nor: ALL ^ (a | b) }[t.op];
  };
  return go(e);
}

function show(e) {
  if (e.c !== undefined) return e.c ? "true" : "false";
  if (e.v) return e.v;
  if (e.op === "not") return "not " + (e.a.op && e.a.op !== "not" ? `(${show(e.a)})` : show(e.a));
  const word = e.op === "imp" ? "->" : e.op === "iff" ? "<->" : e.op;
  // a child of the same associative operator needs no brackets; every other compound child gets them
  const side = (c) => (c.op && c.op !== "not" && !(c.op === e.op && ["and", "or"].includes(e.op)) ? `(${show(c)})` : show(c));
  return `${side(e.a)} ${word} ${side(e.b)}`;
}

// Quine-McCluskey with an exact minimum cover (small inputs only)
function minimise(e, vars) {
  const n = vars.length;
  const on = rows(vars).map((env, r) => (evalRow(e, env) ? r : -1)).filter((r) => r >= 0);
  if (!on.length) return { c: false };
  if (on.length === 1 << n) return { c: true };
  // implicant: [value bits, care mask] over n bits, bit (n-1-i) is variable i; row r has var i true when that bit is 0
  let cur = new Map(on.map((r) => [`${r}|${(1 << n) - 1}`, { v: r, m: (1 << n) - 1 }]));
  const primes = [];
  while (cur.size) {
    const next = new Map(), used = new Set();
    const list = [...cur.values()];
    for (let i = 0; i < list.length; i++) for (let j = i + 1; j < list.length; j++) {
      const A = list[i], B = list[j];
      if (A.m !== B.m) continue;
      const d = (A.v ^ B.v) & A.m;
      if (d && !(d & (d - 1))) {
        const m = A.m & ~d, v = A.v & m;
        next.set(`${v}|${m}`, { v, m });
        used.add(i); used.add(j);
      }
    }
    list.forEach((t, i) => { if (!used.has(i)) primes.push(t); });
    cur = next;
  }
  const covers = (t, r) => (r & t.m) === t.v;
  const lits = (t) => { let c = 0; for (let i = 0; i < n; i++) if (t.m & (1 << (n - 1 - i))) c++; return c; };
  // smallest cover by increasing subset size (primes are few for <= 8 variables in practice)
  let best = null;
  const P = primes.slice(0, 20);
  const search = (k, start, chosen) => {
    if (chosen.length === k) {
      if (on.every((r) => chosen.some((t) => covers(t, r)))) {
        const cost = chosen.reduce((s, t) => s + lits(t), 0);
        if (!best || cost < best.cost) best = { chosen: chosen.slice(), cost };
      }
      return;
    }
    for (let i = start; i < P.length; i++) { chosen.push(P[i]); search(k, i + 1, chosen); chosen.pop(); }
  };
  for (let k = 1; k <= P.length && !best; k++) search(k, 0, []);
  if (!best) return null;
  const term = (t) => {
    const ls = [];
    for (let i = 0; i < n; i++) {
      const bit = 1 << (n - 1 - i);
      if (t.m & bit) ls.push(t.v & bit ? { op: "not", a: { v: vars[i] } } : { v: vars[i] });
    }
    return ls.reduce((x, y) => ({ op: "and", a: x, b: y }));
  };
  const terms = best.chosen.map(term).sort((x, y) => (show(x) < show(y) ? -1 : 1));
  return terms.reduce((x, y) => ({ op: "or", a: x, b: y }));
}
const size = (e) => (e.c !== undefined || e.v ? 1 : 1 + size(e.a) + (e.b ? size(e.b) : 0));

// ---------------------------------------------------------------- finite sets
function parseSet(s) {
  const m = /^\{\s*([^{}]*)\}$/.exec(s.trim());
  if (!m) return null;
  const items = m[1].trim() ? m[1].split(",").map((x) => x.trim()) : [];
  if (!items.every((x) => /^-?\d+(?:\.\d+)?$|^[A-Za-z]\w*$/.test(x))) return null;
  const canon = (x) => (/^-?\d/.test(x) ? String(Number(x)) : x);
  return [...new Set(items.map(canon))];
}
const sortSet = (a) => a.slice().sort((x, y) => { const nx = Number(x), ny = Number(y); const ix = Number.isNaN(nx), iy = Number.isNaN(ny); return ix !== iy ? (ix ? 1 : -1) : ix ? (x < y ? -1 : x > y ? 1 : 0) : nx - ny; });
const showSet = (a) => `{${sortSet(a).join(", ")}}`;

// ---------------------------------------------------------------- results
function result(text, label, answers, verification, steps = []) {
  return {
    ok: true, input: { text, tree: null, warnings: [] }, recognition: { source: "text", confidence: 1 },
    classification: { kind: "command", family: "logic", unknowns: [], goal: "evaluate", label, method: "structural" },
    answers, solutionStatus: "exact", verification, steps, conditions: [], rejected: [], attempts: [], graph: null, ms: 0,
    confidence: { recognition: 1, classification: 1, solution: 1, verification: verification.status === "passed" ? 1 : 0 },
  };
}
function verdict(ok, detail, name) {
  return { status: ok ? "passed" : "failed", level: "exact", checks: [{ name, method: "exact", passed: ok, detail }] };
}

const LOGIC_WORD = /\b(?:not|and|or|xor|implies|iff|nand|nor)\b|[¬∧∨→↔~⊕]|->|<->|=>|&&|\|\|/;
const onlyLogic = (s) => !/[0-9=<>+*/^]/.test(s.replace(/<->|<=>|->|=>/g, ""));

export function solveLogic(input) {
  if (typeof input !== "string") return null;
  const text = input.trim().replace(/[?.]$/, "").trim();
  let m;

  // truth tables
  if ((m = /^(?:make |build |draw |show |give )?(?:a |the )?truth table (?:of|for) (.+)$/i.exec(text))) {
    const e = parseFormula(m[1]);
    if (!e) return null;
    const vars = [...varsOf(e)].sort();
    if (vars.length > 5) return null;
    const rs = rows(vars), vals = rs.map((env) => evalRow(e, env));
    const head = [...vars, show(e)].join(" | ");
    const body = rs.map((env, i) => [...vars.map((v) => (env[v] ? "T" : "F")), vals[i] ? "T" : "F"].join(" | "));
    const table = [head, ...body].join("\n");
    const mask = evalMask(e, vars);
    const ok = vals.every((v, r) => v === !!((mask >> BigInt(r)) & 1n));
    const kind = vals.every(Boolean) ? "It is a tautology (true in every row)." : !vals.some(Boolean) ? "It is a contradiction (false in every row)." : `True in ${vals.filter(Boolean).length} of ${vals.length} rows.`;
    return result(input, "Truth table", [{ kind: "exact", label: "Truth table", text: table + "\n\n" + kind }], verdict(ok, "every row agrees with a bit-parallel evaluation of the whole column", "rows"));
  }

  // tautology / contradiction / satisfiable
  if ((m = /^(?:is|check (?:if|whether)) (.+?) (?:a |an )?(tautology|contradiction|satisfiable|valid)$/i.exec(text))) {
    const e = parseFormula(m[1]);
    if (!e) return null;
    const vars = [...varsOf(e)].sort();
    if (vars.length > MAX_VARS) return null;
    const vals = rows(vars).map((env) => evalRow(e, env));
    const want = m[2].toLowerCase();
    const yes = want === "tautology" || want === "valid" ? vals.every(Boolean) : want === "contradiction" ? !vals.some(Boolean) : vals.some(Boolean);
    const mask = evalMask(e, vars), ALL = (1n << BigInt(vals.length)) - 1n;
    const indep = want === "tautology" || want === "valid" ? mask === ALL : want === "contradiction" ? mask === 0n : mask !== 0n;
    const witness = !yes && (want === "tautology" || want === "valid") ? rows(vars).find((env) => !evalRow(e, env)) : yes && want === "satisfiable" ? rows(vars).find((env) => evalRow(e, env)) : null;
    const wtext = witness ? ` (${vars.map((v) => `${v} = ${witness[v] ? "T" : "F"}`).join(", ")} ${want === "satisfiable" ? "makes it true" : "makes it false"})` : "";
    const answer = `${yes ? "Yes" : "No"}: ${show(e)} is ${yes ? "" : "not "}${want === "valid" ? "a tautology" : want === "satisfiable" ? "satisfiable" : "a " + want}${wtext}.`;
    return result(input, "Propositional logic", [{ kind: "exact", label: yes ? "Yes" : "No", text: answer }], verdict(indep === yes, "a bit-parallel evaluation over all rows gives the same verdict", "all-rows"));
  }

  // equivalence of two formulas
  if ((m = /^(?:is|are) (.+?) (?:logically )?equivalent to (.+)$/i.exec(text)) || (m = /^(?:are )?(.+?) and (.+?) (?:logically )?equivalent$/i.exec(text))) {
    const a = parseFormula(m[1]), b = parseFormula(m[2]);
    if (!a || !b || !(LOGIC_WORD.test(m[1]) || LOGIC_WORD.test(m[2]))) return null;
    const vars = [...new Set([...varsOf(a), ...varsOf(b)])].sort();
    if (vars.length > MAX_VARS) return null;
    const diff = rows(vars).find((env) => evalRow(a, env) !== evalRow(b, env));
    const yes = !diff;
    const indep = evalMask(a, vars) === evalMask(b, vars);
    const answer = yes ? `Yes: ${show(a)}  is logically equivalent to  ${show(b)} (same value in all ${1 << vars.length} rows).`
      : `No: they differ when ${vars.map((v) => `${v} = ${diff[v] ? "T" : "F"}`).join(", ")}.`;
    return result(input, "Logical equivalence", [{ kind: "exact", label: yes ? "Yes" : "No", text: answer }], verdict(indep === yes, "a bit-parallel evaluation over all rows gives the same verdict", "all-rows"));
  }

  // simplify a boolean formula
  if ((m = /^(?:simplify|minimi[sz]e|reduce) (.+)$/i.exec(text)) && LOGIC_WORD.test(m[1]) && onlyLogic(m[1])) {
    const e = parseFormula(m[1]);
    if (!e || !hasOp(e)) return null;
    const vars = [...varsOf(e)].sort();
    if (vars.length > 6) return null;
    const s = minimise(e, vars);
    if (!s) return null;
    const out = s; // the minimal sum of products is the normal form shown
    const printed = show(out);
    const back = parseFormula(printed);
    const ok = !!back && evalMask(back, vars) === evalMask(e, vars);
    const note = "Minimal sum of products (Quine-McCluskey): the fewest literals in an OR of ANDs with the same truth table.";
    return result(input, "Boolean simplification", [{ kind: "exact", label: "Simplified", text: printed }], verdict(ok, "the printed answer, parsed again, has the same truth table as the input", "truth-table"),
      [{ rule: "logic.qm", title: "Minimise", why: note, kind: "note" }]);
  }

  // finite sets
  if ((m = /^(\{[^{}]*\})\s*(union|∪|intersect(?:ion)?|∩|minus|\\|-|difference|symmetric difference|xor)\s*(?:with\s*)?(\{[^{}]*\})$/i.exec(text))) {
    const A = parseSet(m[1]), B = parseSet(m[3]);
    if (!A || !B) return null;
    const op = m[2].toLowerCase();
    const inA = (x) => A.includes(x), inB = (x) => B.includes(x);
    const pred = /union|∪/.test(op) ? (x) => inA(x) || inB(x) : /intersect|∩/.test(op) ? (x) => inA(x) && inB(x) : /symmetric|xor/.test(op) ? (x) => inA(x) !== inB(x) : (x) => inA(x) && !inB(x);
    const R = /union|∪/.test(op) ? [...new Set([...A, ...B])] : /intersect|∩/.test(op) ? A.filter(inB) : /symmetric|xor/.test(op) ? [...A.filter((x) => !inB(x)), ...B.filter((x) => !inA(x))] : A.filter((x) => !inB(x));
    // independent: membership table over every element of A and B
    const ok = [...A, ...B].every((x) => pred(x) === R.includes(x)) && R.every((x) => inA(x) || inB(x)) && new Set(R).size === R.length;
    const name = /union|∪/.test(op) ? "Union" : /intersect|∩/.test(op) ? "Intersection" : /symmetric|xor/.test(op) ? "Symmetric difference" : "Difference";
    return result(input, "Set operation", [{ kind: "exact", label: name, text: R.length ? showSet(R) : "{} (the empty set)" }], verdict(ok, "every element of either set was tested for membership", "membership"));
  }
  if ((m = /^(?:(?:find |what is |list )?the )?(?:(number of (?:elements in the |subsets of )?)|(size of the |cardinality of the ))?(power ?set|subsets)(?: of)? (\{[^{}]*\})$/i.exec(text)) || (m = /^(?:how many subsets (?:does|of)) ()()()(\{[^{}]*\})(?: have)?$/i.exec(text))) {
    const A = parseSet(m[4]);
    if (!A) return null;
    const count = m[1] || m[2] || /how many/i.test(text);
    const n = A.length;
    if (count) {
      const v = 2n ** BigInt(n);
      // independent: count subsets by the binomial sum C(n,0) + ... + C(n,n)
      let s = 0n, c = 1n;
      for (let k = 0; k <= n; k++) { s += c; c = (c * BigInt(n - k)) / BigInt(k + 1); }
      return result(input, "Power set size", [{ kind: "exact", label: `2^${n}`, tree: X.num(v) }], verdict(s === v, "the sum of C(n, k) over k gives the same count", "binomial-sum"));
    }
    if (n > 6) return null;
    const S = sortSet(A);
    const subsets = [];
    for (let k = 0; k <= n; k++) {
      const rec = (start, cur) => { if (cur.length === k) { subsets.push(cur.slice()); return; } for (let i = start; i < n; i++) { cur.push(S[i]); rec(i + 1, cur); cur.pop(); } };
      rec(0, []);
    }
    const ok = subsets.length === 2 ** n && new Set(subsets.map((s) => s.join(","))).size === subsets.length;
    return result(input, "Power set", [{ kind: "exact", label: `${subsets.length} subsets`, text: `{${subsets.map((s) => `{${s.join(", ")}}`).join(", ")}}` }], verdict(ok, `there are 2^${n} distinct subsets`, "count"));
  }
  return null;
}
