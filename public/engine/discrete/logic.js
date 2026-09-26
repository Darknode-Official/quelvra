// Propositional logic on explicit formulas.
//
// Formulas arrive as LAND / LOR / LNOT / LXOR / LIMP / LIFF / LNAND / LNOR calls over variables
// (and 0 / 1). Two evaluators are kept deliberately separate:
//   evalRec   recursive evaluation of the formula tree, one assignment at a time
//   evalBits  bit-parallel evaluation: every variable is a 2^n-bit truth vector (BigInt) and the
//             connectives act on whole columns at once
// Each answer produced by one route is checked with the other, and normal forms / minimal SOPs are
// re-evaluated on every row against the original formula.
//
// Commands: truthtable(f)  istautology(f)  issatisfiable(f)  logicequiv(f, g)  cnf(f)  dnf(f)
//           minsop(f | mterms(...)[, dcterms(...)][, bvars(...)])  validargument(p1, ..., pk, conclusion)

import { refuse, ansNum, ansText, ansYes, check, step } from "./util.js";
import { labelOf, intOf } from "./decode.js";

const OPS = { LAND: "and", LOR: "or", LNOT: "not", LXOR: "xor", LIMP: "imp", LIFF: "iff", LNAND: "nand", LNOR: "nor" };
const MAXVARS = 12;

// tree -> { op, args } | { v: name } | { c: bool }
export function formulaOf(u) {
  if (u.k === "fn" && OPS[u.name]) {
    const op = OPS[u.name];
    const args = u.args.map(formulaOf);
    if (op === "not" && args.length !== 1) throw refuse("NOT takes one argument");
    if ((op === "imp" || op === "iff") && args.length !== 2) throw refuse("-> and <-> take two arguments");
    if (args.length < 1) throw refuse("empty connective");
    return { op, args };
  }
  if (u.k === "num") { if (u.v.d === 1n && (u.v.n === 0n || u.v.n === 1n)) return { c: u.v.n === 1n }; throw refuse("only 0 and 1 are logical constants"); }
  if (u.k === "bool") return { c: !!u.v };
  try { return { v: labelOf(u) }; } catch (_) { throw refuse("expected a propositional formula (variables joined by and, or, not, ->, <->, xor)"); }
}
export function varsOf(f, out = new Set()) { if (f.v) out.add(f.v); else if (f.args) f.args.forEach((a) => varsOf(a, out)); return out; }
const sortVars = (vs) => [...vs].sort((a, b) => (a.length - b.length) || (a < b ? -1 : a > b ? 1 : 0));

export function evalRec(f, env) {
  if ("c" in f) return f.c;
  if (f.v) return !!env[f.v];
  const a = f.args.map((x) => evalRec(x, env));
  switch (f.op) {
    case "not": return !a[0];
    case "and": return a.every(Boolean);
    case "or": return a.some(Boolean);
    case "xor": return a.reduce((p, q) => p !== q, false);
    case "imp": return !a[0] || a[1];
    case "iff": return a[0] === a[1];
    case "nand": return !a.every(Boolean);
    case "nor": return !a.some(Boolean);
  }
  throw new Error("bad op");
}
// bit-parallel: row r (0 .. 2^n - 1) has variable j (MSB first) = bit (n - 1 - j) of r
export function evalBits(f, vars) {
  const n = vars.length, R = 1 << n, full = (1n << BigInt(R)) - 1n;
  const col = new Map();
  vars.forEach((v, j) => { let m = 0n; for (let r = 0; r < R; r++) if ((r >> (n - 1 - j)) & 1) m |= 1n << BigInt(r); col.set(v, m); });
  const go = (g) => {
    if ("c" in g) return g.c ? full : 0n;
    if (g.v) return col.get(g.v);
    const a = g.args.map(go);
    switch (g.op) {
      case "not": return full ^ a[0];
      case "and": return a.reduce((p, q) => p & q, full);
      case "or": return a.reduce((p, q) => p | q, 0n);
      case "xor": return a.reduce((p, q) => p ^ q, 0n);
      case "imp": return (full ^ a[0]) | a[1];
      case "iff": return full ^ (a[0] ^ a[1]);
      case "nand": return full ^ a.reduce((p, q) => p & q, full);
      case "nor": return full ^ a.reduce((p, q) => p | q, 0n);
    }
    throw new Error("bad op");
  };
  return go(f);
}
const envOf = (vars, r) => Object.fromEntries(vars.map((v, j) => [v, !!((r >> (vars.length - 1 - j)) & 1)]));
const bitAt = (m, r) => ((m >> BigInt(r)) & 1n) === 1n;
const popcount = (m) => { let c = 0; while (m) { c += Number(m & 1n); m >>= 1n; } return c; };
function prep(u, extra = []) {
  const f = formulaOf(u);
  const vs = varsOf(f); extra.forEach((g) => varsOf(g, vs));
  const vars = sortVars(vs);
  if (vars.length > MAXVARS) throw refuse(`at most ${MAXVARS} variables are supported (2^${MAXVARS} rows)`);
  return { f, vars };
}
const SYM = { and: " ∧ ", or: " ∨ ", xor: " ⊕ ", imp: " → ", iff: " ↔ " };
export function fText(f, top = true) {
  if ("c" in f) return f.c ? "1" : "0";
  if (f.v) return f.v;
  if (f.op === "not") { const inner = f.args[0]; return "¬" + (inner.v || "c" in inner ? fText(inner, false) : `(${fText(inner, true)})`); }
  if (f.op === "nand" || f.op === "nor") return `¬(${f.args.map((a) => fText(a, false)).join(f.op === "nand" ? " ∧ " : " ∨ ")})`;
  const s = f.args.map((a) => fText(a, false)).join(SYM[f.op]);
  return top ? s : `(${s})`;
}
// rows where the two routes agree
function agreeAll(f, vars) {
  const bits = evalBits(f, vars);
  for (let r = 0; r < 1 << vars.length; r++) if (evalRec(f, envOf(vars, r)) !== bitAt(bits, r)) return { ok: false, bits };
  return { ok: true, bits };
}
const rowText = (vars, r) => vars.map((v, j) => `${v} = ${(r >> (vars.length - 1 - j)) & 1 ? "T" : "F"}`).join(", ");

// ---------------------------------------------------------------- truth table and classification
function tableText(f, vars) {
  if (vars.length > 5) return null;
  const R = 1 << vars.length;
  const lines = [`${vars.join(" ")} | ${fText(f)}`];
  for (let r = R - 1; r >= 0; r--) lines.push(`${vars.map((_, j) => ((r >> (vars.length - 1 - j)) & 1 ? "T" : "F")).join(" ")} | ${evalRec(f, envOf(vars, r)) ? "T" : "F"}`);
  return lines.join("\n");
}
function classify(f, vars, mode) {
  const R = 1 << vars.length;
  let trueRows = 0, first = -1, firstFalse = -1;
  for (let r = R - 1; r >= 0; r--) { if (evalRec(f, envOf(vars, r))) { trueRows++; if (first < 0) first = r; } else if (firstFalse < 0) firstFalse = r; }
  const cls = trueRows === R ? "tautology" : trueRows === 0 ? "contradiction" : "contingent";
  const answers = [];
  if (mode === "sat") answers.push(ansYes("satisfiable", trueRows > 0));
  answers.push(ansText("classification", cls), ansNum("true rows", trueRows));
  if (mode !== "table") answers.push(ansYes("tautology", cls === "tautology"));
  if (trueRows > 0 && cls !== "tautology") answers.push(ansText("satisfying assignment", rowText(vars, first)));
  if (cls === "contingent" && mode !== "table") answers.push(ansText("falsifying assignment", rowText(vars, firstFalse)));
  const tt = tableText(f, vars);
  if (tt && mode === "table") answers.push(ansText("truth table", tt));
  return {
    answers,
    steps: [step("logic.table", `Evaluate ${fText(f)} on all ${R} assignments of ${vars.join(", ")}`, `${trueRows} of ${R} rows are true, so the formula is ${cls === "contingent" ? "contingent (neither a tautology nor a contradiction)" : `a ${cls}`}.`)],
    checks: () => {
      const { ok, bits } = agreeAll(f, vars);
      const cs = [check("bit-parallel evaluation", ok && popcount(bits) === trueRows, `evaluating whole truth columns at once also gives ${popcount(bits)} true rows`)];
      if (first >= 0 && cls !== "tautology") cs.push(check("witness", bitAt(bits, first), `the assignment ${rowText(vars, first)} makes the formula true`));
      if (firstFalse >= 0 && cls !== "contradiction") cs.push(check("counter-witness", !bitAt(bits, firstFalse), `the assignment ${rowText(vars, firstFalse)} makes it false`));
      return cs;
    },
  };
}
const cmdTable = (args) => { if (args.length !== 1) throw refuse("truthtable takes one formula"); const { f, vars } = prep(args[0]); return classify(f, vars, "table"); };
const cmdTaut = (args) => { if (args.length !== 1) throw refuse("one formula expected"); const { f, vars } = prep(args[0]); return classify(f, vars, "taut"); };
const cmdSat = (args) => { if (args.length !== 1) throw refuse("one formula expected"); const { f, vars } = prep(args[0]); return classify(f, vars, "sat"); };

function cmdEquiv(args) {
  if (args.length !== 2) throw refuse("logicequiv takes two formulas");
  const f = formulaOf(args[0]), g = formulaOf(args[1]);
  const vars = sortVars(new Set([...varsOf(f), ...varsOf(g)]));
  if (vars.length > MAXVARS) throw refuse("too many variables");
  let diff = -1;
  for (let r = 0; r < 1 << vars.length && diff < 0; r++) { const e = envOf(vars, r); if (evalRec(f, e) !== evalRec(g, e)) diff = r; }
  const answers = [ansYes("equivalent", diff < 0)];
  if (diff >= 0) answers.push(ansText("counterexample", `${rowText(vars, diff)}: ${fText(f)} is ${evalRec(f, envOf(vars, diff)) ? "T" : "F"} but ${fText(g)} is ${evalRec(g, envOf(vars, diff)) ? "T" : "F"}`));
  return {
    answers,
    steps: [step("logic.equiv", "Compare the truth tables", diff < 0 ? `Both formulas agree on all ${1 << vars.length} rows.` : `They differ at ${rowText(vars, diff)}.`)],
    checks: () => {
      const a = evalBits(f, vars), b = evalBits(g, vars);
      return [diff < 0 ? check("bit-parallel", a === b, "the full truth columns are identical") : check("counterexample", bitAt(a, diff) !== bitAt(b, diff), "the two formulas take different values on the counterexample row")];
    },
  };
}

// ---------------------------------------------------------------- Quine-McCluskey + exact cover
// cube: { bits, mask } (mask bit = 1 where the variable is eliminated); variable j <-> bit (n - 1 - j)
function primeImplicants(n, on, dc) {
  const all = new Set([...on, ...dc]);
  let level = new Map([...all].map((m) => [`${m}|0`, { bits: m, mask: 0, used: false }]));
  const primes = new Map();
  while (level.size) {
    const next = new Map(); const arr = [...level.values()];
    for (let i = 0; i < arr.length; i++) for (let j = i + 1; j < arr.length; j++) {
      const a = arr[i], b = arr[j];
      if (a.mask !== b.mask) continue;
      const d = a.bits ^ b.bits;
      if (d && !(d & (d - 1))) { a.used = b.used = true; const c = { bits: a.bits & ~d, mask: a.mask | d, used: false }; next.set(`${c.bits}|${c.mask}`, c); }
    }
    for (const c of arr) if (!c.used) primes.set(`${c.bits}|${c.mask}`, { bits: c.bits, mask: c.mask });
    level = next;
  }
  return [...primes.values()];
}
const covers = (c, m) => (m & ~c.mask) === c.bits;
const lits = (c, n) => n - popcount(BigInt(c.mask));
// minimum-cost cover: branch and bound over the essential-reduced table; cost = (terms, literals)
function minCover(n, on, pis) {
  let best = null;
  const cost = (sel) => [sel.length, sel.reduce((s, c) => s + lits(c, n), 0)];
  const better = (a, b) => !b || a[0] < b[0] || (a[0] === b[0] && a[1] < b[1]);
  let nodes = 0;
  const rec = (rem, sel) => {
    if (++nodes > 2e6) throw refuse("the cover search is too large");
    if (!rem.length) { const c = cost(sel); if (better(c, best && best.cost)) best = { sel: sel.slice(), cost: c }; return; }
    if (best && sel.length + 1 > best.cost[0]) return;
    // branch on the minterm with the fewest covering implicants
    let pick = rem[0], opts = null;
    for (const m of rem) { const o = pis.filter((c) => covers(c, m)); if (!opts || o.length < opts.length) { pick = m; opts = o; } }
    void pick;
    for (const c of opts) { sel.push(c); rec(rem.filter((m) => !covers(c, m)), sel); sel.pop(); }
  };
  rec(on, []);
  return best;
}
// independent route: brute force over all 3^n cubes for the prime implicants, and over subsets of them for the cover
function bruteForcePrimes(n, on, dc) {
  const ok = new Set([...on, ...dc]);
  const cubes = [];
  for (let mask = 0; mask < 1 << n; mask++) for (let bits = 0; bits < 1 << n; bits++) {
    if (bits & mask) continue;
    let impl = true;
    for (let m = 0; m < 1 << n && impl; m++) if ((m & ~mask) === bits && !ok.has(m)) impl = false;
    if (impl) cubes.push({ bits, mask });
  }
  // prime: no implicant strictly contains it
  return cubes.filter((c) => !cubes.some((d) => d !== c && (d.mask & c.mask) === c.mask && d.mask !== c.mask && (c.bits & ~d.mask) === d.bits));
}
function bruteForceCoverCost(n, on, pis) {
  if (pis.length > 22) return null;
  let best = null;
  for (let S = 0; S < 1 << pis.length; S++) {
    const sel = pis.filter((_, i) => S & (1 << i));
    if (best && sel.length > best[0]) continue;
    if (!on.every((m) => sel.some((c) => covers(c, m)))) continue;
    const cost = [sel.length, sel.reduce((s, c) => s + lits(c, n), 0)];
    if (!best || cost[0] < best[0] || (cost[0] === best[0] && cost[1] < best[1])) best = cost;
  }
  return best;
}
function cubeText(c, vars) {
  const n = vars.length; let s = "";
  vars.forEach((v, j) => { const bit = 1 << (n - 1 - j); if (c.mask & bit) return; s += (c.bits & bit) ? v : `${v}'`; });
  return s || "1";
}
function cubeFormula(c, vars, neg = false) { // neg: the clause of a maxterm cube
  const n = vars.length; const ls = [];
  vars.forEach((v, j) => { const bit = 1 << (n - 1 - j); if (c.mask & bit) return; const pos = !!(c.bits & bit) !== neg; ls.push(pos ? { v } : { op: "not", args: [{ v }] }); });
  if (!ls.length) return { c: !neg };
  return ls.length === 1 ? ls[0] : { op: neg ? "or" : "and", args: ls };
}
function minimise(n, on, dc) {
  const pis = primeImplicants(n, on, dc);
  const best = on.length ? minCover(n, on, pis) : { sel: [], cost: [0, 0] };
  return { pis, best };
}

function readMinterms(u, what) {
  return u.args.map((a) => Number(intOf(a, what)));
}
function cmdMinSOP(args) {
  let on, dc = [], vars, f = null;
  const mt = args.find((a) => a.k === "fn" && a.name === "mterms");
  if (mt) {
    on = readMinterms(mt, "a minterm number");
    const d = args.find((a) => a.k === "fn" && a.name === "dcterms"); if (d) dc = readMinterms(d, "a don't-care number");
    const bv = args.find((a) => a.k === "fn" && a.name === "bvars");
    const maxm = Math.max(0, ...on, ...dc);
    let n = bv ? bv.args.length : Math.max(1, Math.ceil(Math.log2(maxm + 1)));
    if (!bv) n = Math.max(n, 2);
    if (n > 8) throw refuse("minimisation is limited to 8 variables");
    vars = bv ? bv.args.map(labelOf) : "abcdefgh".slice(0, n).split("");
    if ([...on, ...dc].some((m) => m < 0 || m >= 1 << n)) throw refuse(`minterm numbers must be between 0 and ${(1 << n) - 1}`);
    if (on.some((m) => dc.includes(m))) throw refuse("a row cannot be both a minterm and a don't-care");
  } else {
    if (args.length !== 1) throw refuse("minsop takes a formula or a minterm list m(...)");
    const p = prep(args[0]); f = p.f; vars = p.vars;
    if (vars.length > 8) throw refuse("minimisation is limited to 8 variables");
    on = []; for (let r = 0; r < 1 << vars.length; r++) if (evalRec(f, envOf(vars, r))) on.push(r);
  }
  on = [...new Set(on)].sort((a, b) => a - b); dc = [...new Set(dc)].sort((a, b) => a - b);
  const n = vars.length;
  const { pis, best } = minimise(n, on, dc);
  const text = best.sel.length ? best.sel.map((c) => cubeText(c, vars)).join(" + ") : "0";
  return {
    answers: [ansText("minimal sop", text), ansNum("literals", best.cost[1]), ansNum("terms", best.cost[0]), ansText("prime implicants", pis.map((c) => cubeText(c, vars)).join(", "))],
    steps: [step("logic.qm", "Quine-McCluskey: combine minterms differing in one variable", `This gives ${pis.length} prime implicant(s): ${pis.map((c) => cubeText(c, vars)).join(", ")}.`),
      step("logic.cover", "Choose a cheapest set of prime implicants covering every minterm", `Fewest terms, then fewest literals: ${text}.`)],
    checks: () => {
      const cs = [];
      // the expression is correct on every row that is not a don't-care
      let ok = true;
      for (let r = 0; r < 1 << n; r++) { if (dc.includes(r)) continue; const val = best.sel.some((c) => covers(c, r)); if (val !== on.includes(r)) ok = false; }
      if (f) { const bits = evalBits(f, vars); for (let r = 0; r < 1 << n; r++) if (best.sel.some((c) => covers(c, r)) !== bitAt(bits, r)) ok = false; }
      cs.push(check("rows", ok, `the expression is ${on.length ? "true exactly on the minterms" : "identically false"} on all ${1 << n} rows (don't-cares aside)`));
      if (n <= 6) {
        const bp = bruteForcePrimes(n, on, dc);
        const key = (c) => `${c.bits}|${c.mask}`;
        const same = bp.length === pis.length && bp.every((c) => pis.some((d) => key(d) === key(c)));
        cs.push(check("prime implicants", same, `listing all ${3 ** n} cubes finds the same ${bp.length} prime implicants`));
        const bc = bruteForceCoverCost(n, on, bp);
        cs.push(check("minimality", !!bc && bc[0] === best.cost[0] && bc[1] === best.cost[1], bc ? `searching every subset of the prime implicants, the cheapest cover has ${bc[0]} term(s) and ${bc[1]} literal(s)` : "too many prime implicants to search every subset"));
      } else cs.push(check("minimality", false, "minimality is only certified by exhaustive search for up to 6 variables"));
      return cs;
    },
  };
}

// ---------------------------------------------------------------- CNF / DNF (minimal, via QM)
function normalForm(args, kind) {
  if (args.length !== 1) throw refuse(`${kind} takes one formula`);
  const { f, vars } = prep(args[0]);
  if (vars.length > 8) throw refuse("normal forms are computed for at most 8 variables");
  const n = vars.length;
  const on = [], off = [];
  for (let r = 0; r < 1 << n; r++) (evalRec(f, envOf(vars, r)) ? on : off).push(r);
  let g;
  if (kind === "dnf") {
    const { best } = minimise(n, on, []);
    const terms = best.sel.map((c) => cubeFormula(c, vars));
    g = !terms.length ? { c: false } : terms.length === 1 ? terms[0] : { op: "or", args: terms };
  } else {
    const { best } = minimise(n, off, []); // cover the false rows, then negate each cube into a clause
    const clauses = best.sel.map((c) => cubeFormula(c, vars, true));
    g = !clauses.length ? { c: true } : clauses.length === 1 ? clauses[0] : { op: "and", args: clauses };
  }
  const text = fText(g);
  return {
    answers: [ansText(kind, text)],
    steps: [step(`logic.${kind}`, kind === "dnf" ? "Collect the true rows and merge them (Quine-McCluskey)" : "Collect the false rows, merge them, and negate each term into a clause", kind === "dnf" ? "An OR of AND-terms that is true exactly on the true rows." : "An AND of OR-clauses, each clause ruling out a block of false rows.")],
    checks: () => {
      const a = evalBits(f, vars), b = evalBits(g, vars);
      let rec = true; for (let r = 0; r < 1 << n; r++) if (evalRec(g, envOf(vars, r)) !== evalRec(f, envOf(vars, r))) rec = false;
      const shape = kind === "dnf" ? isNF(g, "or", "and") : isNF(g, "and", "or");
      return [check("equivalent", a === b && rec, `the ${kind.toUpperCase()} agrees with the original formula on all ${1 << n} rows`), check("shape", shape, `it is ${kind === "dnf" ? "an OR of ANDs of literals" : "an AND of ORs of literals"}`)];
    },
  };
}
function isNF(g, outer, inner) {
  const lit = (x) => !!x.v || "c" in x || (x.op === "not" && x.args[0].v);
  const term = (x) => lit(x) || (x.op === inner && x.args.every(lit));
  return term(g) || (g.op === outer && g.args.every(term));
}

// ---------------------------------------------------------------- arguments
function cmdValid(args) {
  if (args.length < 2) throw refuse("give at least one premise and a conclusion");
  const fs = args.map(formulaOf);
  const prem = fs.slice(0, -1), concl = fs[fs.length - 1];
  const vars = sortVars(fs.reduce((s, g) => varsOf(g, s), new Set()));
  if (vars.length > MAXVARS) throw refuse("too many variables");
  let bad = -1;
  for (let r = 0; r < 1 << vars.length && bad < 0; r++) { const e = envOf(vars, r); if (prem.every((p) => evalRec(p, e)) && !evalRec(concl, e)) bad = r; }
  const answers = [ansYes("valid", bad < 0)];
  if (bad >= 0) answers.push(ansText("counterexample", `${rowText(vars, bad)}: every premise is true and the conclusion is false`));
  return {
    answers,
    steps: [step("logic.valid", "An argument is valid when no row makes every premise true and the conclusion false", bad < 0 ? `Checked all ${1 << vars.length} rows: none does.` : `The row ${rowText(vars, bad)} does.`)],
    checks: () => {
      const P = prem.reduce((m, p) => m & evalBits(p, vars), (1n << BigInt(1 << vars.length)) - 1n);
      const C = evalBits(concl, vars);
      const badBits = P & ~C;
      return [bad < 0 ? check("bit-parallel", badBits === 0n, "(premises) ∧ ¬(conclusion) is false on every row") : check("counterexample", bitAt(badBits, bad), "the counterexample row makes all premises true and the conclusion false")];
    },
  };
}

export const LOGIC_HANDLERS = {
  truthtable: cmdTable, istautology: cmdTaut, issatisfiable: cmdSat, logicequiv: cmdEquiv,
  cnf: (a) => normalForm(a, "cnf"), dnf: (a) => normalForm(a, "dnf"), minsop: cmdMinSOP, validargument: cmdValid,
};
