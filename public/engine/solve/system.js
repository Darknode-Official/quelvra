// Quelvra solvers: systems of equations.
//
//   linear      exact Gauss-Jordan (linalg.solve): unique / none (inconsistent row) / parametric
//               family with free parameters t1, t2, ...
//   polynomial  reduced lex Groebner basis (groebner.js); {1} proves there is no solution; a
//               zero-dimensional basis is triangular, so the last variable's univariate polynomial
//               is solved exactly and the solutions are extended variable by variable
//               (back-substitution), keeping only extensions that satisfy every basis element.
//   substitution  an equation that is linear in some unknown with a constant coefficient is
//               solved for it and substituted into the others (works for non-polynomial systems).
// Every solution is checked in the ORIGINAL system; in the real domain complex solutions are
// filtered out and the answer says so.

import * as X from "../expr.js";
import * as Q from "../num.js";
import * as P from "../poly.js";
import * as LA from "../linalg.js";
import { toText } from "../print.js";
import { verifySolution } from "../verify.js";
import { toContractVerification } from "../orchestrate.js";
import { C, EX, numDen, safe, fail, unwrap, checkCandidate, cval, signConst, isZeroExact, tidy, passCheck, failCheck, openCheck, makeCompare, approxRec, hasFn, nearZero } from "./util.js";
import { solveCore } from "./core.js";
import { coeffTrees } from "./poly.js";
import { GPoly, groebner, isZeroDimensional } from "./groebner.js";

const NOLOG = { add() {}, group: (h, f) => f() };

export function systemTarget(node, card, env) {
  const { node: inner, vars } = unwrap(node);
  let eqs = null;
  if (inner.k === "system" || inner.k === "and") eqs = inner.args;
  else if (inner.k === "tuple" && inner.args.every((a) => a.k === "eq")) eqs = inner.args;
  if (!eqs || eqs.length < 2 || !eqs.every((e) => e.k === "eq")) return null;
  const syms = [...new Set(eqs.flatMap((e) => [...X.freeSymbols(e)]))];
  let unknowns = vars.length ? vars : (env.options && env.options.variables) || (card && card.unknowns && card.unknowns.length ? card.unknowns : null);
  if (!unknowns) unknowns = syms.slice().sort();
  unknowns = unknowns.filter((u) => syms.includes(u));
  if (!unknowns.length) return null;
  const params = syms.filter((s) => !unknowns.includes(s));
  return { eqs, unknowns, params, original: X.system(...eqs) };
}

// ---------------------------------------------------------------- linear
function linearForm(eqs, vars) {
  const A = [], b = [];
  for (const e of eqs) {
    const d = C(X.sub(e.args[0], e.args[1]));
    const row = [];
    let rest = d;
    for (const v of vars) {
      const cs = coeffTrees(d, v);
      if (!cs || cs.length > 2) return null;
      const a = cs.length === 2 ? cs[1] : X.ZERO;
      if (vars.some((w) => !X.freeOf(a, w))) return null;
      row.push(a);
      rest = X.sub(rest, X.mul(a, X.sym(v)));
    }
    rest = C(rest);
    if (vars.some((w) => !X.freeOf(rest, w))) return null;
    A.push(row);
    b.push(C(X.neg(rest)));
  }
  return { A, b };
}

export function solveLinearSystem(node, card, env) {
  const tg = systemTarget(node, card, env);
  if (!tg) return null;
  const { eqs, unknowns: vars, original } = tg;
  const lf = linearForm(eqs, vars);
  if (!lf) return null;
  const log = env.log;
  const r = LA.solve(lf.A, lf.b);
  for (const s of r.steps || []) {
    const st = { ...s, rule: String(s.rule || "linalg").replace(/^linalg\./, "solve.linsys.") };
    if (typeof st.why === "string") st.why = st.why.replace(/column (\d+)/g, (m, k) => (vars[k - 1] ? `column ${k} (the ${vars[k - 1]} column)` : m));
    // name the columns, and read the reduced matrix back as equations in the unknowns
    if (st.rule === "solve.linsys.solve.augment") { st.before = original; st.why = `Each row is one equation; the columns hold the coefficients of ${vars.join(", ")} and, after the bar, the right side. Row operations do not change the solutions.`; }
    if (st.rule === "solve.linsys.solve.unique" && r.status === "unique") { st.title = "Read off the solution"; st.why = `Each row now says one unknown equals a number. Every column has a pivot (rank ${r.rank}), so this is the only solution.`; st.after = X.system(...vars.map((v, i) => X.eq(X.sym(v), tidy(r.solution[i])))); }
    log.add(st);
  }
  const answers = [];
  let noSolution = false;
  if (r.status === "none") {
    noSolution = true;
    answers.push({ kind: "none", label: "The system has no solution", proof: "row reduction produces the impossible row 0 = c with c != 0" });
  } else if (r.status === "unique") {
    answers.push({ kind: "solution", values: vars.map((v, i) => [v, tidy(r.solution[i])]) });
  } else {
    answers.push({ kind: "family", values: vars.map((v, i) => [v, tidy(r.solution[i])]), params: r.params.map((p) => p.name), label: `infinitely many solutions (${r.params.length} free parameter${r.params.length > 1 ? "s" : ""})` });
  }
  const cand = {
    answers, solutionStatus: "exact", rejected: [], conditions: [], noSolution, note: `linear system, rank ${r.rank}`,
    extra: { rank: r.rank, status: r.status },
    signature: sigOf(answers, true),
    verify: (c) => verifySystem(c, original, vars, env.domain || "real", { rank: r.rank, status: r.status, lin: lf }),
  };
  cand.compare = makeCompare(cand.signature);
  return cand;
}

// ---------------------------------------------------------------- polynomial (Groebner)
export function solvePolySystem(node, card, env) {
  const tg = systemTarget(node, card, env);
  if (!tg) return null;
  const { eqs, unknowns: vars, original, params } = tg;
  if (params.length) throw fail("polynomial systems with parameters are not supported");
  const dom = env.domain || "real";
  const log = env.log;
  const F = [];
  for (const e of eqs) {
    const d = C(X.sub(e.args[0], e.args[1]));
    const [n] = numDenSys(d);
    const m = safe(() => P.fromTree(n, vars));
    if (!m) return null;
    F.push(GPoly.fromMPoly(m, vars));
  }
  const gb = groebner(F, { checkTime: env.checkTime, maxSteps: 300000 });
  const basis = gb.basis;
  const bTrees = basis.map((g) => C(g.toTree(vars)));
  log.add({ rule: "solve.polysys.groebner", title: "Compute a Groebner basis (lex order)", why: `Buchberger's algorithm with lex order ${vars.join(" > ")} (S-pairs: ${gb.stats ? gb.stats.pairs : "?"}, skipped by the coprime criterion: ${gb.stats ? gb.stats.criterion1 : 0}, by the chain criterion: ${gb.stats ? gb.stats.criterion2 : 0}). The basis has the same solutions as the system and is triangular.`, before: original, after: X.system(...bTrees.map((t) => X.eq(t, X.ZERO))) });
  const answers = [];
  const rejected = [];
  let noSolution = false;
  const complexDropped = [];
  if (basis.length === 1 && basis[0]._lead.e.every((x) => x === 0)) {
    noSolution = true;
    answers.push({ kind: "none", label: "The system has no solution", proof: "the Groebner basis is {1}: 1 is a combination of the equations, so they cannot all be 0" });
    log.add({ rule: "solve.polysys.inconsistent", title: "The basis is {1}", why: "1 lies in the ideal generated by the equations, so no (even complex) solution exists.", before: null, after: X.FALSE });
  } else {
    if (!isZeroDimensional(basis, vars.length)) throw fail("the polynomial system has infinitely many solutions (positive-dimensional); only finite solution sets are supported");
    const sols = backSubstitute(basis, bTrees, vars, dom, env);
    for (const s of sols) {
      const vals = new Map(s);
      if (dom === "real" && s.some(([, t]) => Math.abs(cval(t).im) > 1e-12 * Math.max(1, Math.abs(cval(t).re)))) { complexDropped.push(s); continue; }
      const chk = checkSystem(original, vals, dom);
      if (chk.ok) answers.push({ kind: "solution", values: s.map(([v, t]) => [v, tidy(t)]), level: chk.level });
      else rejected.push({ tree: X.tuple(...s.map(([v, t]) => X.eq(X.sym(v), t))), value: s, reason: chk.reason });
    }
    if (complexDropped.length) log.add({ rule: "solve.polysys.complex", title: "Discard complex solutions", why: `${complexDropped.length} solution${complexDropped.length > 1 ? "s are" : " is"} not real and ${complexDropped.length > 1 ? "are" : "is"} left out (real domain).`, before: null, after: null, kind: "note" });
    if (!answers.length) { noSolution = true; answers.push({ kind: "none", label: dom === "real" ? "The system has no real solution" : "The system has no solution", proof: complexDropped.length ? "every solution of the Groebner basis is complex" : "no candidate satisfies the system" }); }
  }
  const cand = {
    answers, solutionStatus: "exact", rejected, conditions: [], noSolution, note: "Groebner basis",
    extra: { basis: bTrees, complexSolutionsDropped: complexDropped.length },
    signature: sigOf(answers, true),
    verify: (c) => verifySystem(c, original, vars, dom, { groebner: true, basisOne: noSolution && !complexDropped.length && basis.length === 1 }),
  };
  cand.compare = makeCompare(cand.signature);
  return cand;
}
function numDenSys(d) {
  const [n] = numDen(d);
  return [EX(n)];
}
function backSubstitute(basis, bTrees, vars, dom, env) {
  const n = vars.length;
  const leadVar = (g) => g._lead.e.findIndex((x) => x > 0);
  // polynomials whose largest variable is vars[i] (lex: leading monomial's first nonzero exponent)
  const byVar = vars.map((_, i) => bTrees.filter((_, j) => usedMax(basis[j]) === i));
  function usedMax(g) { let m = -1; for (const k of g.terms.keys()) { const e = k.split(",").map(Number); e.forEach((x, i) => { if (x > 0 && (m < 0 || i < m)) m = i; }); } return m; }
  let partial = [[]]; // list of assignments [[var, tree], ...] for vars[i..n-1]
  for (let i = n - 1; i >= 0; i--) {
    env.checkTime && env.checkTime();
    const v = vars[i];
    const next = [];
    for (const asg of partial) {
      const map = Object.fromEntries(asg);
      const polys = byVar[i].map((t) => C(X.subs(t, map), dom)).filter((t) => t !== X.ZERO);
      if (!polys.length) throw fail("back-substitution found a free variable");
      // smallest degree with a nonvanishing leading coefficient
      const cands = polys.map((t) => ({ t, cs: coeffTrees(t, v) })).filter((q) => q.cs && q.cs.length >= 2).sort((a, b) => a.cs.length - b.cs.length);
      let chosen = null;
      for (const q of cands) { if (signConst(q.cs[q.cs.length - 1], dom) !== 0) { chosen = q; break; } }
      if (!chosen) { if (polys.every((t) => !X.freeOf(t, v) || signConst(t, dom) === 0)) continue; continue; } // inconsistent branch
      const sol = solveCore(chosen.t, { x: v, topVar: v, log: NOLOG, domain: "complex", allowNumeric: false, depth: 0, checkTime: env.checkTime });
      if (sol.approx.length) throw fail(`the values of ${v} have no closed form`);
      for (const r of sol.exact) {
        const val = tidy(r.tree, "complex");
        // must satisfy the other polynomials of this level
        const ok = polys.every((t) => t === chosen.t || isZeroExact(X.subs(t, { [v]: val }), "complex") || nearZero(X.subs(t, { [v]: val }), 60));
        if (ok) next.push([[v, val], ...asg]);
      }
    }
    partial = next;
  }
  return partial;
}
function checkSystem(original, vals, dom) {
  let level = "exact";
  const [first, ...rest] = [...vals];
  const r = checkCandidate(original, first[0], first[1], dom, new Map(rest));
  if (!r.ok) return r;
  if (r.level === "numeric") level = "numeric";
  return { ok: true, level };
}

// ---------------------------------------------------------------- substitution
export function solveBySubstitution(node, card, env) {
  const tg = systemTarget(node, card, env);
  if (!tg) return null;
  const { eqs, unknowns: vars, original, params } = tg;
  if (params.length) return null;
  const dom = env.domain || "real";
  const log = env.log;
  const sols = substitute(eqs.map((e) => C(X.sub(e.args[0], e.args[1]), dom)), vars, dom, env, log, 0);
  if (sols === null) return null;
  const answers = [], rejected = [];
  for (const s of sols) {
    const vals = new Map(s);
    if (dom === "real" && s.some(([, t]) => Math.abs(cval(t).im) > 1e-12)) continue;
    const chk = checkSystem(original, vals, dom);
    if (chk.ok) answers.push({ kind: "solution", values: vars.map((v) => [v, tidy(vals.get(v))]) });
    else rejected.push({ tree: X.tuple(...s.map(([v, t]) => X.eq(X.sym(v), t))), value: s, reason: chk.reason });
  }
  // dedupe
  const uniq = [];
  for (const a of answers) if (!uniq.some((b) => b.values.every(([v, t], i) => isZeroExact(X.sub(t, a.values[i][1]), dom)))) uniq.push(a);
  let noSolution = false;
  if (!uniq.length) { noSolution = true; uniq.push({ kind: "none", label: "The system has no real solution", proof: "substitution leaves an equation without (valid) solutions" }); }
  const cand = {
    answers: uniq, solutionStatus: "exact", rejected, conditions: [], noSolution, note: "substitution",
    signature: sigOf(uniq, true),
    verify: (c) => verifySystem(c, original, vars, dom, { substitution: true }),
  };
  cand.compare = makeCompare(cand.signature);
  return cand;
}
// returns list of assignments [[v, tree]...] or null (not applicable)
function substitute(ds, vars, dom, env, log, depth) {
  if (depth > 6) return null;
  env.checkTime && env.checkTime();
  ds = ds.filter((d) => d !== X.ZERO);
  const live = vars.filter((v) => ds.some((d) => !X.freeOf(d, v)));
  if (ds.length === 1 && live.length === 1) {
    const v = live[0];
    const sol = solveCore(ds[0], { x: v, topVar: v, log, domain: dom, allowNumeric: false, depth: 0, checkTime: env.checkTime });
    if (sol.approx.length || sol.general.length || sol.all || sol.regions.length || !sol.complete) throw fail("substitution led to an equation without a finite exact solution set");
    return sol.exact.map((r) => [[v, r.tree]]);
  }
  if (!ds.length) return vars.length ? null : [[]];
  if (ds.some((d) => vars.every((v) => X.freeOf(d, v)))) {
    // a constant equation: true (drop) or false (no solution)
    const k = ds.find((d) => vars.every((v) => X.freeOf(d, v)));
    const s = signConst(k, dom);
    if (s === 0) return substitute(ds.filter((d) => d !== k), vars, dom, env, log, depth + 1);
    if (s) return [];
    return null;
  }
  // find (equation, variable) linear with constant nonzero coefficient
  for (let i = 0; i < ds.length; i++) {
    for (const v of live) {
      const cs = coeffTrees(ds[i], v);
      if (!cs || cs.length !== 2) continue;
      const a = cs[1];
      if (vars.some((w) => !X.freeOf(a, w))) continue;
      if (!signConst(a, dom)) continue;
      const expr = C(X.neg(X.div(cs[0], a)), dom);
      log.add({ rule: "solve.system.substitute", title: `Solve for ${v} and substitute`, why: `From ${toText(ds[i])} = 0: ${v} = ${toText(expr)}.`, before: X.eq(ds[i], X.ZERO), after: X.eq(X.sym(v), expr) });
      const rest = ds.filter((_, j) => j !== i).map((d) => C(X.subs(d, { [v]: expr }), dom));
      const others = vars.filter((w) => w !== v);
      const sub = substitute(rest, others, dom, env, log, depth + 1);
      if (sub === null) return null;
      return sub.map((asg) => { const m = Object.fromEntries(asg); return [...asg, [v, C(X.subs(expr, m), dom)]]; });
    }
  }
  return null;
}

// ---------------------------------------------------------------- verification / signatures
function sigOf(answers, complete) {
  const sols = answers.filter((a) => a.kind === "solution").map((a) => a.values.map(([, t]) => cval(t)));
  if (answers.some((a) => a.kind === "family")) return { kind: "other" };
  return { kind: "tuples", sols, complete };
}
function verifySystem(c, original, vars, dom, info) {
  const res = [];
  for (const a of c.answers) {
    if (a.kind === "solution") {
      res.push(verifySolution(original, new Map(a.values), { domain: dom }));
    } else if (a.kind === "family") {
      // symbolic: every equation becomes 0 = 0 identically in the parameters
      const allZero = original.args.every((e) => isZeroExact(X.subs(X.sub(e.args[0], e.args[1]), Object.fromEntries(a.values)), dom));
      res.push(allZero ? passCheck("substitution-exact", `substituting the parametric solution makes every equation an identity in ${a.params.join(", ")}`) : failCheck("substitution-exact", "the parametric solution does not satisfy the system identically"));
      for (const tv of [[0], [1], [-2], [3]]) {
        const pm = Object.fromEntries(a.params.map((p, i) => [p, X.num(Q.Q(BigInt(tv[0] + i)))]));
        res.push(verifySolution(original, new Map(a.values.map(([v, t]) => [v, C(X.subs(t, pm), dom)])), { domain: dom }));
      }
      if (info.rank !== undefined) res.push(passCheck("completeness", `rank ${info.rank} < ${vars.length} unknowns: the solution set is ${vars.length - info.rank}-dimensional and the family covers it (Gauss-Jordan elimination is reversible)`));
    } else if (a.kind === "none") {
      if (info.status === "none") res.push(passCheck("inconsistent", `the reduced row echelon form contains 0 = c with c != 0 (rank of A is ${info.rank}, rank of [A | b] is larger)`));
      else if (info.basisOne) res.push(passCheck("inconsistent", "the reduced Groebner basis is {1}"));
      else res.push(passCheck("no-solution", a.proof));
    }
  }
  if (info.status === "unique") res.push(passCheck("completeness", `rank ${info.rank} = number of unknowns: the solution is unique`));
  if (info.groebner && c.answers.some((a) => a.kind === "solution")) res.push(passCheck("completeness", "the lex Groebner basis is triangular: every solution's last coordinate is a root of the univariate basis element, and every root was extended in all possible ways"));
  if (info.substitution && c.answers.some((a) => a.kind === "solution")) res.push(passCheck("completeness", "each substitution is an equivalence, and the final one-variable equation was solved completely"));
  return toContractVerification(res);
}
