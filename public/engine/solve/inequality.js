// Quelvra solvers: inequalities in one unknown (single, compound with and / or, chained).
//
// Sign-chart method. Critical points are
//   * the zeros of LHS - RHS of every relation (solveCore: exact, or certified numeric),
//   * the zeros of every denominator of the original,
//   * the domain boundaries: zeros of even-root radicands and of logarithm arguments.
// Between consecutive critical points every relation keeps its truth value (the functions allowed
// here are continuous on their domains and the domain boundaries are critical points), so one
// rational test point per open interval decides it EXACTLY; each critical point is decided
// exactly too (open or closed end). The pieces are merged into intervals.
// Periodic (trigonometric) inequalities are not handled (infinitely many pieces).

import * as X from "../expr.js";
import * as Q from "../num.js";
import { toText } from "../print.js";
import { verifySolutionSet, truth } from "../verify.js";
import { toContractVerification } from "../orchestrate.js";
import { C, safe, fail, unwrap, checkCandidate, dedupeTrees, cval, signConst, cmpConst, tidy, findAll, denominators, rationalBetween, decimalTree, passCheck, openCheck, makeCompare, isConstTree, exactAnswer, hasFn } from "./util.js";
import { solveCore } from "./core.js";
import { coeffTrees } from "./poly.js";
import { certifiedRoots, numeratorForNumerics } from "./numeric.js";
import { evalWTree } from "./lambert.js";

const OK_FN = new Set(["abs", "ln", "log", "exp", "sqrt", "cbrt", "sinh", "cosh", "tanh", "atan", "asinh", "acosh", "atanh", "asin", "acos"]);
const REL_OPS = new Set(["<", "<=", ">", ">=", "!="]);

function relations(u) {
  if (u.k === "rel" || u.k === "eq") return [u];
  if (u.k === "and" || u.k === "or") return u.args.flatMap(relations);
  if (u.k === "not") return relations(u.args[0]);
  return null;
}
export function inequalityTarget(node, card, env) {
  let { node: inner, vars } = unwrap(node);
  if (inner.k === "system" && inner.args.every((a) => a.k === "rel" || a.k === "eq" || a.k === "and" || a.k === "or")) inner = X.and(...inner.args);
  const rels = relations(inner);
  if (!rels || !rels.length || !rels.some((r) => r.k === "rel" && REL_OPS.has(r.op))) return null;
  const syms = [...X.freeSymbols(inner)];
  let x = vars[0] || (env.options && env.options.variable) || (card && card.unknowns && card.unknowns[0]) || (syms.includes("x") ? "x" : syms.length === 1 ? syms[0] : null);
  if (!x || !syms.includes(x)) return null;
  return { rel: inner, rels, x, params: syms.filter((s) => s !== x) };
}

export function solveInequality(node, card, env, mode = "exact") {
  const tg = inequalityTarget(node, card, env);
  if (!tg) return null;
  const { rel, rels, x, params } = tg;
  const dom = env.domain || "real";
  if (dom !== "real") throw fail("inequalities are solved over the reals");
  if (params.length) return mode === "exact" ? literalLinear(rel, rels, x, params, env) : null;
  // unsupported functions (periodic or discontinuous)
  const bad = findAll(rel, (w) => w.k === "fn" && !X.freeOf(w, x) && !OK_FN.has(w.name));
  if (bad.length) throw fail(`inequalities with ${bad[0].name} are not supported (the sign chart would need infinitely many pieces)`);
  if (findAll(rel, (w) => w.k === "pow" && !X.freeOf(w.args[0], x) && !X.freeOf(w.args[1], x)).length) throw fail("inequalities with a variable base and exponent are not supported");
  return mode === "numeric-check" ? numericSet(rel, rels, x, env) : exactSet(rel, rels, x, env);
}

// ---------------------------------------------------------------- critical points
function criticalPoints(rel, rels, x, env) {
  const dom = "real";
  const log = { add() {}, group: (h, f) => f() };
  const S = { x, topVar: x, log, domain: dom, digits: env.digits || 20, checkTime: env.checkTime, allowNumeric: true, depth: 0 };
  const exprs = [];
  for (const r of rels) exprs.push({ e: C(X.sub(r.args[0], r.args[1]), dom), why: "zero of " + toText(X.sub(r.args[0], r.args[1])) });
  for (const d of denominators(rel)) if (!X.freeOf(d, x)) exprs.push({ e: C(d, dom), why: "denominator " + toText(d) + " is 0" });
  for (const w of findAll(rel, (w) => w.k === "pow" && X.isNum(w.args[1]) && w.args[1].v.d % 2n === 0n && !X.freeOf(w.args[0], x))) exprs.push({ e: C(w.args[0], dom), why: "radicand " + toText(w.args[0]) + " is 0" });
  for (const w of findAll(rel, (w) => w.k === "fn" && (w.name === "ln" || w.name === "log") && !X.freeOf(w, x))) {
    const a = w.name === "log" && w.args.length === 2 ? w.args[1] : w.args[0];
    exprs.push({ e: C(a, dom), why: "log argument is 0" });
    if (w.name === "log" && w.args.length === 2 && !X.freeOf(w.args[0], x)) { exprs.push({ e: C(w.args[0], dom), why: "log base 0" }); exprs.push({ e: C(X.sub(w.args[0], X.ONE), dom), why: "log base 1" }); }
  }
  for (const w of findAll(rel, (w) => w.k === "fn" && ["asin", "acos", "atanh"].includes(w.name) && !X.freeOf(w, x))) { exprs.push({ e: C(X.sub(w.args[0], X.ONE), dom), why: "domain edge" }); exprs.push({ e: C(X.add(w.args[0], X.ONE), dom), why: "domain edge" }); }
  for (const w of findAll(rel, (w) => w.k === "fn" && w.name === "acosh" && !X.freeOf(w, x))) exprs.push({ e: C(X.sub(w.args[0], X.ONE), dom), why: "domain edge" });
  const pts = [];
  let complete = true, approxUsed = false;
  const notes = [];
  for (const { e } of exprs) {
    if (X.freeOf(e, x)) continue;
    env.checkTime && env.checkTime();
    const sol = solveCore(e, { ...S });
    if (sol.general.length) throw fail("periodic critical points are not supported");
    if (sol.all) continue; // identically zero: no sign change
    for (const r of sol.exact) {
      if (hasFn(r.tree, "W")) { const w = evalWTree(r.tree, 30); if (!w) throw fail("could not evaluate a Lambert W critical point"); approxUsed = true; pts.push({ approx: { value: w.value, digits: 30, errorBound: w.errorBound, method: "Lambert W" }, v: parseFloat(w.value), tree: decimalTree(parseFloat(w.value).toPrecision(15)), closedForm: r.tree }); continue; }
      const v = cval(r.tree); if (Math.abs(v.im) < 1e-12 * Math.max(1, Math.abs(v.re)) && Number.isFinite(v.re)) pts.push({ tree: tidy(r.tree), v: v.re }); }
    for (const a of sol.approx) { if (a.complex) continue; approxUsed = true; pts.push({ approx: a.approx, v: a.value, tree: decimalTree(parseFloat(a.approx.value).toPrecision(15)) }); }
    for (const g of sol.regions) notes.push(`${toText(e)} = 0 on a whole region (${toText(g)})`);
    if (sol.regions.length) {
      // region boundaries: points where the case conditions switch are zeros of abs arguments
      for (const w of findAll(e, (w) => w.k === "fn" && w.name === "abs")) {
        const s2 = solveCore(C(w.args[0]), { ...S });
        for (const r of s2.exact) { const v = cval(r.tree); if (Math.abs(v.im) < 1e-12) pts.push({ tree: tidy(r.tree), v: v.re }); }
      }
    }
    if (!sol.complete) complete = false;
  }
  // dedupe and sort
  pts.sort((a, b) => a.v - b.v);
  const out = [];
  for (const p of pts) {
    const q = out[out.length - 1];
    if (q && Math.abs(q.v - p.v) <= 1e-12 * Math.max(1, Math.abs(p.v))) {
      if (p.tree && q.tree && !p.approx && !q.approx) { const d = signConst(X.sub(p.tree, q.tree)); if (d === 0 || d === null) continue; }
      else continue;
    }
    out.push(p);
  }
  out.sort((a, b) => a.v - b.v);
  return { pts: out, complete, approxUsed, notes };
}

// truth of the ORIGINAL (compound) relation at an exact point: true / false / null (undefined there)
function holdsAt(rel, x, t) {
  const rels = relations(rel);
  const vals = new Map();
  for (const r of rels) {
    const c = checkCandidate(r, x, t, "real");
    if (!c.ok && /undefined|not real|denominator/.test(c.reason)) vals.set(r, null);
    else if (!c.ok && /could not/.test(c.reason)) return "unknown";
    else vals.set(r, c.ok);
  }
  const ev = (u) => {
    if (u.k === "and") { let any = false; for (const a of u.args) { const v = ev(a); if (v === false) return false; if (v === null) any = true; } return any ? null : true; }
    if (u.k === "or") { let any = false; for (const a of u.args) { const v = ev(a); if (v === true) return true; if (v === null) any = true; } return any ? null : false; }
    if (u.k === "not") { const v = ev(u.args[0]); return v === null ? null : !v; }
    return vals.get(u);
  };
  const r = ev(rel);
  return r === null ? false : r; // outside the domain the relation does not hold
}

function exactSet(rel, rels, x, env) {
  const log = env.log;
  const cp = criticalPoints(rel, rels, x, env);
  if (!cp.complete) throw fail("the critical points could not all be found");
  const pts = cp.pts;
  log.add({ rule: "solve.ineq.critical", title: "Find the critical points", why: `Zeros of each side's difference, zeros of denominators and domain edges split the line into intervals on which the truth value cannot change. Critical points: ${pts.length ? pts.map((p) => (p.approx ? "~" + p.approx.value.slice(0, 12) : toText(p.tree))).join(", ") : "none"}.`, before: rel, after: null });
  // pieces: interval i = (p[i-1], p[i]) and point i
  const pieces = [];
  const testVals = [];
  for (let i = 0; i <= pts.length; i++) {
    const lo = i > 0 ? pts[i - 1].v : null, hi = i < pts.length ? pts[i].v : null;
    const tq = testPoint(lo, hi);
    const h = holdsAt(rel, x, tq);
    if (h === "unknown") throw fail("could not decide the sign at a test point");
    pieces.push({ type: "interval", holds: h, test: tq });
    testVals.push([tq, h]);
    if (i < pts.length) {
      const p = pts[i];
      let hp;
      if (p.approx) {
        // an approximate zero of a relation's difference: included iff the relation is non-strict there
        hp = approxPointHolds(rel, x, p);
      } else hp = holdsAt(rel, x, p.tree);
      if (hp === "unknown") throw fail("could not decide the relation at a critical point");
      pieces.push({ type: "point", holds: hp, p });
    }
  }
  // sign chart step
  log.add({ rule: "solve.ineq.sign-chart", title: "Test each interval", why: pieces.map((q) => (q.type === "interval" ? `at ${x} = ${toText(q.test)}: ${q.holds ? "true" : "false"}` : `at ${x} = ${q.p.approx ? "~" + q.p.approx.value.slice(0, 10) : toText(q.p.tree)}: ${q.holds ? "true" : "false"}`)).join("; ") + ".", before: null, after: null, kind: "note" });
  const ivs = mergePieces(pieces);
  const tree = setTree(ivs, x);
  log.add({ rule: "solve.ineq.result", title: "Collect the intervals", why: "Adjacent true pieces merge; an endpoint is closed exactly when the relation holds there.", before: rel, after: tree });
  const answer = { kind: "set", label: x, tree, interval: ivs.map(({ lo, hi, loOpen, hiOpen }) => ({ lo, hi, loOpen, hiOpen })) };
  const approx = cp.approxUsed;
  if (approx) answer.approxEndpoints = true;
  const bnds = pts.map((p) => p.v);
  const setTest = (t) => { const r = truth(tree, { [x]: t }); return r === true; };
  const cand = {
    answers: [answer], solutionStatus: approx ? "approximate" : "exact", rejected: [], conditions: [],
    noSolution: tree === X.FALSE,
    note: "sign chart",
    extra: { criticalPoints: pts.map((p) => (p.approx ? p.approx.value : toText(p.tree))), notes: cp.notes },
    signature: { kind: "set", test: setTest, probe: probePoints(bnds) },
    verify: () => {
      const res = [];
      const v = verifySolutionSet(rel, x, setTest, { boundaries: bnds, span: Math.max(20, ...bnds.map((b) => Math.abs(b) + 5)) });
      res.push(v);
      res.push(passCheck("sign-chart", `exact test at ${testVals.length} interval points and ${pts.length} critical points; all critical points were found by exact methods${approx ? " or certified numerics" : ""}`, approx ? "numeric" : "exact"));
      return toContractVerification(res);
    },
  };
  cand.compare = makeCompare(cand.signature);
  return cand;
}
function probePoints(bnds) {
  const out = [];
  for (let i = 0; i <= 120; i++) out.push(-30 + i * 0.5 + 0.0071);
  for (const b of bnds) out.push(b - 1e-3, b + 1e-3);
  return out;
}
function approxPointHolds(rel, x, p) {
  const t = decimalTree(p.approx.value);
  // check each relation: if its difference changes sign here it is 0 at the true point
  const rels = relations(rel);
  const vals = new Map();
  for (const r of rels) {
    const d = C(X.sub(r.args[0], r.args[1]));
    const v = cval(X.subs(d, { [x]: t })).re;
    const scale = Math.max(1, Math.abs(cval(X.subs(r.args[0], { [x]: t })).re));
    if (!Number.isFinite(v)) { vals.set(r, null); continue; }
    if (Math.abs(v) <= 1e-9 * scale) vals.set(r, r.k === "eq" || r.op === "<=" || r.op === ">=");
    else vals.set(r, r.op === "<" ? v < 0 : r.op === "<=" ? v <= 0 : r.op === ">" ? v > 0 : r.op === ">=" ? v >= 0 : r.op === "!=" ? v !== 0 : false);
  }
  const ev = (u) => (u.k === "and" ? u.args.every(ev) : u.k === "or" ? u.args.some(ev) : u.k === "not" ? !ev(u.args[0]) : !!vals.get(u));
  return ev(rel);
}
function testPoint(lo, hi) {
  if (lo === null && hi === null) return X.ZERO;
  if (lo === null) return X.num(Q.Q(BigInt(Math.floor(hi) - 1)));
  if (hi === null) return X.num(Q.Q(BigInt(Math.ceil(lo) + 1)));
  const q = rationalBetween(lo, hi);
  return X.num(q);
}
function mergePieces(pieces) {
  const ivs = [];
  let cur = null;
  for (let i = 0; i < pieces.length; i++) {
    const q = pieces[i];
    if (q.holds) {
      if (!cur) {
        if (q.type === "interval") cur = { lo: i > 0 ? pieces[i - 1].p.tree : null, loOpen: true };
        else cur = { lo: q.p.tree, loOpen: false };
      }
    } else if (cur) {
      // close at the previous piece
      const prev = pieces[i - 1];
      if (prev.type === "interval") { cur.hi = q.p.tree; cur.hiOpen = true; }
      else { cur.hi = prev.p.tree; cur.hiOpen = false; }
      ivs.push(cur); cur = null;
    }
  }
  if (cur) { cur.hi = null; cur.hiOpen = true; ivs.push(cur); }
  return ivs;
}
function setTree(ivs, x) {
  const X0 = X.sym(x);
  if (!ivs.length) return X.FALSE;
  const parts = ivs.map(({ lo, hi, loOpen, hiOpen }) => {
    if (lo === null && hi === null) return X.TRUE;
    if (lo !== null && hi !== null && lo === hi) return X.eq(X0, lo);
    const cs = [];
    if (lo !== null) cs.push(X.rel(loOpen ? "<" : "<=", lo, X0));
    if (hi !== null) cs.push(X.rel(hiOpen ? "<" : "<=", X0, hi));
    return cs.length === 1 ? cs[0] : X.and(...cs);
  });
  if (parts.includes(X.TRUE)) return X.TRUE;
  // (-oo, a) U (a, oo) -> x != a
  if (ivs.length === 2 && ivs[0].lo === null && ivs[1].hi === null && ivs[0].hiOpen && ivs[1].loOpen && ivs[0].hi === ivs[1].lo) return X.rel("!=", X0, ivs[0].hi);
  return parts.length === 1 ? parts[0] : X.or(...parts);
}

// Normalise a set given as a relation / and / or tree in x into sorted intervals (exact).
export function normalizeSet(tree, x, env = {}) {
  const rels = relations(tree);
  if (!rels) return null;
  const c = exactSet(tree, rels, x, { log: { add() {}, group: (h, f) => f() }, digits: 20, checkTime: env.checkTime });
  return c.answers[0];
}

// ---------------------------------------------------------------- numeric cross-check
function numericSet(rel, rels, x, env) {
  // critical points by certified numeric root finding of every difference numerator and denominator
  const pts = [];
  const exprs = rels.map((r) => C(X.sub(r.args[0], r.args[1])));
  for (const d of denominators(rel)) if (!X.freeOf(d, x)) exprs.push(C(d));
  let complete = true;
  for (const e of exprs) {
    const h = safe(() => C(numeratorForNumerics(e)));
    if (!h || X.freeOf(h, x)) continue;
    const cr = certifiedRoots(h, x, { lo: -40, hi: 40, fixed: true, digits: 16, samples: 800, timeLimitMs: 1500 });
    if (!cr.completeWindow) complete = false;
    for (const r of cr.roots) pts.push(r.v);
  }
  pts.sort((a, b) => a - b);
  const test = (t) => truth(rel, { [x]: t }, "real", 1e-14) === true;
  const sig = { kind: "set", test, probe: probePoints(pts).filter((t) => t > -40 && t < 40) };
  env.log.add({ rule: "solve.ineq.numeric", title: "Numeric sign chart", why: `Truth of the inequality between numerically located critical points on [-40, 40].`, before: rel, after: null, kind: "approximation" });
  const cand = {
    answers: [{ kind: "none", label: "numeric cross-check only" }], solutionStatus: "partial", rejected: [], conditions: [], note: "numeric cross-check",
    signature: sig, verify: () => toContractVerification([openCheck("numeric", complete ? "window [-40, 40] complete" : "window [-40, 40]")]),
  };
  cand.compare = makeCompare(sig);
  return cand;
}

// ---------------------------------------------------------------- linear with parameters
function literalLinear(rel, rels, x, params, env) {
  if (rels.length !== 1 || rel.k !== "rel") throw fail("parametric compound inequalities are not supported");
  const dom = "real";
  const e = C(X.sub(rel.args[0], rel.args[1]));
  const cs = coeffTrees(e, x);
  if (!cs || cs.length !== 2) throw fail("parametric inequalities are solved only when linear in the unknown");
  const [b, a] = cs;
  const X0 = X.sym(x);
  const r = tidy(X.neg(X.div(b, a)));
  const flip = { "<": ">", "<=": ">=", ">": "<", ">=": "<=", "!=": "!=" };
  const sa = signConst(a);
  const answers = [];
  const cases = [];
  const mk = (op) => X.rel(op, X0, r);
  if (sa === 1 || sa === -1) answers.push({ kind: "set", label: x, tree: mk(sa === 1 ? rel.op : flip[rel.op]) });
  else {
    cases.push({ kind: "case", label: `If ${toText(a)} > 0: ${toText(mk(rel.op))}`, condition: X.rel(">", a, X.ZERO), tree: mk(rel.op) });
    cases.push({ kind: "case", label: `If ${toText(a)} < 0: ${toText(mk(flip[rel.op]))}`, condition: X.rel("<", a, X.ZERO), tree: mk(flip[rel.op]) });
    cases.push({ kind: "case", label: `If ${toText(a)} = 0: the inequality is ${toText(X.rel(rel.op, b, X.ZERO))} (true for every ${x} or for none)`, condition: X.eq(a, X.ZERO), tree: X.rel(rel.op, b, X.ZERO) });
    answers.push(...cases);
  }
  env.log.add({ rule: "solve.ineq.literal", title: `Solve for ${x}`, why: `Divide by ${toText(a)}; the direction flips when it is negative.`, before: rel, after: answers[0].tree });
  const cand = {
    answers, solutionStatus: "exact", rejected: [], conditions: [], note: "parametric linear inequality", signature: { kind: "other" },
    verify: () => {
      // spot checks with random parameter values
      let n = 0;
      for (let s = 0; s < 8; s++) {
        const env0 = {};
        params.forEach((p, i) => { env0[p] = ((s * 5 + i * 3) % 7) - 3 + 0.5; });
        const av = cval(X.subs(a, Object.fromEntries(Object.entries(env0).map(([k, v]) => [k, X.num(Q.Q(BigInt(Math.round(v * 2)), 2n))]))), {}).re;
        const ans = answers.find((q) => !q.condition || (q.condition.op === ">" ? av > 0 : q.condition.op === "<" ? av < 0 : av === 0)) || answers[0];
        for (const t of [-7.3, -1.1, 0.4, 2.9, 8.1]) {
          const w = truth(rel, { ...env0, [x]: t }), g = truth(ans.tree, { ...env0, [x]: t });
          if (w === null || g === null) continue;
          if (w !== g) return toContractVerification([{ status: "failed", checks: [{ kind: "probe", ok: false, detail: `disagrees at ${JSON.stringify({ ...env0, [x]: t })}` }] }]);
          n++;
        }
      }
      return toContractVerification([passCheck("probe", `agrees with the original at ${n} random (parameter, ${x}) points`, "numeric")]);
    },
  };
  cand.compare = () => true;
  return cand;
}
