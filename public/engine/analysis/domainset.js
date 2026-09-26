// Quelvra function analysis: the real domain of f(x) as an interval set.
//
// Derivation: domain.js lists the conditions every subexpression imposes (denominators nonzero,
// even-root radicands >= 0, log arguments > 0, arcsin arguments in [-1, 1], ...). Conditions that
// are not periodic are solved together by the inequality solver (exact sign chart). Periodic
// exclusions (tan, sec, cot, csc, 1/sin(x), ...) are solved as equations whose solution families
// are listed as excluded points x != a + k p.
//
// Verification (independent): the verifier's evaluator decides definedness of the ORIGINAL f at
// probe points inside every interval, just outside every boundary, between boundaries and on a
// coarse grid; finite endpoints are checked exactly (open end = undefined, closed end = defined).

import { inferDomain } from "../domain.js";
import { solveInequality } from "../solve/inequality.js";
import { X, toText, C, safe, fail, dv, zerosOf, familyMembers, setTree, ivOut, inIvs, probeGrid, definedNum, valueAt, pass, bad, NOLOG, sortUniq, ivsText } from "./util.js";

const TRIGS = new Set(["sin", "cos", "tan", "cot", "sec", "csc"]);
const hasTrigX = (u, x) => (u.k === "fn" && TRIGS.has(u.name) && !X.freeOf(u, x)) || (u.args || []).some((a) => hasTrigX(a, x));

// -> { ivs, families, conditions: [rel], reasons: [string], approx, tree }
export function domainSet(f, x, env) {
  const dom = inferDomain(f);
  const reasons = [];
  if (dom.empty) return finish({ ivs: [], families: [], conditions: dom.rels, reasons: ["the conditions are contradictory"], approx: false }, x);
  const plain = [], periodic = [];
  for (const c of dom.conditions) {
    const r = c.rel;
    if (X.freeOf(r, x)) {
      const s = safe(() => C(r));
      if (s === X.FALSE) return finish({ ivs: [], families: [], conditions: [r], reasons: [c.reason], approx: false }, x);
      continue;
    }
    if (r.k === "fn" || r.k === "not" || containsIsInteger(r)) throw fail(`the domain needs the condition ${toText(r)}, which is not an interval condition`);
    reasons.push(`${toText(r)}: ${c.reason}`);
    if (hasTrigX(r, x)) {
      if (!(r.k === "rel" && r.op === "!=" && r.args[1] === X.ZERO)) throw fail(`the periodic domain condition ${toText(r)} is not supported`);
      periodic.push(r);
    } else plain.push(r);
  }
  // periodic exclusions: zeros of the expression
  const families = [];
  for (const r of periodic) {
    const z = zerosOf(r.args[0], x, env);
    if (z.all) return finish({ ivs: [], families: [], conditions: [r], reasons, approx: false }, x);
    families.push(...z.families);
    for (const p of z.points) plain.push(X.rel("!=", X.sym(x), p.tree));
  }
  let ivs, approx = false;
  if (!plain.length) ivs = [{ lo: null, hi: null, loOpen: true, hiOpen: true }];
  else {
    const rel = plain.length === 1 ? plain[0] : X.and(...plain);
    const innerEnv = { log: NOLOG, domain: "real", digits: env.digits || 20, checkTime: env.checkTime, options: { variable: x } };
    let c;
    try { c = solveInequality(rel, { unknowns: [x] }, innerEnv, "exact"); } catch (e) { throw fail(`the domain conditions ${toText(rel)} could not be solved (${e.message})`); }
    if (!c || !c.answers || !c.answers[0] || c.answers[0].kind !== "set") throw fail(`the domain conditions ${toText(rel)} could not be solved`);
    const a = c.answers[0];
    ivs = (a.interval || []).map((iv) => ({ lo: iv.lo, hi: iv.hi, loOpen: iv.lo === null ? true : iv.loOpen, hiOpen: iv.hi === null ? true : iv.hiOpen }));
    if (a.tree === X.TRUE) ivs = [{ lo: null, hi: null, loOpen: true, hiOpen: true }];
    approx = !!a.approxEndpoints;
  }
  // de-duplicate families by value modulo period
  const fams = [];
  for (const f0 of families) if (!fams.some((g) => Math.abs(g.p - f0.p) < 1e-12 && Math.abs(((f0.o - g.o) / g.p) - Math.round((f0.o - g.o) / g.p)) < 1e-9)) fams.push(f0);
  return finish({ ivs, families: fams, conditions: dom.rels, reasons, approx }, x);
}
function containsIsInteger(r) { return (r.k === "fn" && r.name === "isInteger") || (r.args || []).some(containsIsInteger); }

function finish(d, x) {
  const X0 = X.sym(x);
  let tree = setTree(d.ivs, x);
  if (d.families.length) {
    const k = X.sym("k");
    const ex = d.families.map((f) => X.rel("!=", X0, C(X.add(f.offset, X.mul(f.period, k)))));
    tree = tree === X.TRUE ? (ex.length === 1 ? ex[0] : X.and(...ex)) : X.and(tree, ...ex);
  }
  d.tree = tree;
  d.contains = (t) => inIvs(d.ivs, t) && !d.families.some((f) => { const q = (t - f.o) / f.p; return Math.abs(q - Math.round(q)) * f.p <= 1e-9 * Math.max(1, Math.abs(t)); });
  d.text = ivsText(d.ivs) + (d.families.length ? ` without ${d.families.map((f) => `${toText(f.offset)} + k*${toText(f.period)}`).join(", ")} (k any integer)` : "");
  return d;
}

// Domain components intersected with a window { lo, hi, loOpen, hiOpen } (tree ends, null = infinite).
// Periodic exclusions inside the window split the components. Each component carries cut flags:
// an end that is only the window's edge (not a real boundary of the domain) has cut = true.
export function components(d, win = null) {
  const out = [];
  const W = win || { lo: null, hi: null, loOpen: true, hiOpen: true };
  const wlo = W.lo === null ? -Infinity : dv(W.lo), whi = W.hi === null ? Infinity : dv(W.hi);
  for (const iv of d.ivs) {
    const lo = iv.lo === null ? -Infinity : dv(iv.lo), hi = iv.hi === null ? Infinity : dv(iv.hi);
    // intersection
    let L, H;
    if (lo > wlo || (lo === wlo && Number.isFinite(lo))) L = { tree: iv.lo, v: lo, open: iv.loOpen || (lo === wlo && W.loOpen), cut: false };
    else L = { tree: W.lo, v: wlo, open: W.lo === null ? true : W.loOpen, cut: W.lo !== null };
    if (hi < whi || (hi === whi && Number.isFinite(hi))) H = { tree: iv.hi, v: hi, open: iv.hiOpen || (hi === whi && W.hiOpen), cut: false };
    else H = { tree: W.hi, v: whi, open: W.hi === null ? true : W.hiOpen, cut: W.hi !== null };
    if (L.v > H.v || (L.v === H.v && (L.open || H.open))) continue;
    // split at periodic exclusions
    const lo2 = Number.isFinite(L.v) ? L.v : -1e6, hi2 = Number.isFinite(H.v) ? H.v : 1e6;
    if (d.families.length && (!Number.isFinite(L.v) || !Number.isFinite(H.v))) throw fail("a periodic function needs a finite window here");
    const ex = sortUniq(familyMembers(d.families, lo2, hi2));
    let cur = L;
    for (const p of ex) {
      if (p.v < cur.v - 1e-12 || p.v > H.v + 1e-12) continue;
      if (Math.abs(p.v - cur.v) <= 1e-12 * Math.max(1, Math.abs(p.v))) { cur = { ...cur, open: true, cut: false }; continue; }
      if (Math.abs(p.v - H.v) <= 1e-12 * Math.max(1, Math.abs(p.v))) { H.open = true; H.cut = false; continue; }
      out.push({ lo: cur, hi: { tree: p.tree, v: p.v, open: true, cut: false } });
      cur = { tree: p.tree, v: p.v, open: true, cut: false };
    }
    out.push({ lo: cur, hi: H });
  }
  return out;
}

// Verification of a domain claim against the ORIGINAL f.
export function verifyDomain(f, x, d) {
  const bounds = [];
  for (const iv of d.ivs) { if (iv.lo !== null) bounds.push(dv(iv.lo)); if (iv.hi !== null) bounds.push(dv(iv.hi)); }
  const fam = familyMembers(d.families, -30, 30).map((p) => p.v);
  const span = Math.max(30, ...bounds.filter(Number.isFinite).map((b) => Math.abs(b) + 5));
  let n = 0;
  for (const t of probeGrid([...bounds, ...fam], span, 400)) {
    // points extremely close to an excluded periodic point are skipped (double rounding decides them)
    if (fam.some((b) => Math.abs(b - t) < 1e-7) && Math.abs(fam.find((b) => Math.abs(b - t) < 1e-7) - t) < 1e-7) continue;
    const want = d.contains(t), got = definedNum(f, x, t);
    if (want !== got) return bad("probe", `at ${x} = ${+t.toPrecision(8)} the function is ${got ? "defined" : "undefined"}, but the claimed domain says ${want ? "defined" : "undefined"}`);
    n++;
  }
  // exact ends
  let ends = 0;
  for (const iv of d.ivs) for (const [e, isOpen] of [[iv.lo, iv.loOpen], [iv.hi, iv.hiOpen]]) {
    if (e === null || d.approx) continue;
    const v = valueAt(f, x, e);
    const defined = v !== null;
    if (defined === !!isOpen) return bad("endpoint", `at ${x} = ${toText(e)} the function is ${defined ? "defined" : "undefined"}, but the endpoint is ${isOpen ? "open" : "closed"}`);
    ends++;
  }
  for (const p of familyMembers(d.families, -7, 7)) {
    if (valueAt(f, x, p.tree) !== null) return bad("excluded point", `f is defined at the excluded point ${toText(p.tree)}`);
    ends++;
  }
  return pass("probe", `definedness of the original function agrees with the claimed domain at ${n} probe points (inside, just outside every boundary, and on a grid) and at ${ends} exact boundary points`);
}
