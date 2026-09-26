// Quelvra solvers: certified numeric roots for equations without a closed form.
//
// h(x) = 0 where h is the numerator of the equation (tan, cot, sec, csc written with sin and cos
// first, so poles do not masquerade as sign changes). Roots come from numeric.findRoots (multi-
// precision refinement, sign-change certified). Then COMPLETENESS is certified independently with
// interval arithmetic:
//   * around each root, an interval enclosure of h' that excludes 0 proves the root is the only one
//     in its neighbourhood (h is monotone there and changes sign);
//   * every other part of the window is proven root-free: the interval enclosure of h excludes 0,
//     or h' excludes 0 and h has the same sign at both ends (recursive bisection, bounded budget);
//   * outside the default window the tails [W, 2W], [2W, 4W], ..., [2^k W, oo) are proven root-free
//     the same way when possible.
// The result says exactly what was proven: "all real roots", "all real roots in [lo, hi]", or
// an explicit incomplete statement. Roots that are rational within 1e-12 are snapped and proven
// exactly.

import * as X from "../expr.js";
import * as IV from "../interval.js";
import { findRoots, makeFuncs } from "../numeric.js";
import { toText } from "../print.js";
import { C, numDen, safe, ratApprox, findAll, isZeroExact, decimalTree } from "./util.js";

const TRIG_REWRITE = { tan: (a) => X.div(X.fn("sin", a), X.fn("cos", a)), cot: (a) => X.div(X.fn("cos", a), X.fn("sin", a)), sec: (a) => X.div(X.ONE, X.fn("cos", a)), csc: (a) => X.div(X.ONE, X.fn("sin", a)) };

export function numeratorForNumerics(e, dom = "real") {
  const r = X.mapTree(e, (w) => (w.k === "fn" && TRIG_REWRITE[w.name] && w.args.length === 1 ? TRIG_REWRITE[w.name](w.args[0]) : w));
  const [n] = numDen(r, dom);
  return n;
}

// Certified root search for h(x) = 0.
//   opts: { lo, hi, fixed (window given by the user), digits, log }
export function certifiedRoots(h, x, opts = {}) {
  const fixed = !!opts.fixed;
  const lo = opts.lo ?? -100, hi = opts.hi ?? 100;
  const digits = opts.digits || 20;
  const fr = findRoots(h, x, { lo, hi, digits, samples: opts.samples || 2000, timeLimitMs: opts.timeLimitMs || 4000 });
  const roots = fr.roots.map((r) => ({ approx: stripRec(r), v: parseFloat(r.value), eb: parseFloat(r.errorBound), certified: !!r.certified, mult: r.multiplicityHint || 1 }))
    .filter((r) => Number.isFinite(r.v)).sort((a, b) => a.v - b.v);
  const F0 = safe(() => makeFuncs(h, x, 0, "real"));
  const F1 = safe(() => makeFuncs(h, x, 1, "real"));
  const notes = [];
  if (!F0 || !F1) return { roots, completeWindow: false, completeAll: false, window: [lo, hi], notes: ["interval evaluation is not available for this function"] };
  let budget = { cells: 20000 };
  // 1. unique neighbourhoods
  const nb = [];
  let unique = true;
  roots.forEach((r, i) => {
    const left = i > 0 ? (r.v + roots[i - 1].v) / 2 : lo, right = i + 1 < roots.length ? (r.v + roots[i + 1].v) / 2 : hi;
    let rho = Math.min(1e-3 * Math.max(1, Math.abs(r.v)), (r.v - left) / 2, (right - r.v) / 2);
    let ok = false;
    for (let t = 0; t < 12 && rho > 20 * r.eb; t++) {
      const d = F1.fi(r.v - rho, r.v + rho);
      const a = F0.f(r.v - rho), b = F0.f(r.v + rho);
      if (d.def && d.cont && !IV.isEmpty(d) && !IV.containsZero(d) && Number.isFinite(a) && Number.isFinite(b) && a * b < 0) { ok = true; break; }
      rho /= 8;
    }
    r.unique = ok && r.certified;
    if (!r.unique) unique = false;
    nb.push(ok ? [r.v - rho, r.v + rho] : [r.v - Math.max(rho, 4 * r.eb), r.v + Math.max(rho, 4 * r.eb)]);
  });
  // 2. gaps
  const gaps = [];
  let a = lo;
  for (const [p, q] of nb) { if (p > a) gaps.push([a, p]); a = Math.max(a, q); }
  if (a < hi) gaps.push([a, hi]);
  let gapsOk = true;
  for (const [p, q] of gaps) if (!rootFree(F0, F1, p, q, budget, 0, 40)) { gapsOk = false; break; }
  const completeWindow = unique && gapsOk;
  // 3. tails
  let completeAll = false;
  if (completeWindow && !fixed) {
    completeAll = tailFree(F0, F1, hi, 1, budget) && tailFree(F0, F1, lo, -1, budget);
    if (!completeAll) notes.push(`Outside [${lo}, ${hi}] the absence of further roots could not be proven.`);
  }
  if (!unique) notes.push("Some roots could not be certified as simple (isolated) roots.");
  if (!gapsOk) notes.push(`Interval arithmetic could not prove that the rest of [${lo}, ${hi}] is free of roots.`);
  return { roots, completeWindow, completeAll, window: [lo, hi], notes, discontinuities: fr.discontinuities };
}
function stripRec(r) { const { residual, multiplicityHint, certified, ...rest } = r; return { ...rest, certified: !!certified }; }

function rootFree(F0, F1, a, b, budget, depth, maxDepth) {
  if (!(b > a)) return true;
  if (--budget.cells < 0) return false;
  const enc = F0.fi(a, b);
  if (IV.isEmpty(enc)) return true; // nowhere defined
  if (enc.def && enc.cont && !IV.containsZero(enc)) return true;
  if (enc.def && enc.cont && Number.isFinite(a) && Number.isFinite(b)) {
    const d = F1.fi(a, b);
    const fa = F0.f(a), fb = F0.f(b);
    if (d.def && d.cont && !IV.isEmpty(d) && !IV.containsZero(d) && Number.isFinite(fa) && Number.isFinite(fb) && fa * fb > 0) return true;
  }
  if (depth >= maxDepth) return false;
  let m;
  if (!Number.isFinite(b)) m = Math.max(2 * Math.abs(a), 1) * (b > 0 ? 1 : -1);
  else if (!Number.isFinite(a)) m = -Math.max(2 * Math.abs(b), 1);
  else m = a + (b - a) / 2;
  if (!(m > a && m < b)) return false;
  return rootFree(F0, F1, a, m, budget, depth + 1, maxDepth) && rootFree(F0, F1, m, b, budget, depth + 1, maxDepth);
}
function tailFree(F0, F1, edge, dir, budget) {
  let a = edge;
  for (let i = 0; i < 1100; i++) {
    const b = Math.abs(a) >= 1e300 ? dir * Infinity : a === 0 ? dir : a * 2;
    const [p, q] = dir > 0 ? [a, b] : [b, a];
    if (!rootFree(F0, F1, p, q, budget, 0, Number.isFinite(b) ? 10 : 0)) return false;
    if (!Number.isFinite(b)) return true;
    a = b;
  }
  return false;
}

// Solve e = 0 numerically (fallback strategy). Returns a core solution record.
export function solveNumeric(e, S) {
  const x = S.x, dom = S.domain;
  if (dom === "complex") return null;
  const h = C(numeratorForNumerics(e, dom), dom);
  if (X.freeOf(h, x)) return null;
  if (findAll(h, (w) => w.k === "sym" && w.name !== x).length) return null;
  const iv = S.interval;
  const cr = certifiedRoots(h, x, { lo: iv ? iv[0] : -100, hi: iv ? iv[1] : 100, fixed: !!iv, digits: S.digits || 20 });
  const out = { exact: [], approx: [], general: [], regions: [], all: false, complete: iv ? cr.completeWindow : cr.completeAll, methods: ["numeric"], notes: cr.notes, window: iv || (cr.completeAll ? null : cr.window), numeric: cr };
  const lo = cr.window[0], hi = cr.window[1];
  const statement = cr.completeAll ? `Proven complete: every real root of ${toText(h)} = 0 is listed (interval arithmetic excludes roots everywhere else, including x -> +-infinity).`
    : cr.completeWindow ? `Proven complete on [${lo}, ${hi}]: interval arithmetic excludes further roots there${iv ? "" : "; outside that range the search is not exhaustive"}.`
      : `Searched [${lo}, ${hi}]; completeness could not be proven.`;
  out.statement = statement;
  for (const r of cr.roots) {
    // snap to a rational and prove it exactly
    const q = ratApprox(r.v, 1000);
    if (q && Math.abs(Number(q.n) / Number(q.d) - r.v) <= 1e-12 * Math.max(1, Math.abs(r.v))) {
      const t = X.num(q);
      if (safe(() => isZeroExact(X.subs(e, { [x]: t }), dom))) { out.exact.push({ tree: t, multiplicity: r.mult, numeric: true }); continue; }
    }
    out.approx.push({ value: r.v, approx: r.approx, certified: r.certified && r.unique !== false, unique: r.unique, multiplicity: r.mult });
  }
  S.log.add({ rule: "solve.numeric.roots", title: "Locate the roots numerically", why: `No closed form applies. Roots of ${toText(h)} = 0 are bracketed by sign changes and refined in multiprecision arithmetic. ${statement}`, before: X.eq(e, X.ZERO), after: X.or(...[...out.exact.map((r) => X.eq(X.sym(x), r.tree)), ...out.approx.map((r) => X.eq(X.sym(x), decimalTree(r.approx.value) || X.sym(x)))]), kind: "approximation" });
  return out;
}
