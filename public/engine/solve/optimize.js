// Quelvra solvers: extrema of f(x) (optimization helper).
//
// Critical points: zeros of f' (solveCore, exact or certified numeric) plus points where f is not
// differentiable (zeros of |.| arguments, radicands, denominators of f'). A sign chart of f'
// (exact signs at rational test points) classifies each point: local max (+ to -), local min
// (- to +), or neither. Global claims:
//   * on a closed interval [a, b] (options.interval) with f continuous: compare the values at the
//     critical points and at a, b exactly;
//   * on the real line: the largest local maximum is global when f increases on the leftmost piece
//     and decreases on the rightmost one (then f is below it everywhere); for a nonconstant
//     polynomial the "wrong" direction proves there is no global extremum (f is unbounded).
// Otherwise only local extrema are reported, and the answer says so.
// verify(): f(p) = value exactly, local claims by exact comparison with f at nearby rational
// points, global claims by verifySolutionSet on the inequality value - f(x) >= 0 (or <= 0).

import * as X from "../expr.js";
import * as Q from "../num.js";
import { toText } from "../print.js";
import { verifySolutionSet, truth } from "../verify.js";
import { toContractVerification } from "../orchestrate.js";
import { diff } from "../calc/diff.js";
import { C, safe, fail, cval, signConst, cmpConst, tidy, findAll, denominators, rationalBetween, decimalTree, passCheck, failCheck, openCheck, exactAnswer, hasFn, isZeroExact } from "./util.js";
import { solveCore } from "./core.js";
import { coeffTrees } from "./poly.js";

const GOALS = new Set(["maximize", "minimize", "extrema", "optimize", "max", "min", "maximum", "minimum"]);
export const isOptimizeGoal = (g) => GOALS.has(String(g || ""));
const NOLOG = { add() {}, group: (h, f) => f() };

export function optimizeTarget(node, card, env) {
  const opts = env.options || {};
  let f = node, x = null, goal = opts.goal || (card && card.goal), iv = opts.interval || null;
  if (node.k === "fn" && GOALS.has(node.name)) {
    goal = node.name;
    f = node.args[0];
    if (node.args[1] && node.args[1].k === "sym") x = node.args[1].name;
    if (node.args.length >= 4) iv = [node.args[2], node.args[3]];
  }
  if (!isOptimizeGoal(goal) || !f || f.k === "eq" || f.k === "rel") return null;
  const syms = [...X.freeSymbols(f)];
  x = x || opts.variable || (syms.includes("x") ? "x" : syms.length === 1 ? syms[0] : null);
  if (!x || syms.length !== 1) return null;
  const want = goal.startsWith("max") ? "max" : goal.startsWith("min") ? "min" : "both";
  return { f, x, want, iv };
}

export function solveOptimize(node, card, env) {
  const tg = optimizeTarget(node, card, env);
  if (!tg) return null;
  const { f: f0, x, want } = tg;
  const dom = "real";
  const log = env.log;
  const f = C(f0, dom);
  const X0 = X.sym(x);
  let iv = null;
  if (tg.iv) iv = tg.iv.map((v) => (v && v.k ? C(v) : decimalTree(String(v))));
  const df = C(diff(f, x), dom);
  if (df.k === "deriv") throw fail("could not differentiate f");
  log.add({ rule: "solve.optimize.derivative", title: "Differentiate", why: "Extrema of a differentiable function occur where f'(x) = 0, where f is not differentiable, or at the ends of the interval.", before: f, after: X.eq(X.sym("f'"), df) });
  // critical points
  const S = { x, topVar: x, log: NOLOG, domain: dom, digits: env.digits || 20, checkTime: env.checkTime, allowNumeric: true, depth: 0 };
  const pts = [];
  const add = (t, approx) => { const v = approx ? parseFloat(approx.value) : cval(t).re; if (Number.isFinite(v)) pts.push({ tree: t, v, approx }); };
  const zs = solveCore(C(df), S);
  if (zs.general.length) throw fail("periodic critical points: extrema are not enumerated");
  if (zs.all) throw fail("f is constant");
  if (!zs.complete) throw fail("the critical points could not all be found");
  for (const r of zs.exact) { if (hasFn(r.tree, "W")) throw fail("critical points with Lambert W are not classified"); if (Math.abs(cval(r.tree).im) < 1e-12) add(tidy(r.tree)); }
  for (const a of zs.approx) if (!a.complex) add(decimalTree(a.approx.value), a.approx);
  const nd = [...findAll(f, (w) => w.k === "fn" && w.name === "abs").map((w) => w.args[0]), ...findAll(f, (w) => w.k === "pow" && X.isNum(w.args[1]) && w.args[1].v.d !== 1n).map((w) => w.args[0]), ...denominators(df)];
  for (const g of nd) {
    if (X.freeOf(g, x)) continue;
    const r = solveCore(C(g), S);
    for (const q of r.exact) if (Math.abs(cval(q.tree).im) < 1e-12) add(tidy(q.tree));
  }
  pts.sort((a, b) => a.v - b.v);
  const uniq = [];
  for (const p of pts) if (!uniq.length || Math.abs(uniq[uniq.length - 1].v - p.v) > 1e-12 * Math.max(1, Math.abs(p.v))) uniq.push(p);
  // f must be defined at the point
  const defined = (t) => { const v = safe(() => C(X.subs(f, { [x]: t }))); if (!v || v === X.UNDEF) return null; const c = cval(v); return Number.isFinite(c.re) && Math.abs(c.im) < 1e-12 ? v : null; };
  let cps = uniq.map((p) => ({ ...p, value: p.approx ? null : defined(p.tree) })).filter((p) => p.approx || p.value);
  if (iv) cps = cps.filter((p) => p.v >= cval(iv[0]).re && p.v <= cval(iv[1]).re);
  // sign of f' on each piece (exact at rational test points)
  const bounds = cps.map((p) => p.v);
  const lo = iv ? cval(iv[0]).re : null, hi = iv ? cval(iv[1]).re : null;
  const cuts = [lo, ...bounds, hi];
  const signs = [];
  for (let i = 0; i + 1 < cuts.length; i++) {
    const a = cuts[i], b = cuts[i + 1];
    const t = a === null && b === null ? X.ZERO : a === null ? X.num(Q.Q(BigInt(Math.floor(b) - 1))) : b === null ? X.num(Q.Q(BigInt(Math.ceil(a) + 1))) : X.num(rationalBetween(a, b));
    const d = safe(() => C(X.subs(df, { [x]: t })));
    const s = d ? signConst(d) : null;
    signs.push(s);
  }
  if (signs.some((s) => s === null)) throw fail("could not decide the sign of f' on every interval");
  log.add({ rule: "solve.optimize.sign-chart", title: "Sign of f'", why: `Critical points ${cps.map((p) => (p.approx ? "~" + p.approx.value.slice(0, 12) : toText(p.tree))).join(", ") || "(none)"}; f' is ${signs.map((s) => (s > 0 ? "+" : s < 0 ? "-" : "0")).join(", ")} on the pieces between them.`, before: null, after: null, kind: "note" });
  const answers = [];
  const claims = [];
  const valOf = (p) => (p.approx ? null : p.value);
  cps.forEach((p, i) => {
    const l = signs[i], r = signs[i + 1];
    const type = l > 0 && r < 0 ? "max" : l < 0 && r > 0 ? "min" : null;
    if (!type) return;
    claims.push({ type, p, global: false });
  });
  // endpoints of a closed interval
  if (iv) {
    for (const [e, side] of [[iv[0], 0], [iv[1], 1]]) {
      const v = defined(e);
      if (!v) continue;
      const s = side === 0 ? signs[0] : signs[signs.length - 1];
      const type = side === 0 ? (s > 0 ? "min" : "max") : (s > 0 ? "max" : "min");
      claims.push({ type, p: { tree: e, v: cval(e).re, value: v }, endpoint: true, global: false });
    }
  }
  // global
  const isPoly = !!safe(() => { const cs = coeffTrees(f, x); return cs && cs.length > 1; });
  const globalOf = (type) => {
    const cands = claims.filter((c) => c.type === type && c.p.value);
    if (!cands.length) return null;
    let best = cands[0];
    for (const c of cands.slice(1)) { const cmp = cmpConst(c.p.value, best.p.value); if (cmp === null) return null; if ((type === "max" && cmp > 0) || (type === "min" && cmp < 0)) best = c; }
    if (iv) return { best, why: "closed interval: the largest/smallest of the values at critical points and endpoints" };
    const first = signs[0], last = signs[signs.length - 1];
    const ok = type === "max" ? first > 0 && last < 0 : first < 0 && last > 0;
    if (ok) return { best, why: `f ${type === "max" ? "increases" : "decreases"} up to the first critical point and ${type === "max" ? "decreases" : "increases"} after the last one` };
    return null;
  };
  for (const type of ["max", "min"]) {
    if (want !== "both" && want !== type) continue;
    const g = globalOf(type);
    if (g) g.best.global = true;
    else if (!iv && isPoly) {
      answers.push({ kind: "none", label: `No global ${type === "max" ? "maximum" : "minimum"}: the polynomial is unbounded ${type === "max" ? "above" : "below"}` });
    } else if (!iv) answers.push({ kind: "none", label: `Global ${type === "max" ? "maximum" : "minimum"} not determined (only local extrema are reported)` });
  }
  for (const c of claims) {
    if (want !== "both" && want !== c.type) continue;
    const name = `${c.global ? "global" : "local"} ${c.type === "max" ? "maximum" : "minimum"}${c.endpoint ? " (endpoint)" : ""}`;
    if (c.p.approx) {
      answers.push({ kind: "approx", label: `${name} at ${x} ~ ${c.p.approx.value}`, approx: c.p.approx, at: [[x, c.p.tree]], type: c.type, global: c.global });
    } else {
      const a = exactAnswer(`${name} at ${x} = ${toText(c.p.tree)}`, tidy(c.p.value), env.digits || 20);
      answers.push({ ...a, at: [[x, c.p.tree]], type: c.type, global: c.global });
    }
  }
  if (!answers.length) answers.push({ kind: "none", label: `f has no local ${want === "both" ? "extrema" : want === "max" ? "maximum" : "minimum"}` });
  log.add({ rule: "solve.optimize.result", title: "Classify the critical points", why: answers.map((a) => a.label + (a.tree ? `: f = ${toText(a.tree)}` : "")).join("; ") + ".", before: null, after: null });
  const cand = {
    answers, solutionStatus: answers.some((a) => a.kind === "approx") ? "approximate" : "exact", rejected: [], conditions: [], note: "extrema",
    verify: () => {
      const res = [];
      for (const a of answers) {
        if (!a.at) continue;
        const [, p] = a.at[0];
        if (a.tree) {
          const fv = C(X.subs(f, { [x]: p }));
          res.push(isZeroExact(X.sub(fv, a.tree)) ? passCheck("value", `f(${toText(p)}) = ${toText(a.tree)}`) : failCheck("value", `f(${toText(p)}) != ${toText(a.tree)}`));
        }
        // local check at nearby points
        const v = a.tree ? cval(a.tree).re : cval(C(X.subs(f, { [x]: p }))).re;
        const pv = cval(p).re;
        let okLocal = true;
        for (const h of [1e-3, 1e-4]) for (const s of [-1, 1]) {
          const t = pv + s * h * Math.max(1, Math.abs(pv));
          if (iv && (t < cval(iv[0]).re || t > cval(iv[1]).re)) continue;
          const w = cval(X.subs(f, { [x]: decimalTree(String(t)) || X.num(0) })).re;
          if (!Number.isFinite(w)) continue;
          if (a.type === "max" ? w > v + 1e-12 * Math.max(1, Math.abs(v)) : w < v - 1e-12 * Math.max(1, Math.abs(v))) okLocal = false;
        }
        res.push(okLocal ? passCheck("local", `f is ${a.type === "max" ? "not larger" : "not smaller"} at nearby points`, "numeric") : failCheck("local", "a nearby point beats the claimed extremum"));
        if (a.global && a.tree) {
          const rel = a.type === "max" ? X.rel(">=", a.tree, f) : X.rel("<=", a.tree, f);
          const inSet = iv ? (t) => t >= cval(iv[0]).re && t <= cval(iv[1]).re : () => true;
          const vs = verifySolutionSet(rel, x, (t) => (inSet(t) ? truth(rel, { [x]: t }) !== null : truth(rel, { [x]: t }) === true), { boundaries: bounds, span: Math.max(20, ...bounds.map((b) => Math.abs(b) + 5)) });
          res.push(vs);
        }
      }
      if (!res.length) res.push(passCheck("sign-chart", "f' does not change sign between critical points"));
      return toContractVerification(res);
    },
  };
  cand.compare = () => true;
  return cand;
}
