// Quelvra function analysis: inverse functions.
//
// Derivation: the sign chart of f' splits the domain into maximal monotone pieces. Solving
// y = f(x) for x gives candidate formulas (isolation of a single occurrence of x, or the linear /
// quadratic formula after clearing denominators); the branch that inverts f on the chosen piece is
// kept. When one formula inverts f on the whole domain, f is one-to-one there; otherwise f is
// restricted to one monotone piece (the rightmost unbounded piece, or for periodic functions the
// piece through or starting at 0, which gives the usual principal branches).
//
// Verification (independent): f(g(y)) = y (exactly when the simplifier can show it, and
// numerically at sample points of the inverse's domain) and g(f(x)) = x at sample points of the
// restricted domain, all with the verifier's evaluator on the ORIGINAL f.

import { toContractVerification } from "../orchestrate.js";
import { together, numerDenom, expand } from "../simplify.js";
import { coeffTrees } from "../solve/poly.js";
import { X, toText, C, safe, fail, dv, fAt, evalReal, setTree, ivOut, ivsText, pass, bad, fnAndVar, tidy, valueAt } from "./util.js";
import { analyze, images, monotonePieces } from "./core.js";

const INV1 = {
  ln: (r) => [X.pow(X.E, r)], exp: (r) => [X.fn("ln", r)], sqrt: (r) => [X.pow(r, X.TWO)], cbrt: (r) => [X.pow(r, X.num(3))],
  sin: (r) => [X.fn("asin", r), X.sub(X.PI, X.fn("asin", r))], cos: (r) => [X.fn("acos", r), X.neg(X.fn("acos", r))], tan: (r) => [X.fn("atan", r)],
  asin: (r) => [X.fn("sin", r)], acos: (r) => [X.fn("cos", r)], atan: (r) => [X.fn("tan", r)],
  sinh: (r) => [X.fn("asinh", r)], cosh: (r) => [X.fn("acosh", r), X.neg(X.fn("acosh", r))], tanh: (r) => [X.fn("atanh", r)],
  asinh: (r) => [X.fn("sinh", r)], acosh: (r) => [X.fn("cosh", r)], atanh: (r) => [X.fn("tanh", r)],
  abs: (r) => [r, X.neg(r)],
};
const count = (u, x) => (u.k === "sym" && u.name === x ? 1 : (u.args || []).reduce((s, a) => s + count(a, x), 0));

function isolate(u, rhs, x, depth = 0) {
  if (depth > 40) return [];
  if (u.k === "sym" && u.name === x) return [rhs];
  const inX = (w) => !X.freeOf(w, x);
  switch (u.k) {
    case "add": {
      const part = u.args.find(inX), rest = u.args.filter((a) => a !== part);
      return isolate(part, X.sub(rhs, X.add(...rest)), x, depth + 1);
    }
    case "mul": {
      const part = u.args.find(inX), rest = u.args.filter((a) => a !== part);
      return isolate(part, X.div(rhs, X.mul(...rest)), x, depth + 1);
    }
    case "pow": {
      const [b, e] = u.args;
      if (inX(b) && !inX(e)) {
        if (!X.isNum(e)) return [];
        const r = X.pow(rhs, C(X.recip(e)));
        const cands = [r];
        if (e.v.n % 2n === 0n) cands.push(X.neg(r));
        return cands.flatMap((c) => isolate(b, c, x, depth + 1));
      }
      if (inX(e) && !inX(b)) {
        const r = b === X.E ? X.fn("ln", rhs) : X.fn("log", b, rhs);
        return isolate(e, r, x, depth + 1);
      }
      return [];
    }
    case "fn": {
      if (u.name === "log") {
        if (u.args.length === 1) return isolate(u.args[0], X.pow(X.num(10), rhs), x, depth + 1);
        if (!inX(u.args[0])) return isolate(u.args[1], X.pow(u.args[0], rhs), x, depth + 1);
        return [];
      }
      const inv = INV1[u.name];
      if (!inv || u.args.length !== 1) return [];
      return inv(rhs).flatMap((c) => isolate(u.args[0], c, x, depth + 1));
    }
    default: return [];
  }
}

// Candidate formulas x = g(y) for y = f(x).
export function inverseCandidates(f, x, y) {
  const Y0 = X.sym(y);
  const out = [];
  if (count(f, x) === 1) out.push(...isolate(f, Y0, x));
  const fs = C(f);
  if (count(fs, x) === 1 && fs !== f) out.push(...isolate(fs, Y0, x));
  // rational: numerator of f - y is linear or quadratic in x
  const lin = safe(() => {
    const t = together(C(X.sub(fs, Y0)));
    const [n] = numerDenom(t);
    const cs = coeffTrees(expand(n), x);
    if (!cs || cs.some((c) => !X.freeOf(c, x))) return null;
    if (cs.length === 2) return [X.div(X.neg(cs[0]), cs[1])];
    if (cs.length === 3) {
      const [c0, c1, c2] = cs;
      const disc = X.sqrt(X.sub(X.pow(c1, X.TWO), X.mul(X.num(4), c2, c0)));
      return [X.div(X.add(X.neg(c1), disc), X.mul(X.TWO, c2)), X.div(X.sub(X.neg(c1), disc), X.mul(X.TWO, c2))];
    }
    return null;
  });
  if (lin) out.push(...lin);
  const uniq = [];
  for (const c of out) { const s = safe(() => tidy(C(c))); if (s && !uniq.includes(s) && s !== X.UNDEF) uniq.push(s); }
  return uniq;
}

const inside = (piece, t) => t > piece.lo.v && t < piece.hi.v;
function samplesIn(piece, n = 14) {
  const a = Number.isFinite(piece.lo.v) ? piece.lo.v : (Number.isFinite(piece.hi.v) ? piece.hi.v : 0) - 25;
  const b = Number.isFinite(piece.hi.v) ? piece.hi.v : a + 25 + (Number.isFinite(piece.lo.v) ? 0 : 25);
  const out = [];
  for (let i = 1; i < n; i++) out.push(a + ((b - a) * (i + 0.137)) / (n + 0.3));
  return out.filter((t) => inside(piece, t));
}
function inverts(f, x, g, y, pieces) {
  let n = 0;
  for (const p of pieces) for (const t of samplesIn(p)) {
    const v = fAt(f, x, t);
    if (!Number.isFinite(v)) continue;
    const back = evalReal(g, { [y]: v });
    if (!Number.isFinite(back) || Math.abs(back - t) > 1e-7 * Math.max(1, Math.abs(t))) return false;
    n++;
  }
  return n >= 4;
}

export function cmdInverse(node, env) {
  const { f, x } = fnAndVar(node.args, "inverse");
  const y = x === "y" ? "u" : "y";
  const res = analyze(f, x, env);
  const pieces = monotonePieces(res).filter((p) => p.hi.v > p.lo.v);
  if (pieces.some((p) => p.sign === 0)) throw fail("f is constant on an interval, so it has no inverse there");
  env.log.add({ rule: "analysis.inverse.monotone", title: "Where is f one-to-one?", why: `f'(${x}) = ${toText(res.df)}. f is strictly monotone on ${pieces.map((p) => `(${p.lo.tree ? toText(p.lo.tree) : "-oo"}, ${p.hi.tree ? toText(p.hi.tree) : "oo"})`).join(", ")}.`, before: res.f, after: res.df });
  const cands = inverseCandidates(f, x, y);
  if (!cands.length) throw fail(`Quelvra could not solve ${y} = ${toText(f)} for ${x}`);
  env.log.add({ rule: "analysis.inverse.solve", title: `Solve ${y} = f(${x}) for ${x}`, why: `Candidate formulas: ${cands.map((c) => `${x} = ${toText(c)}`).join("; ")}.`, before: X.eq(X.sym(y), f), after: X.eq(X.sym(x), cands[0]) });
  // whole domain
  let g = null, region = null, restricted = false;
  const all = res.win && res.win.periodic ? null : pieces;
  if (all) for (const c of cands) if (inverts(f, x, c, y, all)) { g = c; region = all; break; }
  if (!g) {
    // restrict: rightmost unbounded piece (non-periodic) or the principal piece through / from 0
    let pick = null;
    if (res.win && res.win.periodic) pick = pieces.find((p) => p.lo.v < 0 && p.hi.v > 0) || pieces.find((p) => Math.abs(p.lo.v) < 1e-12);
    else pick = pieces[pieces.length - 1];
    if (!pick) throw fail("no suitable interval on which f is one-to-one was found");
    for (const c of cands) if (inverts(f, x, c, y, [pick])) { g = c; region = [pick]; break; }
    if (!g) throw fail("none of the candidate formulas inverts f on the chosen interval");
    restricted = true;
  }
  // inverse's domain: the image of the region
  const lo = region[0].lo, hi = region[region.length - 1].hi;
  const incl = (e, isLo) => {
    if (!e.tree) return false;
    const comp = region.find((p) => (isLo ? p.lo === e : p.hi === e));
    const compEnd = comp && (isLo ? comp.comp.lo : comp.comp.hi);
    if (compEnd && compEnd.v === e.v) return !compEnd.open;
    return valueAt(f, x, e.tree) !== null;
  };
  const win = restricted ? { lo: lo.tree, hi: hi.tree, loOpen: !incl(lo, true), hiOpen: !incl(hi, false) } : null;
  const res2 = restricted ? analyze(f, x, env, { window: win }) : res;
  const im = images(res2);
  const gx = tidy(C(X.subs(g, { [y]: X.sym(x) })));
  const domIvs = im.union;
  const X0 = X.sym(x);
  const restrictTree = restricted ? setTree([{ lo: win.lo, hi: win.hi, loOpen: win.loOpen, hiOpen: win.hiOpen }], x) : null;
  const conditions = restrictTree && restrictTree !== X.TRUE ? [restrictTree] : [];
  if (restricted) env.log.add({ rule: "analysis.inverse.restrict", title: "Restrict the domain", why: `f is not one-to-one on its whole domain, so it is restricted to ${toText(restrictTree)}, where it is strictly ${region[0].sign > 0 ? "increasing" : "decreasing"}; the formula ${x} = ${toText(g)} is the branch that inverts it there.`, kind: "conditional", conditions });
  else env.log.add({ rule: "analysis.inverse.one-to-one", title: "f is one-to-one", why: `The single formula ${x} = ${toText(g)} recovers ${x} from f(${x}) on every monotone piece, so f is one-to-one on its whole domain.`, kind: "note" });
  env.log.add({ rule: "analysis.inverse.result", title: "Swap the roles of x and y", why: `f^(-1)(${x}) = ${toText(gx)}, defined for ${x} in the range of f${restricted ? " on the restricted domain" : ""}: ${ivsText(domIvs)}.`, before: g, after: gx });
  const label = restricted ? `Inverse function f^(-1)(${x}) (f restricted to ${toText(restrictTree)})` : `Inverse function f^(-1)(${x})`;
  return {
    answers: [
      { kind: "exact", label, tree: gx },
      { kind: "set", label: "Domain of the inverse", variable: x, tree: setTree(domIvs, x), interval: ivOut(domIvs), text: ivsText(domIvs) },
    ],
    conditions, solutionStatus: "exact",
    graph: { exprs: [f, gx, X0], marks: [] },
    verify: () => toContractVerification(verifyInverse(f, x, g, y, region, domIvs)),
  };
}

function verifyInverse(f, x, g, y, region, domIvs) {
  const out = [];
  // exact: f(g(y)) - y simplifies to 0
  const comp = safe(() => C(X.sub(X.subs(C(f), { [x]: g }), X.sym(y))));
  if (comp === X.ZERO) out.push({ status: "verified-exact", checks: [{ kind: "f(g(y)) = y", ok: true, detail: `f(${toText(g)}) simplifies to ${y}` }] });
  // numeric: g(f(t)) = t on the region
  let n = 0;
  for (const p of region) for (const t of samplesIn(p, 25)) {
    const v = fAt(f, x, t);
    if (!Number.isFinite(v)) continue;
    const back = evalReal(g, { [y]: v });
    if (!Number.isFinite(back) || Math.abs(back - t) > 1e-7 * Math.max(1, Math.abs(t))) return [bad("g(f(x)) = x", `at ${x} = ${+t.toPrecision(8)}: g(f(x)) = ${back}`)];
    n++;
  }
  out.push(pass("g(f(x)) = x", `g(f(${x})) = ${x} at ${n} points of the restricted domain`));
  // numeric: f(g(s)) = s on the inverse's domain
  let m = 0;
  for (const iv of domIvs) {
    const a = iv.lo === null ? (iv.hi === null ? -20 : dv(iv.hi) - 20) : dv(iv.lo), b = iv.hi === null ? a + 40 : dv(iv.hi);
    for (let i = 1; i < 20; i++) {
      const s = a + ((b - a) * (i + 0.21)) / 20.5;
      const gv = evalReal(g, { [y]: s });
      if (!Number.isFinite(gv)) return [bad("f(g(y)) = y", `g is undefined at ${y} = ${+s.toPrecision(8)}, which is in its claimed domain`)];
      const back = fAt(f, x, gv);
      if (!Number.isFinite(back) || Math.abs(back - s) > 1e-7 * Math.max(1, Math.abs(s))) return [bad("f(g(y)) = y", `at ${y} = ${+s.toPrecision(8)}: f(g(y)) = ${back}`)];
      m++;
    }
  }
  out.push(pass("f(g(y)) = y", `f(g(${y})) = ${y} at ${m} points of the inverse's domain`));
  return out;
}
