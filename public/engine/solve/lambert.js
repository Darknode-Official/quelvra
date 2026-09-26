// Quelvra solvers: equations solved with the Lambert W function.
//
// Canonical form (a x + b)^n * B^(c x + d) = K with integer n != 0, constant B > 0, c != 0. Taking
// the n-th root (both signs for even n) and y = a x + b gives y e^(g y) = R e^(...), and multiplying
// by g gives the form w e^w = z, so g y = W(z). On the reals W0 exists for z >= -1/e and the lower
// branch W-1 for -1/e < z < 0; nothing exists for z < -1/e.
// Recognised shapes: Q^n B^L = K, (linear) + k B^L = 0, m Q^n + k B^L = 0; a single ln(linear) is
// substituted away first (x ln x = K, x + ln x = K); x^x style powers are handled by core.js.
// W values that are elementary (e^w rational, or w rational) are snapped to exact trees and proven
// exactly; the rest are reported as W(z) with a certified multiprecision value.

import * as X from "../expr.js";
import * as Q from "../num.js";
import { toText } from "../print.js";
import { C, EX, tidy, safe, signConst, cmpConst, isZeroExact, findAll, num, hp, ratApprox, decimalTree, fail } from "./util.js";
import { coeffTrees } from "./poly.js";
import { lambertWBig, W, isW, branchOf } from "./lambertw.js";

const dep = (u, x) => !X.freeOf(u, x);
function linear(u, x) {
  const cs = safe(() => coeffTrees(u, x));
  if (!cs || cs.length !== 2 || cs.some((c) => dep(c, x))) return null;
  return { a: cs[1], b: cs[0] };
}
// k * Q^n * B^L with Q linear (optional), constant B > 0, L linear with nonzero slope (optional)
function parseTerm(t, x, dom) {
  const fs = t.k === "mul" ? t.args : [t];
  const ks = [];
  let Qd = null, n = 0n, Bd = null, L = null;
  for (const f of fs) {
    if (!dep(f, x)) { ks.push(f); continue; }
    if (f.k === "pow" && !dep(f.args[0], x)) { if (Bd) return null; Bd = f.args[0]; L = linear(f.args[1], x); if (!L) return null; continue; }
    let base = f, e = 1n;
    if (f.k === "pow" && X.isInt(f.args[1])) { base = f.args[0]; e = f.args[1].v.n; }
    const lq = linear(base, x);
    if (!lq || Qd) return null;
    Qd = { ...lq, tree: base }; n = e;
  }
  if (Bd && signConst(Bd, dom) !== 1) return null;
  if (Bd && isZeroExact(X.sub(Bd, X.ONE), dom)) return null;
  return { k: C(X.mul(...ks), dom), Q: Qd, n, B: Bd, L };
}

export function solveLambert(e, S) {
  const x = S.x, dom = S.domain;
  if (dom === "complex") return null;
  // substitute a single ln(a x + b)
  const lns = findAll(e, (w) => w.k === "fn" && w.name === "ln" && dep(w, x));
  if (lns.length === 1 && !findAll(e, (w) => w.k === "pow" && !dep(w.args[0], x) && dep(w.args[1], x)).length) {
    const lin = linear(lns[0].args[0], x);
    if (!lin) return null;
    const uN = "υ", u = X.sym(uN);
    const xOfU = X.div(X.sub(X.exp(u), lin.b), lin.a);
    const g = C(X.subs(X.replace(e, lns[0], u), { [x]: xOfU }), dom);
    if (dep(g, x)) return null;
    const inner = safe(() => solveForm(g, { ...S, x: uN }), null);
    if (!inner) return null;
    S.log.add({ rule: "solve.lambert.log-sub", title: `Substitute u = ${toText(lns[0])}`, why: `Then ${toText(lns[0].args[0])} = e^u, which turns the equation into one of the form w e^w = z.`, before: X.eq(e, X.ZERO), after: X.eq(X.subs(g, { [uN]: X.sym("u") }), X.ZERO) });
    const out = inner.sol;
    out.exact = out.exact.map((r) => ({ ...r, tree: tidy(X.subs(xOfU, { [uN]: r.tree }), dom) }));
    return out;
  }
  const r = solveForm(e, S);
  return r ? r.sol : null;
}

function solveForm(e, S) {
  const x = S.x, dom = S.domain;
  const terms = e.k === "add" ? e.args : [e];
  const xs = terms.filter((t) => dep(t, x)), cs = terms.filter((t) => !dep(t, x));
  let form = null; // { Q, n, B, L, K }
  if (xs.length === 1) {
    const p = parseTerm(xs[0], x, dom);
    if (p && p.Q && p.B && p.n !== 0n) form = { Q: p.Q, n: p.n, B: p.B, L: p.L, K: C(X.div(X.neg(X.add(...cs)), p.k), dom) };
  } else if (xs.length >= 2) {
    // exponential term + everything else (a linear polynomial or a power of a linear)
    const ex = xs.filter((t) => findAll(t, (w) => w.k === "pow" && !dep(w.args[0], x) && dep(w.args[1], x)).length);
    if (ex.length !== 1) return null;
    const p = parseTerm(ex[0], x, dom);
    if (!p || !p.B || p.Q) return null;
    const rest = C(X.add(...terms.filter((t) => t !== ex[0])), dom);
    const lin = linear(rest, x);
    let Qd, n, m;
    if (lin) { Qd = { ...lin, tree: rest }; n = 1n; m = X.ONE; }
    else {
      const q = parseTerm(rest, x, dom);
      if (!q || !q.Q || q.B || q.n === 0n) return null;
      Qd = q.Q; n = q.n; m = q.k;
    }
    // m Q^n + k B^L = 0  ->  Q^n B^(-L) = -k/m
    form = { Q: Qd, n, B: p.B, L: { a: C(X.neg(p.L.a), dom), b: C(X.neg(p.L.b), dom) }, K: C(X.div(X.neg(p.k), m), dom) };
  }
  if (!form) return null;
  const { Q: Qd, n, B, L, K } = form;
  if (signConst(L.a, dom) === 0) return null;
  const sK = signConst(K, dom);
  if (sK === null) return null;
  const X0 = X.sym(x);
  const lhs = C(X.mul(X.pow(Qd.tree, X.num(Q.Q(n))), X.pow(B, X.add(X.mul(L.a, X0), L.b))), dom);
  S.log.add({ rule: "solve.lambert.form", title: "Recognise a Lambert W equation", why: "The unknown appears both in a power and in an exponent; such equations are solved with the Lambert W function, defined by W(z) e^(W(z)) = z.", before: X.eq(e, X.ZERO), after: X.eq(lhs, K) });
  const out = { exact: [], approx: [], general: [], regions: [], all: false, complete: true, methods: ["lambert"], notes: [] };
  if (sK === 0) {
    // Q^n B^L = 0: only Q = 0 (n > 0)
    if (n > 0n) out.exact.push({ tree: tidy(X.div(X.neg(Qd.b), Qd.a), dom), multiplicity: 1 });
    return { sol: out };
  }
  const nn = n < 0n ? -n : n;
  let Rs = [];
  if (nn % 2n === 0n) {
    if (sK < 0) { out.notes.push("an even power times a positive exponential is never negative"); return { sol: out }; }
    const r = C(X.pow(K, X.num(Q.Q(1n, n))), dom);
    Rs = [r, C(X.neg(r), dom)];
  } else Rs = [C(X.pow(K, X.num(Q.Q(1n, n))), dom)];
  // Q^n B^L = K -> Q * B^(L/n) = R  ; y = a x + b, x = (y - b)/a
  // exponent (lnB/n)(L.a (y - b)/a + L.b) = g y + h
  const lnB = B === X.E ? X.ONE : X.fn("ln", B);
  const mu = C(X.div(lnB, X.num(Q.Q(n))), dom);
  const g = tidy(X.div(X.mul(mu, L.a), Qd.a), dom);
  const h = C(X.mul(mu, X.sub(L.b, X.div(X.mul(L.a, Qd.b), Qd.a))), dom);
  for (const R of Rs) {
    // y e^(g y) = R e^(-h)  ->  (g y) e^(g y) = g R e^(-h) = z
    const z = tidy(X.mul(g, R, X.exp(X.neg(h))), dom);
    const w = X.sym("w");
    S.log.add({ rule: "solve.lambert.canonical", title: "Bring it to the form w e^w = z", why: `With y = ${toText(Qd.tree)}${nn > 1n ? " (after taking the " + nn + "th root" + (nn % 2n === 0n ? ", both signs" : "") + ")" : ""} and w = ${toText(g)} y: w e^w = ${toText(z)}.`, before: null, after: X.eq(X.mul(w, X.exp(w)), z) });
    const branches = wBranches(z, S);
    if (branches === null) throw fail("could not compare the Lambert argument with -1/e");
    for (const br of branches) {
      const wv = wValue(z, br, S);
      if (!wv) throw fail("Lambert W evaluation failed");
      const xt = tidy(X.div(X.sub(X.div(wv.tree, g), Qd.b), Qd.a), dom);
      S.log.add({ rule: "solve.lambert.solve", title: br === -1 ? "Lower branch W-1" : "Principal branch W0", why: wv.snapped ? `${toText(br === -1 ? W(z, -1) : W(z))} = ${toText(wv.tree)} exactly, since ${toText(wv.tree)} e^(${toText(wv.tree)}) = ${toText(z)}.` : `w = ${toText(wv.tree)} ~ ${wv.value}.`, before: null, after: X.eq(X0, xt) });
      out.exact.push({ tree: xt, multiplicity: 1, lambert: !wv.snapped });
    }
  }
  return { sol: out };
}
// which real branches exist for W(z)
function wBranches(z, S) {
  const dom = S.domain;
  const sz = signConst(z, dom);
  if (sz === null) return null;
  if (sz >= 0) return [0];
  const c = cmpConst(z, X.neg(X.exp(X.NEG_ONE)), dom);
  if (c === null) return null;
  if (c < 0) { S.log.add({ rule: "solve.lambert.no-real", title: "No real branch", why: `W(z) is real only for z >= -1/e, and ${toText(z)} < -1/e.`, before: null, after: X.FALSE }); return []; }
  if (c === 0) return [0];
  return [0, -1];
}
// value of W_branch(z): snapped exact tree when elementary, else the W node with a certified value
function wValue(z, br, S, digits = 30) {
  const dom = S.domain;
  const h = hp(z, digits + 15);
  if (!h.ok) return null;
  const r = lambertWBig(h.rec.value, br, digits);
  if (!r) return null;
  if (r.branchPoint) return { tree: X.NEG_ONE, snapped: true, value: "-1" };
  const wd = parseFloat(r.value);
  // snap: e^w rational -> w = ln(q); or w rational
  const cands = [];
  const ew = Math.exp(wd);
  for (const md of [1000, 100000]) {
    const qa = ratApprox(ew, md);
    if (qa) cands.push(X.sub(X.fn("ln", X.num(Q.Q(qa.n))), X.fn("ln", X.num(Q.Q(qa.d)))));
    const qw = ratApprox(wd, md);
    if (qw) cands.push(X.num(qw));
  }
  for (const cand of cands) {
    const t = tidy(cand, dom);
    const hv = hp(t, 30);
    if (!hv.ok || Math.abs(hv.re - wd) > 1e-12 * Math.max(1, Math.abs(wd))) continue;
    if (isZeroExact(tidy(X.sub(X.mul(t, X.exp(t)), z), dom), dom)) return { tree: t, snapped: true, value: r.value };
  }
  return { tree: br === -1 ? W(z, -1) : W(z), snapped: false, value: r.value, errorBound: r.errorBound, certified: r.certified };
}

// Evaluate a constant tree containing W nodes: each W is replaced by its certified decimal value.
export function evalWTree(tree, digits = 30) {
  let ok = true;
  const t = X.mapTree(tree, (w) => {
    if (!isW(w)) return w;
    const h = hp(w.args[0], digits + 15);
    if (!h.ok) { ok = false; return w; }
    const r = lambertWBig(h.rec.value, branchOf(w), digits + 10);
    if (!r || !r.certified) { ok = false; return w; }
    return decimalTree(r.value) || (ok = false, w);
  });
  if (!ok) return null;
  const h = hp(t, digits);
  if (!h.ok) return null;
  return { tree: t, value: h.rec.value, errorBound: h.rec.errorBound, digits };
}
