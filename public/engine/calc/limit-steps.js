// Textbook steps for common limits.
//
// The limit engine (limit.js) finds values with series expansions and the Gruntz algorithm, which
// are reliable but not how a student works a limit by hand. For the usual classroom forms this
// module redoes the limit the textbook way, and returns those steps only when that route reaches
// exactly the value the engine found:
//   direct substitution            f continuous at the point
//   factor and cancel              0/0 with polynomial numerator and denominator
//   L'Hopital's rule               0/0 otherwise (at most three rounds)
//   divide by the highest power    rational functions as x -> oo or -oo
// Otherwise it returns [] and the caller notes which method was used.

import * as X from "../expr.js";
import { simplify, makeCtx } from "../simplify.js";
import { evalC } from "../verify.js";
import { toText } from "../print.js";
import { diff } from "./diff.js";
import * as P from "../poly.js";

const S = (t) => simplify(t, makeCtx({ budget: { ops: 200000 } }));
const safe = (f) => { try { return f(); } catch (e) { if (e && e.code === "TIMEOUT") throw e; return null; } };
const real = (t) => {
  if (!t || t === X.UNDEF || X.contains(t, X.UNDEF) || X.contains(t, X.OO)) return null;
  const c = safe(() => evalC(t, {}, "complex"));
  return c && Number.isFinite(c.re) && Number.isFinite(c.im) && Math.abs(c.im) < 1e-12 * Math.max(1, Math.abs(c.re)) ? c.re : null;
};
const close = (a, b) => a !== null && b !== null && Math.abs(a - b) <= 1e-9 * Math.max(1, Math.abs(b));
const isInfTree = (t) => t === X.OO || (t && t.k === "mul" && t.args.length === 2 && X.isNegNum(t.args[0]) && t.args[1] === X.OO);
const step = (rule, title, why, before, after, kind = "equivalent") => ({ rule, title, why, before, after, conditions: [], sub: [], kind, check: null });

// u = num / den (den = 1 when u is not a fraction)
function numDen(u) {
  const fs = u.k === "mul" ? u.args : [u];
  const num = [], den = [];
  for (const f of fs) {
    if (f.k === "pow" && X.isNum(f.args[1]) && f.args[1].v.n < 0n) den.push(f.args[1] === X.NEG_ONE ? f.args[0] : X.pow(f.args[0], X.num(-Number(f.args[1].v.n), Number(f.args[1].v.d))));
    else num.push(f);
  }
  return { num: num.length ? X.mul(...num) : X.ONE, den: den.length ? X.mul(...den) : null };
}
const at = (t, x, a) => S(X.subs(t, { [x.name]: a }));
const ratCoeffs = (t, x) => { const c = safe(() => P.coefficients(t, x)); return c && c.length && c.every(X.isNum) ? c : null; };

// cancel the factors that the factored numerator and denominator share (with multiplicity)
function cancelCommon(fn, fd) {
  const parts = (t) => (t.k === "mul" ? t.args : [t]).map((f) => (f.k === "pow" && X.isInt(f.args[1]) && f.args[1].v.n > 0n ? [f.args[0], Number(f.args[1].v.n)] : [f, 1]));
  const pn = parts(fn), pd = parts(fd);
  let cancelled = false;
  for (const q of pn) {
    if (X.isNum(q[0])) continue;
    const r = pd.find((w) => w[0] === q[0] && w[1] > 0);
    if (!r) continue;
    const k = Math.min(q[1], r[1]);
    q[1] -= k; r[1] -= k; cancelled = true;
  }
  if (!cancelled) return null;
  const build = (ps) => X.mul(...ps.filter((w) => w[1] > 0).map(([b, e]) => (e === 1 ? b : X.pow(b, X.num(e)))));
  const top = build(pn), bot = build(pd);
  return bot === X.ONE ? top : X.div(top, bot);
}

// steps for lim_{x -> to} u, given the engine's value L (a tree). Returns [] when no textbook route matches.
export function limitSteps(u, x, to, dir, L) {
  const xs = typeof x === "string" ? X.sym(x) : x;
  const Lv = real(L);
  const lim = (e) => X.limit(e, xs, to, dir);
  const out = [];
  if (to === X.OO) {
    // rational function at infinity: divide by the highest power of x in the denominator
    const { num, den } = numDen(u);
    if (!den) return [];
    const cn = ratCoeffs(num, xs), cd = ratCoeffs(den, xs);
    if (!cn || !cd || cd.length < 2) return [];
    const p = cn.length - 1, q = cd.length - 1;
    const xq = q === 1 ? xs : X.pow(xs, X.num(q));
    const termsOver = (c) => c.map((k, i) => (X.isZero(k) ? null : S(X.div(X.mul(k, X.pow(xs, X.num(i))), xq)))).filter(Boolean).reverse();
    const rewritten = X.div(X.add(...termsOver(cn)), X.add(...termsOver(cd)));
    out.push(step("lim.dominant", `Divide the top and the bottom by ${toText(xq)}`, `${toText(xq)} is the highest power of ${xs.name} in the denominator; dividing both by it does not change the fraction.`, lim(u), lim(rewritten)));
    const an = cn[p], ad = cd[q];
    if (p === q) {
      const r = S(X.div(an, ad));
      if (!close(real(r), Lv)) return [];
      out.push(step("lim.dominant", "Let the small terms go to 0", `Every term with ${xs.name} in the denominator tends to 0 as ${xs.name} -> oo, leaving the leading coefficients ${toText(an)}/${toText(ad)}.`, lim(rewritten), r));
      return out;
    }
    if (p < q) {
      if (!close(0, Lv)) return [];
      out.push(step("lim.dominant", "Let the small terms go to 0", `The numerator tends to 0 (every term has ${xs.name} in its denominator) while the denominator tends to ${toText(ad)}.`, lim(rewritten), X.ZERO));
      return out;
    }
    if (!isInfTree(L)) return [];
    out.push(step("lim.dominant", "Compare the growth", `The numerator has the higher degree (${p} > ${q}), so the fraction grows without bound; its sign is the sign of ${toText(an)}/${toText(ad)}.`, lim(rewritten), L));
    return out;
  }
  if (to.k === "const" || X.isConstantExpr(to)) {
    if (isInfTree(to)) return [];
    // 1. direct substitution
    const direct = safe(() => at(u, xs, to));
    const dv = real(direct);
    if (dv !== null && close(dv, Lv)) {
      out.push(step("lim.direct", `Substitute ${xs.name} = ${toText(to)}`, "The function is continuous there, so the limit is simply its value at the point.", lim(u), direct));
      return out;
    }
    const { num, den } = numDen(u);
    if (!den || Lv === null) return [];
    const n0 = real(safe(() => at(num, xs, to))), d0 = real(safe(() => at(den, xs, to)));
    if (!(close(n0, 0) && close(d0, 0))) return [];
    const zz = step("lim.direct", `Substituting ${xs.name} = ${toText(to)} gives 0/0`, "0/0 is not a value: the fraction has to be rewritten before the limit can be read off.", lim(u), null, "note");
    // 2. polynomials: factor and cancel
    const cn = ratCoeffs(num, xs), cd = ratCoeffs(den, xs);
    if (cn && cd) {
      const fn = safe(() => P.factorTree(S(num))), fd = safe(() => P.factorTree(S(den)));
      const reduced = fn && fd ? cancelCommon(fn, fd) : null;
      const rv = reduced ? real(safe(() => at(reduced, xs, to))) : null;
      if (fn && fd && reduced && close(rv, Lv)) {
        out.push(zz);
        out.push(step("lim.factor", "Factor the top and the bottom", "Both are 0 at the point, so both have the factor (x - point).", lim(u), lim(X.div(fn, fd))));
        out.push(step("lim.factor", "Cancel the common factor", `Near the point ${xs.name} != ${toText(to)}, so the common factor is not 0 and can be cancelled.`, lim(X.div(fn, fd)), lim(reduced)));
        out.push(step("lim.direct", `Substitute ${xs.name} = ${toText(to)}`, "What is left is continuous at the point.", lim(reduced), S(X.subs(reduced, { [xs.name]: to }))));
        return out;
      }
      return [];
    }
    // 3. L'Hopital's rule
    out.push(zz);
    let f = num, g = den;
    for (let round = 1; round <= 3; round++) {
      const df = safe(() => S(diff(f, xs))), dg = safe(() => S(diff(g, xs)));
      if (!df || !dg) return [];
      const q = dg === X.ONE ? df : X.div(df, dg);
      out.push(step("lim.lhopital", round === 1 ? "Apply L'Hopital's rule" : "Apply L'Hopital's rule again", `For 0/0, the limit of f/g equals the limit of f'/g': differentiate the top, (${toText(f)})' = ${toText(df)}, and the bottom, (${toText(g)})' = ${toText(dg)}.`, lim(X.div(f, g)), lim(q)));
      const a = real(safe(() => at(df, xs, to))), b = real(safe(() => at(dg, xs, to)));
      if (a === null || b === null) return [];
      if (!close(b, 0)) {
        const v = S(X.div(at(df, xs, to), at(dg, xs, to)));
        if (!close(real(v), Lv)) return [];
        out.push(step("lim.direct", `Substitute ${xs.name} = ${toText(to)}`, `At ${xs.name} = ${toText(to)} the top is ${toText(at(df, xs, to))} and the bottom is ${toText(at(dg, xs, to))}, which is not 0.`, lim(q), v));
        return out;
      }
      if (!close(a, 0)) return [];
      out.push(step("lim.lhopital", "Still 0/0", `Both ${toText(df)} and ${toText(dg)} are 0 at ${xs.name} = ${toText(to)} too.`, lim(q), null, "note"));
      f = df; g = dg;
    }
    return [];
  }
  return [];
}
