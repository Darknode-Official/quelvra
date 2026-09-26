// Quelvra rational functions over Q: partial fractions (apart) and reduction to lowest terms (cancel).

import * as N from "./num.js";
import * as X from "./expr.js";
import { together, makeCtx } from "./simplify.js";
import * as C from "./poly-core.js";
import { factorQ, numDen } from "./poly-factor.js";

const { guard, canon } = C;
const Q1 = N.ONE;

function splitRational(expr) {
  let u = canon(expr);
  if (u.k === "add") u = together(u, makeCtx());
  return numDen(u);
}

// Partial fraction decomposition over Q.
// apartTerms(numer, denom) with UPolys -> { poly, terms: [{ numer, factor, power }], verified }
// meaning numer/denom = poly + sum numer_i / factor_i^power_i, deg numer_i < deg factor_i,
// factor_i irreducible over Q, integer primitive with positive leading coefficient.
export function apartTerms(numer, denom, opts) {
  return guard(opts, () => {
    let n = C.norm(numer), d = C.norm(denom);
    if (!d.length) throw new RangeError("Quelvra: zero denominator");
    const g = C.gcd(n, d);
    if (g.length > 1) { n = C.exactDiv(n, g); d = C.exactDiv(d, g); }
    const { q, r } = C.divmod(n, d);
    const terms = [];
    if (r.length) {
      const fq = factorQ(d);
      const rr = C.scale(r, N.inv(fq.unit));
      const P = fq.factors.map(({ poly, mult }) => C.pow(poly, mult));
      fq.factors.forEach(({ poly: f, mult }, i) => {
        let Qi = [Q1];
        P.forEach((pj, j) => { if (j !== i) Qi = C.mul(Qi, pj); });
        const { g: gg, s } = C.xgcd(C.rem(Qi, P[i]), P[i]);
        if (gg.length !== 1) throw new Error("Quelvra: internal error (partial fractions)");
        let Ri = C.rem(C.mul(rr, s), P[i]);
        // f-adic expansion Ri = sum_j B_j f^j
        for (let j = 0; j < mult && Ri.length; j++) {
          const { q: qq, r: B } = C.divmod(Ri, f);
          if (B.length) terms.push({ numer: B, factor: f, power: mult - j });
          Ri = qq;
        }
      });
    }
    // verification by recombination: q*d + sum numer * d / factor^power == n
    let acc = C.mul(q, d);
    for (const t of terms) acc = C.add(acc, C.mul(t.numer, C.exactDiv(d, C.pow(t.factor, t.power))));
    const verified = C.polyEq(acc, n);
    if (!verified) throw new Error("Quelvra: partial fraction verification failed");
    terms.sort((a, b) => a.factor.length - b.factor.length || a.power - b.power);
    return { poly: q, terms, verified };
  });
}
// apart(expr, x) or apart(numerTree, denomTree, x) -> sum-of-fractions tree, or null when the
// input is not a rational function of x with rational coefficients.
export function apart(a, b, c, opts) {
  return guard(opts, () => {
    let nt, dt, x;
    if (c === undefined || (typeof c === "object" && c !== null && !c.k)) {
      if (c && typeof c === "object") opts = c;
      x = typeof b === "string" ? b : b.name;
      [nt, dt] = splitRational(a);
    } else {
      x = typeof c === "string" ? c : c.name;
      [nt, dt] = splitRational(C.RB.div(a, b));
    }
    const n = C.fromTree(nt, x), d = C.fromTree(dt, x);
    if (n === null || d === null || !d.length) return null;
    const r = apartTerms(n, d);
    const parts = [C.toTree(r.poly, x)];
    for (const t of r.terms) parts.push(X.mul(C.toTree(t.numer, x), X.pow(C.toTree(t.factor, x), X.num(-t.power))));
    return canon(X.add(...parts));
  });
}

// Reduce a rational expression to lowest terms. Returns
// { tree, numerator, denominator, cancelled: tree | null, conditions: [rel(!=)] }.
// With x given the polynomials are taken in x when possible; otherwise in all free symbols.
export function cancel(expr, x, opts) {
  return guard(opts, () => {
    const [nt, dt] = splitRational(expr);
    let vars = [...new Set([...X.freeSymbols(nt), ...X.freeSymbols(dt)])].sort();
    if (x) { const xn = typeof x === "string" ? x : x.name; vars = [xn, ...vars.filter((v) => v !== xn)]; }
    const mn = C.fromTree(nt, vars), md = C.fromTree(dt, vars);
    if (!mn || !md || C.mIsZero(md)) return { tree: canon(C.RB.div(nt, dt)), numerator: nt, denominator: dt, cancelled: null, conditions: [] };
    const g = C.mGcd(mn, md);
    let n2 = C.mDivExact(mn, g), d2 = C.mDivExact(md, g);
    const { unit, p } = C.mNormalize(d2);
    d2 = p;
    n2 = C.mScale(n2, N.inv(unit));
    const numerator = C.toTree(n2), denominator = C.toTree(d2);
    const nontrivial = C.mUsedVars(g).length > 0;
    const gt = nontrivial ? C.toTree(g) : null;
    return {
      tree: canon(C.RB.div(numerator, denominator)), numerator, denominator,
      cancelled: gt, conditions: gt ? [X.rel("!=", gt, X.ZERO)] : [],
    };
  });
}
