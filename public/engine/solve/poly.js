// Quelvra solvers: polynomial equations over Q (any degree) and literal / parametric
// linear and quadratic equations.
//
// Polynomials: content -> exact factorisation over Q (Zassenhaus, poly-factor.js) -> each
// irreducible factor solved in closed form when one exists (linear, quadratic formula, Cardano,
// casus irreducibilis in trigonometric form, Ferrari / biquadratic with denesting, binomials);
// otherwise its real roots are ISOLATED exactly (Sturm) and refined to certified decimals.
// Completeness: a Sturm count of distinct real roots is compared with the number reported.

import * as X from "../expr.js";
import * as Q from "../num.js";
import * as P from "../poly.js";
import { C, EX, tidy, safe, signConst, isZeroExact, approxRec, hasFn, num, fail } from "./util.js";
import { toText } from "../print.js";

// Coefficient trees of expr as a polynomial in x (null when not a polynomial in x).
export function coeffTrees(expr, x) {
  try { return P.coefficients(expr, x); } catch (e) { if (e && e.code === "TIMEOUT") throw e; return null; }
}
export function isRationalPoly(coeffs) { return !!coeffs && coeffs.every(X.isNum); }
export function toUPoly(coeffs) { return P.norm(coeffs.map((t) => t.v)); }

const polyTree = (p, x) => P.toTree(p, x);

// Solve p(x) = 0 for a UPoly p over Q.
// Returns { exact: [{tree, multiplicity, real, form}], approx: [...], complete, realCount, degree, factored }
export function solveUPoly(p, x, S) {
  const log = S.log;
  const domain = S.domain || "real";
  const digits = S.digits || 20;
  p = P.norm(p);
  const deg = p.length - 1;
  if (deg < 0) return { identity: true, exact: [], approx: [], complete: true, realCount: Infinity, degree: -1 };
  if (deg === 0) return { exact: [], approx: [], complete: true, realCount: 0, degree: 0, noRoots: "a nonzero constant is never 0" };
  const ptree = polyTree(p, x);
  const fq = P.factorQ(p);
  const factored = safe(() => P.factorTree(ptree), ptree);
  if (fq.factors.length > 1 || (fq.factors[0] && fq.factors[0].mult > 1)) {
    log.add({ rule: "solve.poly.factor", title: "Factor over the rationals", why: "Exact factorisation (square-free decomposition + Zassenhaus); a product is 0 exactly when one of its factors is 0.", before: X.eq(ptree, X.ZERO), after: X.eq(factored, X.ZERO) });
  }
  const exact = [], approx = [];
  let complete = true;
  for (const { poly: f, mult } of fq.factors) {
    S.checkTime && S.checkTime();
    const d = f.length - 1;
    const ft = polyTree(f, x);
    if (d === 1) {
      const r = X.num(Q.div(Q.neg(f[0]), f[1]));
      exact.push({ tree: r, multiplicity: mult, real: true, form: "linear" });
      log.add({ rule: "solve.poly.linear-factor", title: `Solve ${toText(ft)} = 0`, why: mult > 1 ? `This factor appears ${mult} times, so the root has multiplicity ${mult}.` : "A linear factor gives one root.", before: X.eq(ft, X.ZERO), after: X.eq(X.sym(x), r) });
      continue;
    }
    if (d === 2) {
      const [c0, c1, c2] = f;
      const D = Q.sub(Q.mul(c1, c1), Q.mul(Q.mul(Q.Q(4n), c2), c0));
      const Dt = X.num(D);
      log.add({ rule: "solve.quadratic.discriminant", title: "Compute the discriminant", why: `For a x^2 + b x + c with a = ${Q.toString(c2)}, b = ${Q.toString(c1)}, c = ${Q.toString(c0)}: D = b^2 - 4ac.`, before: ft, after: X.eq(X.sym("D"), Dt) });
      if (Q.isNeg(D) && domain === "real") {
        log.add({ rule: "solve.quadratic.no-real", title: "No real roots from this factor", why: "The discriminant is negative, so the square root of D is not real.", before: X.eq(ft, X.ZERO), after: X.FALSE });
        continue;
      }
      const sd = C(X.sqrt(Dt), domain);
      const den = X.num(Q.mul(Q.TWO, c2));
      const r1 = tidy(X.div(X.sub(X.num(Q.neg(c1)), sd), den), domain), r2 = tidy(X.div(X.add(X.num(Q.neg(c1)), sd), den), domain);
      log.add({ rule: "solve.quadratic.formula", title: "Apply the quadratic formula", why: "x = (-b +- sqrt(D)) / (2a).", before: X.eq(ft, X.ZERO), after: X.or(X.eq(X.sym(x), r1), X.eq(X.sym(x), r2)) });
      for (const r of [r1, r2]) exact.push({ tree: r, multiplicity: mult, real: !Q.isNeg(D), form: "quadratic" });
      continue;
    }
    // degree >= 3 irreducible factor: closed form when available
    let sol = null;
    try { sol = P.solvePolynomial(ft, x, { domain }); } catch (e) { if (e && e.code === "TIMEOUT") throw e; sol = null; }
    if (sol && sol.complete && sol.exact.length) {
      const forms = [...new Set(sol.exact.map((r) => r.form).filter(Boolean))];
      const formWhy = forms.includes("trigonometric") ? "Three real roots (casus irreducibilis): Cardano's formula would need cube roots of complex numbers, so the roots are written in real trigonometric form 2 sqrt(-p/3) cos(theta/3 - 2 pi k/3)."
        : forms.includes("cardano") ? "Cardano's formula (one real root)." : forms.includes("ferrari") ? "Ferrari's method (resolvent cubic)." : forms.includes("biquadratic") ? "A quadratic in x^2; nested radicals are denested where possible." : forms.includes("binomial") ? "A binomial x^n = c." : "Closed form.";
      const rs = sol.exact.map((r) => ({ tree: tidy(r.root, domain), multiplicity: mult, real: r.real, form: r.form }));
      log.add({ rule: "solve.poly.closed-form", title: `Solve the ${["", "", "", "cubic", "quartic"][d] || "degree " + d} factor exactly`, why: formWhy + " Each root was checked by substitution.", before: X.eq(ft, X.ZERO), after: X.or(...rs.filter((r) => domain === "complex" || r.real).map((r) => X.eq(X.sym(x), r.tree))) });
      for (const r of rs) if (domain === "complex" || r.real) exact.push(r);
      continue;
    }
    // no closed form (or none verified): certified isolation of the real roots
    const ivs = P.isolateRealRoots(f);
    log.add({ rule: "solve.poly.isolate", title: `Isolate the real roots of ${toText(ft)}`, why: `This factor of degree ${d} is irreducible over Q${d >= 5 ? " and in general not solvable by radicals" : ""}. A Sturm sequence shows it has exactly ${ivs.length} real root${ivs.length === 1 ? "" : "s"}; each is enclosed in an interval with rational endpoints and refined to ${digits} digits.`, before: X.eq(ft, X.ZERO), after: null, kind: "approximation" });
    for (const iv of ivs) {
      const a = P.approxRealRoot(f, iv, digits);
      approx.push({ value: parseFloat(a.value), approx: { ...a, method: "Sturm isolation + certified bisection/Newton", lo: undefined, hi: undefined, interval: [Q.toString(iv.lo), Q.toString(iv.hi)], certified: true }, multiplicity: mult, factor: ft });
    }
    if (domain === "complex") {
      const cr = P.complexRoots(f).filter((r) => r.im !== 0);
      for (const r of cr) approx.push({ value: r.re, im: r.im, approx: { value: `${r.approx.re.value} ${r.im < 0 ? "-" : "+"} ${Math.abs(r.im).toPrecision(15)}i`, digits: 15, requested: digits, errorBound: null, method: "Aberth-Ehrlich (double precision, not certified)", iterations: 0, converged: true }, multiplicity: mult, complex: true, factor: ft });
    }
  }
  const realCount = P.countRealRoots(p);
  return { exact, approx, complete, realCount, degree: deg, factored };
}

// ---------------------------------------------------------------- literal / parametric
// a x + b = 0 or a x^2 + b x + c = 0 where the coefficients involve other symbols.
// Returns { answers, conditions, cases, steps logged } or null.
export function solveLiteral(expr, x, S) {
  const cs = coeffTrees(expr, x);
  if (!cs || cs.length < 2 || cs.length > 3) return null;
  const params = [...new Set(cs.flatMap((c) => [...X.freeSymbols(c)]))];
  if (!params.length) return null;
  const log = S.log, domain = S.domain || "real";
  const X0 = X.sym(x);
  const out = { answers: [], cases: [], conditions: [] };
  const zeroSet = (a) => paramZeroes(a, S); // [{param, value}] when a is a polynomial in one parameter, else null
  if (cs.length === 2) {
    const [b, a] = cs;
    const root = tidy(X.neg(X.div(b, a)), domain);
    const aSign = signConst(a);
    log.add({ rule: "solve.linear.literal", title: `Solve for ${x}`, why: `The equation is linear in ${x}: (${toText(a)}) ${x} + (${toText(b)}) = 0. Dividing by the coefficient is allowed only when it is not 0.`, before: X.eq(expr, X.ZERO), after: X.eq(X0, root), conditions: aSign ? [] : [X.rel("!=", a, X.ZERO)], kind: aSign ? "equivalent" : "conditional" });
    out.answers.push({ kind: "exact", label: x, tree: root, condition: aSign ? null : X.rel("!=", a, X.ZERO) });
    if (!aSign) {
      out.conditions.push(X.rel("!=", a, X.ZERO));
      const zs = zeroSet(a);
      if (zs) {
        for (const z of zs) {
          const bz = C(X.subs(b, { [z.param]: z.value }), domain);
          const cond = X.eq(X.sym(z.param), z.value);
          const bzn = C(X.neg(bz), domain);
          const bzShow = toText(bzn).length < toText(bz).length ? bzn : bz;
          if (bz === X.ZERO) out.cases.push({ kind: "case", label: `If ${toText(cond)}: every ${x} is a solution`, condition: cond, tree: X.TRUE, all: true });
          else if (X.freeSymbols(bz).size) {
            // the remaining constant still depends on parameters: split again
            const c1 = X.and(cond, X.eq(bzShow, X.ZERO)), c2 = X.and(cond, X.rel("!=", bzShow, X.ZERO));
            out.cases.push({ kind: "case", label: `If ${toText(c1)}: every ${x} is a solution`, condition: c1, tree: X.TRUE, all: true });
            out.cases.push({ kind: "case", label: `If ${toText(c2)}: no solution`, condition: c2, tree: X.FALSE, none: true });
          } else out.cases.push({ kind: "case", label: `If ${toText(cond)}: no solution (the equation becomes ${toText(bz)} = 0)`, condition: cond, tree: X.FALSE, none: true });
        }
      } else {
        out.cases.push({ kind: "case", label: `If ${toText(a)} = 0 and ${toText(b)} = 0: every ${x} is a solution`, condition: X.and(X.eq(a, X.ZERO), X.eq(b, X.ZERO)), tree: X.TRUE, all: true });
        out.cases.push({ kind: "case", label: `If ${toText(a)} = 0 and ${toText(b)} != 0: no solution`, condition: X.and(X.eq(a, X.ZERO), X.rel("!=", b, X.ZERO)), tree: X.FALSE, none: true });
      }
      log.add({ rule: "solve.linear.cases", title: "Degenerate case", why: out.cases.map((c) => c.label).join("; ") + ".", before: null, after: null, kind: "note" });
    }
    return out;
  }
  // quadratic with parameters
  const [c, b, a] = cs;
  const aSign = signConst(a);
  if (!aSign) {
    // a = 0 branch: linear equation
    const zs = zeroSet(a);
    if (zs) {
      for (const z of zs) {
        const sub = C(X.subs(expr, { [z.param]: z.value }), domain);
        const lc = coeffTrees(sub, x);
        const cond = X.eq(X.sym(z.param), z.value);
        if (lc && lc.length === 2 && signConst(lc[1])) {
          const r = tidy(X.neg(X.div(lc[0], lc[1])), domain);
          out.cases.push({ kind: "case", label: `If ${toText(cond)}: the equation is linear, ${x} = ${toText(r)}`, condition: cond, tree: X.eq(X0, r), values: [[x, r]] });
        } else if (lc && lc.length === 0) out.cases.push({ kind: "case", label: `If ${toText(cond)}: every ${x} is a solution`, condition: cond, tree: X.TRUE, all: true });
        else if (lc && lc.length === 1) out.cases.push({ kind: "case", label: `If ${toText(cond)}: no solution`, condition: cond, tree: X.FALSE, none: true });
        else out.cases.push({ kind: "case", label: `If ${toText(cond)}: ${toText(sub)} = 0`, condition: cond, tree: X.eq(sub, X.ZERO) });
      }
    } else {
      out.cases.push({ kind: "case", label: `If ${toText(a)} = 0: the equation is linear, ${toText(b)} ${x} + ${toText(c)} = 0`, condition: X.eq(a, X.ZERO), tree: X.eq(X.add(X.mul(b, X0), c), X.ZERO) });
    }
    out.conditions.push(X.rel("!=", a, X.ZERO));
  }
  const D = C(EX(X.sub(X.pow(b, X.TWO), X.mul(num(4), a, c))), domain);
  log.add({ rule: "solve.quadratic.discriminant", title: "Compute the discriminant", why: `a = ${toText(a)}, b = ${toText(b)}, c = ${toText(c)}; D = b^2 - 4ac.`, before: expr, after: X.eq(X.sym("D"), D) });
  const dSign = signConst(D);
  const sd = X.sqrt(D), den = X.mul(X.TWO, a);
  const r1 = tidy(X.div(X.sub(X.neg(b), sd), den), domain), r2 = tidy(X.div(X.add(X.neg(b), sd), den), domain);
  const aCond = aSign ? null : X.rel("!=", a, X.ZERO);
  if (dSign === -1 && domain === "real") {
    out.answers.push({ kind: "none", label: `No real solution when ${toText(a)} != 0 (the discriminant ${toText(D)} is negative)` });
    return out;
  }
  if (dSign === 0) {
    const r = tidy(X.div(X.neg(b), den), domain);
    out.answers.push({ kind: "exact", label: x, tree: r, multiplicity: 2, condition: aCond });
    log.add({ rule: "solve.quadratic.double", title: "Double root", why: "D = 0.", before: expr, after: X.eq(X0, r) });
    return out;
  }
  const dCond = dSign === 1 || domain === "complex" ? null : X.rel(">=", D, X.ZERO);
  const cond = aCond && dCond ? X.and(aCond, dCond) : aCond || dCond;
  log.add({ rule: "solve.quadratic.formula", title: "Apply the quadratic formula", why: `x = (-b +- sqrt(D)) / (2a)${dCond ? "; the roots are real exactly when D >= 0" : ""}.`, before: X.eq(expr, X.ZERO), after: X.or(X.eq(X0, r1), X.eq(X0, r2)), conditions: cond ? [cond] : [], kind: cond ? "conditional" : "equivalent" });
  out.answers.push({ kind: "exact", label: x, tree: r1, condition: cond }, { kind: "exact", label: x, tree: r2, condition: cond });
  if (dCond) {
    out.conditions.push(dCond);
    out.cases.push({ kind: "case", label: `If ${toText(D)} = 0: one double root ${x} = ${toText(tidy(X.div(X.neg(b), den), domain))}`, condition: X.eq(D, X.ZERO) });
    out.cases.push({ kind: "case", label: `If ${toText(D)} < 0: no real solution`, condition: X.rel("<", D, X.ZERO), tree: X.FALSE, none: true });
    if (S.describeParamSet) {
      const nice = safe(() => S.describeParamSet(D));
      if (nice) out.paramSets = nice;
    }
  }
  return out;
}

// Values of a single parameter p that make the polynomial a(p) vanish (exact), or null.
function paramZeroes(a, S) {
  const fs = [...X.freeSymbols(a)];
  if (fs.length !== 1) return null;
  const cs = coeffTrees(a, fs[0]);
  if (!isRationalPoly(cs)) return null;
  const p = toUPoly(cs);
  if (p.length <= 1) return [];
  const sol = solveUPoly(p, fs[0], { ...S, log: { add() {}, group: (h, f) => f() }, domain: "real" });
  if (sol.approx.length) return null;
  return sol.exact.filter((r) => r.real).map((r) => ({ param: fs[0], value: r.tree }));
}
