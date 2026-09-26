// Quelvra solvers: trigonometric equations.
//
// Families are { offset, period } meaning x = offset + k * period for every integer k.
// Every family produced here has period 2 pi / |a| where theta = a x is the common angle, which is a
// period of every trigonometric term of the equation; so a family is correct as soon as its
// representative (k = 0) satisfies the original equation. The caller checks representatives
// against the original and merges surviving families (e.g. 0 + 2k pi and pi + 2k pi -> k pi).
//
// Methods: a single occurrence is inverted by trigInvert (called from core isolation); otherwise
// every trig atom is written in s = sin(theta), c = cos(theta) with theta = a x (multiple angles by
// Chebyshev expansion, shifted angles by the addition formulas), the equation becomes P(s, c) = 0,
// and P is solved as: polynomial in s alone or c alone (c^2 = 1 - s^2), product of factors,
// linear a s + b c + g = 0 (R-form), homogeneous (divide by cos^n -> tan), or in general by the
// eliminant A(s)^2 - (1 - s^2) B(s)^2 = 0 (each sin value gives two candidate families, checked).
// sin A = sin B, cos A = cos B, tan A = tan B with incommensurable arguments are solved directly.

import * as X from "../expr.js";
import * as Q from "../num.js";
import * as P from "../poly.js";
import { toText } from "../print.js";
import { C, EX, numDen, tidy, safe, signConst, cmpConst, isZeroExact, findAll, num, fail, cval } from "./util.js";
import { coeffTrees } from "./poly.js";

const TRIG = new Set(["sin", "cos", "tan", "cot", "sec", "csc"]);
export const isTrigName = (n) => TRIG.has(n);
const TWO_PI = X.mul(X.TWO, X.PI);
const dep = (u, x) => !X.freeOf(u, x);

// A = a x + b with constant a != 0 (b may be any x-free tree)
export function linearIn(A, x) {
  const cs = safe(() => coeffTrees(A, x));
  if (!cs || cs.length !== 2) return null;
  if (cs.some((c) => dep(c, x))) return null;
  return { a: cs[1], b: cs[0] };
}

// Families for f(a x + b) = c.  Returns [] when there is no solution, null when undecidable.
export function trigInvert(name, c, lin, S) {
  const dom = S.domain;
  c = C(c, dom);
  let base = name, val = c;
  if (name === "sec" || name === "csc" || name === "cot") {
    if (name === "cot") {
      // cot A = c  <=>  A = pi/2 - atan(c) + k pi  (and cot A = 0 at A = pi/2 + k pi)
      const th = C(X.sub(X.mul(X.HALF, X.PI), X.fn("atan", c)), dom);
      return famFromTheta([th, C(X.add(th, X.PI), dom)], lin, S, name, c);
    }
    if (isZeroExact(c, dom)) return logNone(S, name, c, `${name} is never 0.`);
    base = name === "sec" ? "cos" : "sin";
    val = C(X.div(X.ONE, c), dom);
  }
  if (S.domain === "complex") return null;
  if (base === "tan") {
    const th = tidy(X.fn("atan", val), dom);
    return famFromTheta([th, C(X.add(th, X.PI), dom)], lin, S, name, c);
  }
  const lo = cmpConst(val, X.NEG_ONE, dom), hi = cmpConst(val, X.ONE, dom);
  if (lo === null || hi === null) return null;
  if (lo < 0 || hi > 0) return logNone(S, name, c, `${base} only takes values between -1 and 1, and ${toText(val)} is outside that range.`);
  let ths;
  if (base === "sin") {
    const al = tidy(X.fn("asin", val), dom);
    ths = hi === 0 || lo === 0 ? [al] : [al, C(X.sub(X.PI, al), dom)];
  } else {
    const al = tidy(X.fn("acos", val), dom);
    ths = hi === 0 || lo === 0 ? [al] : [al, C(X.neg(al), dom)];
  }
  return famFromTheta(ths, lin, S, name, c);
}
function logNone(S, name, c, why) {
  S.log.add({ rule: "solve.trig.range", title: "No solution", why, before: X.eq(X.fn(name, X.sym("A")), c), after: X.FALSE });
  return [];
}
function famFromTheta(ths, lin, S, name, c) {
  const dom = S.domain;
  const { a, b } = lin;
  const sa = signConst(a, dom);
  if (!sa) return null;
  const per = tidy(X.div(TWO_PI, sa > 0 ? a : X.neg(a)), dom);
  const fams = ths.map((th) => ({ offset: tidy(X.div(X.sub(th, b), a), dom), period: per }));
  const A = C(X.add(X.mul(a, X.sym(S.x)), b), dom);
  const k = X.sym("k");
  S.log.add({ rule: "solve.trig.general", title: `General solution of ${name}(${toText(A)}) = ${toText(c)}`, why: name === "sin" || name === "csc" ? "sin A = sin(alpha) exactly when A = alpha + 2k pi or A = pi - alpha + 2k pi." : name === "cos" || name === "sec" ? "cos A = cos(alpha) exactly when A = alpha + 2k pi or A = -alpha + 2k pi." : "tan and cot repeat every pi, so A = alpha + k pi.", before: X.eq(X.fn(name, A), c), after: X.or(...fams.map((f) => X.eq(X.sym(S.x), C(X.add(f.offset, X.mul(f.period, k)), dom)))) });
  return fams;
}

// ---------------------------------------------------------------- general trig equations
export function solveTrig(e, S) {
  const x = S.x, dom = S.domain;
  if (dom === "complex") return null;
  const atoms = findAll(e, (w) => w.k === "fn" && TRIG.has(w.name) && dep(w, x));
  if (!atoms.length) return null;
  const lins = atoms.map((w) => linearIn(w.args[0], x));
  if (lins.some((l) => !l)) return null;
  // sin A = sin B type with two terms
  const pair = sameFunctionPair(e, x, S);
  if (pair) return pair;
  // common angle theta = g x: every a_i must be a rational multiple of a_0
  const a0 = lins[0].a;
  const ratios = lins.map((l) => C(X.div(l.a, a0), dom));
  if (!ratios.every(X.isNum)) return null;
  let gn = 0n, gd = 1n;
  for (const r of ratios) { gn = Q.bgcd(gn, r.v.n); gd = gd * r.v.d / Q.bgcd(gd, r.v.d); }
  const g = C(X.mul(X.num(Q.Q(gn, gd)), a0), dom);
  const ms = lins.map((l) => C(X.div(l.a, g), dom).v.n);
  if (ms.some((m) => (m < 0n ? -m : m) > 12n)) throw fail("multiple angles above 12 are not expanded");
  const sN = "σ", cN = "κ";
  const s = X.sym(sN), c = X.sym(cN);
  const sinM = (m) => cheb(m, s, c, "sin"), cosM = (m) => cheb(m, s, c, "cos");
  let u = e;
  atoms.forEach((w, i) => {
    const m = ms[i], b = lins[i].b;
    let sn = sinM(m), cs = cosM(m);
    if (b !== X.ZERO) {
      const cb = C(X.fn("cos", b), dom), sb = C(X.fn("sin", b), dom);
      [sn, cs] = [X.add(X.mul(sn, cb), X.mul(cs, sb)), X.sub(X.mul(cs, cb), X.mul(sn, sb))];
    }
    const rep = { sin: sn, cos: cs, tan: X.div(sn, cs), cot: X.div(cs, sn), sec: X.div(X.ONE, cs), csc: X.div(X.ONE, sn) }[w.name];
    u = X.replace(u, w, rep);
  });
  u = C(u, dom);
  if (dep(u, x)) return null; // x also outside trig functions: transcendental, numeric
  const [n0] = numDen(u, dom);
  const Pn = EX(n0, dom);
  const theta = C(X.mul(g, X.sym(x)), dom);
  S.log.add({ rule: "solve.trig.rewrite", title: `Write everything with sin and cos of ${toText(theta)}`, why: "Multiple and shifted angles are expanded with the addition formulas; denominators are cleared (points where they vanish are rejected afterwards).", before: X.eq(e, X.ZERO), after: X.eq(X.subs(Pn, { [sN]: X.fn("sin", theta), [cN]: X.fn("cos", theta) }), X.ZERO), kind: "conditional" });
  const lin = { a: g, b: X.ZERO };
  const fams = solveSC(Pn, sN, cN, lin, S, 0);
  if (fams === null) return null;
  const out = { exact: [], approx: [], general: fams, regions: [], all: false, complete: true, methods: ["trigonometric"], notes: [] };
  return out;
}

// Chebyshev: sin(m t), cos(m t) as polynomials in s = sin t, c = cos t (Re/Im of (c + i s)^m).
function cheb(m, s, c, which) {
  const neg = m < 0n;
  const M = Number(neg ? -m : m);
  if (M === 0) return which === "sin" ? X.ZERO : X.ONE;
  const terms = [];
  for (let j = 0; j <= M; j++) {
    if ((which === "cos") !== (j % 2 === 0)) continue;
    // i^j: j even -> (-1)^(j/2); j odd -> i * (-1)^((j-1)/2)
    const sign = which === "cos" ? ((j / 2) % 2 ? -1 : 1) : (((j - 1) / 2) % 2 ? -1 : 1);
    terms.push(X.mul(num(sign * binom(M, j)), X.pow(c, num(M - j)), X.pow(s, num(j))));
  }
  const r = X.add(...terms);
  return neg && which === "sin" ? X.neg(r) : r;
}
function binom(n, k) { let r = 1; for (let i = 1; i <= k; i++) r = (r * (n - k + i)) / i; return r; }

function polyIn(u, v) { return safe(() => coeffTrees(u, v)); }
// Solve P(s, c) = 0 for theta families.
function solveSC(Pn, sN, cN, lin, S, depth) {
  const dom = S.domain;
  if (depth > 4) return null;
  S.checkTime && S.checkTime();
  const s = X.sym(sN), c = X.sym(cN);
  if (Pn === X.ZERO) throw fail("the trigonometric equation reduced to an identity");
  // reduce with c^2 = 1 - s^2 -> A(s) + c B(s)
  const byC = polyIn(Pn, cN);
  const byS = polyIn(Pn, sN);
  if (!byC || !byS) return null;
  const red = (cs, other) => {
    let A = X.ZERO, B = X.ZERO;
    cs.forEach((k, j) => {
      const q = X.pow(X.sub(X.ONE, X.pow(other, X.TWO)), num(Math.floor(j / 2)));
      if (j % 2 === 0) A = X.add(A, X.mul(k, q)); else B = X.add(B, X.mul(k, q));
    });
    return [EX(A, dom), EX(B, dom)];
  };
  const [As, Bs] = red(byC, s); // Pn = As(s) + c Bs(s)
  const [Ac, Bc] = red(byS, c); // Pn = Ac(c) + s Bc(c)
  const inSin = (poly) => rootsThen(poly, sN, S, (r) => trigInvert("sin", r, lin, S), "sin");
  const inCos = (poly) => rootsThen(poly, cN, S, (r) => trigInvert("cos", r, lin, S), "cos");
  if (Bs === X.ZERO) {
    step(S, "solve.trig.in-sin", "An equation in sin alone", "cos^2 = 1 - sin^2 leaves a polynomial in sin.", As, sN, cN, lin);
    return inSin(As);
  }
  if (Bc === X.ZERO) {
    step(S, "solve.trig.in-cos", "An equation in cos alone", "sin^2 = 1 - cos^2 leaves a polynomial in cos.", Ac, sN, cN, lin);
    return inCos(Ac);
  }
  if (As === X.ZERO) {
    // c * B(s) = 0
    step(S, "solve.trig.factor", "Factor out cos", "cos(theta) * B(sin theta) = 0.", Pn, sN, cN, lin);
    const f1 = trigInvert("cos", X.ZERO, lin, S);
    const f2 = inSin(Bs);
    return f1 && f2 ? [...f1, ...f2] : null;
  }
  if (Ac === X.ZERO) {
    step(S, "solve.trig.factor", "Factor out sin", "sin(theta) * B(cos theta) = 0.", Pn, sN, cN, lin);
    const f1 = trigInvert("sin", X.ZERO, lin, S);
    const f2 = inCos(Bc);
    return f1 && f2 ? [...f1, ...f2] : null;
  }
  // factor over Q when possible
  const fac = safe(() => {
    const mp = P.fromTree(Pn, [sN, cN]);
    const r = P.mFactor(mp);
    const fs = (r.factors || []).filter((f) => P.mTotalDegree(f.poly) > 0);
    return fs.length > 1 ? fs.map((f) => P.toTree(f.poly)) : null;
  });
  if (fac) {
    step(S, "solve.trig.factor", "Factor", `The equation factors into ${fac.map((f) => "(" + toText(f) + ")").join(" ")} (s = sin, c = cos); solve each factor.`, Pn, sN, cN, lin);
    const out = [];
    for (const f of fac) { const r = solveSC(EX(f, dom), sN, cN, lin, S, depth + 1); if (r === null) return null; out.push(...r); }
    return out;
  }
  // linear: alpha s + beta c + gamma = 0  ->  R-form
  if (byC.length === 2 && byS.length === 2) {
    const beta = byC[1];
    if (!dep(beta, sN)) {
      const rest = byC[0];
      const al = polyIn(rest, sN);
      if (al && al.length === 2 && !X.freeSymbols(al[1]).size && !X.freeSymbols(beta).size) {
        const alpha = al[1], gamma = al[0];
        return rForm(alpha, beta, gamma, lin, S);
      }
    }
  }
  // homogeneous of degree d in (s, c): divide by c^d -> tan
  const hom = homogeneousDegree(Pn, sN, cN);
  if (hom) {
    const tN = "τt";
    const Tp = EX(X.subs(Pn, { [sN]: X.sym(tN), [cN]: X.ONE }), dom);
    step(S, "solve.trig.tan", `Divide by cos^${hom}`, "Every term has the same total degree in sin and cos, so dividing by cos^n gives a polynomial in tan (points with cos = 0 are checked separately).", Tp, sN, cN, lin, tN);
    const out = [];
    const r1 = rootsThen(Tp, tN, S, (r) => trigInvert("tan", r, lin, S), "tan");
    if (r1 === null) return null;
    out.push(...r1);
    // cos theta = 0: P(+-1, 0) = 0?
    const atPole = C(X.subs(Pn, { [sN]: X.ONE, [cN]: X.ZERO }), dom);
    if (atPole === X.ZERO) out.push(...(trigInvert("cos", X.ZERO, lin, S) || []));
    return out;
  }
  // general: eliminate c. A + c B = 0 implies A^2 = (1 - s^2) B^2.
  const E = EX(X.sub(X.pow(As, X.TWO), X.mul(X.sub(X.ONE, X.pow(s, X.TWO)), X.pow(Bs, X.TWO))), dom);
  step(S, "solve.trig.eliminate", "Eliminate cos", "Write the equation as A(sin) = -cos * B(sin) and square, using cos^2 = 1 - sin^2. Squaring can add candidates; each candidate family is checked in the original equation.", E, sN, cN, lin);
  if (E === X.ZERO) return null;
  return inSin(E);
}
function step(S, rule, title, why, tree, sN, cN, lin, tN) {
  const th = C(X.add(X.mul(lin.a, X.sym(S.x)), lin.b), S.domain);
  const map = { [sN]: X.fn("sin", th), [cN]: X.fn("cos", th) };
  if (tN) map[tN] = X.fn("tan", th);
  S.log.add({ rule, title, why, before: null, after: X.eq(X.subs(tree, map), X.ZERO) });
}
function homogeneousDegree(Pn, sN, cN) {
  const terms = Pn.k === "add" ? Pn.args : [Pn];
  let d = null;
  for (const t of terms) {
    const fs = t.k === "mul" ? t.args : [t];
    let deg = 0;
    for (const f of fs) {
      if (f.k === "sym" && (f.name === sN || f.name === cN)) deg += 1;
      else if (f.k === "pow" && f.args[0].k === "sym" && (f.args[0].name === sN || f.args[0].name === cN) && X.isInt(f.args[1])) deg += Number(f.args[1].v.n);
      else if (!X.freeSymbols(f).size) continue;
      else return null;
    }
    if (d === null) d = deg; else if (d !== deg) return null;
  }
  return d && d > 0 ? d : null;
}
function rForm(alpha, beta, gamma, lin, S) {
  const dom = S.domain;
  const sa = signConst(alpha, dom);
  if (!sa) return null;
  const R = tidy(X.sqrt(X.add(X.pow(alpha, X.TWO), X.pow(beta, X.TWO))), dom);
  let phi = tidy(X.fn("atan", X.div(beta, alpha)), dom);
  if (sa < 0) phi = C(X.add(phi, X.PI), dom);
  const th = C(X.mul(lin.a, X.sym(S.x)), dom);
  const rhs = tidy(X.div(X.neg(gamma), R), dom);
  S.log.add({ rule: "solve.trig.r-form", title: "Combine into a single sine (R-form)", why: `a sin t + b cos t = R sin(t + phi) with R = sqrt(a^2 + b^2) = ${toText(R)} and phi = ${toText(phi)} (cos phi = a/R, sin phi = b/R).`, before: X.eq(X.add(X.mul(alpha, X.fn("sin", th)), X.mul(beta, X.fn("cos", th)), gamma), X.ZERO), after: X.eq(X.fn("sin", C(X.add(th, phi), dom)), rhs) });
  return trigInvert("sin", rhs, { a: lin.a, b: C(X.add(lin.b, phi), dom) }, S);
}
// exact roots of a polynomial in v, each mapped to families
function rootsThen(poly, vN, S, famOf, fname) {
  const dom = S.domain;
  if (!X.freeSymbols(poly).has(vN)) {
    if (poly === X.ZERO) throw fail("identity in the trig variable");
    return signConst(poly, dom) ? [] : null;
  }
  const r = S.solveCore(poly, { x: vN, allowNumeric: false });
  if (r.approx.length || r.general.length || r.regions.length || r.all) throw fail(`the values of ${fname} are not exact`);
  const out = [];
  for (const q of r.exact) {
    const v = cval(q.tree);
    if (Math.abs(v.im) > 1e-12 * Math.max(1, Math.abs(v.re))) continue;
    const f = famOf(q.tree);
    if (f === null) return null;
    out.push(...f);
  }
  return out;
}

// f(A) - f(B) = 0 (or f(A) = f(B) after moving), f in sin/cos/tan, arguments linear in x
function sameFunctionPair(e, x, S) {
  const dom = S.domain;
  const terms = e.k === "add" ? e.args : [e];
  if (terms.length !== 2) return null;
  const parts = terms.map((t) => {
    const fs = t.k === "mul" ? t.args : [t];
    const tr = fs.filter((f) => f.k === "fn" && TRIG.has(f.name));
    const k = fs.filter((f) => !(f.k === "fn" && TRIG.has(f.name)));
    if (tr.length !== 1 || k.some((f) => dep(f, x))) return null;
    return { f: tr[0], k: C(X.mul(...k), dom) };
  });
  if (parts.some((p) => !p)) return null;
  const [p, q] = parts;
  if (p.f.name !== q.f.name || !["sin", "cos", "tan"].includes(p.f.name)) return null;
  if (!isZeroExact(X.add(p.k, q.k), dom)) return null;
  const L1 = linearIn(p.f.args[0], x), L2 = linearIn(q.f.args[0], x);
  if (!L1 || !L2) return null;
  const ratio = C(X.div(L1.a, L2.a), dom);
  if (X.isNum(ratio)) return null; // commensurable: the general method gives cleaner families
  const name = p.f.name;
  const A = p.f.args[0], B = q.f.args[0];
  const cases = name === "sin" ? [[1, TWO_PI, X.ZERO], [-1, TWO_PI, X.PI]] : name === "cos" ? [[1, TWO_PI, X.ZERO], [-1, TWO_PI, X.ZERO]] : [[1, X.PI, X.ZERO]];
  // A = s*B + c0 + k*P  ->  (a1 - s a2) x = s b2 - b1 + c0 + kP
  const fams = [];
  for (const [sg, per, c0] of cases) {
    const coef = C(X.sub(L1.a, X.mul(num(sg), L2.a)), dom);
    const sc = signConst(coef, dom);
    if (sc === null) return null;
    if (sc === 0) continue;
    fams.push({ offset: tidy(X.div(X.add(X.mul(num(sg), L2.b), X.neg(L1.b), c0), coef), dom), period: tidy(X.div(per, sc > 0 ? coef : X.neg(coef)), dom), equivalence: true });
  }
  S.log.add({ rule: "solve.trig.same-function", title: `${name} A = ${name} B`, why: name === "sin" ? "sin A = sin B exactly when A = B + 2k pi or A = pi - B + 2k pi." : name === "cos" ? "cos A = cos B exactly when A = B + 2k pi or A = -B + 2k pi." : "tan A = tan B exactly when A = B + k pi (where both are defined).", before: X.eq(X.fn(name, A), X.fn(name, B)), after: X.or(...fams.map((f) => X.eq(X.sym(x), C(X.add(f.offset, X.mul(f.period, X.sym("k"))), dom)))) });
  return { exact: [], approx: [], general: fams, regions: [], all: false, complete: true, methods: ["trigonometric"], notes: [] };
}
