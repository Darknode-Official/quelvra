import { test, eq, ok, throws, rng } from "./harness.js";
import * as N from "../public/engine/num.js";
import * as X from "../public/engine/expr.js";
import { parse } from "../public/engine/parse.js";
import { expand, makeCtx, simplify } from "../public/engine/simplify.js";
import { toText } from "../public/engine/print.js";
import * as P from "../public/engine/poly.js";

const q = (n, d = 1n) => N.Q(n, d);
const up = (...c) => P.poly(c); // low -> high
const ps = (p) => p.map((r) => N.toString(r)).join(",");
const peq = (a, b, msg = "") => ok(P.polyEq(a, b), `${msg} expected [${ps(b)}] got [${ps(a)}]`);
const U = (s) => P.fromTree(parse(s), "x");
const txt = (u) => toText(u);
const FT = (s) => txt(P.factorTree(parse(s)));
const canon = (u) => simplify(u, makeCtx());

// random integer polynomial helpers
function randPoly(r, deg, c = 9) {
  const out = [];
  for (let i = 0; i <= deg; i++) out.push(q(r.int(-c, c)));
  if (out[deg].n === 0n) out[deg] = q(r.pick([1, -1, 2, 3]));
  return P.norm(out);
}
const prod = (...ps2) => ps2.reduce((a, b) => P.mul(a, b), [N.ONE]);

// ---------------------------------------------------------------- representation / arithmetic
test("poly: construction and normalisation", () => {
  peq(up(1, 2, 0, 0), up(1, 2));
  eq(P.deg([]), -1);
  eq(P.deg(up(5)), 0);
  ok(P.isZeroPoly(up(0, 0)));
  eq(N.toString(P.lc(up(1, 2, 3))), "3");
});
test("poly: add sub mul", () => {
  peq(P.add(up(1, 2), up(3, 0, 1)), up(4, 2, 1));
  peq(P.sub(up(1, 2), up(1, 2)), []);
  peq(P.mul(up(-1, 1), up(1, 1)), up(-1, 0, 1));
  peq(P.mul(up("1/2", 1), up("1/3", 1)), up("1/6", "5/6", 1));
  peq(P.mul([], up(1, 2)), []);
});
test("poly: Karatsuba path agrees with schoolbook", () => {
  const r = rng(3);
  const a = [], b = [];
  for (let i = 0; i < 90; i++) { a.push(BigInt(r.int(-1000, 1000))); b.push(BigInt(r.int(-1000, 1000))); }
  a[89] = 7n; b[89] = -3n;
  const k = P.zMul(a, b);
  const s = new Array(179).fill(0n);
  for (let i = 0; i < 90; i++) for (let j = 0; j < 90; j++) s[i + j] += a[i] * b[j];
  ok(P.zEq(k, P.zNorm(s)));
});
test("poly: divmod, synthetic, pseudo, exact division", () => {
  const { q: qq, r } = P.divmod(up(-6, 11, -6, 1), up(-1, 1));
  peq(qq, up(6, -5, 1)); peq(r, []);
  const sd = P.syntheticDivide(up(-6, 11, -6, 1), 2);
  peq(sd.q, up(3, -4, 1)); eq(N.toString(sd.rem), "0");
  const s2 = P.syntheticDivide(up(1, 0, 1), 1);
  eq(N.toString(s2.rem), "2");
  const pd = P.pseudoDivmod(up(1, 0, 1), up(1, 2));
  // lc(b)^m a = q b + r
  peq(P.scale(up(1, 0, 1), N.pow(q(2), pd.m)), P.add(P.mul(pd.q, up(1, 2)), pd.r));
  peq(P.exactDiv(up(-1, 0, 1), up(1, 1)), up(-1, 1));
  eq(P.exactDiv(up(1, 0, 1), up(1, 1)), null);
  throws(() => P.divmod(up(1), []));
});
test("poly: pow, eval, derivative, composition", () => {
  peq(P.pow(up(1, 1), 3), up(1, 3, 3, 1));
  peq(P.pow(up(1, 1), 0), up(1));
  eq(N.toString(P.evalAt(up(1, 2, 3), "1/2")), "11/4");
  peq(P.deriv(up(5, 3, 0, 4)), up(3, 0, 12));
  peq(P.compose(up(0, 0, 1), up(1, 1)), up(1, 2, 1));
  peq(P.compose(up(1, 1), up(0, 0, 1)), up(1, 0, 1));
});
test("poly: content and primitive part", () => {
  eq(N.toString(P.content(up(4, 6, 8))), "2");
  peq(P.primitivePart(up(4, 6, 8)), up(2, 3, 4));
  eq(N.toString(P.content(up("1/2", "-3/4"))), "-1/4");
  peq(P.primitivePart(up("1/2", "-3/4")), up(-2, 3));
  const p = up("2/3", "-4/9", 6);
  peq(P.scale(P.primitivePart(p), P.content(p)), p);
});

// ---------------------------------------------------------------- gcd family
test("poly: gcd and lcm", () => {
  peq(P.gcd(up(-1, 0, 1), up(1, 2, 1)), up(1, 1));
  peq(P.gcd(up(1, 0, 1), up(-1, 1)), up(1));
  peq(P.gcd([], up(2, 4)), up("1/2", 1));
  peq(P.gcd([], []), []);
  peq(P.lcm(up(-1, 1), up(1, 1)), up(-1, 0, 1));
});
test("poly: extended gcd gives Bezout coefficients", () => {
  const a = up(-1, 0, 0, 1), b = up(-1, 0, 1);
  const { g, s, t } = P.xgcd(a, b);
  peq(g, up(-1, 1));
  peq(P.add(P.mul(s, a), P.mul(t, b)), g);
});
test("poly: remainder sequences end in an associate of the gcd", () => {
  const a = prod(up(-2, 1), up(1, 0, 1), up(3, 1)), b = prod(up(-2, 1), up(5, 1, 1));
  for (const kind of ["euclid", "primitive", "subresultant"]) {
    const seq = P.prs(a, b, kind);
    peq(P.monic(seq[seq.length - 1]), up(-2, 1), kind);
  }
  // classic Knuth example: subresultant PRS stays small and ends in a constant
  const k1 = up(-5, 2, 8, -3, -3, 0, 1, 0, 1), k2 = up(21, -9, -4, 0, 5, 0, 3);
  const seq = P.prs(k1, k2, "subresultant");
  eq(P.deg(seq[seq.length - 1]), 0);
  ok(seq.every((s) => s.every((c) => c.d === 1n)));
});
test("poly: square-free decomposition (Yun)", () => {
  const p = prod(P.pow(up(-1, 1), 3), P.pow(up(2, 1), 2), up(1, 0, 1));
  const sf = P.squareFree(p);
  eq(sf.factors.length, 3);
  let r = [sf.unit];
  for (const f of sf.factors) r = P.mul(r, P.pow(f.poly, f.mult));
  peq(r, p);
  const m3 = sf.factors.find((f) => f.mult === 3);
  peq(m3.poly, up(-1, 1));
  peq(P.squareFreePart(p), prod(up(-1, 1), up(2, 1), up(1, 0, 1)));
});

// ---------------------------------------------------------------- rational roots, resultants
test("poly: rational roots", () => {
  eq(P.rationalRoots(up(-1, 6, -11, 6)).map(N.toString).join(" "), "1/3 1/2 1");
  eq(P.rationalRoots(up(0, 0, -4, 1)).map(N.toString).join(" "), "0 4");
  eq(P.rationalRoots(up(1, 0, 1)).length, 0);
  eq(P.rationalRoots(up(5)).length, 0);
});
test("poly: rational roots with unfactorable coefficients (isolation fallback)", () => {
  const big = 1000000007n * 998244353n;
  const p = prod(up(-big, 1000000009n * 1000000021n), up(1, 0, 1), up(-3, 1));
  const rr = P.rationalRoots(p);
  eq(rr.length, 2);
  ok(rr.some((r) => N.eq(r, N.Q(big, 1000000009n * 1000000021n))));
});
test("poly: resultant", () => {
  eq(N.toString(P.resultant(up(-1, 0, 1), up(-1, 1))), "0");
  eq(N.toString(P.resultant(up(1, 0, 1), up(-2, 1))), "5");
  eq(N.toString(P.resultant(up(-3, 1), up(-7, 1))), "-4"); // res(x-a, x-b) = b(a) = a - b
  eq(N.toString(P.resultant(up(2), up(1, 1, 1))), "4");
  eq(N.toString(P.resultant([], up(1, 1))), "0");
  // res(a, b) = (-1)^(mn) res(b, a)
  const a = up(1, 2, 3), b = up(4, 0, 5, 6);
  eq(N.toString(P.resultant(a, b)), N.toString(N.mul(N.Q(1), P.resultant(b, a))));
});
test("poly: resultant matches product formula lc(a)^n prod b(roots of a)", () => {
  const a = prod(up(-1, 1), up(-2, 1), up(-5, 1)); // roots 1, 2, 5
  const b = up(3, -1, 2);
  let v = N.ONE;
  for (const r of [1, 2, 5]) v = N.mul(v, P.evalAt(b, r));
  eq(N.toString(P.resultant(a, b)), N.toString(v));
});
test("poly: discriminant", () => {
  eq(N.toString(P.discriminant(up(3, 5, 2))), "1"); // 25 - 24
  eq(N.toString(P.discriminant(up(1, 0, 1))), "-4");
  // x^3 + p x + q: -4p^3 - 27q^2
  eq(N.toString(P.discriminant(up(1, -3, 0, 1))), String(-4 * -27 - 27));
  eq(N.toString(P.discriminant(P.pow(up(-1, 1), 2))), "0");
});

// ---------------------------------------------------------------- real roots
test("poly: Sturm sequence and counts", () => {
  const p = prod(up(-1, 1), up(-2, 1), up(-3, 1), up(1, 0, 1));
  const seq = P.sturmSequence(p);
  ok(seq.length >= 2);
  eq(P.countRealRoots(p), 3);
  eq(P.countRealRoots(p, 1, 3), 3);
  eq(P.countRealRoots(p, "3/2", 3), 2);
  eq(P.countRealRoots(p, "3/2", "5/2"), 1);
  eq(P.countRealRoots(p, 4, 10), 0);
  eq(P.countRealRoots(P.pow(up(-1, 1), 5)), 1);
  eq(P.countRealRoots(up(7)), 0);
  throws(() => P.countRealRoots([]));
});
test("poly: isolation of Wilkinson-like product (x-1)...(x-10)", () => {
  let p = [N.ONE];
  for (let k = 1; k <= 10; k++) p = P.mul(p, up(-k, 1));
  const ivs = P.isolateRealRoots(p);
  eq(ivs.length, 10);
  for (let i = 0; i < 10; i++) {
    const iv = ivs[i], k = q(i + 1);
    if (iv.exact) ok(N.eq(iv.lo, k));
    else ok(N.cmp(iv.lo, k) < 0 && N.cmp(k, iv.hi) < 0, "root inside");
  }
});
test("poly: isolation of a perturbed Wilkinson polynomial (irrational roots)", () => {
  let p = [N.ONE];
  for (let k = 1; k <= 10; k++) p = P.mul(p, up(-k, 1));
  p = P.add(p, up(0, 0, 0, 0, 0, 0, 0, 0, 0, "1/1000000"));
  const ivs = P.isolateRealRoots(p);
  ok(ivs.length >= 6);
  for (let i = 1; i < ivs.length; i++) ok(N.cmp(ivs[i - 1].hi, ivs[i].lo) <= 0, "disjoint");
  for (const iv of ivs) if (!iv.exact) ok(N.sign(P.evalAt(p, iv.lo)) * N.sign(P.evalAt(p, iv.hi)) < 0, "sign change");
});
test("poly: real roots with multiplicities", () => {
  const p = prod(P.pow(up(-1, 1), 3), P.pow(up(2, 1), 2), up(-2, 0, 1));
  const rr = P.realRoots(p);
  eq(rr.map((r) => r.multiplicity).join(","), "2,1,3,1");
});
test("poly: refinement to a given width", () => {
  const p = up(-2, 0, 1);
  const iv = P.isolateRealRoots(p).find((i) => N.isPos(i.hi));
  const r = P.refineInterval(p, iv, "1/1000000");
  ok(N.cmp(N.sub(r.hi, r.lo), q(1, 1000000)) <= 0);
  ok(N.cmp(N.mul(r.lo, r.lo), q(2)) < 0 && N.cmp(N.mul(r.hi, r.hi), q(2)) > 0);
});
test("poly: certified decimal of sqrt(2) to 60 digits", () => {
  const p = up(-2, 0, 1);
  const iv = P.isolateRealRoots(p).find((i) => N.isPos(i.hi));
  const a = P.approxRealRoot(p, iv, 60);
  eq(a.value, "1.41421356237309504880168872420969807856967187537694807317668"); // rounded, trailing zero dropped
  eq(a.errorBound, "1e-60");
  // certificate: the decimal is within 10^-60 of an interval that brackets the root
  const v = N.fromDecimal(a.value), e = N.Q(1n, 10n ** 60n);
  ok(N.cmp(N.mul(N.sub(v, e), N.sub(v, e)), q(2)) < 0 && N.cmp(N.mul(N.add(v, e), N.add(v, e)), q(2)) > 0);
});
test("poly: certified decimals of the real root of x^5 - x - 1", () => {
  const p = up(-1, -1, 0, 0, 0, 1);
  const ivs = P.isolateRealRoots(p);
  eq(ivs.length, 1);
  const a = P.approxRealRoot(p, ivs[0], 30);
  const v = N.fromDecimal(a.value), e = N.Q(1n, 10n ** 30n);
  ok(N.sign(P.evalAt(p, N.sub(v, e))) * N.sign(P.evalAt(p, N.add(v, e))) < 0);
  ok(a.value.startsWith("1.1673039782614186842"));
});

// ---------------------------------------------------------------- interpolation
test("poly: interpolation (Newton and Lagrange agree)", () => {
  const pts = [[0, 1], [1, 3], [2, 11], [-1, -1]];
  const a = P.interpolate(pts), b = P.lagrange(pts);
  peq(a, b);
  for (const [x, y] of pts) eq(N.toString(P.evalAt(a, x)), String(y));
  throws(() => P.interpolate([[1, 1], [1, 2]]));
  peq(P.interpolate([["1/2", "1/3"]]), up("1/3"));
});

// ---------------------------------------------------------------- multivariate
test("poly: multivariate arithmetic, gcd, lcm, division", () => {
  const V = ["x", "y"];
  const A = P.fromTree(parse("(x+y)*(x-y)"), V), B = P.fromTree(parse("(x+y)^2"), V);
  eq(txt(P.toTree(P.mGcd(A, B))), "x + y");
  eq(txt(P.toTree(P.mDivExact(A, P.fromTree(parse("x-y"), V)))), "x + y");
  eq(P.mDivExact(A, P.fromTree(parse("x+2y"), V)), null);
  eq(txt(P.toTree(P.mLcm(A, B))), txt(expand(parse("(x+y)^2(x-y)"))));
  const g3 = P.mGcd(P.fromTree(parse("x^2*y*z - y*z"), ["x", "y", "z"]), P.fromTree(parse("x*y^2*z + y^2*z"), ["x", "y", "z"]));
  eq(txt(P.toTree(g3)), "y*z(x + 1)".replace("y*z(x + 1)", txt(expand(parse("y*z*(x+1)")))));
  eq(P.mDegree(A, "x"), 2);
  eq(P.mTotalDegree(B), 2);
});
test("poly: multivariate gcd with rational coefficients and constants", () => {
  const V = ["a", "b"];
  const g = P.mGcd(P.fromTree(parse("a^2/2 - b^2/2"), V), P.fromTree(parse("3a + 3b"), V));
  eq(txt(P.toTree(g)), "a + b");
  eq(txt(P.toTree(P.mGcd(P.fromTree(parse("2"), V), P.fromTree(parse("a"), V)))), "1");
});
test("poly: multivariate resultant eliminates a variable", () => {
  const V = ["x", "y"];
  const r = P.mResultant(P.fromTree(parse("x^2 + y^2 - 1"), V), P.fromTree(parse("x - y"), V), "x");
  eq(txt(P.toTree(r)), "2y^2 - 1");
  const r2 = P.mResultant(P.fromTree(parse("x*y - 1"), V), P.fromTree(parse("x^2 + y^2 - 4"), V), "y");
  eq(txt(P.toTree(r2)), "x^4 - 4x^2 + 1");
});

// ---------------------------------------------------------------- trees
test("poly: fromTree / toTree round trip", () => {
  peq(U("x^3 - 2x + 1/2"), up("1/2", -2, 0, 1));
  eq(U("sqrt(x)"), null);
  eq(U("1/x"), null);
  eq(U("sin(x)"), null);
  eq(U("a*x"), null);
  eq(U("pi*x"), null);
  peq(U("(x+1)^2/4"), up("1/4", "1/2", "1/4"));
  eq(txt(P.toTree(up(1, -2, 1))), "x^2 - 2x + 1");
  eq(txt(P.toTree([])), "0");
  eq(txt(P.toTree(up(1, 1), "t")), "t + 1");
  const m = P.fromTree(parse("a*x^2 + b*x + c"), ["x", "a", "b", "c"]);
  eq(m.terms.size, 3);
  eq(txt(P.toTree(m)), "a*x^2 + b*x + c");
});
test("poly: symbolic coefficients, degree, leading coefficient", () => {
  const c = P.coefficients(parse("a*x^2 + b*x + c"), "x");
  eq(c.map(txt).join(" | "), "c | b | a");
  eq(P.coefficients(parse("(a*x + b)^2"), "x").map(txt).join(" | "), "b^2 | 2a*b | a^2");
  eq(P.degree(parse("(x+1)^3 - x^3"), "x"), 2);
  eq(P.degree(parse("0"), "x"), -1);
  eq(P.degree(parse("sqrt(x) + 1"), "x"), null);
  eq(txt(P.leadingCoeff(parse("3x^2 y + x y^2"), "x")), "3y");
  ok(P.isPolynomial(parse("x^2 + sin(y) x"), "x"));
  ok(!P.isPolynomial(parse("x^2 + sin(x)"), "x"));
  ok(!P.isPolynomial(parse("1/(x+1)"), "x"));
  ok(P.isPolynomial(parse("x*y + 1"), ["x", "y"]));
});

// ---------------------------------------------------------------- factorisation
const FACTOR_CASES = [
  ["x^2 - 5x + 6", "(x - 2)(x - 3)"],
  ["2x^2 + 4x", "2x(x + 2)"],
  ["x^4 - 1", "(x - 1)(x + 1)(x^2 + 1)"],
  ["x^3 - 8", "(x - 2)(x^2 + 2x + 4)"],
  ["x^3 + 27", "(x + 3)(x^2 - 3x + 9)"],
  ["x^4 + 1", "x^4 + 1"],
  ["x^4 - 10x^2 + 1", "x^4 - 10x^2 + 1"],
  ["(x-1)^3(x+2)^2", "(x - 1)^3(x + 2)^2"],
  ["x^6 - 1", "(x - 1)(x + 1)(x^2 + x + 1)(x^2 - x + 1)"],
  ["x^5 + x + 1", "(x^2 + x + 1)(x^3 - x^2 + 1)"],
  ["x^4 + 4", "(x^2 - 2x + 2)(x^2 + 2x + 2)"],
  ["6x^2 + x - 2", "(2x - 1)(3x + 2)"],
  ["x^2/2 - 2", "(x - 2)(x + 2)/2"],
  ["-x^2 + 1", "-(x - 1)(x + 1)"],
  ["x^2 - 2", "x^2 - 2"],
  ["0", "0"],
  ["7", "7"],
  ["x", "x"],
  ["3x - 6", "3(x - 2)"],
  ["x^2 - y^2", "(x + y)(x - y)"],
  ["a*x^2 - a", "a(x - 1)(x + 1)"],
  ["x^2 + 5x*y + 6y^2", "(x + 2y)(x + 3y)"],
  ["x*y + x + y + 1", "(x + 1)(y + 1)"],
  ["x^2 + 2x*y + y^2 - z^2", "(x + y + z)(x + y - z)"],
  ["x^3 + x^2*y - x*y^2 - y^3", "(x + y)^2(x - y)"],
  ["x^2 + y^2", "x^2 + y^2"],
  ["sin(x)^2 - 1", "(sin(x) - 1)(sin(x) + 1)"],
  ["(x^2 - 1)/(x^2 + 3x + 2)", "(x - 1)/(x + 2)"],
];
for (const [src, want] of FACTOR_CASES) test(`factor ${src}`, () => eq(FT(src), want, src));
test("factor: cyclotomic x^n - 1 has d(n) irreducible factors", () => {
  const divisorsCount = (n) => { let c = 0; for (let d = 1; d <= n; d++) if (n % d === 0) c++; return c; };
  for (const n of [2, 3, 4, 5, 6, 8, 9, 10, 12, 15, 16, 18, 20, 24, 30]) {
    const p = P.sub(P.pow(up(0, 1), n), up(1));
    const f = P.factorQ(p);
    eq(f.factors.length, divisorsCount(n), "x^" + n + " - 1");
    ok(f.verified);
  }
});
test("factor: irreducible cyclotomics and Swinnerton-Dyer-like quartics", () => {
  for (const s of ["x^4 + 1", "x^4 - 10x^2 + 1", "x^4 + x^3 + x^2 + x + 1", "x^6 + x^3 + 1", "x^8 - 40x^6 + 352x^4 - 960x^2 + 576", "x^16 - 136x^14 + 6476x^12 - 141912x^10 + 1513334x^8 - 7453176x^6 + 13950764x^4 - 5596840x^2 + 46225", "x^4 - 2x^2 + 9"]) {
    ok(P.isIrreducible(U(s)), s);
  }
});
test("factor: large coefficients", () => {
  const a = up(-987654321987654321n, 123456789123456789n), b = up(1000000007n, 0, 1), c = up(3, -5, 0, 7);
  const p = prod(a, b, c, a);
  const f = P.factorQ(p);
  ok(f.verified);
  eq(f.factors.length, 3);
  eq(f.factors.map((x) => x.mult).sort().join(","), "1,1,2");
  let r = [f.unit];
  for (const x of f.factors) r = P.mul(r, P.pow(x.poly, x.mult));
  peq(r, p);
});
test("factor: degree 12 product of quartics needing recombination", () => {
  const a = U("x^4 + 1"), b = U("x^4 - 10x^2 + 1"), c = U("x^4 + 2x^3 - x + 7");
  const f = P.factorQ(prod(a, b, c));
  eq(f.factors.length, 3);
  ok(f.factors.every((x) => P.deg(x.poly) === 4));
});
test("factor: zero and constants", () => {
  eq(P.factorQ([]).factors.length, 0);
  eq(N.toString(P.factorQ(up("5/3")).unit), "5/3");
  eq(P.factorZ([0n]).factors.length, 0);
});
test("factor: budget exhaustion throws BUDGET", () => {
  let code = null;
  try { P.factorQ(U("x^8 - 40x^6 + 352x^4 - 960x^2 + 576"), { budget: { ops: 20 } }); } catch (e) { code = e.code; }
  eq(code, "BUDGET");
});
test("factor: multivariate content, square-free and Kronecker", () => {
  const V = ["x", "y"];
  const m = P.fromTree(parse("x^3*y - x*y^3 + 2x^2*y^2 - 2x*y^2 * 0"), V);
  const f = P.mFactor(m);
  ok(f.verified && f.complete);
  let r = P.mConst(V, f.unit);
  for (const x of f.factors) r = P.mMul(r, P.mPow(x.poly, x.mult));
  ok(P.mEq(r, m));
  const m2 = P.fromTree(parse("(x^2 + y + 1)^2 (x - y^2)(2x + 3y)"), V);
  const f2 = P.mFactor(m2);
  eq(f2.factors.length, 3);
  eq(f2.factors.map((x) => x.mult).sort().join(","), "1,1,2");
});
test("factor: three variables", () => {
  eq(FT("x*y*z + x*y + x*z + y*z + x + y + z + 1"), "(x + 1)(y + 1)(z + 1)");
  eq(FT("a^3 - b^3"), "(a - b)(a^2 + a*b + b^2)");
  eq(FT("x^8 - 16x^6 + 88x^4 - 192x^2 + 144"), "(x^2 - 6)^2(x^2 - 2)^2");
});

test("factor: modulo p (Cantor-Zassenhaus)", () => {
  const r = P.factorModP([1, 0, 0, 0, 1], 17); // x^4 + 1 splits into linear factors mod 17
  eq(r.factors.length, 4);
  ok(r.factors.every((f) => f.length === 2));
  const s = P.factorModP([1, 0, 0, 0, 1], 3); // two quadratics mod 3
  eq(s.factors.map((f) => f.length - 1).join(","), "2,2");
  // product check mod p
  let prod2 = [s.lc];
  const mulp = (a, b) => { const o = new Array(a.length + b.length - 1).fill(0); a.forEach((x, i) => b.forEach((y, j) => { o[i + j] = (o[i + j] + x * y) % 3; })); return o; };
  for (const f of s.factors) prod2 = mulp(prod2, f);
  eq(prod2.join(","), "1,0,0,0,1");
  throws(() => P.factorModP([1, 2, 1], 5));
  throws(() => P.factorModP([1, 1], 9));
});
test("factor: trivariate products via Kronecker", () => {
  const V = ["x", "y", "z"];
  const m = P.fromTree(parse("(3x^2 + 2x*y + 3y^2 - 2x*z - 4y*z - 2z^2 - 2)(2x^2 + 3y^2 + x*z + 2y*z - x*y - z^2 - z)(y + 2z - 3x + 4)"), V);
  const f = P.mFactor(m);
  ok(f.complete && f.verified);
  eq(f.factors.length, 3);
});

// ---------------------------------------------------------------- factor with steps
function stepRules(src) { return P.factorSteps(parse(src)).steps.map((s) => s.rule).join(","); }
test("factor steps: rule ids", () => {
  eq(stepRules("2x^2 + 4x"), "factor.common");
  eq(stepRules("x^4 - 1"), "factor.diff-squares,factor.diff-squares");
  eq(stepRules("x^3 - 8"), "factor.diff-cubes");
  eq(stepRules("x^3 + 8"), "factor.sum-cubes");
  eq(stepRules("x^2 - 6x + 9"), "factor.perfect-square");
  eq(stepRules("x^2 - 5x + 6"), "factor.trinomial");
  eq(stepRules("6x^2 + x - 2"), "factor.trinomial-ac");
  eq(stepRules("x^3 + 3x^2 - 4x - 12"), "factor.grouping,factor.diff-squares");
  eq(stepRules("x^3 - 6x^2 + 11x - 6"), "factor.rational-root,factor.trinomial");
  eq(stepRules("x^5 + x + 1"), "factor.zassenhaus");
  eq(stepRules("(x^2+1)^2 (x^2+2)"), "factor.expand,factor.square-free");
  eq(stepRules("x^4 + 1"), "");
});
test("factor steps: records are well formed and chain", () => {
  for (const src of ["3x^3 - 3x", "x^6 - 64", "x^4 + 5x^2 + 4", "2x^3 - 2x^2 - 12x", "x^2 y - y^3", "x^5 + x^4 + x + 1"]) {
    const r = P.factorSteps(parse(src));
    eq(txt(r.result), FT(src), src);
    for (let i = 0; i < r.steps.length; i++) {
      const s = r.steps[i];
      ok(s.rule && s.title && s.why && s.before && s.after && s.kind === "equivalent", src);
      if (i) ok(r.steps[i - 1].after === s.before, "chained " + src);
      const a = expand(s.before, makeCtx()), b = expand(s.after, makeCtx());
      ok(a === b, `step ${s.rule} preserves value in ${src}`);
    }
    if (r.steps.length) ok(r.steps[r.steps.length - 1].after === r.result, src);
  }
});

// ---------------------------------------------------------------- closed-form roots / solve
function solveText(src, domain = "real") {
  const r = P.solvePolynomial(parse(src), "x", { domain });
  return { r, s: r.exact.map((e) => txt(e.root) + (e.multiplicity > 1 ? "^" + e.multiplicity : "")).join(" ; ") };
}
test("solve: linear and quadratic", () => {
  eq(solveText("2x - 3").s, "3/2");
  eq(solveText("x^2 - 5x + 6").s, "2 ; 3");
  eq(solveText("x^2 - 2").s, "-sqrt(2) ; sqrt(2)");
  eq(solveText("x^2 + 1").s, "");
  ok(solveText("x^2 + 1").r.complete);
  eq(solveText("x^2 + 1", "complex").s, "-i ; i");
  eq(solveText("x^2 + x + 1", "complex").r.exact.length, 2);
  ok(solveText("x^2 + x + 1", "complex").r.exact.every((e) => e.verified === "exact"));
});
test("solve: repeated roots carry multiplicity", () => {
  eq(solveText("(x-1)^3(x+2)^2").s, "-2^2 ; 1^3");
});
test("solve: cubic via Cardano and casus irreducibilis", () => {
  const a = solveText("x^3 - 2");
  eq(a.s, "cbrt(2)");
  ok(a.r.complete);
  const b = solveText("x^3 - 3x + 1");
  eq(b.r.exact.length, 3);
  ok(b.r.exact.every((e) => e.verified === "numeric" && e.real));
  const c = solveText("x^3 - 2", "complex");
  eq(c.r.exact.length, 3);
  const d = solveText("x^3 - x - 1");
  eq(d.r.exact.length, 1);
  ok(d.r.complete);
});
test("solve: quartics (biquadratic, denesting, Ferrari)", () => {
  eq(solveText("x^4 - 10x^2 + 1").s, "-(sqrt(2) + sqrt(3)) ; -(sqrt(3) - sqrt(2)) ; sqrt(3) - sqrt(2) ; sqrt(2) + sqrt(3)");
  ok(solveText("x^4 - 10x^2 + 1").r.exact.every((e) => e.verified === "exact"));
  const a = solveText("x^4 + 1", "complex");
  eq(a.r.exact.length, 4);
  ok(a.r.exact.every((e) => e.verified === "exact"));
  eq(solveText("x^4 + 1").r.exact.length, 0);
  const b = solveText("x^4 - 4x - 1");
  eq(b.r.exact.length, 2);
  ok(b.r.complete);
  const c = solveText("x^4 + x + 1", "complex");
  eq(c.r.exact.length, 4);
  ok(c.r.complete);
  const d = solveText("x^4 - 3x^2 + x + 1"); // four real roots? check count against Sturm
  eq(d.r.exact.length, P.countRealRoots(U("x^4 - 3x^2 + x + 1")));
});
test("solve: degree 5 falls back to certified approximations", () => {
  const r = P.solvePolynomial(parse("x^5 - x - 1"), "x");
  ok(!r.complete);
  eq(r.approx.length, 1);
  ok(r.approx[0].certified && r.approx[0].re.value.startsWith("1.16730397826141868"));
  const c = P.solvePolynomial(parse("x^5 - x - 1"), "x", { domain: "complex" });
  eq(c.approx.length, 5);
});
test("solve: binomials of high degree", () => {
  const r = P.solvePolynomial(parse("x^5 - 2"), "x", { domain: "complex" });
  ok(r.complete);
  eq(r.exact.length, 5);
  eq(txt(r.exact[0].root), "2^(1/5)");
  const s = P.solvePolynomial(parse("x^6 - 3"), "x");
  eq(s.exact.map((e) => txt(e.root)).join(" ; "), "-3^(1/6) ; 3^(1/6)");
});
test("solve: zero polynomial, constants, symbolic coefficients", () => {
  ok(P.solvePolynomial(parse("0"), "x").identity);
  eq(P.solvePolynomial(parse("5"), "x").exact.length, 0);
  const s = P.solvePolynomial(parse("a*x^2 + b*x + c"), "x");
  eq(s.exact.map((e) => txt(e.root)).join(" ; "), "(-b - sqrt(b^2 - 4a*c))/(2a) ; (-b + sqrt(b^2 - 4a*c))/(2a)");
  ok(s.exact.every((e) => e.verified === "exact"));
  eq(txt(s.conditions[0]), "a != 0");
  eq(txt(P.solvePolynomial(parse("a*x - b"), "x").exact[0].root), "b/a");
  eq(P.solvePolynomial(parse("sin(x) + 1"), "x").complete, false);
});
test("solve: every exact root substitutes to zero (exact or high-accuracy numeric)", () => {
  for (const src of ["x^2 - 3x + 1", "2x^2 + 3x + 5", "x^3 - 3x + 1", "x^3 + x + 1", "x^4 - 10x^2 + 1", "x^4 + 1", "x^4 - 4x - 1", "3x^3 - x^2 + 2"]) {
    const r = P.solvePolynomial(parse(src), "x", { domain: "complex" });
    ok(r.complete, src);
    const deg = P.deg(U(src));
    eq(r.exact.reduce((s, e) => s + e.multiplicity, 0), deg, src);
    for (const e of r.exact) {
      if (e.verified === "exact") {
        const v = canon(expand(X.subs(parse(src), { x: e.root }), makeCtx()));
        ok(X.isZero(v), `${src} at ${txt(e.root)}`);
      } else {
        const z = P.evalComplex(e.root);
        ok(z && isFinite(z.re), src);
      }
    }
  }
});
test("complex roots: Aberth with residuals and multiplicities", () => {
  const r = P.complexRoots(U("x^4 + 1"));
  eq(r.length, 4);
  for (const z of r) { ok(Math.abs(Math.hypot(z.re, z.im) - 1) < 1e-12); ok(z.residual < 1e-12); }
  const m = P.complexRoots(prod(P.pow(up(-1, 1), 3), up(1, 0, 1)));
  eq(m.length, 3);
  eq(m.find((z) => z.im === 0).multiplicity, 3);
  let w = [N.ONE];
  for (let k = 1; k <= 10; k++) w = P.mul(w, up(-k, 1));
  const wr = P.complexRoots(w);
  wr.forEach((z, i) => ok(Math.abs(z.re - (i + 1)) < 1e-6 && Math.abs(z.im) < 1e-6, "wilkinson " + i));
});

// ---------------------------------------------------------------- apart / cancel
test("apart: decompositions", () => {
  eq(txt(P.apart(parse("1/(x^2-1)"), "x")), "1/(2(x - 1)) - 1/(2(x + 1))");
  eq(txt(P.apart(parse("(x^3+1)/(x^2-1)"), "x")), "x + 1/(x - 1)");
  eq(txt(P.apart(parse("(2x+3)/(x^3-x)"), "x")), "5/(2(x - 1)) + 1/(2(x + 1)) - 3/x");
  eq(txt(P.apart(parse("x+1"), parse("x^2+3x+2"), "x")), "1/(x + 2)");
  eq(P.apart(parse("1/(x^2 - a)"), "x"), null);
});
test("apart: repeated and irreducible factors", () => {
  const r = P.apartTerms(up(1), prod(P.pow(up(-1, 1), 2), up(1, 0, 1)));
  ok(r.verified);
  eq(r.terms.length, 3);
  const t = P.apartTerms(up(0, 1), P.pow(up(1, 1, 1), 2));
  eq(t.terms.length, 1);
  eq(t.terms[0].power, 2);
  const cub = P.apartTerms(up(1), up(-2, 0, 0, 1)); // x^3 - 2 irreducible: stays as one term
  eq(cub.terms.length, 1);
});
test("cancel: lowest terms with the cancelled factor as a condition", () => {
  const c = P.cancel(parse("(x^2-1)/(x^2+2x+1)"), "x");
  eq(txt(c.tree), "(x - 1)/(x + 1)");
  eq(txt(c.cancelled), "x + 1");
  eq(txt(c.conditions[0]), "x + 1 != 0");
  const c2 = P.cancel(parse("(x^2 - y^2)/(2x - 2y)"));
  eq(txt(c2.tree), "x/2 + y/2"); // canonical form distributes the numeric factor
  eq(txt(c2.cancelled), "x - y");
  const c3 = P.cancel(parse("(x+1)/(x+2)"), "x");
  eq(c3.cancelled, null);
  eq(c3.conditions.length, 0);
});

// ---------------------------------------------------------------- property tests
test("property: factor then expand reproduces random products (univariate)", () => {
  const r = rng(101);
  for (let i = 0; i < 160; i++) {
    const k = r.int(1, 4);
    const parts = [];
    let linear = 0;
    for (let j = 0; j < k; j++) {
      const d = r.int(1, 3);
      const f = randPoly(r, d, 6);
      parts.push(f);
      if (d === 1) linear++;
    }
    const p = P.scale(prod(...parts), q(r.int(1, 5), r.int(1, 4)));
    const f = P.factorQ(p);
    ok(f.verified, "verified");
    let back = [f.unit];
    for (const x of f.factors) back = P.mul(back, P.pow(x.poly, x.mult));
    peq(back, p, "factorQ reconstructs");
    const lin = f.factors.filter((x) => P.deg(x.poly) === 1).reduce((s, x) => s + x.mult, 0);
    ok(lin >= linear, "linear factors found");
    // factors are irreducible: no rational roots in factors of degree >= 2
    for (const x of f.factors) if (P.deg(x.poly) >= 2) eq(P.rationalRoots(x.poly).length, 0);
  }
});
test("property: factorTree then expand is the identity on random polynomials", () => {
  const r = rng(202);
  for (let i = 0; i < 120; i++) {
    const p = r.next() < 0.5 ? randPoly(r, r.int(0, 6)) : prod(randPoly(r, r.int(1, 2), 4), randPoly(r, r.int(1, 3), 4));
    const t = P.toTree(p);
    const back = P.fromTree(P.factorTree(t), "x");
    peq(back, p, txt(t));
  }
});
test("property: gcd divides both and equals the constructed gcd", () => {
  const r = rng(303);
  for (let i = 0; i < 120; i++) {
    const g = randPoly(r, r.int(0, 3), 5), a0 = randPoly(r, r.int(0, 3), 5), b0 = randPoly(r, r.int(0, 3), 5);
    const a = P.mul(g, a0), b = P.mul(g, b0);
    const d = P.gcd(a, b);
    ok(P.exactDiv(a, d) !== null && P.exactDiv(b, d) !== null, "divides");
    ok(P.exactDiv(d, P.monic(g)) !== null, "constructed gcd divides the gcd");
    if (!N.isZero(P.resultant(a0, b0))) peq(d, P.monic(g), "equals constructed gcd");
    const { s, t, g: gg } = P.xgcd(a, b);
    peq(P.add(P.mul(s, a), P.mul(t, b)), gg, "Bezout");
  }
});
test("property: division identity a = b q + r with deg r < deg b", () => {
  const r = rng(404);
  for (let i = 0; i < 200; i++) {
    const a = randPoly(r, r.int(0, 8)), b = randPoly(r, r.int(0, 5));
    const { q: qq, r: rr } = P.divmod(a, b);
    peq(P.add(P.mul(b, qq), rr), a);
    ok(P.deg(rr) < P.deg(b));
    const pd = P.pseudoDivmod(a, b);
    peq(P.scale(a, N.pow(P.lc(b), pd.m)), P.add(P.mul(pd.q, b), pd.r));
  }
});
test("property: square-free decomposition reconstructs", () => {
  const r = rng(505);
  for (let i = 0; i < 80; i++) {
    let p = [q(r.int(1, 6))];
    for (let j = r.int(1, 3); j > 0; j--) p = P.mul(p, P.pow(randPoly(r, r.int(1, 2), 4), r.int(1, 3)));
    const sf = P.squareFree(p);
    let back = [sf.unit];
    for (const f of sf.factors) back = P.mul(back, P.pow(f.poly, f.mult));
    peq(back, p);
    for (const f of sf.factors) eq(P.deg(P.gcd(f.poly, P.deriv(f.poly))), 0, "square-free part");
  }
});
test("property: resultant vanishes iff there is a common root", () => {
  const r = rng(606);
  for (let i = 0; i < 100; i++) {
    const c = up(-r.int(-5, 5), r.int(1, 3));
    const a = P.mul(c, randPoly(r, r.int(0, 3), 5)), b = P.mul(c, randPoly(r, r.int(0, 3), 5));
    eq(N.toString(P.resultant(a, b)), "0");
    const u = randPoly(r, r.int(1, 4), 7), v = randPoly(r, r.int(1, 4), 7);
    eq(N.isZero(P.resultant(u, v)), P.deg(P.gcd(u, v)) > 0);
  }
});
test("property: Sturm counts match constructed roots; isolation intervals are disjoint", () => {
  const r = rng(707);
  for (let i = 0; i < 60; i++) {
    const roots = new Set();
    const n = r.int(1, 6);
    while (roots.size < n) roots.add(r.int(-20, 20) / r.pick([1, 2, 3]));
    let p = [N.ONE];
    const rs = [...roots].map((v) => (Number.isInteger(v) ? q(v) : N.div(q(Math.round(v * 6)), q(6))));
    for (const x of rs) p = P.mul(p, [N.neg(x), N.ONE]);
    if (r.next() < 0.5) p = P.mul(p, up(r.int(1, 5), 0, 1));
    if (r.next() < 0.3) p = P.mul(p, P.pow([N.neg(rs[0]), N.ONE], 2));
    eq(P.countRealRoots(p), n);
    const lo = q(-5), hi = q(5);
    eq(P.countRealRoots(p, lo, hi), rs.filter((x) => N.cmp(x, lo) >= 0 && N.cmp(x, hi) <= 0).length);
    const ivs = P.isolateRealRoots(p);
    eq(ivs.length, n);
    for (let j = 1; j < ivs.length; j++) ok(N.cmp(ivs[j - 1].hi, ivs[j].lo) <= 0, "disjoint");
    const sfp = P.squareFreePart(p);
    for (const iv of ivs) {
      if (iv.exact) ok(N.isZero(P.evalAt(p, iv.lo)));
      else ok(N.sign(P.evalAt(sfp, iv.lo)) * N.sign(P.evalAt(sfp, iv.hi)) < 0, "sign change");
      ok(rs.filter((x) => (iv.exact ? N.eq(x, iv.lo) : N.cmp(iv.lo, x) < 0 && N.cmp(x, iv.hi) < 0)).length === 1, "exactly one root");
    }
  }
});
test("property: isolation of random irrational polynomials (sign changes)", () => {
  const r = rng(808);
  for (let i = 0; i < 40; i++) {
    const p = randPoly(r, r.int(2, 9), 20);
    const ivs = P.isolateRealRoots(p);
    eq(ivs.length, P.countRealRoots(p));
    const s = P.squareFreePart(p);
    for (let j = 0; j < ivs.length; j++) {
      if (j) ok(N.cmp(ivs[j - 1].hi, ivs[j].lo) <= 0);
      if (!ivs[j].exact) {
        ok(N.sign(P.evalAt(s, ivs[j].lo)) * N.sign(P.evalAt(s, ivs[j].hi)) < 0);
        eq(P.countRealRoots(p, ivs[j].lo, ivs[j].hi), 1);
      }
    }
  }
});
test("property: apart recombines to the original rational function", () => {
  const r = rng(909);
  for (let i = 0; i < 50; i++) {
    let d = [q(r.int(1, 3))];
    for (let j = r.int(1, 3); j > 0; j--) d = P.mul(d, P.pow(randPoly(r, r.int(1, 2), 4), r.int(1, 2)));
    const n = randPoly(r, r.int(0, P.deg(d) + 1), 6);
    const res = P.apartTerms(n, d);
    ok(res.verified);
    for (const t of res.terms) ok(P.deg(t.numer) < P.deg(t.factor));
    // independent check: evaluate at rational points
    for (let k = 0; k < 4; k++) {
      const x = q(r.int(-30, 30), r.int(1, 7));
      const dv = P.evalAt(d, x);
      if (N.isZero(dv)) continue;
      let s = P.evalAt(res.poly, x);
      for (const t of res.terms) s = N.add(s, N.div(P.evalAt(t.numer, x), N.pow(P.evalAt(t.factor, x), t.power)));
      ok(N.eq(s, N.div(P.evalAt(n, x), dv)), "value at x");
    }
  }
});
test("property: apart tree evaluates to the original", () => {
  const r = rng(1001);
  for (let i = 0; i < 15; i++) {
    const d = prod(up(r.int(-4, 4), 1), up(r.int(1, 3), r.int(-2, 2), 1));
    const n = randPoly(r, r.int(0, 2), 5);
    const t = P.apart(P.toTree(n), P.toTree(d), "x");
    if (!t) continue;
    for (let k = 0; k < 3; k++) {
      const x = q(r.int(-9, 9), r.int(1, 5));
      if (N.isZero(P.evalAt(d, x))) continue;
      const v = canon(X.subs(t, { x: X.num(x) }));
      ok(X.isNum(v) && N.eq(v.v, N.div(P.evalAt(n, x), P.evalAt(d, x))));
    }
  }
});
test("property: exact quadratic roots substitute to zero", () => {
  const r = rng(1101);
  for (let i = 0; i < 40; i++) {
    const p = randPoly(r, 2, 9);
    const res = P.solvePolynomial(P.toTree(p), "x", { domain: "complex" });
    ok(res.complete);
    for (const e of res.exact) {
      eq(e.verified, "exact");
      const v = canon(expand(X.subs(P.toTree(p), { x: e.root }), makeCtx()));
      ok(X.isZero(v), txt(P.toTree(p)) + " at " + txt(e.root));
    }
  }
});
test("property: multivariate factorisation reconstructs products of linear/quadratic factors", () => {
  const r = rng(1201);
  const V = ["x", "y"];
  const rnd = (deg) => {
    const ts = [];
    for (let a = 0; a <= deg; a++) for (let b = 0; a + b <= deg; b++) if (r.next() < 0.6 || a + b === deg) ts.push([[a, b], r.int(-3, 3)]);
    return P.mpoly(V, ts);
  };
  for (let i = 0; i < 25; i++) {
    const fs = [];
    for (let j = r.int(1, 3); j > 0; j--) { const f = rnd(r.int(1, 2)); if (P.mUsedVars(f).length) fs.push(f); }
    if (!fs.length) continue;
    const m = fs.reduce((a, b) => P.mMul(a, b));
    const f = P.mFactor(m);
    ok(f.verified);
    let back = P.mConst(V, f.unit);
    for (const x of f.factors) back = P.mMul(back, P.mPow(x.poly, x.mult));
    ok(P.mEq(back, m), "reconstructs");
    const lin = fs.filter((g) => P.mTotalDegree(g) === 1 && P.mNormalize(g).p.terms.size >= 1).length;
    const got = f.factors.filter((x) => P.mTotalDegree(x.poly) === 1).reduce((s, x) => s + x.mult, 0);
    ok(got >= lin, "linear factors found");
  }
});
test("property: interpolation reproduces random polynomials", () => {
  const r = rng(1301);
  for (let i = 0; i < 40; i++) {
    const p = randPoly(r, r.int(0, 6));
    const pts = [];
    for (let k = 0; k <= P.deg(p); k++) pts.push([k - 3, P.evalAt(p, k - 3)]);
    peq(P.interpolate(pts), p);
  }
});
