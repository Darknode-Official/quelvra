import { test, eq, ok, throws, close, P, rng } from "./harness.js";
import * as Q from "../public/engine/num.js";
import * as X from "../public/engine/expr.js";
import * as B from "../public/engine/bigfloat.js";
import * as IV from "../public/engine/interval.js";
import * as Nm from "../public/engine/numeric.js";
import { parse } from "../public/engine/parse.js";

// ---------------- known constants (100 significant digits) ----------------
const PI100 = "3.141592653589793238462643383279502884197169399375105820974944592307816406286208998628034825342117068";
const E100 = "2.718281828459045235360287471352662497757247093699959574966967627724076630353547594571382178525166427";
const SQRT2_100 = "1.414213562373095048801688724209698078569671875376948073176679737990732478462107038850387534327641573";
const LN2_100 = "0.6931471805599453094172321214581765680755001343602552541206800094933936219696947156058633269964186875";
const SIN1_100 = "0.8414709848078965066525023216302989996225630607983710656727517099919104043912396689486397435430526959";
const COS1_100 = "0.5403023058681397174009366074429766037323104206179222276700972553811003947744717645179518560871830893";
const DOTTIE = "0.739085133215160641655312087673873404013411758900757464965";
const ZETA2_50 = "1.6449340668482264364724151666460251892189499012068";

const bits = (d) => B.digitsToBits(d) + 16;
// round a decimal string to n significant digits (exactly, via rationals)
const roundStr = (s, n) => B.toString(B.fromRational(Q.fromDecimal(s), 4000), n);
const RECORD_KEYS = ["value", "digits", "requested", "errorBound", "method", "iterations", "converged", "warnings"];
function isRecord(r, extra = []) {
  ok(typeof r.value === "string", "value is a string");
  ok(Number.isInteger(r.digits) && r.digits >= 0 && r.digits <= r.requested, `digits ${r.digits} within [0, requested ${r.requested}]`);
  ok(r.errorBound === null || typeof r.errorBound === "string", "errorBound string|null");
  ok(typeof r.method === "string" && r.method.length > 0, "method");
  ok(Number.isInteger(r.iterations), "iterations");
  ok(typeof r.converged === "boolean", "converged");
  if (r.warnings) ok(Array.isArray(r.warnings) && r.warnings.every((w) => typeof w === "string"), "warnings");
  for (const k of Object.keys(r)) ok(RECORD_KEYS.includes(k) || extra.includes(k), `unexpected key ${k}`);
}
// exact polynomial evaluation at a decimal string
function polyAt(coeffs, xs) {
  const x = Q.fromDecimal(xs);
  let r = Q.ZERO;
  for (const c of coeffs) r = Q.add(Q.mul(r, x), Q.Q(c));
  return r;
}

// ============================ bigfloat ============================
test("bigfloat: pi to 100 digits", () => eq(B.toString(B.pi(bits(100)), 100), PI100));
test("bigfloat: e = exp(1) to 100 digits", () => {
  eq(B.toString(B.e(bits(100)), 100), E100);
  eq(B.toString(B.exp(B.ONE, bits(100)), 100), E100);
});
test("bigfloat: sqrt(2) to 100 digits", () => eq(B.toString(B.sqrt(B.TWO, bits(100)), 100), SQRT2_100));
test("bigfloat: ln 2 (cached constant and ln) to 100 digits", () => {
  eq(B.toString(B.ln2(bits(100)), 100), LN2_100);
  eq(B.toString(B.ln(B.TWO, bits(100)), 100), LN2_100);
});
test("bigfloat: sin(1), cos(1) to 100 digits", () => {
  eq(B.toString(B.sin(B.ONE, bits(100)), 100), SIN1_100);
  eq(B.toString(B.cos(B.ONE, bits(100)), 100), COS1_100);
});
test("bigfloat: 4 atan(1), 6 asin(1/2), 3 acos(-1/2)/2, gamma(1/2)^2 all equal pi (60 digits)", () => {
  const p = bits(60), want = PI100.slice(0, 61);
  const s = (x) => B.toString(x, 60);
  eq(s(B.mulPow2(B.atan(B.ONE, p), 2)), roundStr(PI100, 60));
  eq(s(B.mul(B.asin(B.HALF, p), B.fromInt(6), p)), roundStr(PI100, 60));
  eq(s(B.div(B.mul(B.acos(B.fromString("-0.5"), p), B.fromInt(3), p), B.TWO, p)), roundStr(PI100, 60));
  eq(s(B.powInt(B.gamma(B.HALF, p), 2, p)), roundStr(PI100, 60));
  ok(want.length === 61);
});
test("bigfloat: atan2 quadrants", () => {
  const p = 120, pi = B.pi(p);
  eq(B.toString(B.atan2(B.ONE, B.fromInt(-1), p), 30), B.toString(B.mul(pi, B.fromString("0.75"), p), 30));
  eq(B.toString(B.atan2(B.fromInt(-1), B.fromInt(-1), p), 30), B.toString(B.mul(pi, B.fromString("-0.75"), p), 30));
  throws(() => B.atan2(B.ZERO, B.ZERO, p));
});
test("bigfloat: gamma(5.5) = 945/32 sqrt(pi); gamma(-1/2) = -2 sqrt(pi); gamma(6) = 120", () => {
  const p = bits(50);
  const sp = B.sqrt(B.pi(p + 8), p + 8);
  eq(B.toString(B.gamma(B.fromString("5.5"), p), 50), B.toString(B.mul(B.fromRational(Q.Q(945, 32), p), sp, p), 50));
  eq(B.toString(B.gamma(B.fromString("-0.5"), p), 50), B.toString(B.mul(B.fromInt(-2), sp, p), 50));
  eq(B.toString(B.gamma(B.fromInt(6), p), 10), "120.0000000");
  throws(() => B.gamma(B.fromInt(-2), p));
});
test("bigfloat: erf(1) matches the exact rational Taylor series times 2/sqrt(pi) (50 digits)", () => {
  // sum_{n<80} (-1)^n / (n! (2n+1)) exactly
  let s = Q.ZERO, fact = 1n;
  for (let n = 0; n < 80; n++) {
    if (n > 0) fact *= BigInt(n);
    const t = Q.Q(n % 2 ? -1n : 1n, fact * BigInt(2 * n + 1));
    s = Q.add(s, t);
  }
  const p = bits(50);
  const ref = B.div(B.mul(B.fromRational(s, p + 20), B.TWO, p + 20), B.sqrt(B.pi(p + 20), p + 20), p);
  eq(B.toString(B.erf(B.ONE, p), 50), B.toString(ref, 50));
  eq(B.toString(B.erf(B.fromInt(-30), 100), 10), "-1.000000000");
});
test("bigfloat: digamma(1) = -Euler gamma", () => eq(B.toString(B.digamma(B.ONE, bits(40)), 30), "-0.577215664901532860606512090082"));
test("bigfloat: Bernoulli numbers B2, B4, B6, B8, B10", () => {
  const want = [[1n, 6n], [-1n, 30n], [1n, 42n], [-1n, 30n], [5n, 66n]];
  want.forEach(([n, d], i) => { const b = B.bernoulli2k(i + 1); ok(b.n === n && b.d === d, `B${2 * i + 2}`); });
});
test("bigfloat: hyperbolic identities at 1 and tiny arguments keep relative precision", () => {
  const p = bits(40), x = B.fromString("1e-30");
  eq(B.toString(B.sinh(x, p), 30), "1.00000000000000000000000000000e-30");
  eq(B.toString(B.tanh(x, p), 30), "1.00000000000000000000000000000e-30");
  eq(B.toString(B.asinh(x, p), 30), "1.00000000000000000000000000000e-30");
  eq(B.toString(B.sin(x, p), 30), "1.00000000000000000000000000000e-30");
  eq(B.toString(B.atan(x, p), 30), "1.00000000000000000000000000000e-30");
  eq(B.toString(B.ln(B.add(B.ONE, x, Infinity), p), 25), "1.000000000000000000000000e-30");
});
test("bigfloat: sin near a multiple of pi keeps relative precision", () => {
  // sin(355) = -sin(355 - 113 pi), where 355 - 113 pi ~ 3.0144e-5 is formed at 400 bits
  const d = B.sub(B.fromInt(355), B.mul(B.fromInt(113), B.pi(400), 400), 400);
  eq(B.toString(B.sin(B.fromInt(355), bits(30)), 30), B.toString(B.neg(B.sin(d, 400)), 30));
  ok(B.toString(B.sin(B.fromInt(355), bits(30)), 30).startsWith("-0.0000301443533594884"));
});
test("bigfloat: correct rounding of conversions and toString (half to even)", () => {
  ok(B.eq(B.fromString("0.1", 53), B.fromNumber(0.1)), "fromString rounds like IEEE");
  eq(B.toNumber(B.fromRational(Q.Q(1, 3), 53)), 1 / 3);
  eq(B.toString(B.fromString("0.125", 200), 2), "0.12");
  eq(B.toString(B.fromString("0.375", 200), 2), "0.38");
  eq(B.toString(B.fromString("-2.5", 200), 1), "-2");
  eq(B.toString(B.fromString("9.9999", 200), 3), "10.0");
  eq(B.toString(B.fromString("123456789012345678901234", 200), 5), "1.2346e23");
  eq(B.toString(B.fromString("0.000123456", 200), 5), "0.00012346");
  eq(B.toString(B.fromString("1e-40", 200), 3, { trim: true }), "1e-40");
});
test("bigfloat: nth roots, integer and rational powers", () => {
  const p = bits(30);
  eq(B.toString(B.nthRoot(B.fromInt(-8), 3, p), 30), "-2.00000000000000000000000000000");
  eq(B.toString(B.powRat(B.fromInt(8), 2, 3, p), 5), "4.0000");
  eq(B.toString(B.powRat(B.fromInt(-8), 1, 3, p), 5), "-2.0000");
  throws(() => B.powRat(B.fromInt(-8), 1, 2, p));
  eq(B.toString(B.powInt(B.fromInt(3), 100, 400), 48), "515377520732011331036461129765621272702107522001");
  throws(() => B.powInt(B.ZERO, 0, p));
});
test("bigfloat: domain errors throw code DOMAIN", () => {
  for (const f of [() => B.ln(B.ZERO), () => B.sqrt(B.fromInt(-1)), () => B.div(B.ONE, B.ZERO), () => B.asin(B.TWO), () => B.acosh(B.HALF), () => B.atanh(B.ONE)]) {
    try { f(); ok(false, "should throw"); } catch (e) { eq(e.code, "DOMAIN"); }
  }
});
test("bigfloat property: add/mul/div/sqrt are correctly rounded (vs exact rationals)", () => {
  const R = rng(101);
  const rnd = () => new B.BigFloat(BigInt(R.int(-1e9, 1e9)) * BigInt(R.int(1, 1e6)), R.int(-80, 40));
  for (let i = 0; i < 150; i++) {
    const a = rnd(), b = rnd(), prec = R.int(10, 120);
    const qa = B.toRational(a), qb = B.toRational(b);
    ok(B.eq(B.add(a, b, prec), B.fromRational(Q.add(qa, qb), prec)), "add");
    ok(B.eq(B.mul(a, b, prec), B.fromRational(Q.mul(qa, qb), prec)), "mul");
    if (b.m !== 0n) ok(B.eq(B.div(a, b, prec), B.fromRational(Q.div(qa, qb), prec)), "div");
    const aa = B.abs(a);
    if (aa.m !== 0n) {
      const r = B.sqrt(aa, prec);
      // |r^2 - a| must be within half an ulp of r times ~2r (rounding bracket)
      const ulp = new B.BigFloat(1n, r.e);
      const lo = B.toRational(B.sub(r, B.mulPow2(ulp, -1), Infinity)), hi = B.toRational(B.add(r, B.mulPow2(ulp, -1), Infinity));
      const qa2 = B.toRational(aa);
      ok(Q.cmp(Q.mul(lo, lo), qa2) <= 0 && Q.cmp(qa2, Q.mul(hi, hi)) <= 0, "sqrt within half ulp");
    }
  }
});
test("bigfloat property: exp(ln x) = x and sin^2 + cos^2 = 1 to 40 digits at random points", () => {
  const R = rng(202);
  const p = bits(40) + 16;
  for (let i = 0; i < 25; i++) {
    const x = B.fromString((R.next() * 200 - 100).toFixed(12), p);
    const ax = B.abs(x);
    if (ax.m !== 0n) eq(B.toString(B.exp(B.ln(ax, p), p), 40), B.toString(ax, 40), "exp(ln x)");
    const [s, c] = B.sincos(x, p);
    eq(B.toString(B.add(B.mul(s, s, p), B.mul(c, c, p), p), 40), B.toString(B.ONE, 40), "sin^2+cos^2");
  }
});
test("bigfloat property: inverse functions round-trip (atan/tan, asin/sin, acosh/cosh, nthRoot)", () => {
  const R = rng(303);
  const p = bits(35) + 16;
  for (let i = 0; i < 15; i++) {
    const x = B.fromString((R.next() * 2.8 - 1.4).toFixed(10), p);
    eq(B.toString(B.atan(B.tan(x, p), p), 30), B.toString(x, 30), "atan(tan x)");
    eq(B.toString(B.asin(B.sin(x, p), p), 30), B.toString(x, 30), "asin(sin x)");
    const y = B.fromString((1 + R.next() * 5).toFixed(10), p);
    eq(B.toString(B.acosh(B.cosh(y, p), p), 30), B.toString(y, 30), "acosh(cosh y)");
    eq(B.toString(B.powInt(B.nthRoot(y, 5, p), 5, p), 30), B.toString(y, 30), "root^5");
    const ch = B.cosh(y, p), sh = B.sinh(y, p);
    eq(B.toString(B.sub(B.mul(ch, ch, p), B.mul(sh, sh, p), p), 25), B.toString(B.ONE, 25), "cosh^2 - sinh^2");
  }
});
test("bigfloat complex: i^2 = -1 exactly, e^(i pi) = -1, sqrt(-4) = 2i, ln(-1) = i pi", () => {
  const p = bits(30);
  const i2 = B.cpow(B.CI, B.TWO, p);
  ok(B.eq(i2.re, B.fromInt(-1)) && i2.im.m === 0n, "i^2");
  const e = B.cexp(B.cmul(B.CI, B.pi(p + 16), p + 16), p);
  eq(B.toString(e.re, 30), "-1.00000000000000000000000000000");
  ok(B.top(e.im) < -90, "imaginary part tiny");
  eq(B.cToString(B.csqrt(B.fromInt(-4), p), 5), "2.0000i");
  const l = B.cln(B.fromInt(-1), p);
  ok(l.re.m === 0n);
  eq(B.toString(l.im, 30), roundStr(PI100, 30));
  eq(B.cToString(B.cdiv(new B.Complex(B.ONE, B.ONE), new B.Complex(B.ONE, B.fromInt(-1)), p), 5), "1.0000i");
});

// ============================ interval ============================
test("interval: nextUp / nextDown", () => {
  eq(IV.nextUp(1), 1 + Number.EPSILON);
  eq(IV.nextDown(1), 1 - Number.EPSILON / 2);
  eq(IV.nextUp(0), Number.MIN_VALUE);
  eq(IV.nextDown(-Number.MAX_VALUE), -Infinity);
});
test("interval: outward-rounded 0.1 + 0.2 contains the exact sum 3/10", () => {
  const a = IV.fromRational(Q.Q(1, 10)), b = IV.fromRational(Q.Q(2, 10));
  const s = IV.add(a, b);
  const exact = Q.Q(3, 10);
  ok(Q.cmp(B.toRational(B.fromNumber(s.lo)), exact) < 0 && Q.cmp(exact, B.toRational(B.fromNumber(s.hi))) < 0);
});
test("interval: division by an interval containing zero", () => {
  const r = IV.div(IV.I(1, 2), IV.I(-1, 1));
  ok(r.lo === -Infinity && r.hi === Infinity && !r.def && !r.cont);
  const parts = IV.divSplit(IV.I(1, 2), IV.I(-1, 1));
  eq(parts.length, 2);
  ok(parts[0].hi >= -1 && parts[0].hi < -0.99 && parts[1].lo <= 1 && parts[1].lo > 0.99, "outward-rounded halves");
  const half = IV.div(IV.I(1, 2), IV.I(0, 1));
  ok(half.lo <= 1 && half.hi === Infinity && !half.def);
  ok(IV.isEmpty(IV.div(IV.I(1), IV.I(0))));
});
test("interval: sin/cos extrema, tan pole, sqrt/ln domain flags, floor discontinuity", () => {
  const s = IV.sin(IV.I(1, 2));
  eq(s.hi, 1);
  const t = IV.tan(IV.I(1, 2));
  ok(!t.cont && !t.def);
  ok(IV.tan(IV.I(-1, 1)).cont);
  const q = IV.sqrt(IV.I(-1, 4));
  ok(!q.def && q.lo === 0 && q.hi >= 2);
  const l = IV.ln(IV.I(0, 1));
  ok(l.lo === -Infinity && !l.def);
  ok(!IV.floor(IV.I(0.5, 1.5)).cont && IV.floor(IV.I(0.2, 0.8)).cont);
  const p = IV.powInt(IV.I(-2, 1), 2);
  ok(p.lo === 0 && p.hi >= 4);
});
test("interval property: point values lie inside the interval enclosure", () => {
  const R = rng(404);
  const fns = [
    [IV.sin, Math.sin], [IV.cos, Math.cos], [IV.exp, Math.exp], [IV.atan, Math.atan], [IV.sinh, Math.sinh], [IV.cosh, Math.cosh],
    [IV.tanh, Math.tanh], [(a) => IV.powInt(a, 3), (x) => x ** 3], [(a) => IV.powInt(a, 2), (x) => x * x], [IV.abs, Math.abs],
    [(a) => IV.mul(a, a), (x) => x * x], [(a) => IV.sub(a, IV.I(0.3)), (x) => x - 0.3], [(a) => IV.div(IV.I(1), IV.add(a, IV.I(20))), (x) => 1 / (x + 20)],
  ];
  for (let i = 0; i < 300; i++) {
    const lo = R.next() * 20 - 10, hi = lo + R.next() * 3;
    const x = lo + R.next() * (hi - lo);
    const [fi, fd] = R.pick(fns);
    const r = fi(IV.I(lo, hi));
    const v = fd(x);
    ok(r.lo <= v && v <= r.hi, `value ${v} in [${r.lo}, ${r.hi}]`);
  }
});
test("interval: evalInterval over a tree and pole detection", () => {
  const r = Nm.evalInterval(P("x^2 - 2x"), { x: [0, 1] });
  ok(r.lo <= -1 && r.hi >= 0 && r.def && r.cont);
  const t = Nm.evalInterval(P("tan(x)"), { x: [1, 2] });
  ok(!t.cont);
  ok(!Nm.evalInterval(P("1/x"), { x: [-1, 1] }).cont);
});

// ============================ evaluation ============================
test("evalTree: values, env types and exact-constant functions", () => {
  eq(B.toString(Nm.evalTree(P("x^2 + y"), { x: "1.5", y: 2 }, { digits: 20 }), 20), "4.2500000000000000000");
  eq(B.toString(Nm.evalTree(P("log(2, 8) + floor(2.5) + ceil(2.5) + |x| + sign(x)"), { x: -3 }, { digits: 20 }), 10), "10.00000000");
  eq(B.toString(Nm.evalTree(parse("5! + gamma(4)"), {}, { digits: 20 }), 10), "126.0000000");
  eq(B.toString(Nm.evalTree(parse("sum(k^2, k, 1, 10) + prod(k, k, 1, 5)"), {}, { digits: 20 }), 10), "505.0000000");
  eq(B.toString(Nm.evalTree(parse("sec(0) + csc(pi/2) + cot(pi/4)"), {}, { digits: 30 }), 25), "3.000000000000000000000000");
});
test("evalTree: undefined points return an explicit UNDEFINED marker, never NaN", () => {
  ok(Nm.isUndefined(Nm.evalTree(P("1/(x-1)"), { x: 1 })));
  ok(Nm.isUndefined(Nm.evalTree(parse("ln(x)"), { x: -1 })));
  ok(Nm.isUndefined(Nm.evalTree(parse("sqrt(x)"), { x: -1 })));
  ok(Nm.isUndefined(Nm.evalTree(parse("asin(x)"), { x: 2 })));
  ok(Nm.isUndefined(Nm.evalTree(parse("x^0"), { x: 0 })), "0^0");
  ok(Nm.isUndefined(Nm.evalTree(parse("gamma(x)"), { x: -2 })));
  ok(typeof Nm.evalTree(parse("ln(x)"), { x: -1 }).reason === "string");
});
test("evalTree: complex values with I and in complex mode", () => {
  eq(B.cToString(Nm.evalTree(parse("(1+i)^2"), {}, { digits: 20 }), 5), "2.0000i");
  eq(B.cToString(Nm.evalTree(parse("sqrt(x)"), { x: -4 }, { mode: "complex" }), 5), "2.0000i");
});
test("evalTree: unbound symbols and huge finite sums throw", () => {
  throws(() => Nm.evalTree(P("x + y"), { x: 1 }));
  try { Nm.evalTree(parse("sum(k, k, 1, 10^9)"), {}); ok(false); } catch (e) { eq(e.code, "BUDGET"); }
});
test("compileDouble: fast closures, NaN only at undefined points, real odd roots", () => {
  const f = Nm.compileDouble(P("1/x + ln(x)"), ["x"]);
  eq(f(1), 1);
  ok(Number.isNaN(f(0)) && Number.isNaN(f(-1)));
  eq(Nm.compileDouble(P("x^(1/3)"), ["x"])(-8), -2);
  ok(Number.isNaN(Nm.compileDouble(P("sqrt(x)"), ["x"])(-1)));
  const g = Nm.compileDouble(P("sin(x)*cos(y) + x^2"), ["x", "y"]);
  close(g(0.3, 0.7), Math.sin(0.3) * Math.cos(0.7) + 0.09, 1e-15);
  const t0 = performance.now();
  let s = 0;
  for (let i = 0; i < 100000; i++) s += g(i * 1e-5, 0.5);
  ok(performance.now() - t0 < 500 && Number.isFinite(s), "fast");
});
test("compileDual: forward-mode AD derivative", () => {
  const d = Nm.compileDual(P("x^3 + sin(x) + e^(2x)"), "x");
  const [v, dv] = d(0.5);
  close(v, 0.125 + Math.sin(0.5) + Math.exp(1), 1e-14);
  close(dv, 0.75 + Math.cos(0.5) + 2 * Math.exp(1), 1e-14);
});

// ============================ N ============================
test("N: pi to 100 digits, sqrt(2) to 60, e to 50", () => {
  const r = Nm.N(P("pi"), 100);
  isRecord(r);
  eq(r.value, PI100);
  ok(r.converged && r.digits === 100 && r.requested === 100);
  eq(Nm.N(P("sqrt(2)"), 60).value, roundStr(SQRT2_100, 60));
  eq(Nm.N(P("e"), 50).value, roundStr(E100, 50));
});
test("N: gamma(1/3), erf(1), ln(10) and sums", () => {
  eq(Nm.N(parse("gamma(1/3)"), 30).value, "2.67893853470774763365569294097");
  eq(Nm.N(parse("ln(10)"), 30).value, "2.30258509299404568401799145468");
  eq(Nm.N(parse("sum(1/n^2, n, 1, oo)"), 25).value, roundStr(ZETA2_50, 25));
});
test("N: complex constant e^(i pi) = -1 with the imaginary part below the error bound", () => {
  const r = Nm.N(parse("e^(i*pi)"), 20);
  eq(r.value, "-1.0000000000000000000");
  ok(r.warnings.some((w) => /imaginary/.test(w)));
  eq(Nm.N(parse("(1+i)^2 / (3 - 4i)"), 10).value, "-0.3200000000 + 0.2400000000i");
});
test("N: honest about zero, undefined, cancellation and free symbols", () => {
  const z = Nm.N(parse("sin(pi)"), 20);
  isRecord(z);
  eq(z.value, "0");
  ok(!z.converged && z.digits === 0 && z.warnings.length);
  const u = Nm.N(parse("ln(-1)"), 20);
  eq(u.value, "undefined");
  const c = Nm.N(parse("(1 + 10^(-30)) - 1"), 20);
  eq(c.value, "1.0000000000000000000e-30");
  try { Nm.N(P("x + 1"), 10); ok(false); } catch (e) { eq(e.code, "NOT_CONSTANT"); }
});

// ============================ roots ============================
test("findRoots: Wallis x^3 - 2x - 5 to 50 digits, certified by exact rational sign change", () => {
  const res = Nm.findRoots(P("x^3 - 2x - 5"), "x", { digits: 50 });
  eq(res.roots.length, 1);
  const r = res.roots[0];
  isRecord(r, ["residual", "multiplicityHint", "certified"]);
  ok(r.converged && r.certified && r.digits === 50 && r.multiplicityHint === 1);
  ok(r.value.startsWith("2.09455148154232659148238654057930296385730610562"));
  const d = "0.0000000000000000000000000000000000000000000000001";
  const lo = Q.sub(Q.fromDecimal(r.value), Q.fromDecimal(d)), hi = Q.add(Q.fromDecimal(r.value), Q.fromDecimal(d));
  const f = (q) => Q.sub(Q.sub(Q.mul(Q.mul(q, q), q), Q.mul(Q.Q(2), q)), Q.Q(5));
  ok(Q.sign(f(lo)) < 0 && Q.sign(f(hi)) > 0, "exact sign change around the reported value");
  ok(/not searched/.test(res.caveat) && res.complete === false);
});
test("findRoots: cos(x) = x gives the Dottie number to 50 digits", () => {
  const res = Nm.findRoots(parse("cos(x) = x"), "x", { digits: 50 });
  eq(res.roots.length, 1);
  eq(res.roots[0].value, roundStr(DOTTIE, 50));
  ok(res.roots[0].certified);
});
test("findRoots: x e^x = 2 to 30 digits (Lambert W(2))", () => {
  const res = Nm.findRoots(parse("x e^x = 2"), "x", { digits: 30 });
  eq(res.roots.length, 1);
  eq(res.roots[0].value, "0.852605502013725491346472414695");
  // independent check: f(v +- 1e-30) has opposite signs in 200-bit arithmetic
  const f = (s) => Nm.evalTree(parse("x e^x - 2"), { x: s }, { digits: 60 });
  ok(B.sign(f("0.852605502013725491346472414694")) < 0 && B.sign(f("0.852605502013725491346472414696")) > 0);
});
test("findRoots: tan(x) on (1, 2) reports the pole at pi/2, not a root", () => {
  const res = Nm.findRoots(P("tan(x)"), "x", { lo: 1, hi: 2 });
  eq(res.roots.length, 0);
  eq(res.discontinuities.length, 1);
  eq(res.discontinuities[0].kind, "pole");
  ok(res.discontinuities[0].at.startsWith("1.570796326"));
});
test("findRoots: 1/x and 1/x^2 have no roots (poles reported)", () => {
  const a = Nm.findRoots(P("1/x"), "x", { lo: -1, hi: 1 });
  eq(a.roots.length, 0);
  ok(a.discontinuities.some((d) => d.kind === "pole" && d.at === "0"));
  const b = Nm.findRoots(P("1/x^2"), "x", { lo: -1, hi: 1 });
  eq(b.roots.length, 0);
  ok(b.discontinuities.some((d) => d.kind === "pole"));
});
test("findRoots: double root (x-1)^2 found without a sign change, multiplicity 2, not certified", () => {
  const res = Nm.findRoots(P("(x-1)^2"), "x", { digits: 30 });
  eq(res.roots.length, 1);
  const r = res.roots[0];
  eq(r.value, "1.00000000000000000000000000000");
  eq(r.multiplicityHint, 2);
  ok(!r.certified && r.warnings.some((w) => /Even-multiplicity/.test(w)));
  const r2 = Nm.findRoots(parse("x^2 - 0.6x + 0.09"), "x", { digits: 25 }).roots;
  eq(r2.length, 1);
  eq(r2[0].value, "0.3000000000000000000000000");
});
test("findRoots: (x-1)^2 + 1e-10 has no real root; x^2 + 1 has none", () => {
  eq(Nm.findRoots(parse("(x-1)^2 + 1/10000000000"), "x", {}).roots.length, 0);
  eq(Nm.findRoots(P("x^2 + 1"), "x", {}).roots.length, 0);
});
test("findRoots: close roots (x-1)(x-1.000001) are separated", () => {
  const res = Nm.findRoots(P("(x-1)(x-1.000001)"), "x", { digits: 20 });
  eq(res.roots.map((r) => r.value).join(" "), "1.0000000000000000000 1.0000010000000000000");
  ok(res.roots.every((r) => r.certified));
});
test("findRoots: triple and quadruple roots get multiplicity hints 3 and 4", () => {
  const a = Nm.findRoots(P("(x-1)^3"), "x", { digits: 25 }).roots;
  eq(a.length, 1);
  eq(a[0].multiplicityHint, 3);
  ok(a[0].certified);
  const b = Nm.findRoots(P("(x-2)^4"), "x", { digits: 20 }).roots;
  eq(b.length, 1);
  eq(b[0].value, "2.0000000000000000000");
  eq(b[0].multiplicityHint, 4);
});
test("findRoots: sin(x) on [-10, 10] finds 7 roots including 0 and +-pi", () => {
  const res = Nm.findRoots(P("sin(x)"), "x", { digits: 20 });
  eq(res.roots.length, 7);
  ok(res.roots.some((r) => r.value === "0"));
  ok(res.roots.some((r) => r.value === roundStr(PI100, 20)));
  ok(res.roots.some((r) => r.value === "-" + roundStr(PI100, 20)));
});
test("findRoots: domain boundaries (ln x root at 1, sqrt x root at the edge 0)", () => {
  const a = Nm.findRoots(P("ln(x)"), "x", { lo: -1, hi: 3, digits: 25 });
  eq(a.roots.length, 1);
  eq(a.roots[0].value, "1.000000000000000000000000");
  ok(a.discontinuities.some((d) => d.kind === "domain-boundary"));
  const b = Nm.findRoots(P("sqrt(x)"), "x", { lo: -1, hi: 1 });
  eq(b.roots.length, 1);
  eq(b.roots[0].value, "0");
});
test("findRoots: jump discontinuity of floor is not a root", () => {
  const res = Nm.findRoots(parse("floor(x) - 1/2"), "x", { lo: -3, hi: 3 });
  eq(res.roots.length, 0);
  ok(res.discontinuities.some((d) => d.kind === "jump" && d.at.startsWith("1.0")));
});
test("findRoots: poles and roots of tan on [-5, 5]", () => {
  const res = Nm.findRoots(P("tan(x)"), "x", { lo: -5, hi: 5, digits: 20 });
  eq(res.roots.length, 3);
  eq(res.discontinuities.filter((d) => d.kind === "pole").length, 4);
});
test("findRoots property: random integer-root polynomials, all roots found and certified", () => {
  const R = rng(505);
  for (let i = 0; i < 6; i++) {
    const roots = new Set();
    while (roots.size < R.int(2, 4)) roots.add(R.int(-8, 8));
    const rs = [...roots].sort((a, b) => a - b);
    const node = X.mul(...rs.map((r) => X.add(X.sym("x"), X.num(-r))));
    const res = Nm.findRoots(node, "x", { lo: -9.5, hi: 9.5, digits: 20 });
    eq(res.roots.length, rs.length, `roots of ${rs}`);
    res.roots.forEach((r, k) => {
      ok(Math.abs(Number(r.value) - rs[k]) < 1e-15, `root ${r.value} vs ${rs[k]}`);
      ok(r.certified && r.converged, "certified");
    });
  }
});
test("findRoots: invalid window throws", () => { throws(() => Nm.findRoots(P("x"), "x", { lo: 1, hi: 1 })); });

// ============================ scalar methods ============================
test("scalar root methods on x^2 - 2 return metadata records", () => {
  const s2 = Math.SQRT2;
  const rs = [
    Nm.bisection((x) => x * x - 2, 0, 2), Nm.brent(P("x^2 - 2"), 0, 2), Nm.newton(P("x^2 - 2"), 1),
    Nm.secant((x) => x * x - 2, 1, 2), Nm.safeguardedNewton(P("x^2 - 2"), 0, 2),
  ];
  for (const r of rs) {
    isRecord(r, ["x", "fx", "bracket", "fa", "fb"]);
    ok(r.converged, r.method);
    close(r.x, s2, 1e-15, r.method);
    ok(r.value.startsWith("1.41421356237"));
  }
  ok(rs[1].iterations < rs[0].iterations, "brent beats bisection");
  const bad = Nm.brent((x) => x * x + 1, 0, 2);
  ok(!bad.converged && bad.warnings.length);
});

// ============================ differentiation ============================
test("diffRichardson: d/dx sin at 1 with an error estimate", () => {
  const r = Nm.diffRichardson(P("sin(x)"), 1, { x: "x" });
  isRecord(r, ["x"]);
  close(r.x, Math.cos(1), 1e-12);
  ok(Number(r.errorBound) < 1e-10);
});
test("derivative: automatic differentiation to 40 digits and second derivatives", () => {
  eq(Nm.derivative(P("sin(x)"), "x", 1, { digits: 40 }).value, roundStr(COS1_100, 40));
  eq(Nm.derivative(P("x^3"), "x", 2, { digits: 20, order: 2 }).value, "12.000000000000000000");
  eq(Nm.derivative(P("e^(x^2)"), "x", 0, { digits: 10, order: 2 }).value, "2.000000000");
});

// ============================ integration ============================
test("integrate: x^2 on [0,1] = 1/3 and sin on [0, pi] = 2", () => {
  const a = Nm.integrate(P("x^2"), "x", 0, 1);
  isRecord(a);
  ok(a.converged);
  close(Number(a.value), 1 / 3, 1e-12);
  const b = Nm.integrate(P("sin(x)"), "x", 0, P("pi"));
  close(Number(b.value), 2, 1e-11);
  ok(b.converged && Number(b.errorBound) < 1e-10);
});
test("integrate: ln(x) on [0,1] = -1 (endpoint singularity)", () => {
  const r = Nm.integrate(P("ln(x)"), "x", 0, 1);
  ok(r.converged);
  close(Number(r.value), -1, 1e-11);
  close(Number(Nm.integrate(P("1/sqrt(x)"), "x", 0, 1).value), 2, 1e-10);
});
test("integrate: e^(-x^2) on [0, oo) = sqrt(pi)/2, also over the whole line", () => {
  const r = Nm.integrate(P("e^(-x^2)"), "x", 0, "oo");
  ok(r.converged);
  close(Number(r.value), Math.sqrt(Math.PI) / 2, 1e-12);
  close(Number(Nm.integrate(P("e^(-x^2)"), "x", "-oo", "oo").value), Math.sqrt(Math.PI), 1e-11);
  close(Number(Nm.integrate(parse("1/(1+x^2)"), "x", X.mul(X.NEG_ONE, X.OO), X.OO).value), Math.PI, 1e-11);
});
test("integrate: sqrt(x) on [0,1] to 30 digits (multiprecision tanh-sinh)", () => {
  const r = Nm.integrate(P("sqrt(x)"), "x", 0, 1, { digits: 30 });
  isRecord(r);
  ok(r.converged && r.digits === 30);
  eq(r.value, "0.666666666666666666666666666667");
});
test("integrate: e^(-x^2) on [0, oo) to 30 digits", () => {
  const r = Nm.integrate(P("e^(-x^2)"), "x", 0, "oo", { digits: 30 });
  ok(r.converged);
  eq(r.value, Nm.N(P("sqrt(pi)/2"), 30).value);
});
test("integrate: divergent 1/x on [0,1] is reported, not given a number", () => {
  const r = Nm.integrate(P("1/x"), "x", 0, 1);
  eq(r.value, "undefined");
  ok(!r.converged && r.warnings.some((w) => /diverge/.test(w)));
  const s = Nm.integrate(parse("1/(x-3/10)^2"), "x", 0, 1);
  ok(!s.converged && s.value === "undefined");
});
test("integrate: removable point sin(x)/x, reversed bounds", () => {
  const r = Nm.integrate(parse("sin(x)/x"), "x", -1, 1);
  close(Number(r.value), 1.8921661407343662, 1e-11);
  ok(r.warnings.some((w) => /removable/.test(w)));
  close(Number(Nm.integrate(P("x"), "x", 1, 0).value), -0.5, 1e-12);
});

// ============================ optimization ============================
test("minimization: (x-2)^2 + 1 by Brent, golden section and AD-polished to 30 digits", () => {
  const r = Nm.brentMin(P("(x-2)^2 + 1"), 0, 5);
  isRecord(r, ["x", "fx"]);
  close(r.x, 2, 1e-7);
  close(r.fx, 1, 1e-12);
  close(Nm.goldenSection((x) => (x - 2) ** 2 + 1, 0, 5).x, 2, 1e-7);
  const h = Nm.minimize(P("(x-2)^2 + 1"), 0, 5, { digits: 30 });
  eq(h.value, "2.00000000000000000000000000000");
  eq(h.fValue, "1.00000000000000000000000000000");
  const c = Nm.minimize(P("cos(x)"), 2, 4, { digits: 25 });
  eq(c.value, roundStr(PI100, 25));
});
test("nelderMead: 2-D quadratic and Rosenbrock", () => {
  const r = Nm.nelderMead(P("(x-1)^2 + (y+2)^2 + 3"), [0, 0]);
  isRecord(r, ["point", "fx"]);
  close(r.point[0], 1, 1e-5);
  close(r.point[1], -2, 1e-5);
  const ro = Nm.nelderMead((p) => 100 * (p[1] - p[0] ** 2) ** 2 + (1 - p[0]) ** 2, [-1.2, 1]);
  close(ro.point[0], 1, 1e-4);
  close(ro.point[1], 1, 1e-4);
});
test("localExtrema: x^3 - 3x has a max at -1 and a min at 1", () => {
  const r = Nm.localExtrema(P("x^3 - 3x"), "x", { lo: -3, hi: 3, digits: 20 });
  eq(r.extrema.map((e) => `${e.kind}@${e.x.value}=${e.fx}`).join(" "), "max@-1.0000000000000000000=2.0000000000000000000 min@1.0000000000000000000=-2.0000000000000000000");
});

// ============================ ODE ============================
test("solveODE: y' = y from 0 to 1 gives e", () => {
  const r = Nm.solveODE([P("y")], "t", ["y"], 0, [1], 1, { samples: 11 });
  ok(r.converged);
  close(r.y[r.y.length - 1][0], Math.E, 1e-9);
  isRecord(r.final[0]);
  close(Number(r.final[0].value), Math.E, 1e-8);
  eq(r.t.length, 11);
  close(r.y[5][0], Math.exp(0.5), 1e-7, "dense output");
});
test("solveODE: harmonic oscillator returns after 2 pi; blow-up of y' = y^2 is reported", () => {
  const r = Nm.solveODE([P("v"), P("-x")], "t", ["x", "v"], 0, [1, 0], 2 * Math.PI);
  close(r.y[r.y.length - 1][0], 1, 1e-8);
  const b = Nm.solveODE([P("y^2")], "t", ["y"], 0, [1], 2, { maxSteps: 5000 });
  ok(!b.converged && b.warnings.length > 0);
  ok(b.tEnd < 1.0001 && b.tEnd > 0.99);
});

// ============================ linear algebra ============================
test("linear: LU solve, singular detection, determinant, condition number", () => {
  const s = Nm.solveLinear([[2, 1], [1, 3]], [3, 5]);
  close(s.x[0], 0.8, 1e-14);
  close(s.x[1], 1.4, 1e-14);
  ok(Nm.solveLinear([[1, 2], [2, 4]], [3, 5]).singular);
  close(Nm.det([[1, 2, 3], [4, 5, 6], [7, 8, 10]]), -3, 1e-12);
  const H = Array.from({ length: 8 }, (_, i) => Array.from({ length: 8 }, (_, j) => 1 / (i + j + 1)));
  ok(Nm.conditionNumber(H) > 1e9);
  ok(Nm.solveLinear(H, H.map(() => 1)).warnings.length > 0 || Nm.conditionNumber(H) < 1e12);
});

// ============================ series ============================
test("sumInfinite: zeta(2) = pi^2/6 to 30 digits; alternating harmonic = ln 2", () => {
  const r = Nm.sumInfinite(parse("1/n^2"), "n", 1, { digits: 30 });
  isRecord(r);
  ok(r.converged);
  eq(r.value, roundStr(ZETA2_50, 30));
  eq(Nm.sumInfinite(parse("(-1)^(n+1)/n"), "n", 1, { digits: 25 }).value, roundStr(LN2_100, 25));
  eq(Nm.sumInfinite(parse("1/n!"), "n", 0, { digits: 25 }).value, roundStr(E100, 25));
});
test("sumInfinite: the harmonic series is flagged as divergent", () => {
  const r = Nm.sumInfinite(parse("1/n"), "n", 1, { digits: 15 });
  ok(!r.converged && r.warnings.some((w) => /divergent/.test(w)));
});
test("fmtErr rounds up to one significant digit", () => {
  eq(Nm.fmtErr(1.2e-21), "2e-21");
  eq(Nm.fmtErr(9.5e-3), "1e-2");
  eq(Nm.fmtErr(3e-5), "3e-5");
  eq(Nm.fmtErr(0), "0");
});
