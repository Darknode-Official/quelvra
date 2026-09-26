// Regressions found by the differential fuzzer (tools/quelvra-fuzz.mjs). Each test names the root
// cause that was fixed, not only the example that exposed it.
import { test, eq, ok, close } from "./harness.js";
import { solve } from "../public/engine/quelvra.js";
import { parse } from "../public/engine/parse.js";
import { toText } from "../public/engine/print.js";
import { evalC } from "../public/engine/verify.js";

const S = (q) => solve(q, { timeLimit: 10000 });
const verified = (r) => r.ok && r.verification.status === "passed";
const vals = (r) => r.answers.filter((a) => a.tree && (a.kind === "exact")).map((a) => evalC(a.tree, {}, "real").re).sort((a, b) => a - b);
const roots = (q, want) => {
  const r = S(q);
  ok(verified(r), `${q} should be verified`);
  const got = vals(r);
  eq(got.length, want.length, `${q} root count (${got})`);
  want.forEach((w, i) => close(got[i], w, 1e-9, q));
};

// parse.js: "int (" opened an integrate(...) call, so "int (2x+1)/(x+2)^2 dx" became
// integrate(2x+1)/(x+2)^2 * d * x and was "verified" as its own simplification.
test("fuzz regress: int (f)/(g) dx integrates the whole quotient", () => {
  for (const [src, want] of [["int (2*x + 1)/(x^2 + 4*x + 4) dx", "integrate((2x + 1)/(x^2 + 4x + 4), x)"], ["int (x+1)(x-1) dx", "integrate((x + 1)(x - 1), x)"], ["int (x) d x", "integrate(x, x)"]]) eq(toText(parse(src)), want, src);
  eq(toText(parse("int(x^2, x)")), "integrate(x^2, x)");
  eq(toText(parse("int(x^2) + 1")), "integrate(x^2, x) + 1");
  eq(toText(parse("int (x) dx + int (x^2) dx")), "integrate(x, x) + integrate(x^2, x)");
  const r = S("int (2*x + 1)/(x^2 + 4*x + 4) dx");
  ok(verified(r) && r.classification.kind === "integral", "an integral");
  ok(!/\bd\b|integrate/.test(toText(r.answers[0].tree)), toText(r.answers[0].tree));
});

// print.js: a factor printing with a leading minus inside an unsimplified product lost its
// brackets (|3|*(-2z) printed "|3|-2z"), and negateCoeff assumed the coefficient came first.
test("fuzz regress: toText of raw products stays re-parseable", () => {
  for (const src of ["|3|*(-2z)", "z*(-4) - pi^2", "(x + 1)*(-2/x)*x", "3 - 2*x*(-1/2)*y", "2*(-3x)"]) {
    const a = parse(src), b = parse(toText(a));
    for (const p of [0.37, 1.7, -2.3]) {
      const env = { x: p, y: 0.61, z: p };
      close(evalC(b, env, "real").re, evalC(a, env, "real").re, 1e-12, `${src} -> ${toText(a)}`);
    }
  }
});

// numeric.js: an unsimplified rational exponent ((x+6)^(1/3) parses as 1 * 3^-1) was evaluated as a
// complex principal power, so the real cube root x = -7 was rejected as "undefined" and
// "No real solution" was verified.
test("fuzz regress: odd roots of negatives written as ^(p/q) keep their real solutions", () => {
  roots("(x + 6)^(1/3) = -1", [-7]);
  roots("x^(1/3) = -2", [-8]);
  roots("(x - 3)^(3/5) = -1", [2]);
  roots("x^(2/3) = 4", [-8, 8]);
  const r = S("x^(1/2) = -2");
  ok(verified(r) && r.noSolution, "an even root stays non-negative");
});

// parse.js: the body of d/dx and lim without brackets ran only to the next + or -, so
// "d/dx x^2 + 1" was d/dx(x^2) + 1 and the echo was "verified" as a simplification.
test("fuzz regress: d/dx and lim bodies take the whole sum; unevaluated operators are never echoed", () => {
  const d = S("d/dx x^2 + 1");
  ok(verified(d) && toText(d.answers[0].tree) === "2x", toText(d.answers[0].tree || { k: "none" }));
  const l = S("lim x->1 x^2 + 1");
  ok(verified(l) && toText(l.answers[0].tree) === "2", "limit of the whole sum");
  eq(toText(parse("d/dx x^2 + d/dx x^3")), "d/dx (x^2) + d/dx (x^3)");
  for (const q of ["d/dx (x^2) + 1", "d/dx x^2 + d/dx x^3"]) {
    const r = S(q);
    ok(!verified(r) || !/d\/d|lim|integrate/.test(r.answers.map((a) => a.tree ? toText(a.tree) : "").join(" ")), `${q} must not echo an unevaluated operator`);
  }
});

// basic.js: an operator embedded in a larger expression is now solved and verified on its own and
// substituted; parse.js: a bracket ends the body only when the body is exactly that bracket group.
test("fuzz regress: embedded operators are evaluated; bracket-initial bodies", () => {
  const want = { "d/dx (x^2) + 1": "2x + 1", "d/dx x^2 + d/dx x^3": "3x^2 + 2x", "lim x->1 (x^2) + 1": "2", "int_0^1 x dx + int_0^2 x dx": "5/2", "sum_(k=1)^(10) k + 5": "60", "d/dx (-4+x)/(-3)-(pi+x+pi)": "-4/3" };
  for (const [q, w] of Object.entries(want)) {
    const r = S(q);
    ok(verified(r), `${q} verified`);
    eq(toText(r.answers[0].tree), w, q);
  }
  ok(!verified(S("int x dx + 1")), "an indefinite integral inside a sum is declined (+C)");
});

// simplify.js: a^(c log_a y) and a^(c ln y / ln a) did not reduce to y^c, so the exact sign test at
// the critical point of 2^t >= 9 could not decide and the answer fell back to "numeric cross-check only".
test("fuzz regress: a^(log_a y) = y and exponential inequalities verify exactly", () => {
  for (const [q, w] of [["simplify 2^(log_2(9))", "9"], ["simplify 2^(2ln(3)/ln(2))", "9"], ["simplify 3^(ln(5)/ln(3) + 1)", "15"]]) eq(toText(S(q).answers[0].tree), w, q);
  for (const [q, lo, hi] of [["2^t >= 9", Math.log2(9), Infinity], ["2^x < 5", -Infinity, Math.log2(5)], ["(1/2)^t > 3", -Infinity, -Math.log2(3)]]) {
    const r = S(q);
    ok(verified(r) && r.answers[0].kind === "set", q);
    const iv = r.answers[0].interval[0];
    eq(iv.lo === null ? "-Infinity" : evalC(iv.lo, {}, "real").re.toPrecision(12), lo.toPrecision(12), q);
    eq(iv.hi === null ? "Infinity" : evalC(iv.hi, {}, "real").re.toPrecision(12), hi.toPrecision(12), q);
  }
});

// solve/equation.js: an identity (sqrt(x+5) - sqrt(x+5) = 0) was answered "every real x", which
// failed verification (undefined for x < -5) and so was refused; it now holds on the real domain.
test("fuzz regress: identities hold exactly on the real domain of the original", () => {
  for (const [q, lo, loOpen] of [["sqrt(x + 5) - sqrt(x + 5) = 0", -5, false], ["ln(x) - ln(x) = 0", 0, true], ["sqrt(x)/sqrt(x) = 1", 0, true], ["ln(x^2) = 2ln(x)", 0, true]]) {
    const r = S(q);
    ok(verified(r) && r.answers[0].kind === "set", q);
    const iv = r.answers[0].interval;
    eq(iv.length, 1, q);
    eq(iv[0].hi, null, q);
    eq(evalC(iv[0].lo, {}, "real").re, lo, q);
    eq(iv[0].loOpen, loOpen, q);
  }
  const r = S("1/x - 1/x = 0");
  ok(verified(r) && r.answers[0].kind === "all", "denominator-only identities keep the 'except' form");
});
