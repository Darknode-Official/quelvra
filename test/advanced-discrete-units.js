// Unit tests for the advanced discrete checkers: helper algorithms cross-checked against brute
// force, the verification gate (no checks / a failing check means the answer is withheld), and
// honest refusals.
import { test, ok, eq, throws } from "./harness.js";
import { parse } from "../public/engine/parse.js";
import { solve } from "../public/engine/quelvra.js";
import { toText } from "../public/engine/print.js";
import * as N from "../public/engine/num.js";
import { HANDLERS, runDiscrete } from "../public/engine/strategies/advanced-discrete.js";
import { berlekampMassey, seriesDiv, evalQuad } from "../public/engine/discrete/sequences.js";
import { millerRabin, evalR } from "../public/engine/discrete/proof.js";
import { isPrimeSmall, powMod, powModRL, modInv } from "../public/engine/discrete/util.js";
import * as G from "../public/engine/discrete/gfpoly.js";
import { lpSolve } from "../public/engine/discrete/lp.js";
import { formulaOf, evalRec, evalBits, varsOf } from "../public/engine/discrete/logic.js";

const Q = (n, d = 1n) => N.Q(BigInt(n), BigInt(d));
const run = (src) => { const node = parse(src); return runDiscrete(node.name, node, {}); };
const answered = (s) => { const r = solve(s, { timeLimit: 20000 }); return r.ok && (r.answers || []).some((a) => a.kind !== "none"); };
const label = (r, l) => { const a = (r.answers || []).find((x) => x.label === l); return a ? (a.text != null ? a.text : toText(a.tree)) : null; };

// ---------------------------------------------------------------- verification gate
test("adv units: a handler with no checks is withheld", () => {
  HANDLERS.__nochecks = () => ({ answers: [{ kind: "exact", label: "x", text: "1" }], checks: () => [] });
  try { eq(runDiscrete("__nochecks", { args: [] }, {}).verify().status, "failed"); } finally { delete HANDLERS.__nochecks; }
});
test("adv units: one failing check fails verification", () => {
  HANDLERS.__bad = () => ({ answers: [{ kind: "exact", label: "x", text: "1" }], checks: () => [{ kind: "a", ok: true }, { kind: "b", ok: false }] });
  try { eq(runDiscrete("__bad", { args: [] }, {}).verify().status, "failed"); } finally { delete HANDLERS.__bad; }
});
test("adv units: a throwing check fails verification", () => {
  HANDLERS.__throw = () => ({ answers: [{ kind: "exact", label: "x", text: "1" }], checks: () => { throw new Error("boom"); } });
  try { eq(runDiscrete("__throw", { args: [] }, {}).verify().status, "failed"); } finally { delete HANDLERS.__throw; }
});

// ---------------------------------------------------------------- helper algorithms vs brute force
test("adv units: Berlekamp-Massey finds Fibonacci and (1-x)^-3 recurrences", () => {
  const fib = [0n, 1n]; for (let i = 2; i < 20; i++) fib.push(fib[i - 1] + fib[i - 2]);
  const r = berlekampMassey(fib.map((v) => Q(v)));
  eq(r.L, 2); ok(N.eq(r.c[0], Q(1)) && N.eq(r.c[1], Q(1)));
  const sq = Array.from({ length: 12 }, (_, n) => Q(n * n));
  eq(berlekampMassey(sq).L, 3);
});
test("adv units: series division matches binomial coefficients", () => {
  // 1/(1-x)^3 -> C(k+2, 2)
  const s = seriesDiv([Q(1)], [Q(1), Q(-3), Q(3), Q(-1)], 30);
  for (let k = 0; k < 30; k++) ok(N.eq(s[k], Q((k + 1) * (k + 2) / 2)), `k=${k}`);
});
test("adv units: exact evaluation in Q(sqrt 5) gives Fibonacci numbers", () => {
  const t = parse("((1+sqrt(5))/2)^n/sqrt(5) - ((1-sqrt(5))/2)^n/sqrt(5)");
  const fib = [0n, 1n]; for (let i = 2; i < 25; i++) fib.push(fib[i - 1] + fib[i - 2]);
  for (let n = 0; n < 25; n++) { const v = evalQuad(t, { n: Q(n) }); ok(N.isZero(v.b) && N.eq(v.a, Q(fib[n])), `n=${n}`); }
});
test("adv units: Miller-Rabin agrees with trial division below 20000", () => {
  for (let n = 0n; n < 20000n; n++) ok(millerRabin(n) === isPrimeSmall(n), `n=${n}`);
});
test("adv units: modular power routes agree; inverses are inverses", () => {
  for (let m = 2n; m < 60n; m++) for (let b = 0n; b < m; b++) {
    eq(powMod(b, 37n, m), powModRL(b, 37n, m));
    const i = modInv(b, m);
    if (i !== null) eq(b * i % m, 1n % m);
  }
});
test("adv units: Rabin irreducibility agrees with brute force over GF(2) and GF(3), degree <= 4", () => {
  for (const p of [2n, 3n]) {
    const monics = (d) => { const out = []; const P = Number(p); for (let c = 0; c < P ** d; c++) { const a = []; let t = c; for (let i = 0; i < d; i++) { a.push(BigInt(t % P)); t = Math.floor(t / P); } a.push(1n); out.push(a); } return out; };
    for (let d = 1; d <= 4; d++) for (const f of monics(d)) {
      let red = false;
      for (let e = 1; e <= Math.floor(d / 2) && !red; e++) for (const g of monics(e)) if (!G.rem(f, g, p).length) { red = true; break; }
      eq(G.rabin(f, p), !red, `f=${f} p=${p}`);
    }
  }
});
test("adv units: exact simplex matches grid search on a small LP", () => {
  // maximise 3x + 2y, x + y <= 4, x + 3y <= 6, x, y >= 0  (optimum 12 at (4, 0))
  const r = lpSolve([Q(3), Q(2)], [[Q(1), Q(1)], [Q(1), Q(3)], [Q(-1), Q(0)], [Q(0), Q(-1)]], ["<=", "<=", "<=", "<="], [Q(4), Q(6), Q(0), Q(0)]);
  eq(r.status, "optimal");
  let best = -Infinity;
  for (let x = 0; x <= 4; x += 0.25) for (let y = 0; y <= 4; y += 0.25) if (x + y <= 4 && x + 3 * y <= 6) best = Math.max(best, 3 * x + 2 * y);
  eq(N.toFloat(r.value), best);
});
test("adv units: bit-parallel truth tables agree with the recursive evaluator", () => {
  const f = formulaOf(parse("LIFF(LIMP(p, q), LOR(LNOT(p), LXOR(q, r)))"));
  const vars = [...varsOf(f)].sort();
  const bits = evalBits(f, vars);
  for (let r = 0; r < 8; r++) {
    const env = Object.fromEntries(vars.map((v, j) => [v, !!((r >> (vars.length - 1 - j)) & 1)]));
    eq(!!((bits >> BigInt(r)) & 1n), evalRec(f, env), `row ${r}`);
  }
});
test("adv units: proof evaluator handles factorials and powers exactly", () => {
  ok(N.eq(evalR(parse("n! - 2^n"), { n: Q(10) }), Q(3628800 - 1024)));
});

// ---------------------------------------------------------------- handler outputs and their checks
test("adv units: rsolve closed form verified by iteration", () => {
  const r = run("rsolve(a(n) = 5a(n-1) - 6a(n-2), a(0) = 1, a(1) = 4)");
  eq(r.verify().status, "passed");
});
test("adv units: genfunc and seriescoeff certify", () => {
  const g = run("genfunc(n^2, n)");
  eq(g.verify().status, "passed");
  const c = run("seriescoeff(1/(1-x-x^2), x, 10)");
  eq(label(c, "coefficient"), "89"); eq(c.verify().status, "passed");
});
test("adv units: findsequence is labelled as evidence", () => {
  const r = run("findsequence(2, 6, 18, 54, 162)");
  eq(r.solutionStatus, "evidence"); eq(label(r, "next term"), "486"); eq(r.verify().status, "passed");
});
test("adv units: divisibility proof and counterexample", () => {
  const a = run("provedivisible(n^3 - n, n, 6)");
  eq(label(a, "status"), "proved"); eq(a.verify().status, "passed");
  const b = run("provedivisible(n^2 + 1, n, 5)");
  eq(label(b, "status"), "disproved"); eq(b.verify().status, "passed");
});
test("adv units: bounded search is evidence, never proved", () => {
  const r = run("provebound(2^n > n^2, n, 5)");
  eq(label(r, "status"), "no counterexample found"); eq(r.solutionStatus, "evidence");
});
test("adv units: Euler's polynomial fails at n = 40 with a factor certificate", () => {
  const r = run("provealwaysprime(n^2 + n + 41, n, 0)");
  eq(label(r, "counterexample"), "n = 40"); eq(r.verify().status, "passed");
});

// ---------------------------------------------------------------- refusals (never guess)
test("adv units: refusals", () => {
  for (const s of [
    "findsequence(1, 3)",
    "genfunc(n!, n)",
    "modinverse(6, 9)",
    "prove that there are infinitely many primes",
    "prove that sqrt(2) is irrational",
    "rsakeys(61, 53, 6)",
  ]) ok(!answered(s), `should refuse: ${s}`);
});
test("adv units: a sequence with too few spare terms is refused", () => {
  throws(() => run("findsequence(1, 2, 4, 8, 16, 31)"));
});
