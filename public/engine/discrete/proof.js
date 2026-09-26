// Proof-style requests. Quelvra never writes a free-form proof: it only answers "proved" when the
// statement is settled by a mechanical argument that is itself checked, "disproved" with a checked
// counterexample, or "no counterexample found" (solutionStatus "evidence") after a bounded search.
//
//   provedivisible(E, n, m)          m | E(n) for every integer n  (E has integer coefficients)
//                                    proof: E(n) mod m depends only on n mod m; all m residues checked
//   proveidentity(L, R)              rational-function identity: numerator of L - R expands to 0
//                                    check: L and R evaluated directly on a grid large enough for the
//                                    degree (a polynomial of degree <= D in each variable that vanishes
//                                    on a (D+1)^k grid is zero)
//   provesum(term, k, n, F, lo)      sum_{k=lo}^{n} term = F(n) for all n >= lo (polynomial term and F)
//   provesum(term, k, n, F, [t..])   ... with lo found from the listed first terms (1 + 2 + ... + n)
//                                    proof: induction (base case, F(n) - F(n-1) = term(n) expanded)
//                                    check: brute-force sums at D + 1 values of n (both sides are
//                                    polynomials of degree <= D)
//   provebound(rel, n, a)            rel(n) for all integers n >= a: bounded search only (evidence)
//   provealwaysprime(E, n, a)        E(n) prime for all n >= a: bounded search; composites are
//                                    certified by an explicit factor
//   provefinite(rel, x, [values])    rel(x) for every listed x: proved by exhaustion
//   proveequiv(f, g)                 propositional equivalence by the full truth table
//   proofrequest(...)                general theorems: refused with the reason

import { refuse, ansText, check, step, N, X, isPrimeSmall } from "./util.js";
import { intOf, intPolyOf, polyOf, labelOf, listOf, ratOf } from "./decode.js";
import { simplify } from "../simplify.js";
import { toText } from "../print.js";
import { LOGIC_HANDLERS } from "./logic.js";

const Z = N.ZERO, ONE = N.ONE;
const qs = (r) => N.toString(r);

// ---------------------------------------------------------------- exact evaluation (route 1)
function evalR(u, env) {
  switch (u.k) {
    case "num": return u.v;
    case "sym": if (u.name in env) return env[u.name]; throw refuse(`unbound variable ${u.name}`);
    case "add": return u.args.reduce((s, a) => N.add(s, evalR(a, env)), Z);
    case "mul": return u.args.reduce((s, a) => N.mul(s, evalR(a, env)), ONE);
    case "pow": {
      const b = evalR(u.args[0], env), e = evalR(u.args[1], env);
      if (e.d !== 1n) throw refuse("fractional powers are not supported here");
      if (e.n > 100000n || e.n < -100000n) throw refuse("power too large");
      if (e.n < 0n && N.isZero(b)) throw refuse("division by zero");
      return N.pow(b, Number(e.n));
    }
    case "fn": {
      const a = u.args.map((x) => evalR(x, env));
      if (u.name === "factorial" && a.length === 1) { if (a[0].d !== 1n || a[0].n < 0n || a[0].n > 5000n) throw refuse("factorial needs a small non-negative integer"); return N.Q(N.factorial(a[0].n)); }
      if (u.name === "abs" && a.length === 1) return N.abs(a[0]);
      throw refuse(`function ${u.name} is not supported here`);
    }
    default: throw refuse("unsupported expression");
  }
}
// route 2: the general simplifier
function evalS(u, env) {
  const m = {};
  for (const [k, v] of Object.entries(env)) m[k] = X.num(v);
  const s = simplify(X.subs(u, m));
  if (!s || s.k !== "num") throw refuse("the expression does not evaluate to a rational number");
  return s.v;
}
const REL = { ">": (c) => c > 0, "<": (c) => c < 0, ">=": (c) => c >= 0, "<=": (c) => c <= 0, "!=": (c) => c !== 0, "=": (c) => c === 0 };
function relOf(u) {
  if (u.k === "eq") return { op: "=", l: u.args[0], r: u.args[1] };
  if (u.k === "rel" && REL[u.op]) return { op: u.op, l: u.args[0], r: u.args[1] };
  throw refuse("expected a comparison such as 2^n > n^2");
}
const holds = (rel, ev, env) => REL[rel.op](N.cmp(ev(rel.l, env), ev(rel.r, env)));
const relText = (rel) => `${toText(rel.l)} ${rel.op} ${toText(rel.r)}`;
const symName = (u, what) => { if (u.k !== "sym") throw refuse(`expected ${what}`); return u.name; };

// ---------------------------------------------------------------- multivariate rational functions
// polynomial: Map(monomial key "x^2*y" -> Rational); key "" = constant
const mkey = (m) => Object.keys(m).sort().filter((v) => m[v]).map((v) => (m[v] === 1 ? v : `${v}^${m[v]}`)).join("*");
const parseKey = (k) => { const m = {}; if (k) for (const f of k.split("*")) { const [v, e] = f.split("^"); m[v] = e ? Number(e) : 1; } return m; };
function mpClean(p) { for (const [k, v] of p) if (N.isZero(v)) p.delete(k); return p; }
function mpAdd(a, b, s = ONE) { const r = new Map(a); for (const [k, v] of b) r.set(k, N.add(r.get(k) || Z, N.mul(s, v))); return mpClean(r); }
function mpMul(a, b) {
  const r = new Map();
  for (const [ka, va] of a) for (const [kb, vb] of b) {
    const ma = parseKey(ka), mb = parseKey(kb);
    for (const [v, e] of Object.entries(mb)) ma[v] = (ma[v] || 0) + e;
    const k = mkey(ma);
    r.set(k, N.add(r.get(k) || Z, N.mul(va, vb)));
    if (r.size > 20000) throw refuse("the expansion is too large");
  }
  return mpClean(r);
}
const mpConst = (c) => mpClean(new Map([["", c]]));
function ratMP(u) {
  switch (u.k) {
    case "num": return { P: mpConst(u.v), Q: mpConst(ONE) };
    case "sym": return { P: new Map([[u.name, ONE]]), Q: mpConst(ONE) };
    case "add": return u.args.map(ratMP).reduce((s, t) => ({ P: mpAdd(mpMul(s.P, t.Q), mpMul(t.P, s.Q)), Q: mpMul(s.Q, t.Q) }));
    case "mul": return u.args.map(ratMP).reduce((s, t) => ({ P: mpMul(s.P, t.P), Q: mpMul(s.Q, t.Q) }));
    case "pow": {
      const e = ratOf(u.args[1]);
      if (!e || e.d !== 1n || e.n > 64n || e.n < -64n) throw refuse("only small integer powers are supported in an identity");
      const b = ratMP(u.args[0]);
      let P = mpConst(ONE), Qm = mpConst(ONE);
      for (let i = 0n; i < (e.n < 0n ? -e.n : e.n); i++) { P = mpMul(P, b.P); Qm = mpMul(Qm, b.Q); }
      if (e.n < 0n) { if (!P.size) throw refuse("division by zero"); return { P: Qm, Q: P }; }
      return { P, Q: Qm };
    }
    default: throw refuse("identities are checked for polynomial and rational expressions only");
  }
}
export function isRationalExpr(u) { try { ratMP(u); return true; } catch (_) { return false; } }
// independent per-variable degree bound [numerator, denominator] from the tree shape
function degBound(u, x) {
  switch (u.k) {
    case "num": return [0, 0];
    case "sym": return [u.name === x ? 1 : 0, 0];
    case "add": return u.args.map((a) => degBound(a, x)).reduce(([n1, d1], [n2, d2]) => [Math.max(n1 + d2, n2 + d1), d1 + d2]);
    case "mul": return u.args.map((a) => degBound(a, x)).reduce(([n1, d1], [n2, d2]) => [n1 + n2, d1 + d2]);
    case "pow": { const e = Number(ratOf(u.args[1]).n); const [n, d] = degBound(u.args[0], x); return e >= 0 ? [e * n, e * d] : [-e * d, -e * n]; }
    default: throw refuse("unsupported");
  }
}

// ---------------------------------------------------------------- answers
const statusAns = (s) => ansText("status", s);
const pointText = (env) => Object.entries(env).map(([k, v]) => `${k} = ${qs(v)}`).join(", ");

// ---------------------------------------------------------------- provedivisible
function cmdDivisible(args) {
  if (args.length !== 3) throw refuse("use provedivisible(expression, n, m)");
  const n = symName(args[1], "the variable");
  const m = intOf(args[2], "a positive integer divisor");
  if (m < 1n || m > 1000000n) throw refuse("the divisor must be between 1 and 10^6");
  const cs = intPolyOf(args[0], n);
  const horner = (r) => cs.reduceRight((s, c) => ((s * r + c) % m + m) % m, 0n);
  let bad = -1n;
  for (let r = 1n; r <= m && bad < 0n; r++) if (horner(r % m) !== 0n) bad = r; // residues 1..m (m = class 0)
  const E = toText(args[0]);
  if (bad < 0n) {
    return {
      answers: [statusAns("proved")], solutionStatus: "exact",
      steps: [step("proof.residues", "Reduce modulo " + m, `${E} has integer coefficients, so its value mod ${m} depends only on ${n} mod ${m}.`),
        step("proof.cases", `Check all ${m} residues`, `${E} ≡ 0 (mod ${m}) for ${n} ≡ 0, 1, ..., ${m - 1n} (mod ${m}), so ${m} divides ${E} for every integer ${n}.`)],
      checks: () => {
        // route 2: evaluate the original expression exactly at every residue and at a shifted
        // representative; each value must be a multiple of m
        for (let r = 0n; r < m; r++) for (const t of [r, r + m, r - 7n * m]) {
          const v = evalR(args[0], { [n]: N.Q(t) });
          if (v.d !== 1n || v.n % m !== 0n) return [check("residue check", false, `${E} at ${n} = ${t} is ${qs(v)}, not a multiple of ${m}`)];
        }
        return [check("residue check", true, `direct evaluation at every residue class mod ${m} (and shifted representatives) gives multiples of ${m}`)];
      },
    };
  }
  return {
    answers: [statusAns("disproved"), ansText("counterexample", `${n} = ${bad}`)], solutionStatus: "exact",
    steps: [step("proof.counterexample", "Counterexample", `At ${n} = ${bad}, ${E} is not divisible by ${m}.`)],
    checks: () => {
      const v = evalS(args[0], { [n]: N.Q(bad) });
      return [check("counterexample", v.d !== 1n || v.n % m !== 0n, `${E} at ${n} = ${bad} equals ${qs(v)}, which is not a multiple of ${m}`)];
    },
  };
}

// ---------------------------------------------------------------- proveidentity
const POOL = [N.Q(2n), N.Q(3n), N.Q(5n), N.Q(-7n), N.Q(11n, 3n), N.Q(13n), N.Q(-17n, 5n), N.Q(19n), N.Q(23n, 7n), N.Q(-29n), N.Q(31n, 2n), N.Q(37n), N.Q(41n, 11n), N.Q(-43n), N.Q(47n, 13n), N.Q(53n), N.Q(59n, 17n)];
function cmdIdentity(args) {
  if (args.length !== 2) throw refuse("use proveidentity(left, right)");
  const [L, R] = args;
  const a = ratMP(L), b = ratMP(R);
  const num = mpAdd(mpMul(a.P, b.Q), mpMul(b.P, a.Q), N.NEG_ONE);
  const vars = [...new Set([...X.freeSymbols(L), ...X.freeSymbols(R)])].sort();
  const stmt = `${toText(L)} = ${toText(R)}`;
  if (!num.size) {
    return {
      answers: [statusAns("proved")], solutionStatus: "exact",
      steps: [step("proof.expand", "Expand both sides", `Bringing everything over one denominator, the numerator of (${toText(L)}) - (${toText(R)}) expands to 0, so the identity holds wherever both sides are defined.`)],
      checks: () => {
        const D = Math.max(0, ...vars.map((v) => { const s = degBound(X.sub(L, R), v); return s[0]; }));
        if (D + 1 > POOL.length) return [check("grid evaluation", false, "the degree is too high for the evaluation check")];
        const size = (D + 1) ** vars.length;
        if (size > 20000) return [check("grid evaluation", false, "too many variables for the evaluation check")];
        const idx = vars.map(() => 0);
        for (let c = 0; c < size; c++) {
          let t = c;
          for (let i = 0; i < vars.length; i++) { idx[i] = t % (D + 1); t = Math.floor(t / (D + 1)); }
          const env = Object.fromEntries(vars.map((v, i) => [v, POOL[idx[i]]]));
          let l, r;
          try { l = evalR(L, env); r = evalR(R, env); } catch (e) { return [check("grid evaluation", false, `evaluation failed at ${pointText(env)} (${e.message})`)]; }
          if (!N.eq(l, r)) return [check("grid evaluation", false, `the sides differ at ${pointText(env)}`)];
        }
        return [check("grid evaluation", true, `both sides were evaluated directly at all ${size} points of a grid with ${D + 1} values per variable; the numerator of the difference has degree <= ${D} in each variable (bound read from the expression), so vanishing on this grid forces it to be the zero polynomial`)];
      },
    };
  }
  // find a small counterexample where both sides are defined and differ
  const cands = [0, 1, 2, -1, 3, -2, 5].map((v) => N.Q(BigInt(v)));
  let found = null;
  const total = cands.length ** vars.length;
  for (let c = 0; c < Math.min(total, 5000) && !found; c++) {
    let t = c; const env = {};
    for (const v of vars) { env[v] = cands[t % cands.length]; t = Math.floor(t / cands.length); }
    try { if (!N.eq(evalR(L, env), evalR(R, env))) found = env; } catch (_) { /* undefined there */ }
  }
  if (!found) throw refuse("the two sides differ as expressions but no small counterexample was found");
  return {
    answers: [statusAns("disproved"), ansText("counterexample", pointText(found))], solutionStatus: "exact",
    steps: [step("proof.counterexample", "Counterexample", `At ${pointText(found)} the two sides of ${stmt} take different values.`)],
    checks: () => {
      const l = evalS(L, found), r = evalS(R, found);
      return [check("counterexample", !N.eq(l, r), `at ${pointText(found)}: left side ${qs(l)}, right side ${qs(r)}`)];
    },
  };
}

// ---------------------------------------------------------------- provesum
function cmdSum(args) {
  if (args.length !== 5) throw refuse("use provesum(term, k, n, F, lo)");
  const [term, kS, nS, F, loArg] = args;
  const k = symName(kS, "the summation index"), n = symName(nS, "the upper limit");
  const termN = X.subs(term, { [k]: X.sym(n) }); // term as a function of n
  const tp = polyOf(termN, n), fp = polyOf(F, n); // refuses non-polynomials
  const tAt = (j) => evalR(term, { [k]: N.Q(j) });
  let lo;
  if (loArg.k === "vector" || loArg.k === "tuple" || loArg.k === "set") {
    const listed = listOf(loArg).map((u) => { const r = ratOf(u); if (!r) throw refuse("the listed terms must be numbers"); return r; });
    for (let s = 0n; s <= 3n && lo === undefined; s++) if (listed.every((v, i) => N.eq(tAt(s + BigInt(i)), v))) lo = s;
    if (lo === undefined) throw refuse("the listed first terms do not follow the pattern of the last term");
  } else lo = intOf(loArg, "an integer starting index");
  const Fat = (m) => evalR(F, { [n]: N.Q(m) });
  // induction: base case and F(n) - F(n-1) - term(n) == 0 as a polynomial
  const Fm1 = polyOf(X.subs(F, { [n]: X.sub(X.sym(n), X.ONE) }), n);
  const len = Math.max(fp.length, Fm1.length, tp.length);
  const stepZero = Array.from({ length: len }, (_, i) => N.sub(N.sub(fp[i] || Z, Fm1[i] || Z), tp[i] || Z)).every(N.isZero);
  const baseOk = N.eq(Fat(lo), tAt(lo));
  const claim = `sum of ${toText(term)} for ${k} = ${lo} .. ${n} equals ${toText(F)} for every integer ${n} >= ${lo}`;
  if (baseOk && stepZero) {
    return {
      answers: [statusAns("proved")], solutionStatus: "exact",
      steps: [step("proof.base", "Base case", `${n} = ${lo}: both sides equal ${qs(tAt(lo))}.`),
        step("proof.step", "Inductive step", `Assuming the formula for ${n} - 1, adding ${toText(termN)} gives F(${n} - 1) + ${toText(termN)}, and F(${n}) - F(${n} - 1) expands to ${toText(termN)} exactly. By induction the formula holds for all ${n} >= ${lo}.`)],
      note: claim,
      checks: () => {
        // both sides are polynomials in n of degree <= D: compare brute-force sums at D + 2 points
        const D = Math.max(tp.length, fp.length) + 1;
        let s = Z;
        for (let m = lo, c = 0; c <= D; m++, c++) {
          s = N.add(s, evalS(term, { [k]: N.Q(m) }));
          if (!N.eq(s, evalS(F, { [n]: N.Q(m) }))) return [check("brute-force sums", false, `the sum up to ${n} = ${m} is ${qs(s)}, not ${qs(Fat(m))}`)];
        }
        return [check("brute-force sums", true, `the partial sums were added up directly for ${n} = ${lo} .. ${lo + BigInt(D)}; both sides are polynomials in ${n} of degree < ${D + 1}, so agreement at ${D + 1} values is itself a proof`)];
      },
    };
  }
  // disproved: smallest n where the sums differ
  let s = Z, bad = null;
  for (let m = lo; m < lo + 200n && bad === null; m++) { s = N.add(s, tAt(m)); if (!N.eq(s, Fat(m))) bad = { m, s }; }
  if (!bad) throw refuse("the algebra and the direct sums disagree; the statement is withheld");
  return {
    answers: [statusAns("disproved"), ansText("counterexample", `${n} = ${bad.m}`)], solutionStatus: "exact",
    steps: [step("proof.counterexample", "Counterexample", `For ${n} = ${bad.m} the sum is ${qs(bad.s)} but the formula gives ${qs(Fat(bad.m))}.`)],
    checks: () => {
      let t = Z;
      for (let m = lo; m <= bad.m; m++) t = N.add(t, evalS(term, { [k]: N.Q(m) }));
      const f = evalS(F, { [n]: N.Q(bad.m) });
      return [check("counterexample", !N.eq(t, f), `direct sum ${qs(t)} vs formula ${qs(f)} at ${n} = ${bad.m}`)];
    },
  };
}

// ---------------------------------------------------------------- bounded searches
const SEARCH = 500n;
function cmdBound(args) {
  if (args.length !== 3) throw refuse("use provebound(relation, n, start)");
  const rel = relOf(args[0]);
  const n = symName(args[1], "the variable");
  const a = intOf(args[2], "an integer start");
  let bad = null;
  for (let m = a; m < a + SEARCH && bad === null; m++) if (!holds(rel, evalR, { [n]: N.Q(m) })) bad = m;
  const stmt = `${relText(rel)} for all integers ${n} >= ${a}`;
  if (bad !== null) {
    return {
      answers: [statusAns("disproved"), ansText("counterexample", `${n} = ${bad}`)], solutionStatus: "exact",
      steps: [step("proof.counterexample", "Counterexample", `At ${n} = ${bad}: ${toText(rel.l)} = ${qs(evalR(rel.l, { [n]: N.Q(bad) }))} and ${toText(rel.r)} = ${qs(evalR(rel.r, { [n]: N.Q(bad) }))}.`)],
      checks: () => [check("counterexample", !holds(rel, evalS, { [n]: N.Q(bad) }), `re-evaluated at ${n} = ${bad} with the simplifier: the relation fails`)],
    };
  }
  const hi = a + SEARCH - 1n;
  return {
    answers: [statusAns("no counterexample found"), ansText("range checked", `${n} = ${a} .. ${hi}`)], solutionStatus: "evidence",
    note: `This is evidence, not a proof: ${stmt} was checked exactly for ${n} = ${a} .. ${hi} only. A proof for all ${n} (for example by induction) is not generated.`,
    steps: [step("proof.search", "Bounded search", `Checked ${SEARCH} consecutive values exactly; the relation held every time.`)],
    checks: () => {
      for (let m = a; m <= hi; m++) if (!holds(rel, evalS, { [n]: N.Q(m) })) return [check("second evaluation", false, `the simplifier finds a failure at ${n} = ${m}`)];
      return [check("second evaluation", true, `every value ${n} = ${a} .. ${hi} was re-checked with an independent evaluator`)];
    },
  };
}
// Miller-Rabin with the first 13 prime bases (deterministic below 3.3 * 10^24)
function millerRabin(nv) {
  if (nv < 2n) return false;
  const bases = [2n, 3n, 5n, 7n, 11n, 13n, 17n, 19n, 23n, 29n, 31n, 37n, 41n];
  for (const p of bases) { if (nv === p) return true; if (nv % p === 0n) return false; }
  if (nv >= 3317044064679887385961981n) throw refuse("numbers this large are not certified here");
  let d = nv - 1n, s = 0;
  while (!(d & 1n)) { d >>= 1n; s++; }
  const pw = (b, e) => { let r = 1n; b %= nv; while (e) { if (e & 1n) r = r * b % nv; b = b * b % nv; e >>= 1n; } return r; };
  outer: for (const a of bases) {
    let x = pw(a, d);
    if (x === 1n || x === nv - 1n) continue;
    for (let i = 1; i < s; i++) { x = x * x % nv; if (x === nv - 1n) continue outer; }
    return false;
  }
  return true;
}
function smallFactor(v) { for (let p = 2n; p * p <= v && p < 10000000n; p++) if (v % p === 0n) return p; return null; }
function cmdAlwaysPrime(args) {
  if (args.length !== 3) throw refuse("use provealwaysprime(expression, n, start)");
  const n = symName(args[1], "the variable");
  const a = intOf(args[2], "an integer start");
  const E = toText(args[0]);
  const valAt = (m) => { const v = evalR(args[0], { [n]: N.Q(m) }); if (v.d !== 1n) throw refuse("the expression must take integer values"); return v.n; };
  let bad = null;
  for (let m = a; m < a + 1000n && bad === null; m++) {
    const v = valAt(m);
    if (v > 100000000000000n) throw refuse("the values grow too large to certify");
    if (!isPrimeSmall(v)) bad = { m, v, f: v < 2n ? null : smallFactor(v) };
  }
  if (bad) {
    return {
      answers: [statusAns("disproved"), ansText("counterexample", `${n} = ${bad.m}`)], solutionStatus: "exact",
      steps: [step("proof.counterexample", "Counterexample", bad.f ? `At ${n} = ${bad.m}, ${E} = ${bad.v} = ${bad.f} x ${bad.v / bad.f}, which is not prime.` : `At ${n} = ${bad.m}, ${E} = ${bad.v}, which is not prime.`)],
      checks: () => {
        const v = evalS(args[0], { [n]: N.Q(bad.m) });
        if (v.d !== 1n) return [check("counterexample", false, "non-integer value")];
        if (v.n < 2n) return [check("counterexample", true, `${E} = ${v.n} at ${n} = ${bad.m}, and numbers below 2 are not prime`)];
        return [check("factor certificate", !!bad.f && bad.f > 1n && bad.f < v.n && v.n % bad.f === 0n, `${bad.f} divides ${v.n} (computed independently at ${n} = ${bad.m})`)];
      },
    };
  }
  const hi = a + 999n;
  return {
    answers: [statusAns("no counterexample found"), ansText("range checked", `${n} = ${a} .. ${hi}`)], solutionStatus: "evidence",
    note: `This is evidence, not a proof: ${E} was prime for every ${n} = ${a} .. ${hi}.`,
    steps: [step("proof.search", "Bounded search", "Each value was tested by trial division.")],
    checks: () => {
      for (let m = a; m <= hi; m++) { const v = evalS(args[0], { [n]: N.Q(m) }); if (v.d !== 1n || !millerRabin(v.n)) return [check("second primality test", false, `value at ${n} = ${m} is not prime by Miller-Rabin`)]; }
      return [check("second primality test", true, "every value was re-evaluated and confirmed prime by a deterministic Miller-Rabin test")];
    },
  };
}
function cmdFinite(args) {
  if (args.length !== 3) throw refuse("use provefinite(relation, x, [values])");
  const rel = relOf(args[0]);
  const x = symName(args[1], "the variable");
  const vals = listOf(args[2], "a list of values").map((u) => { const r = ratOf(u); if (!r) throw refuse("the values must be numbers"); return r; });
  if (!vals.length || vals.length > 100000) throw refuse("between 1 and 100000 values are supported");
  const bad = vals.find((v) => !holds(rel, evalR, { [x]: v }));
  if (bad) {
    return {
      answers: [statusAns("disproved"), ansText("counterexample", `${x} = ${qs(bad)}`)], solutionStatus: "exact",
      steps: [step("proof.counterexample", "Counterexample", `${relText(rel)} fails at ${x} = ${qs(bad)}.`)],
      checks: () => [check("counterexample", !holds(rel, evalS, { [x]: bad }), "re-evaluated with the simplifier: the relation fails there")],
    };
  }
  return {
    answers: [statusAns("proved")], solutionStatus: "exact",
    steps: [step("proof.exhaustion", "Proof by exhaustion", `${relText(rel)} was checked for each of the ${vals.length} values: ${vals.slice(0, 20).map(qs).join(", ")}${vals.length > 20 ? ", ..." : ""}.`)],
    checks: () => {
      const f = vals.find((v) => !holds(rel, evalS, { [x]: v }));
      return [check("second evaluation", !f, f ? `fails at ${qs(f)} with the simplifier` : "every case re-checked with an independent evaluator")];
    },
  };
}
function cmdEquiv(args) {
  const r = LOGIC_HANDLERS.logicequiv(args);
  const eq = r.answers.find((a) => a.label === "equivalent");
  const same = eq && eq.text === "yes";
  const ce = r.answers.find((a) => a.label === "counterexample");
  return {
    answers: [statusAns(same ? "proved" : "disproved"), ...(ce ? [ce] : [])], solutionStatus: "exact",
    steps: [...r.steps, step("proof.truthtable", same ? "Proof by truth table" : "Counterexample row", same ? "The two formulas agree on every assignment of truth values, which is exactly logical equivalence." : "One assignment gives the formulas different values.")],
    checks: r.checks,
  };
}
function cmdRequest(args) {
  let what = "";
  try { what = args.length ? labelOf(args[0]) : ""; } catch (_) { /* unnamed */ }
  throw refuse(`${what ? `"${what}" ` : "This "}is a general theorem. Quelvra does not write free-form proofs and never presents an unchecked argument as one. It certifies statements that can be settled mechanically (polynomial identities, divisibility for all integers via residues, summation formulas by induction, finite checks, truth tables) and reports bounded searches only as evidence.`);
}

export const PROOF_HANDLERS = {
  provedivisible: cmdDivisible, proveidentity: cmdIdentity, provesum: cmdSum, provebound: cmdBound,
  provealwaysprime: cmdAlwaysPrime, provefinite: cmdFinite, proveequiv: cmdEquiv, proofrequest: cmdRequest,
};
export { evalR, millerRabin };
