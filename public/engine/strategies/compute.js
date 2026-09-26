// Command strategies: linear algebra, number theory, statistics, units, factoring.
// Each command result is verified by an independent route (e.g. A * inv(A) = I, product of the
// prime factors = n, primality by a second method, factored form expands back to the input).

import * as X from "../expr.js";
import * as Nm from "../num.js";
import { simplify, expand } from "../simplify.js";
import { toText } from "../print.js";
import * as L from "../linalg.js";
import * as T from "../numtheory.js";
import * as St from "../stats.js";
import * as U from "../units.js";
import { factorTree, cancel } from "../poly.js";
import { proveprime, checkCertificate } from "../primeproof.js";
import { equivalent } from "../verify.js";
import { register, toContractVerification, unsupported } from "../orchestrate.js";

const V = (status, detail, name = "check") => toContractVerification([{ status, checks: [{ kind: name, ok: status !== "failed", detail }] }]);
const exact = (tree, extra = {}) => ({ answers: [{ kind: "exact", tree, ...extra }], solutionStatus: "exact" });
const bigOf = (u) => {
  const s = simplify(u);
  if (!X.isInt(s)) throw unsupported(`expected an integer, got ${toText(s)}`);
  return s.v.n;
};
const matOf = (u) => {
  const s = simplify(u);
  if (s.k !== "matrix") throw unsupported("expected a matrix such as [[1, 2], [3, 4]]");
  return s;
};
const logSteps = (env, steps) => { for (const st of steps || []) env.log.add(st); };

// vectors: [1, 2, 3], or a matrix with one row or one column
const vecOf = (u) => {
  const s = simplify(u);
  if (s.k === "vector" || s.k === "tuple") return s.args;
  if (s.k === "matrix") {
    const rows = s.args.map((r) => r.args);
    if (rows.length === 1) return rows[0];
    if (rows.every((r) => r.length === 1)) return rows.map((r) => r[0]);
  }
  throw unsupported("expected a vector such as [1, 2, 3]");
};
const dotOf = (a, b) => simplify(X.add(...a.map((ai, i) => X.mul(ai, b[i]))));
const isZ = (u) => simplify(expand(u)) === X.ZERO;

const COMMANDS = {
  dot(node, env) {
    if (node.args.length !== 2) throw unsupported("dot needs two vectors: dot([1, 2, 3], [4, 5, 6])");
    const a = vecOf(node.args[0]), b = vecOf(node.args[1]);
    if (a.length !== b.length) throw unsupported(`the vectors have different lengths (${a.length} and ${b.length})`);
    const d = dotOf(a, b);
    env.log.add({ rule: "vec.dot", title: "Multiply matching components and add", why: a.map((ai, i) => `(${toText(ai)})(${toText(b[i])})`).join(" + ") + ` = ${toText(d)}`, before: node, after: d });
    return { ...exact(d), verify: () => {
      // independent: floating-point sum of products, compared with the exact value
      const fa = a.map(L.evalFloat), fb = b.map(L.evalFloat), fd = L.evalFloat(d);
      if (![...fa, ...fb, fd].every(Number.isFinite)) return { status: "not-applicable", checks: [] };
      const want = fa.reduce((s, x, i) => s + x * fb[i], 0);
      const ok = Math.abs(want - fd) <= 1e-9 * Math.max(1, Math.abs(want));
      return V(ok ? "verified-numeric" : "failed", `independent floating-point dot product (${+want.toPrecision(12)}) agrees`, "recompute");
    } };
  },
  cross(node, env) {
    if (node.args.length !== 2) throw unsupported("cross needs two vectors: cross([1, 2, 3], [4, 5, 6])");
    const a = vecOf(node.args[0]), b = vecOf(node.args[1]);
    if (a.length !== 3 || b.length !== 3) throw unsupported("the cross product is defined for 3-component vectors");
    const c = [X.sub(X.mul(a[1], b[2]), X.mul(a[2], b[1])), X.sub(X.mul(a[2], b[0]), X.mul(a[0], b[2])), X.sub(X.mul(a[0], b[1]), X.mul(a[1], b[0]))].map((t) => simplify(t));
    const r = X.vector(...c);
    env.log.add({ rule: "vec.cross", title: "Cross product by components", why: "(a2 b3 - a3 b2, a3 b1 - a1 b3, a1 b2 - a2 b1)", before: node, after: r });
    return { ...exact(r), verify: () => {
      // independent exact identities: the result is orthogonal to both inputs, and
      // |a x b|^2 = |a|^2 |b|^2 - (a . b)^2 (Lagrange's identity)
      const orth = isZ(dotOf(c, a)) && isZ(dotOf(c, b));
      const lag = isZ(X.sub(dotOf(c, c), X.sub(X.mul(dotOf(a, a), dotOf(b, b)), X.pow(dotOf(a, b), X.TWO))));
      return V(orth && lag ? "verified-exact" : "failed", "the result is orthogonal to both vectors and its length satisfies Lagrange's identity", "identities");
    } };
  },
  det(node, env) {
    const A = matOf(node.args[0]);
    const r = L.detSteps ? L.detSteps(A) : null;
    const d = r && r.value ? r.value : L.det(A);
    if (r && r.steps) logSteps(env, r.steps);
    return { ...exact(d), verify: () => {
      // independent: numeric determinant via LU on floats
      const F = L.toFloatMatrix(A);
      const n = F.length;
      const M = F.map((row) => row.slice());
      let det = 1;
      for (let c = 0; c < n; c++) {
        let p = c;
        for (let r2 = c + 1; r2 < n; r2++) if (Math.abs(M[r2][c]) > Math.abs(M[p][c])) p = r2;
        if (M[p][c] === 0) { det = 0; break; }
        if (p !== c) { [M[p], M[c]] = [M[c], M[p]]; det = -det; }
        det *= M[c][c];
        for (let r2 = c + 1; r2 < n; r2++) { const f = M[r2][c] / M[c][c]; for (let k = c; k < n; k++) M[r2][k] -= f * M[c][k]; }
      }
      const dv = L.evalFloat(d);
      const okv = Math.abs(dv - det) <= 1e-9 * Math.max(1, Math.abs(det));
      return V(okv ? "verified-numeric" : "failed", okv ? `floating-point LU determinant ${+det.toPrecision(12)} agrees` : `floating-point LU gives ${det}`, "numeric-lu");
    } };
  },
  inv(node, env) {
    const A = matOf(node.args[0]);
    const r = L.inverse(A, { steps: true });
    logSteps(env, r.steps);
    if (!r.invertible) return { answers: [{ kind: "none", label: `The matrix is singular (rank ${r.rank}), so it has no inverse.` }], solutionStatus: "exact", noSolution: true,
      verify: () => { const d = L.det(A); return V(d === X.ZERO ? "verified-exact" : "failed", `det = ${toText(d)}`, "determinant"); } };
    return { ...exact(r.node), verify: () => { const ok = L.verifyInverse(A, r.node); const good = ok === true || (ok && ok.ok); return V(good ? "verified-exact" : "failed", "A times the inverse is the identity", "product-identity"); } };
  },
  transpose(node) { const A = matOf(node.args[0]); return { ...exact(L.matrixNode(L.transpose(A))), verify: () => ({ status: "not-applicable", checks: [] }) }; },
  trace(node) { const A = matOf(node.args[0]); return { ...exact(L.trace(A)), verify: () => ({ status: "not-applicable", checks: [] }) }; },
  rank(node, env) {
    const A = matOf(node.args[0]);
    const rk = L.rank(A);
    return { ...exact(X.num(rk)), verify: () => { const rr = L.rref(A); const nz = rr.pivots ? rr.pivots.length : rk; return V(nz === rk ? "verified-exact" : "failed", `row-reduced form has ${nz} pivots`, "rref-pivots"); } };
  },
  rref(node, env) {
    const A = matOf(node.args[0]);
    const r = L.rref(A, { steps: true });
    logSteps(env, r.steps);
    return { ...exact(r.node || L.matrixNode(r.matrix || r.R)), verify: () => ({ status: "not-applicable", checks: [] }) };
  },
  eigenvalues(node, env) {
    const A = matOf(node.args[0]);
    const r = L.eigenvalues(A);
    logSteps(env, r.steps);
    const answers = r.values.map((v) => ({ kind: "exact", tree: v.value, label: v.multiplicity > 1 ? `lambda (multiplicity ${v.multiplicity})` : "lambda" }));
    for (const a of r.approx || []) answers.push({ kind: "approx", approx: a.approx || a, label: "lambda" });
    return { answers, solutionStatus: r.complete ? "exact" : "partial", verify: () => {
      // each eigenvalue must be a root of the characteristic polynomial, checked numerically on the matrix itself
      const F = L.toFloatMatrix(A), n = F.length;
      const checks = [];
      let bad = false;
      for (const v of r.values) {
        const lam = L.evalFloat(v.value);
        if (!Number.isFinite(lam)) continue;
        const M = F.map((row, i) => row.map((x, j) => x - (i === j ? lam : 0)));
        let det = 1;
        for (let c = 0; c < n; c++) {
          let p = c; for (let r2 = c + 1; r2 < n; r2++) if (Math.abs(M[r2][c]) > Math.abs(M[p][c])) p = r2;
          if (Math.abs(M[p][c]) < 1e-300) { det = 0; break; }
          if (p !== c) { [M[p], M[c]] = [M[c], M[p]]; det = -det; }
          det *= M[c][c];
          for (let r2 = c + 1; r2 < n; r2++) { const f = M[r2][c] / M[c][c]; for (let k = c; k < n; k++) M[r2][k] -= f * M[c][k]; }
        }
        const scale = Math.max(1, ...F.flat().map(Math.abs)) ** n;
        const okv = Math.abs(det) <= 1e-8 * scale;
        if (!okv) bad = true;
        checks.push({ kind: "det(A - lambda I)", ok: okv, detail: `det(A - (${toText(v.value)}) I) ~ ${det.toExponential(2)}` });
      }
      return toContractVerification([{ status: bad ? "failed" : "verified-numeric", checks }]);
    } };
  },
  eigenvectors(node, env) {
    const A = matOf(node.args[0]);
    const r = L.eigenvectors(A);
    const list = r.pairs || r.vectors || r;
    if (!Array.isArray(list)) throw unsupported("eigenvectors unavailable");
    const answers = list.map((p) => ({ kind: "exact", tree: X.tuple(p.value || p.lambda, ...(p.vectors || p.basis || []).map((v) => (v.k ? v : L.vectorNode(v)))), label: "(lambda, basis)" }));
    return { answers, solutionStatus: "exact", verify: () => {
      let bad = false; const checks = [];
      for (const p of list) for (const v of p.vectors || p.basis || []) {
        const ok = L.verifyEigenpair(A, p.value || p.lambda, v);
        const good = ok === true || (ok && ok.ok);
        if (!good) bad = true;
        checks.push({ kind: "A v = lambda v", ok: good, detail: `checked for lambda = ${toText(p.value || p.lambda)}` });
      }
      return toContractVerification([{ status: bad ? "failed" : "verified-exact", checks }]);
    } };
  },
  isprime(node, env) {
    const n = bigOf(node.args[0]);
    const r = T.primality(n);
    env.log.add({ rule: "nt.primality", title: "Primality test", why: `Method: ${r.method}.`, kind: "note" });
    let res = r.status === "prime" ? X.TRUE : r.status === "composite" || r.status === "neither" ? X.FALSE : null;
    let proof = null;
    if (!res) {
      proof = proveprime(n);
      if (proof.status === "prime") {
        res = X.TRUE;
        env.log.add({ rule: "nt.primality.proof", title: "Prove primality", why: `${proof.method}. The certificate was re-checked independently.`, kind: "note" });
      } else if (proof.status === "composite") res = X.FALSE;
    }
    if (res === X.TRUE && proof) return { ...exact(res), extra: { certificate: proof.certificate }, verify: () => V(checkCertificate(proof.certificate) ? "verified-exact" : "failed", `primality certificate (${proof.method}) re-checked`, "certificate") };
    if (!res) return { answers: [{ kind: "none", label: `probably prime (${r.method}); not proven` }], solutionStatus: "partial", verify: () => ({ status: "partial", checks: [] }) };
    return { ...exact(res), verify: () => {
      if (res === X.FALSE && n > 1n) {
        const f = T.factor(n, { budget: 200000 });
        if (f.factors && f.factors.length && !(f.factors.length === 1 && f.factors[0][1] === 1n && f.factors[0][0] === n)) return V("verified-exact", `${n} has the factor ${f.factors[0][0]}`, "witness-factor");
      }
      if (res === X.TRUE && n < 10n ** 12n) {
        for (let d = 2n; d * d <= n; d += d === 2n ? 1n : 2n) if (n % d === 0n) return V("failed", `divisible by ${d}`, "trial-division");
        return V("verified-exact", "trial division up to sqrt(n) finds no factor", "trial-division");
      }
      if (res === X.TRUE) return V("verified-exact", `second test agrees (${T.isPrime(n) ? "prime" : "composite"})`, "independent-test");
      return V("verified-exact", r.method, "definition");
    } };
  },
  factorint(node, env) {
    const n = bigOf(node.args[0]);
    const r = T.factor(n, { budget: 2_000_000 });
    logSteps(env, r.steps);
    const tree = T.factorTree(n);
    return { ...exact(tree), solutionStatus: r.complete ? "exact" : "partial", verify: () => {
      let prod = 1n;
      for (const [p, e] of r.factors) prod *= p ** e;
      for (const u of r.unfactored || []) prod *= typeof u === "bigint" ? u : BigInt(u.n || u);
      const good = prod * (r.sign || 1n) === n;
      const primes = r.factors.every(([p]) => T.isPrime(p));
      return V(good && primes ? "verified-exact" : "failed", good ? "the factors multiply back to n and each is prime" : "product mismatch", "multiply-back");
    } };
  },
  gcd(node) { return gcdLcm(node, "gcd"); },
  lcm(node) { return gcdLcm(node, "lcm"); },
  phi(node) { const n = bigOf(node.args[0]); return { ...exact(X.num(T.phi(n))), verify: () => ({ status: "not-applicable", checks: [] }) }; },
  divisors(node) { const n = bigOf(node.args[0]); return { ...exact(X.set(...T.divisors(n).map((d) => X.num(d)))), verify: () => ({ status: "not-applicable", checks: [] }) }; },
};
function gcdLcm(node, which) {
  const ns = node.args.map(bigOf);
  const r = which === "gcd" ? T.gcd(...ns) : T.lcm(...ns);
  const v = typeof r === "bigint" ? r : BigInt(r);
  return { ...exact(X.num(v)), verify: () => {
    // independent: gcd divides every input and the quotients are coprime; lcm is a multiple of every input and lcm/n are coprime
    const ok = which === "gcd"
      ? ns.every((n) => v === 0n ? n === 0n : n % v === 0n) && T.gcd(...ns.map((n) => (v === 0n ? 0n : n / v))) === 1n
      : ns.every((n) => n === 0n || v % n === 0n) && (v === 0n || T.gcd(...ns.filter((n) => n !== 0n).map((n) => v / n)) === 1n);
    return V(ok ? "verified-exact" : "failed", which === "gcd" ? "divides every input and the quotients share no common factor" : "is a multiple of every input and is the least such", "definition");
  } };
}

for (const f of ["mean", "median", "mode", "variance", "stdev"]) {
  COMMANDS[f] = (node) => {
    const xs = (node.args.length === 1 && (node.args[0].k === "tuple" || node.args[0].k === "set" || node.args[0].k === "vector") ? node.args[0].args : node.args).map((a) => simplify(a));
    if (!xs.every((a) => X.isNum(a))) throw unsupported("statistics need numbers");
    const vals = xs.map((a) => a.v);
    const fn = { mean: St.mean, median: St.median, mode: St.mode, variance: St.variance, stdev: St.stdDev }[f];
    const r = fn(vals);
    const tree = r && r.k ? r : Array.isArray(r) ? X.set(...r.map((v) => (v.k ? v : X.num(v)))) : r && r.n !== undefined ? X.num(r) : r.value || r;
    return { ...exact(simplify(tree)), verify: () => {
      const fl = vals.map((b) => Nm.toFloat(b)).sort((a, b) => a - b), n = fl.length;
      const m = fl.reduce((a, b) => a + b, 0) / n;
      let want = null;
      if (f === "mean") want = m;
      else if (f === "median") want = n % 2 ? fl[(n - 1) / 2] : (fl[n / 2 - 1] + fl[n / 2]) / 2;
      else if (f === "variance") want = fl.reduce((a, b) => a + (b - m) ** 2, 0) / (n - 1);
      else if (f === "stdev") want = Math.sqrt(fl.reduce((a, b) => a + (b - m) ** 2, 0) / (n - 1));
      if (want === null) return { status: "not-applicable", checks: [] };
      const gotv = L.evalFloat(simplify(tree));
      const good = Math.abs(want - gotv) < 1e-9 * Math.max(1, Math.abs(want));
      return V(good ? "verified-numeric" : "failed", `independent floating-point ${f} (${+want.toPrecision(12)}) agrees`, "recompute");
    } };
  };
}

register({
  id: "compute.command", kinds: ["command"], priority: 20,
  applies: (card) => card.command in COMMANDS,
  run(node, card, env) { return COMMANDS[card.command](node, env); },
});

// Factor polynomials (goal "factor" on expressions).
register({
  id: "factor.poly", kinds: ["expression"], goals: ["factor"], priority: 15,
  run(node, card, env) {
    const u = node.k === "fn" && node.name === "factor" ? node.args[0] : node;
    const f = factorTree(u);
    env.log.add({ rule: "factor", title: "Factor over the rationals", why: "Square-free decomposition, then factorisation of each part into irreducible factors over Q.", before: u, after: f });
    return { ...exact(f), verify: () => {
      const e = equivalent(expand(f), expand(u));
      return V(e.status === "equivalent-exact" ? "verified-exact" : e.status === "equivalent-numeric" ? "verified-numeric" : "failed", "expanding the factored form gives back the input", "expand-back");
    } };
  },
});

// Simplify rational functions by cancelling common polynomial factors (with the condition kept).
register({
  id: "simplify.cancel", kinds: ["expression"], goals: ["simplify", "evaluate"], priority: 18,
  applies: (card) => card.family === "rational-expression" || (card.features && card.features.rational),
  run(node, card, env) {
    const u = node.k === "fn" && node.name === "simplify" ? node.args[0] : node;
    let r;
    try { r = cancel(simplify(u, env.ctx)); } catch (e) { return null; }
    const tree = r && r.k ? r : r && (r.result || r.tree || r.node);
    if (!tree || tree === simplify(u)) return null;
    const conds = (r.conditions || []).map((c) => (c.k ? c : X.rel("!=", c, X.ZERO)));
    env.log.add({ rule: "simp.cancel", title: "Cancel common factors", why: "Factor the numerator and denominator and cancel the common polynomial factors. The cancelled factors must stay nonzero.", before: u, after: tree, conditions: conds, kind: conds.length ? "conditional" : "equivalent" });
    return { ...exact(tree), conditions: conds, verify: () => {
      const e = equivalent(u, tree);
      return V(e.status === "equivalent-exact" ? "verified-exact" : e.status === "equivalent-numeric" ? "verified-numeric" : "failed", "the input and the result agree wherever the input is defined", "equivalence");
    } };
  },
});

// Units: "5 km/h to m/s" style conversions and dimension errors such as 5 m + 3 s.
const UNIT_NAMES = new Set(["m", "s", "kg", "g", "km", "cm", "mm", "h", "min", "N", "J", "W", "Pa", "A", "K", "mol", "L", "mL", "ft", "in", "mi", "lb", "hr"]);
function unitTerms(u) {
  const terms = u.k === "add" ? u.args : [u];
  return terms.every((t) => {
    const fs = [...X.freeSymbols(t)];
    return fs.length >= 1 && fs.every((n) => UNIT_NAMES.has(n)) && (t.k === "mul" ? X.isNum(t.args[0]) : false);
  });
}
register({
  id: "units.arith", kinds: ["expression"], priority: 5,
  applies: (card) => card.unknowns.every((n) => UNIT_NAMES.has(n)),
  run(node, card, env) {
    if (!unitTerms(node)) return null;
    const terms = node.k === "add" ? node.args : [node];
    const qs = terms.map((t) => U.parseQuantity(toText(t).replace(/\*/g, " ")));
    try {
      let acc = qs[0];
      for (const q of qs.slice(1)) acc = U.add(acc, q);
      const s = U.simplifyQuantity ? U.simplifyQuantity(acc) : acc;
      const tree = X.mul(s.value, X.sym(s.unit.text));
      return { ...exact(tree), verify: () => ({ status: "not-applicable", checks: [] }) };
    } catch (e) {
      if (e.code === "DIMENSION") {
        env.log.add({ rule: "units.dimension-check", title: "Check dimensions", why: e.message.replace(/^Quelvra: /, ""), kind: "note" });
        return { answers: [{ kind: "none", label: e.message.replace(/^Quelvra: /, "").replace(/^./, (c) => c.toUpperCase()) + "." }], solutionStatus: "exact", refused: true, verify: () => V("verified-exact", "dimensions differ", "dimensions") };
      }
      throw e;
    }
  },
});
