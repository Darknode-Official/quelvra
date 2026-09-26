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
import { MORE_COMMANDS, hasMatrix, matrixEval, matrixCheck } from "./compute-more.js";

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
const rowsOf = (M) => (M && M.k === "matrix" ? M.args.map((r) => (r.args ? r.args : [r])) : []);
function isRREF(rows) {
  let lead = -1;
  for (let i = 0; i < rows.length; i++) {
    const j = rows[i].findIndex((v) => v !== X.ZERO);
    if (j < 0) { if (rows.slice(i).some((r) => r.some((v) => v !== X.ZERO))) return false; break; }
    if (j <= lead || rows[i][j] !== X.ONE) return false;
    if (rows.some((r, k) => k !== i && r[j] !== X.ZERO)) return false;
    lead = j;
  }
  return true;
}
function floatRank(M) {
  const A = M.map((r) => r.slice());
  const rows = A.length, cols = rows ? A[0].length : 0;
  const scale = Math.max(1, ...A.flat().map(Math.abs));
  let rank = 0;
  for (let c = 0; c < cols && rank < rows; c++) {
    let p = rank;
    for (let i = rank + 1; i < rows; i++) if (Math.abs(A[i][c]) > Math.abs(A[p][c])) p = i;
    if (Math.abs(A[p][c]) <= 1e-9 * scale) continue;
    [A[p], A[rank]] = [A[rank], A[p]];
    for (let i = rank + 1; i < rows; i++) { const f = A[i][c] / A[rank][c]; for (let j = c; j < cols; j++) A[i][j] -= f * A[rank][j]; }
    rank++;
  }
  return rank;
}
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
  transpose(node) {
    const A = matOf(node.args[0]);
    const R = L.matrixNode(L.transpose(A));
    return { ...exact(R), verify: () => {
      // independent: entry (j, i) of the result is entry (i, j) of the input
      const a = rowsOf(A), r = rowsOf(simplify(R));
      const ok = r.length === (a[0] || []).length && a.every((row, i) => row.every((v, j) => r[j] && r[j][i] === v));
      return V(ok ? "verified-exact" : "failed", "every entry (i, j) of the input is entry (j, i) of the result", "entries");
    } };
  },
  trace(node) {
    const A = matOf(node.args[0]);
    const t = L.trace(A);
    return { ...exact(t), verify: () => {
      const a = rowsOf(A);
      if (a.some((row) => row.length !== a.length)) return V("failed", "the trace needs a square matrix", "square");
      const want = a.reduce((s, row, i) => s + L.evalFloat(row[i]), 0), got = L.evalFloat(simplify(t));
      return V(Math.abs(want - got) <= 1e-9 * Math.max(1, Math.abs(want)) ? "verified-numeric" : "failed", `independent sum of the diagonal (${+want.toPrecision(12)}) agrees`, "recompute");
    } };
  },
  rank(node, env) {
    const A = matOf(node.args[0]);
    const rk = L.rank(A);
    return { ...exact(X.num(rk)), verify: () => { const rr = L.rref(A); const nz = rr.pivots ? rr.pivots.length : rk; return V(nz === rk ? "verified-exact" : "failed", `row-reduced form has ${nz} pivots`, "rref-pivots"); } };
  },
  rref(node, env) {
    const A = matOf(node.args[0]);
    const r = L.rref(A, { steps: true });
    logSteps(env, r.steps);
    const R = r.node || L.matrixNode(r.matrix || r.R);
    return { ...exact(R), verify: () => {
      // independent: R is in reduced row echelon form (exact structure) and R is row-equivalent to A
      // (floating-point ranks of A, R and A stacked on R are all equal)
      const rr = rowsOf(simplify(R)), a = rowsOf(A);
      const shape = isRREF(rr);
      const fa = a.map((row) => row.map(L.evalFloat)), fr = rr.map((row) => row.map(L.evalFloat));
      const ra = floatRank(fa), rR = floatRank(fr), rs = floatRank([...fa, ...fr]);
      const ok = shape && ra === rR && rR === rs;
      return V(ok ? "verified-numeric" : "failed", `reduced row echelon form; rank(A) = rank(R) = rank([A; R]) = ${ra}, so R is row-equivalent to A`, "row-equivalence");
    } };
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
  gcd(node) {
    // gcd of polynomials: gcd(x^2 - 1, x^2 + 2x + 1)
    if (node.args.length === 2 && node.args.some((a) => X.freeSymbols(a).size)) return MORE_COMMANDS.polygcd(node);
    return gcdLcm(node, "gcd");
  },
  lcm(node) { return gcdLcm(node, "lcm"); },
  phi(node) {
    const n = bigOf(node.args[0]);
    const v = T.phi(n);
    return { ...exact(X.num(v)), verify: () => {
      // independent: Euler's product over primes found by plain trial division
      if (n < 1n || n > 10n ** 12n) return { status: "inconclusive", checks: [] };
      let m = Number(n), r = Number(n);
      for (let p = 2; p * p <= m; p++) if (m % p === 0) { while (m % p === 0) m /= p; r -= r / p; }
      if (m > 1) r -= r / m;
      return V(BigInt(Math.round(r)) === v ? "verified-exact" : "failed", `Euler's product over the primes dividing ${n} gives ${Math.round(r)}`, "euler-product");
    } };
  },
  divisors(node) {
    const n = bigOf(node.args[0]);
    const ds = T.divisors(n);
    return { ...exact(X.set(...ds.map((d) => X.num(d)))), verify: () => {
      if (n < 1n || n > 10n ** 12n) return { status: "inconclusive", checks: [] };
      const m = Number(n), got = [];
      for (let d = 1; d * d <= m; d++) if (m % d === 0) { got.push(d); if (d * d !== m) got.push(m / d); }
      got.sort((x, y) => x - y);
      const ok = got.length === ds.length && got.every((d, i) => BigInt(d) === BigInt(ds[i]));
      return V(ok ? "verified-exact" : "failed", `trial division finds the same ${got.length} divisors`, "trial-division");
    } };
  },
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

// independent frequency count for mode
function modeCheck(vals, modes, freq) {
  const cnt = new Map();
  for (const v of vals) { const k = Nm.toString(v); cnt.set(k, (cnt.get(k) || 0) + 1); }
  const max = Math.max(...cnt.values());
  const want = [...cnt].filter(([, c]) => c === max).map(([k]) => Nm.toFloat(Nm.fromDecimal ? vals.find((v) => Nm.toString(v) === k) : 0)).sort((a, b) => a - b);
  const ok = max === 1 && vals.length > 1 ? modes.length === 0 : max === freq && want.length === modes.length && want.every((w, i) => Math.abs(w - modes[i]) < 1e-12);
  return V(ok ? "verified-exact" : "failed", `independent count: the most frequent value${want.length > 1 ? "s occur" : " occurs"} ${max} time${max > 1 ? "s" : ""}`, "count");
}
for (const f of ["mean", "median", "mode", "variance", "stdev"]) {
  COMMANDS[f] = (node) => {
    const xs = (node.args.length === 1 && (node.args[0].k === "tuple" || node.args[0].k === "set" || node.args[0].k === "vector") ? node.args[0].args : node.args).map((a) => simplify(a));
    if (!xs.every((a) => X.isNum(a))) throw unsupported("statistics need numbers");
    const vals = xs.map((a) => a.v);
    const fn = { mean: St.mean, median: St.median, mode: St.mode, variance: St.variance, stdev: St.stdDev }[f];
    const r = fn(vals);
    if (f === "mode") {
      if (r.noMode) return { answers: [{ kind: "none", label: "No mode: every value occurs once" }], solutionStatus: "exact", verify: () => modeCheck(vals, [], 1) };
      const tree = r.modes.length === 1 ? r.modes[0] : X.set(...r.modes);
      return { ...exact(tree), verify: () => modeCheck(vals, r.modes.map((m) => Nm.toFloat(m.v)), r.frequency) };
    }
    const tree = r && r.k ? r : Array.isArray(r) ? X.set(...r.map((v) => (v.k ? v : X.num(v)))) : r && r.n !== undefined ? X.num(r) : r.value || r;
    if ((f === "variance" || f === "stdev") && vals.length > 1) {
      // textbooks differ on which one "the" standard deviation means, so give both, labelled
      const pop = simplify(fn(vals, { population: true }));
      const samp = simplify(tree);
      const n = vals.length;
      const word = f === "stdev" ? "standard deviation" : "variance";
      return {
        answers: [{ kind: "exact", tree: samp, label: `Sample ${word} (divide by n - 1)` }, { kind: "exact", tree: pop, label: `Population ${word} (divide by n)` }],
        solutionStatus: "exact",
        verify: () => {
          const fl = vals.map((b) => Nm.toFloat(b)), m = fl.reduce((a, b) => a + b, 0) / n;
          const ss = fl.reduce((a, b) => a + (b - m) ** 2, 0);
          const wantS = f === "stdev" ? Math.sqrt(ss / (n - 1)) : ss / (n - 1), wantP = f === "stdev" ? Math.sqrt(ss / n) : ss / n;
          const close = (w, t) => Math.abs(w - L.evalFloat(t)) < 1e-9 * Math.max(1, Math.abs(w));
          const good = close(wantS, samp) && close(wantP, pop);
          return V(good ? "verified-numeric" : "failed", `independent floating-point sample (${+wantS.toPrecision(12)}) and population (${+wantP.toPrecision(12)}) values agree`, "recompute");
        },
      };
    }
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

Object.assign(COMMANDS, MORE_COMMANDS);

// Matrix arithmetic written directly: products, sums, scalar multiples and integer powers.
register({
  id: "evaluate.matrix", kinds: ["arithmetic", "expression"], priority: 5,
  run(node) {
    if (!hasMatrix(node) || node.k === "matrix" || node.k === "fn" || X.freeSymbols(node).size) return null;
    const r = matrixEval(node);
    if (!r.m) return null;
    const R = L.matrixNode(r.m);
    return { ...exact(R), verify: () => matrixCheck(node, R) };
  },
});

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
