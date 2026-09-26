import { test, eq, ok, throws, close, rng } from "./harness.js";
import * as L from "../public/engine/linalg.js";
import * as X from "../public/engine/expr.js";
import { toText } from "../public/engine/print.js";

const txt = (A) => A.map((r) => r.map(toText).join(",")).join(";");
const vtxt = (v) => v.map(toText).join(",");
const randInt = (r, lo, hi) => r.int(lo, hi);
const randMat = (r, m, n, lo = -5, hi = 5) => Array.from({ length: m }, () => Array.from({ length: n }, () => randInt(r, lo, hi)));
function randInvertible(r, n) {
  for (let i = 0; i < 100; i++) {
    const A = randMat(r, n, n);
    if (L.det(A) !== X.ZERO) return A;
  }
  throw new Error("could not build an invertible matrix");
}
// unimodular-ish P: product of an upper and a lower unit triangular integer matrix (det 1)
function unimodular(r, n) {
  const U = Array.from({ length: n }, (_, i) => Array.from({ length: n }, (_, j) => (i === j ? 1 : j > i ? randInt(r, -2, 2) : 0)));
  const Lw = Array.from({ length: n }, (_, i) => Array.from({ length: n }, (_, j) => (i === j ? 1 : j < i ? randInt(r, -2, 2) : 0)));
  return L.mul(Lw, U);
}

// ---------------- basics
test("linalg: det 2x2 and 3x3", () => {
  eq(toText(L.det([[1, 2], [3, 4]])), "-2");
  eq(toText(L.det([[2, 0, 1], [1, 3, 2], [1, 1, 2]])), "6");
  eq(toText(L.det([[1, 2, 3], [4, 5, 6], [7, 8, 9]])), "0");
  eq(toText(L.det([["1/2", "1/3"], ["1/4", "1/5"]])), "1/60");
});
test("linalg: det needs a row swap", () => eq(toText(L.det([[0, 1, 2], [1, 0, 3], [4, -3, 8]])), "-2"));
test("linalg: symbolic det is ad - bc", () => eq(toText(L.det([["a", "b"], ["c", "d"]])), "a*d - b*c"));
test("linalg: det with radicals", () => eq(toText(L.det([["sqrt(2)", 1], [1, "sqrt(2)"]])), "1"));
test("linalg: det steps carry rule ids", () => {
  const r = L.detSteps([[0, 1], [1, 0]]);
  ok(r.steps.some((s) => s.rule === "linalg.det.swap"));
  eq(r.method, "bareiss");
  eq(toText(r.value), "-1");
});
test("linalg: inverse 2x2", () => eq(txt(L.inv([[2, 1], [1, 1]])), "1,-1;-1,2"));
test("linalg: inverse of a rational matrix verifies", () => {
  const A = [["1/2", 1], [2, "1/3"]];
  ok(L.verifyInverse(A, L.inv(A)));
});
test("linalg: singular matrix is reported", () => {
  const r = L.inverse([[1, 2], [2, 4]]);
  eq(r.invertible, false);
  eq(r.rank, 1);
  ok(r.steps.some((s) => s.rule === "linalg.inverse.singular"));
  throws(() => L.inv([[1, 2], [2, 4]]));
});
test("linalg: symbolic inverse cancels to d/(ad - bc)", () => {
  const I = L.inv([["a", "b"], ["c", "d"]]);
  eq(toText(I[0][0]), "d/(a*d - b*c)");
  ok(L.verifyInverse([["a", "b"], ["c", "d"]], I));
});
test("linalg: verifyInverse rejects a wrong inverse", () => ok(!L.verifyInverse([[2, 1], [1, 1]], [[1, 1], [-1, 2]])));
test("linalg: rref row operations are recorded and chain", () => {
  const r = L.rref([[1, 2, 3], [4, 5, 6], [7, 8, 10]]);
  eq(txt(r.rref), "1,0,0;0,1,0;0,0,1");
  const rules = new Set(r.steps.map((s) => s.rule));
  ok(rules.has("linalg.rref.addmul") && rules.has("linalg.rref.scale"));
  for (let i = 1; i < r.steps.length; i++) ok(r.steps[i].before === r.steps[i - 1].after, "steps chain");
  eq(r.steps[0].title, "R2 -> R2 - 4R1");
});
test("linalg: rref swap step", () => {
  const r = L.rref([[0, 1], [1, 0]]);
  eq(r.steps[0].rule, "linalg.rref.swap");
  eq(r.steps[0].title, "R1 <-> R2");
});
test("linalg: symbolic pivot scaling is conditional", () => {
  const r = L.rref([["a", 1], [0, 1]]);
  const s = r.steps.find((x) => x.rule === "linalg.rref.scale");
  eq(s.kind, "conditional");
  eq(toText(s.conditions[0]), "a != 0");
});
test("linalg: solve unique", () => {
  const r = L.solve([[2, 1], [1, -1]], [5, 1]);
  eq(r.status, "unique");
  eq(vtxt(r.solution), "2,1");
  ok(r.steps.some((s) => s.rule === "linalg.solve.unique"));
});
test("linalg: solve inconsistent", () => {
  const r = L.solve([[1, 1], [2, 2]], [1, 3]);
  eq(r.status, "none");
  ok(r.steps.some((s) => s.rule === "linalg.solve.inconsistent"));
});
test("linalg: solve infinitely many with parameters", () => {
  const r = L.solve([[1, 2, 1], [2, 4, 0]], [3, 2]);
  eq(r.status, "infinite");
  eq(r.params.map((p) => p.name).join(), "t1");
  eq(vtxt(r.solution), "-2t1 + 1,t1,2");
  ok(L.verifySolution([[1, 2, 1], [2, 4, 0]], r.solution, [3, 2]));
});
test("linalg: rank, null, column and row spaces", () => {
  const A = [[1, 2, 3], [2, 4, 6], [1, 0, 1]];
  eq(L.rank(A), 2);
  const ns = L.nullSpace(A);
  eq(ns.length, 1);
  eq(vtxt(ns[0]), "-1,-1,1");
  eq(L.columnSpace(A).map(vtxt).join("|"), "1,2,1|2,4,0");
  eq(L.rowSpace(A).map(vtxt).join("|"), "1,0,1|0,1,1");
});
test("linalg: add, sub, scale, mul, transpose, trace", () => {
  eq(txt(L.add([[1, 2]], [[3, 4]])), "4,6");
  eq(txt(L.sub([[1, 2]], [[3, 4]])), "-2,-2");
  eq(txt(L.scale("1/2", [[2, 4]])), "1,2");
  eq(txt(L.mul([[1, 2], [3, 4]], [[5], [6]])), "17;39");
  eq(txt(L.transpose([[1, 2, 3]])), "1;2;3");
  eq(toText(L.trace([[1, 2], [3, "x"]])), "x + 1");
  throws(() => L.mul([[1, 2]], [[1, 2]]));
  throws(() => L.add([[1]], [[1, 2]]));
});
test("linalg: integer and negative powers", () => {
  eq(txt(L.power([[1, 1], [1, 0]], 10)), "89,55;55,34");
  eq(txt(L.power([[2, 1], [1, 1]], -1)), "1,-1;-1,2");
  eq(txt(L.power([[5, 7], [1, 2]], 0)), "1,0;0,1");
  throws(() => L.power([[1, 2], [2, 4]], -1));
});
test("linalg: matrix and vector nodes convert both ways", () => {
  const n = L.matrixNode([[1, 2], [3, 4]]);
  eq(n.k, "matrix");
  eq(txt(L.toMatrix(n)), "1,2;3,4");
  eq(txt(L.toMatrix("[[1,2],[3,4]]")), "1,2;3,4");
  eq(L.vectorNode([1, 2]).k, "vector");
});
test("linalg: LU with pivoting reproduces PA", () => {
  const A = [[1, 2, 0], [3, 4, 4], [5, 6, 3]];
  const { P, L: Lo, U } = L.lu(A);
  ok(L.equal(L.mul(P, A), L.mul(Lo, U)));
  ok(U.every((r, i) => r.every((u, j) => j >= i || u === X.ZERO)), "U upper triangular");
});
test("linalg: exact QR", () => {
  const A = [[1, 1], [1, 0], [0, 1]];
  const { Q, R } = L.qr(A);
  ok(L.equal(L.mul(L.transpose(Q), Q), L.identity(2)), "Q^T Q = I");
  ok(L.equal(L.mul(Q, R), A), "QR = A");
  eq(toText(R[0][0]), "sqrt(2)");
});
test("linalg: numeric QR is labelled approximate", () => {
  const r = L.qrNumeric([[1, 2], [3, 4]]);
  ok(r.approximate);
  close(r.Q[0][0] * r.R[0][0], 1, 1e-12);
});
test("linalg: least squares line fit", () => {
  const r = L.leastSquares([[1, 1], [1, 2], [1, 3]], [1, 2, 2]);
  eq(r.status, "unique");
  eq(vtxt(r.x), "2/3,1/2");
  // residual is orthogonal to the columns
  eq(toText(L.dot(r.residual, [1, 1, 1])), "0");
  eq(toText(L.dot(r.residual, [1, 2, 3])), "0");
});
test("linalg: projection onto a column space", () => {
  const p = L.projectOntoColumnSpace([[1, 0], [0, 1], [0, 0]], [3, 4, 5]);
  eq(vtxt(p), "3,4,0");
  const P = L.projectionMatrix([[1], [1]]);
  eq(txt(P), "1/2,1/2;1/2,1/2");
});
test("linalg: vector operations", () => {
  eq(toText(L.dot([1, 2, 3], [4, 5, 6])), "32");
  eq(vtxt(L.cross([1, 0, 0], [0, 1, 0])), "0,0,1");
  eq(toText(L.vnorm([1, 1])), "sqrt(2)");
  eq(toText(L.angle([1, 0], [1, 1])), "pi/4");
  eq(toText(L.angle([1, 0], [-1, 0])), "pi");
  eq(vtxt(L.unit([3, 4])), "3/5,4/5");
  eq(vtxt(L.projectVector([2, 3], [1, 0])), "2,0");
  throws(() => L.unit([0, 0]));
  throws(() => L.cross([1, 2], [3, 4]));
});
test("linalg: characteristic polynomial", () => {
  eq(toText(L.charpoly([[2, 1], [1, 2]]).poly), "lambda^2 - 4lambda + 3");
  eq(toText(L.charpoly([[1, 2, 0], [0, 1, 0], [0, 0, 3]], "x").poly), "x^3 - 5x^2 + 7x - 3");
  const s = L.charpoly([["a", "b"], ["c", "d"]]);
  eq(toText(s.poly), "a*d + lambda^2 - b*c - a*lambda - d*lambda");
});
test("linalg: eigenvalues with radicals verify", () => {
  const A = [[1, 2], [3, 4]];
  const e = L.eigenvectors(A);
  eq(e.eigen.length, 2);
  ok(e.eigen.some((x) => toText(x.value) === "sqrt(33)/2 + 5/2"));
  for (const x of e.eigen) ok(L.verifyEigenpair(A, x.value, x.vectors[0]));
});
test("linalg: complex eigenvalues of a rotation", () => {
  const A = [[0, -1], [1, 0]];
  const e = L.eigenvectors(A);
  eq(e.eigen.map((x) => toText(x.value)).sort().join(","), "-i,i");
  for (const x of e.eigen) ok(L.verifyEigenpair(A, x.value, x.vectors[0]));
  const d = L.diagonalize(A);
  eq(d.diagonalizable, true);
  eq(d.real, false);
});
test("linalg: defective matrix is not diagonalizable", () => {
  const d = L.diagonalize([[1, 1], [0, 1]]);
  eq(d.diagonalizable, false);
  eq(d.reason, "eigenvalue 1 has algebraic multiplicity 2 but geometric multiplicity 1");
  eq(d.eigen[0].algebraic, 2);
  eq(d.eigen[0].geometric, 1);
});
test("linalg: diagonalize a symmetric matrix", () => {
  const d = L.diagonalize([[2, 1], [1, 2]]);
  ok(d.diagonalizable && d.verified);
  eq(d.D.map((r, i) => toText(r[i])).sort().join(","), "1,3");
});
test("linalg: repeated eigenvalue with full eigenspace", () => {
  const d = L.diagonalize([[2, 0, 0], [0, 2, 0], [0, 0, 5]]);
  ok(d.diagonalizable);
  const two = d.eigen.find((x) => toText(x.value) === "2");
  eq(two.algebraic, 2); eq(two.geometric, 2);
});
test("linalg: biquadratic eigenvalues", () => {
  // companion of x^4 - 5x^2 + 6 = (x^2 - 2)(x^2 - 3)
  const A = [[0, 0, 0, -6], [1, 0, 0, 0], [0, 1, 0, 5], [0, 0, 1, 0]];
  const e = L.eigenvalues(A);
  ok(e.complete);
  eq(e.values.map((v) => toText(v.value)).sort().join(","), "-sqrt(2),-sqrt(3),sqrt(2),sqrt(3)");
  const ev = L.eigenvectors(A);
  for (const x of ev.eigen) ok(L.verifyEigenpair(A, x.value, x.vectors[0]), toText(x.value));
});
test("linalg: unresolved cubic falls back to approximations", () => {
  const e = L.eigenvalues([[0, 1, 0], [0, 0, 1], [2, 0, 0]]);
  eq(e.complete, false);
  eq(e.approx.length, 3);
  ok(e.approx.every((a) => a.approximate));
  ok(e.approx.some((a) => Math.abs(a.re - Math.cbrt(2)) < 1e-12 && a.im === 0));
});
test("linalg: injected polynomial solver is used for higher degree", () => {
  let called = 0;
  const solvePoly = (p, x) => { called++; ok(x.name === "lambda"); return [X.pow(X.TWO, X.num(1, 3))]; };
  const A = [[0, 1, 0], [0, 0, 1], [2, 0, 0]];
  const e = L.eigenvalues(A, { solvePoly });
  eq(called, 1);
  eq(toText(e.values[0].value), "cbrt(2)");
  const ev = L.eigenvectors(A, { solvePoly });
  ok(L.verifyEigenpair(A, ev.eigen[0].value, ev.eigen[0].vectors[0]));
});
test("linalg: numeric eigenvalues (QR algorithm)", () => {
  const r = L.eigenNumeric([[2, 1, 0], [1, 3, 1], [0, 1, 4]]);
  ok(r.approximate && r.converged);
  const vals = r.values.map((v) => v.re).sort((a, b) => a - b);
  close(vals[0], 3 - Math.sqrt(3), 1e-10); close(vals[1], 3, 1e-10); close(vals[2], 3 + Math.sqrt(3), 1e-10);
  const c = L.eigenNumeric([[0, -1], [1, 0]]);
  close(Math.abs(c.values[0].im), 1, 1e-12);
});
test("linalg: numeric SVD", () => {
  const r = L.svdNumeric([[3, 0], [0, 4], [0, 0]]);
  close(r.S[0], 4, 1e-12); close(r.S[1], 3, 1e-12);
  ok(r.approximate);
});

// ---------------- properties
test("property: A * inv(A) = I for random invertible integer matrices up to 5x5", () => {
  const r = rng(101);
  for (let t = 0; t < 25; t++) {
    const n = 1 + (t % 5);
    const A = randInvertible(r, n);
    const Ai = L.inv(A);
    ok(L.equal(L.mul(A, Ai), L.identity(n)), "A Ainv");
    ok(L.verifyInverse(A, Ai));
  }
});
test("property: det(AB) = det(A) det(B)", () => {
  const r = rng(202);
  for (let t = 0; t < 30; t++) {
    const n = 2 + (t % 4);
    const A = randMat(r, n, n), B = randMat(r, n, n);
    const lhs = L.det(L.mul(A, B)), rhs = L.norm(X.mul(L.det(A), L.det(B)));
    ok(lhs === rhs, `n=${n}`);
  }
});
test("property: Bareiss determinant agrees with the LU pivot product", () => {
  const r = rng(203);
  for (let t = 0; t < 20; t++) {
    const n = 2 + (t % 4);
    const A = randMat(r, n, n);
    const { U, swaps } = L.lu(A);
    let prod = X.num(swaps % 2 ? -1 : 1);
    for (let i = 0; i < n; i++) prod = L.norm(X.mul(prod, U[i][i]));
    ok(prod === L.det(A));
  }
});
test("property: rank-nullity and A v = 0 on the null space", () => {
  const r = rng(303);
  for (let t = 0; t < 30; t++) {
    const m = r.int(1, 5), n = r.int(1, 5);
    let A = randMat(r, m, n, -3, 3);
    if (m > 1 && r.next() < 0.5) A[m - 1] = A[0].map((v, j) => v * 2 - A[m > 2 ? 1 : 0][j]); // force dependence
    const ns = L.nullSpace(A);
    eq(L.rank(A) + ns.length, n, "rank + nullity = n");
    for (const v of ns) ok(L.mul(A, v.map((u) => [u])).every((row) => row[0] === X.ZERO));
  }
});
test("property: row reduction preserves solution sets of consistent systems", () => {
  const r = rng(404);
  for (let t = 0; t < 30; t++) {
    const m = r.int(1, 5), n = r.int(1, 5);
    const A = randMat(r, m, n, -4, 4);
    const x0 = Array.from({ length: n }, () => r.int(-5, 5));
    const b = L.mul(A, x0.map((v) => [v])).map((row) => row[0]);
    const s = L.solve(A, b, { steps: false });
    ok(s.status !== "none", "consistent");
    ok(L.verifySolution(A, s.particular, b), "particular solves");
    // substitute random parameter values into the general solution
    for (let k = 0; k < 2 && s.params.length; k++) {
      const map = new Map(s.params.map((p) => [p.name, X.num(r.int(-9, 9))]));
      ok(L.verifySolution(A, s.solution.map((u) => X.subs(u, map)), b), "general solves");
    }
  }
});
test("property: eigenpairs of P D P^-1 with integer eigenvalues verify", () => {
  const r = rng(505);
  for (let t = 0; t < 12; t++) {
    const n = 2 + (t % 3);
    const P = unimodular(r, n);
    const d = Array.from({ length: n }, () => r.int(-4, 4));
    const D = d.map((v, i) => d.map((_, j) => (i === j ? v : 0)));
    const A = L.mul(L.mul(P, D), L.inv(P));
    const e = L.eigenvectors(A);
    ok(e.complete);
    const total = e.eigen.reduce((s, x) => s + x.algebraic, 0);
    eq(total, n);
    for (const x of e.eigen) {
      eq(x.algebraic, d.filter((v) => X.num(v) === x.value).length, "multiplicity");
      for (const v of x.vectors) ok(L.verifyEigenpair(A, x.value, v));
    }
    const dg = L.diagonalize(A);
    ok(dg.diagonalizable && dg.verified);
  }
});
test("property: Cayley-Hamilton p(A) = 0", () => {
  const r = rng(606);
  for (let t = 0; t < 15; t++) {
    const n = 1 + (t % 5);
    const A = randMat(r, n, n, -4, 4);
    const c = L.charpoly(A).rational;
    let acc = L.zeros(n, n), Pk = L.identity(n);
    for (let k = 0; k < c.length; k++) { acc = L.add(acc, L.scale(X.num(c[k]), Pk)); Pk = L.mul(Pk, A); }
    ok(L.equal(acc, L.zeros(n, n)));
  }
});
test("property: numeric SVD reconstructs A", () => {
  const r = rng(707);
  for (let t = 0; t < 10; t++) {
    const m = r.int(2, 5), n = r.int(2, 5);
    const A = randMat(r, m, n);
    const { U, S, V } = L.svdNumeric(A);
    for (let i = 0; i < m; i++) for (let j = 0; j < n; j++) {
      let s = 0;
      for (let k = 0; k < S.length; k++) s += U[i][k] * S[k] * V[j][k];
      close(s, A[i][j], 1e-9);
    }
  }
});
