// Quelvra linear algebra.
//
// Matrices are plain 2-D arrays of trees (A[i][j] is a canonical node). Every public function
// also accepts matrix / vector nodes, arrays of JS integers, BigInts, Rationals or source strings.
// Arithmetic is exact: all-rational matrices run on BigInt Rationals (fast path); anything else
// (radicals, i, symbols) runs on simplified trees with an exact zero test
// (together -> expand -> rationalise conjugates). Approximate algorithms (QR eigenvalues, SVD,
// numeric QR) run in double precision and are labelled `approximate: true`.
//
// Step records follow CONTRACT.md: { rule, title, why, before, after, conditions, sub, kind }.

import * as N from "./num.js";
import * as X from "./expr.js";
import { simplify, expand, together, numerDenom, makeCtx } from "./simplify.js";
import { parse } from "./parse.js";
import { toText } from "./print.js";

// ------------------------------------------------------------------ utilities
const fresh = () => makeCtx();
const Z = (u) => simplify(u, fresh());
const budget = (msg) => Object.assign(new Error("Quelvra: " + msg), { code: "BUDGET" });
const fail = (msg, code) => Object.assign(new Error(msg), { code });
const isNode = (u) => !!u && typeof u === "object" && typeof u.k === "string" && typeof u.id === "number";
const step = (rule, title, why, before, after, extra = {}) =>
  ({ rule, title, why, before, after, conditions: extra.conditions || [], sub: extra.sub || [], kind: extra.kind || "equivalent", ...(extra.data ? { data: extra.data } : {}) });

// Convert any scalar-like input into a canonical tree.
export function toTree(x) {
  if (isNode(x)) return Z(x);
  if (typeof x === "bigint") return X.num(x);
  if (typeof x === "number") {
    if (!Number.isFinite(x)) throw fail("Quelvra: non-finite number", "DOMAIN");
    return Number.isInteger(x) ? X.num(BigInt(x)) : X.num(N.fromDecimal(String(x)));
  }
  if (x && typeof x === "object" && typeof x.n === "bigint" && typeof x.d === "bigint") return X.num(x);
  if (typeof x === "string") return Z(parse(x));
  throw fail("Quelvra: cannot read matrix entry " + String(x), "INPUT");
}

// Normal form for exact field arithmetic on trees. Constant expressions end in the canonical
// form p + q*r of the smallest radical extension the canonicaliser exposes (denominators are
// rationalised); symbolic ones as expanded numerator / expanded denominator.
const NORM = new Map();
export function norm(u) {
  const hit = NORM.get(u);
  if (hit) return hit;
  let r = Z(u);
  if (r.k !== "num" && r !== X.UNDEF && !(r.k === "sym")) {
    try {
      const t = together(r, fresh());
      let [n, d] = numerDenom(t);
      n = expand(n, fresh());
      d = expand(d, fresh());
      if (X.freeSymbols(d).size === 0 && !X.isNum(d)) [n, d] = rationalise(n, d);
      if (X.isZero(n)) r = X.ZERO;
      else {
        if (!X.isNum(d)) [n, d] = cancelCommon(n, d);
        r = X.isNum(d) ? expand(X.mul(n, X.num(N.inv(d.v))), fresh()) : Z(X.div(n, d));
      }
    } catch (e) {
      if (e.code !== "BUDGET") throw e;
    }
  }
  if (NORM.size > 50000) NORM.clear();
  NORM.set(u, r);
  return r;
}
// Cancel common factors of an expanded numerator / denominator: the common monomial content
// (a*d / (a^2 d - a b c) -> d / (a d - b c)) and, for polynomials in one symbol with rational
// coefficients, their polynomial gcd.
const termsOf = (P) => (P.k === "add" ? P.args : [P]);
function monomialOf(t) {
  const m = new Map();
  for (const f of t.k === "mul" ? t.args : [t]) {
    if (f.k === "sym") m.set(f.name, (m.get(f.name) || 0n) + 1n);
    else if (f.k === "pow" && f.args[0].k === "sym" && X.isInt(f.args[1]) && f.args[1].v.n > 0n) m.set(f.args[0].name, (m.get(f.args[0].name) || 0n) + f.args[1].v.n);
  }
  return m;
}
function contentOf(P) {
  let c = null;
  for (const t of termsOf(P)) {
    const m = monomialOf(t);
    if (!c) { c = m; continue; }
    for (const [k, e] of c) { const f = m.get(k) || 0n; if (f < e) { if (f) c.set(k, f); else c.delete(k); } }
  }
  return c || new Map();
}
function uniCoeffs(P, name) {
  const out = [];
  for (const t of termsOf(P)) {
    let c = N.ONE, k = 0;
    for (const f of t.k === "mul" ? t.args : [t]) {
      if (f.k === "num") c = N.mul(c, f.v);
      else if (f.k === "sym" && f.name === name) k += 1;
      else if (f.k === "pow" && f.args[0].k === "sym" && f.args[0].name === name && X.isInt(f.args[1]) && f.args[1].v.n > 0n && f.args[1].v.n < 10000n) k += Number(f.args[1].v.n);
      else return null;
    }
    while (out.length <= k) out.push(N.ZERO);
    out[k] = N.add(out[k], c);
  }
  return out.length ? out : [N.ZERO];
}
function cancelCommon(n, d) {
  const cn = contentOf(n), cd = contentOf(d);
  const g = [];
  for (const [k, e] of cn) if (cd.has(k)) { const m = e < cd.get(k) ? e : cd.get(k); g.push(X.pow(X.sym(k), X.num(m))); }
  if (g.length) {
    const G = X.mul(...g);
    n = expand(X.div(n, G), fresh());
    d = expand(X.div(d, G), fresh());
  }
  const fs = new Set([...X.freeSymbols(n), ...X.freeSymbols(d)]);
  if (fs.size === 1) {
    const name = [...fs][0];
    const pn = uniCoeffs(n, name), pd = uniCoeffs(d, name);
    if (pn && pd && pd.length > 1) {
      const gg = pGcd(pn, pd);
      if (pDeg(gg) > 0) {
        const x = X.sym(name);
        n = pToTree(pDivmod(pn, gg)[0], x);
        d = pToTree(pDivmod(pd, gg)[0], x);
      }
      // make the denominator monic-ish: leading coefficient 1
      const pd2 = uniCoeffs(d, name);
      if (pd2) {
        const lc = pTrim(pd2).at(-1);
        if (!N.isOne(lc) && !N.isZero(lc)) {
          n = expand(X.mul(n, X.num(N.inv(lc))), fresh());
          d = expand(X.mul(d, X.num(N.inv(lc))), fresh());
        }
      }
    }
  }
  return [n, d];
}
const isRadical = (f) => (f.k === "pow" && X.isNum(f.args[1]) && f.args[1].v.d === 2n) || f === X.I;
function findRadical(u) {
  if (isRadical(u)) return u;
  for (const a of u.args) { const r = findRadical(a); if (r) return r; }
  return null;
}
function rationalise(n, d) {
  for (let it = 0; it < 12 && !X.isNum(d); it++) {
    const r = findRadical(d);
    if (!r) break;
    const P = [], Qs = [];
    for (const t of d.k === "add" ? d.args : [d]) {
      if (t === r) Qs.push(X.ONE);
      else if (t.k === "mul" && t.args.includes(r)) {
        const i = t.args.indexOf(r);
        Qs.push(Z(X.mul(...t.args.filter((_, j) => j !== i))));
      } else P.push(t);
    }
    const conj = X.sub(X.add(...P), X.mul(X.add(...Qs), r));
    n = expand(X.mul(n, conj), fresh());
    d = expand(X.mul(d, conj), fresh());
  }
  return [n, d];
}

// ------------------------------------------------------------------ fields
const QF = {
  name: "Q", zero: N.ZERO, one: N.ONE, add: N.add, sub: N.sub, mul: N.mul, div: N.div, neg: N.neg,
  isZero: N.isZero, isOne: N.isOne, tree: (r) => X.num(r),
};
const TF = {
  name: "tree", zero: X.ZERO, one: X.ONE,
  add: (a, b) => norm(X.add(a, b)), sub: (a, b) => norm(X.sub(a, b)), mul: (a, b) => norm(X.mul(a, b)),
  div: (a, b) => { if (TF.isZero(b)) throw fail("Quelvra: division by zero", "DOMAIN"); return norm(X.div(a, b)); },
  neg: (a) => norm(X.neg(a)), isZero: (u) => norm(u) === X.ZERO, isOne: (u) => norm(u) === X.ONE, tree: (u) => u,
};
const allNum = (A) => A.every((r) => r.every((u) => u.k === "num"));
function lift(A) {
  if (allNum(A)) return { F: QF, M: A.map((r) => r.map((u) => u.v)) };
  return { F: TF, M: A.map((r) => r.map(norm)) };
}
const lower = (F, M) => M.map((r) => r.map(F.tree));

// ------------------------------------------------------------------ conversion
export function toMatrix(x) {
  if (typeof x === "string") x = parse(x);
  if (isNode(x)) {
    if (x.k === "matrix") return check(x.args.map((r) => r.args.map(toTree)));
    if (x.k === "vector") return x.args.map((u) => [toTree(u)]);
    if (x.k === "tuple" && x.args.every((r) => r.k === "tuple" || r.k === "vector")) return check(x.args.map((r) => r.args.map(toTree)));
    if (x.k === "tuple") return x.args.map((u) => [toTree(u)]);
    return [[toTree(x)]];
  }
  if (Array.isArray(x)) {
    if (!x.length) throw fail("Quelvra: empty matrix", "INPUT");
    if (Array.isArray(x[0])) return check(x.map((r) => r.map(toTree)));
    return x.map((u) => [toTree(u)]);
  }
  throw fail("Quelvra: not a matrix", "INPUT");
}
function check(A) {
  if (!A.length || !A[0].length) throw fail("Quelvra: empty matrix", "INPUT");
  const n = A[0].length;
  if (A.some((r) => r.length !== n)) throw fail("Quelvra: rows of different lengths", "INPUT");
  return A;
}
// Vector input -> array of trees (accepts column / row matrices too).
export function toVector(x) {
  if (Array.isArray(x) && x.length && !Array.isArray(x[0])) return x.map(toTree);
  const A = toMatrix(x);
  if (A[0].length === 1) return A.map((r) => r[0]);
  if (A.length === 1) return A[0].slice();
  throw fail("Quelvra: expected a vector", "INPUT");
}
export const matrixNode = (A) => X.matrix(toMatrix(A).map((r) => X.tuple(...r)));
export const vectorNode = (v) => X.vector(...toVector(v));
export const dims = (A) => { A = toMatrix(A); return [A.length, A[0].length]; };
export const identity = (n) => Array.from({ length: n }, (_, i) => Array.from({ length: n }, (_, j) => (i === j ? X.ONE : X.ZERO)));
export const zeros = (m, n) => Array.from({ length: m }, () => Array.from({ length: n }, () => X.ZERO));
const node = (A) => X.matrix(A.map((r) => X.tuple(...r)));
const colsOf = (vs) => vs[0].map((_, i) => vs.map((v) => v[i])); // vectors -> matrix with those columns

// ------------------------------------------------------------------ basic operations
export function add(A, B) { return zipWith(A, B, (F) => F.add, "add"); }
export function sub(A, B) { return zipWith(A, B, (F) => F.sub, "subtract"); }
function zipWith(A, B, op, verb) {
  A = toMatrix(A); B = toMatrix(B);
  if (A.length !== B.length || A[0].length !== B[0].length)
    throw fail(`Quelvra: cannot ${verb} a ${A.length}x${A[0].length} and a ${B.length}x${B[0].length} matrix`, "DIMENSION");
  const F = allNum(A) && allNum(B) ? QF : TF;
  const L = (u) => (F === QF ? u.v : norm(u));
  return A.map((r, i) => r.map((u, j) => F.tree(op(F)(L(u), L(B[i][j])))));
}
export function scale(c, A) {
  c = toTree(c); A = toMatrix(A);
  return A.map((r) => r.map((u) => (c.k === "num" && u.k === "num" ? X.num(N.mul(c.v, u.v)) : norm(X.mul(c, u)))));
}
export function mul(A, B) {
  A = toMatrix(A); B = toMatrix(B);
  if (A[0].length !== B.length)
    throw fail(`Quelvra: cannot multiply a ${A.length}x${A[0].length} by a ${B.length}x${B[0].length} matrix (inner sizes differ)`, "DIMENSION");
  if (allNum(A) && allNum(B)) {
    return A.map((r) => B[0].map((_, j) => {
      let s = N.ZERO;
      for (let k = 0; k < r.length; k++) s = N.add(s, N.mul(r[k].v, B[k][j].v));
      return X.num(s);
    }));
  }
  return A.map((r) => B[0].map((_, j) => norm(X.add(...r.map((u, k) => X.mul(u, B[k][j]))))));
}
export function transpose(A) { A = toMatrix(A); return A[0].map((_, j) => A.map((r) => r[j])); }
export function trace(A) {
  A = toMatrix(A);
  if (A.length !== A[0].length) throw fail("Quelvra: trace needs a square matrix", "DIMENSION");
  return norm(X.add(...A.map((r, i) => r[i])));
}
export function power(A, k) {
  A = toMatrix(A);
  if (A.length !== A[0].length) throw fail("Quelvra: power needs a square matrix", "DIMENSION");
  k = typeof k === "bigint" ? k : isNode(k) ? (X.isInt(k) ? k.v.n : null) : Number.isInteger(k) ? BigInt(k) : null;
  if (k === null) throw fail("Quelvra: matrix power needs an integer exponent", "DOMAIN");
  if (k < 0n) {
    const r = inverse(A);
    if (!r.invertible) throw fail("Quelvra: negative power of a singular matrix", "SINGULAR");
    A = r.inverse; k = -k;
  }
  if (k > 1000000n) throw budget("matrix power exponent too large");
  let R = identity(A.length), P = A;
  while (k > 0n) {
    if (k & 1n) R = mul(R, P);
    k >>= 1n;
    if (k) P = mul(P, P);
  }
  return R;
}
export function equal(A, B) {
  A = toMatrix(A); B = toMatrix(B);
  if (A.length !== B.length || A[0].length !== B[0].length) return false;
  return A.every((r, i) => r.every((u, j) => u === B[i][j] || TF.isZero(X.sub(u, B[i][j]))));
}

// ------------------------------------------------------------------ determinant
// Fraction-free Bareiss on integers (rows scaled by their denominators' lcm) for rational
// matrices; Laplace expansion with minor memoisation for symbolic matrices up to 8x8,
// exact Gaussian elimination beyond.
export function detSteps(A) {
  A = toMatrix(A);
  const n = A.length;
  if (n !== A[0].length) throw fail("Quelvra: determinant needs a square matrix", "DIMENSION");
  const steps = [];
  if (allNum(A)) {
    let scaleDen = 1n;
    const M = A.map((r) => {
      let l = 1n;
      for (const u of r) l = (l / N.bgcd(l, u.v.d)) * u.v.d;
      scaleDen *= l;
      return r.map((u) => (u.v.n * l) / u.v.d);
    });
    if (scaleDen !== 1n)
      steps.push(step("linalg.det.clear-denominators", "Clear denominators row by row", `Multiplying each row by the lcm of its denominators multiplies the determinant by ${scaleDen}.`, node(A), node(M.map((r) => r.map((v) => X.num(v))))));
    let sgn = 1n, prev = 1n;
    for (let k = 0; k < n - 1; k++) {
      if (M[k][k] === 0n) {
        const p = M.findIndex((r, i) => i > k && r[k] !== 0n);
        if (p < 0) {
          steps.push(step("linalg.det.zero-column", "Zero column below the diagonal", `Column ${k + 1} has no nonzero pivot, so the determinant is 0.`, node(A), X.ZERO));
          return { value: X.ZERO, method: "bareiss", steps };
        }
        [M[k], M[p]] = [M[p], M[k]];
        sgn = -sgn;
        steps.push(step("linalg.det.swap", `R${k + 1} <-> R${p + 1}`, "Swapping two rows changes the sign of the determinant.", null, node(M.map((r) => r.map((v) => X.num(v))))));
      }
      for (let i = k + 1; i < n; i++) {
        for (let j = k + 1; j < n; j++) M[i][j] = (M[i][j] * M[k][k] - M[i][k] * M[k][j]) / prev;
        M[i][k] = 0n;
      }
      prev = M[k][k];
      steps.push(step("linalg.det.bareiss", `Bareiss elimination on column ${k + 1}`, "Each entry becomes (a_ij a_kk - a_ik a_kj) / previous pivot; the division is exact.", null, node(M.map((r) => r.map((v) => X.num(v))))));
    }
    const value = X.num(N.Q(sgn * M[n - 1][n - 1], scaleDen));
    steps.push(step("linalg.det.result", "Read the determinant", "After Bareiss elimination the last pivot equals the determinant (times the row scalings and sign changes).", node(A), value));
    return { value, method: "bareiss", steps };
  }
  if (n <= 8) {
    const T = A.map((r) => r.map(norm));
    const memo = new Map();
    const full = (1 << n) - 1;
    const f = (row, mask) => {
      if (row === n) return X.ONE;
      const key = row * 1024 + mask;
      if (memo.has(key)) return memo.get(key);
      const terms = [];
      let pos = 0;
      for (let j = 0; j < n; j++) {
        if (mask & (1 << j)) continue;
        if (T[row][j] !== X.ZERO) {
          const minor = f(row + 1, mask | (1 << j));
          if (minor !== X.ZERO) terms.push(X.mul(pos % 2 ? X.NEG_ONE : X.ONE, T[row][j], minor));
        }
        pos++;
      }
      const r = terms.length ? norm(X.add(...terms)) : X.ZERO;
      memo.set(key, r);
      return r;
    };
    void full;
    const value = f(0, 0);
    steps.push(step("linalg.det.cofactor", "Cofactor (Laplace) expansion along the first row", "Symbolic entries: expanding by minors avoids dividing by expressions that might vanish.", node(A), value));
    return { value, method: "cofactor", steps };
  }
  const { M } = lift(A);
  let d = X.ONE;
  for (let k = 0; k < n; k++) {
    const p = M.findIndex((r, i) => i >= k && !TF.isZero(r[k]));
    if (p < 0) return { value: X.ZERO, method: "gauss", steps };
    if (p !== k) { [M[k], M[p]] = [M[p], M[k]]; d = TF.neg(d); }
    d = TF.mul(d, M[k][k]);
    for (let i = k + 1; i < n; i++) {
      const f = TF.div(M[i][k], M[k][k]);
      for (let j = k; j < n; j++) M[i][j] = TF.sub(M[i][j], TF.mul(f, M[k][j]));
    }
  }
  steps.push(step("linalg.det.gauss", "Gaussian elimination", "The determinant is the product of the pivots, with a sign change per row swap.", node(A), d));
  return { value: d, method: "gauss", steps };
}
export const det = (A) => detSteps(A).value;

// ------------------------------------------------------------------ row reduction
function fmtFactor(t) {
  const s = toText(t);
  return /^[\w.]+$/.test(s) || /^\d+\/\d+$/.test(s) ? s : `(${s})`;
}
// Core RREF on a lifted matrix. pivotLimit: only columns < pivotLimit may hold pivots
// (for augmented matrices). record: produce step records.
function rrefCore(F, M, { pivotLimit = M[0].length, record = true, augment = 0 } = {}) {
  const m = M.length, n = M[0].length;
  const steps = [], pivots = [];
  const snap = () => node(lower(F, M));
  const mk = (rule, title, why, before, extra) => {
    if (!record) return;
    const s = step(rule, title, why, before, snap(), extra);
    if (augment) s.augment = augment;
    steps.push(s);
  };
  let r = 0;
  for (let c = 0; c < pivotLimit && r < m; c++) {
    let p = -1;
    for (let i = r; i < m; i++) {
      if (F.isZero(M[i][c])) continue;
      if (p < 0) p = i;
      if (F.isOne(M[i][c])) { p = i; break; }
    }
    if (p < 0) continue;
    if (p !== r) {
      const before = record ? snap() : null;
      [M[p], M[r]] = [M[r], M[p]];
      mk("linalg.rref.swap", `R${r + 1} <-> R${p + 1}`, `Bring a nonzero entry of column ${c + 1} into the pivot position.`, before, { data: { op: "swap", i: r, j: p } });
    }
    const piv = M[r][c];
    if (!F.isOne(piv)) {
      const before = record ? snap() : null;
      const invp = F.div(F.one, piv);
      M[r] = M[r].map((v) => F.mul(v, invp));
      const conds = F === TF && X.freeSymbols(piv).size ? [X.rel("!=", piv, X.ZERO)] : [];
      mk("linalg.rref.scale", `R${r + 1} -> ${fmtFactor(F.tree(invp))} R${r + 1}`, `Scale row ${r + 1} so the pivot in column ${c + 1} becomes 1.`, before,
        { conditions: conds, kind: conds.length ? "conditional" : "equivalent", data: { op: "scale", i: r, factor: F.tree(invp) } });
    }
    for (let i = 0; i < m; i++) {
      if (i === r || F.isZero(M[i][c])) continue;
      const before = record ? snap() : null;
      const f = M[i][c];
      M[i] = M[i].map((v, j) => F.sub(v, F.mul(f, M[r][j])));
      const c2 = F.tree(F.neg(f));
      const neg = c2.k === "num" ? N.isNeg(c2.v) : c2.k === "mul" && X.isNum(c2.args[0]) && N.isNeg(c2.args[0].v);
      const shown = neg ? fmtFactor(F.tree(f)) : fmtFactor(c2);
      mk("linalg.rref.addmul", `R${i + 1} -> R${i + 1} ${neg ? "-" : "+"} ${shown === "1" ? "" : shown}R${r + 1}`.replace("  ", " "),
        `Eliminate the entry in column ${c + 1} of row ${i + 1} using the pivot row ${r + 1}.`, before, { data: { op: "addmul", i, j: r, factor: c2 } });
    }
    pivots.push(c);
    r++;
  }
  void n;
  return { M, pivots, steps };
}
export function rref(A, opts = {}) {
  A = toMatrix(A);
  const { F, M } = lift(A);
  const { pivots, steps } = rrefCore(F, M, { pivotLimit: opts.pivotLimit, record: opts.steps !== false, augment: opts.augment || 0 });
  const R = lower(F, M);
  return { rref: R, node: node(R), pivots, rank: pivots.length, steps };
}
export const rank = (A) => rref(A, { steps: false }).rank;

export function inverse(A, opts = {}) {
  A = toMatrix(A);
  const n = A.length;
  if (n !== A[0].length) throw fail("Quelvra: only square matrices have inverses", "DIMENSION");
  const aug = A.map((r, i) => [...r, ...identity(n)[i]]);
  const record = opts.steps !== false;
  const { F, M } = lift(aug);
  const steps = [];
  if (record) steps.push(step("linalg.inverse.augment", "Form the augmented matrix [A | I]", "Row operations that turn A into I turn I into the inverse of A.", node(A), node(aug), {}));
  const res = rrefCore(F, M, { pivotLimit: n, record, augment: n });
  steps.push(...res.steps);
  if (res.pivots.length < n) {
    if (record) steps.push(step("linalg.inverse.singular", "The matrix is singular", `Row reduction gives only ${res.pivots.length} pivots for a ${n}x${n} matrix, so A has no inverse (det A = 0).`, node(A), X.UNDEF));
    return { invertible: false, singular: true, rank: res.pivots.length, inverse: null, node: null, steps };
  }
  const Inv = lower(F, M).map((r) => r.slice(n));
  if (record) steps.push(step("linalg.inverse.read", "Read off the inverse", "The left block is now I, so the right block is the inverse.", node(lower(F, M)), node(Inv)));
  return { invertible: true, singular: false, rank: n, inverse: Inv, node: node(Inv), steps };
}
export function inv(A) {
  const r = inverse(A, { steps: false });
  if (!r.invertible) throw fail("Quelvra: matrix is singular", "SINGULAR");
  return r.inverse;
}

// ------------------------------------------------------------------ linear systems
// solve(A, b): unique / none / infinite with free parameters t1, t2, ...
export function solve(A, b, opts = {}) {
  A = toMatrix(A);
  const bv = toVector(b);
  const m = A.length, n = A[0].length;
  if (bv.length !== m) throw fail(`Quelvra: right-hand side has ${bv.length} entries, the matrix has ${m} rows`, "DIMENSION");
  const aug = A.map((r, i) => [...r, bv[i]]);
  const record = opts.steps !== false;
  const { F, M } = lift(aug);
  const steps = [];
  if (record) steps.push(step("linalg.solve.augment", "Write the augmented matrix [A | b]", "Row operations do not change the solution set of the system.", null, node(aug)));
  const res = rrefCore(F, M, { pivotLimit: n, record, augment: n });
  steps.push(...res.steps);
  const R = lower(F, M);
  const piv = res.pivots;
  for (let i = piv.length; i < m; i++) {
    if (!F.isZero(M[i][n])) {
      if (record) steps.push(step("linalg.solve.inconsistent", "Inconsistent row", `Row ${i + 1} reads 0 = ${toText(R[i][n])}, which is impossible.`, node(R), X.FALSE));
      return { status: "none", solution: null, rank: piv.length, rref: R, steps };
    }
  }
  const free = [];
  for (let j = 0; j < n; j++) if (!piv.includes(j)) free.push(j);
  const pname = opts.param || "t";
  const params = free.map((_, k) => X.sym(pname + (k + 1)));
  const x = new Array(n), particular = new Array(n).fill(X.ZERO);
  free.forEach((j, k) => { x[j] = params[k]; });
  piv.forEach((c, i) => {
    particular[c] = R[i][n];
    x[c] = norm(X.add(R[i][n], ...free.map((j, k) => X.mul(X.NEG_ONE, R[i][j], params[k]))));
  });
  const basis = nullFromRref(R.map((r) => r.slice(0, n)), piv, n);
  if (!free.length) {
    if (record) steps.push(step("linalg.solve.unique", "Unique solution", `Every column of A has a pivot (rank ${n}), so the system has exactly one solution.`, node(R), X.vector(...x)));
    return { status: "unique", solution: x, particular: x, nullBasis: [], params: [], rank: piv.length, rref: R, steps };
  }
  if (record) steps.push(step("linalg.solve.parametric", "Infinitely many solutions",
    `Columns ${free.map((j) => j + 1).join(", ")} have no pivot; their variables become free parameters ${params.map((p) => p.name).join(", ")}.`, node(R), X.vector(...x)));
  return { status: "infinite", solution: x, particular, nullBasis: basis, params, rank: piv.length, rref: R, steps };
}
function nullFromRref(R, piv, n) {
  const out = [];
  for (let f = 0; f < n; f++) {
    if (piv.includes(f)) continue;
    const v = new Array(n).fill(X.ZERO);
    v[f] = X.ONE;
    piv.forEach((c, i) => { v[c] = norm(X.neg(R[i][f])); });
    out.push(v);
  }
  return out;
}
export function nullSpace(A) {
  A = toMatrix(A);
  const r = rref(A, { steps: false });
  return nullFromRref(r.rref, r.pivots, A[0].length);
}
export function columnSpace(A) {
  A = toMatrix(A);
  const r = rref(A, { steps: false });
  return r.pivots.map((c) => A.map((row) => row[c]));
}
export function rowSpace(A) {
  const r = rref(A, { steps: false });
  return r.rref.slice(0, r.rank).map((row) => row.slice());
}
export function verifySolution(A, x, b) {
  A = toMatrix(A);
  const xv = toVector(x), bv = toVector(b);
  const Ax = mul(A, xv.map((u) => [u]));
  return Ax.every((r, i) => TF.isZero(X.sub(r[0], bv[i])));
}

// ------------------------------------------------------------------ LU / QR
// PA = LU with row pivoting (largest |pivot| for rational matrices, first nonzero otherwise).
export function lu(A) {
  A = toMatrix(A);
  const m = A.length, n = A[0].length;
  const { F, M } = lift(A);
  const L = Array.from({ length: m }, (_, i) => Array.from({ length: m }, (_, j) => (i === j ? F.one : F.zero)));
  const perm = [...Array(m).keys()];
  const steps = [];
  let swaps = 0, r = 0;
  for (let c = 0; c < n && r < m; c++) {
    let p = -1;
    for (let i = r; i < m; i++) {
      if (F.isZero(M[i][c])) continue;
      if (p < 0) { p = i; if (F === TF) break; } else if (N.cmp(N.abs(M[i][c]), N.abs(M[p][c])) > 0) p = i;
    }
    if (p < 0) continue;
    if (p !== r) {
      [M[p], M[r]] = [M[r], M[p]];
      [perm[p], perm[r]] = [perm[r], perm[p]];
      for (let j = 0; j < r; j++) [L[p][j], L[r][j]] = [L[r][j], L[p][j]];
      swaps++;
      steps.push(step("linalg.lu.swap", `Swap R${r + 1} and R${p + 1}`, "Partial pivoting: move the pivot row up (recorded in P).", null, node(lower(F, M))));
    }
    for (let i = r + 1; i < m; i++) {
      if (F.isZero(M[i][c])) continue;
      const f = F.div(M[i][c], M[r][c]);
      L[i][r] = f;
      M[i] = M[i].map((v, j) => F.sub(v, F.mul(f, M[r][j])));
      steps.push(step("linalg.lu.eliminate", `R${i + 1} -> R${i + 1} - ${fmtFactor(F.tree(f))}R${r + 1}`, `The multiplier ${toText(F.tree(f))} is stored in L at (${i + 1}, ${r + 1}).`, null, node(lower(F, M))));
    }
    r++;
  }
  const P = perm.map((pi) => Array.from({ length: m }, (_, j) => (j === pi ? X.ONE : X.ZERO)));
  return { P, L: lower(F, L), U: lower(F, M), perm, swaps, steps };
}

// Exact Gram-Schmidt QR: A = Q R with Q having orthonormal columns (radicals appear through
// the norms). Rank-deficient columns are skipped (Q is m x r, R is r x n).
export function qr(A, opts = {}) {
  A = toMatrix(A);
  if (opts.numeric) return qrNumeric(A);
  const m = A.length, n = A[0].length;
  const cols = transpose(A);
  const us = [], n2 = [];
  const dotT = (u, v) => norm(X.add(...u.map((a, i) => X.mul(a, v[i]))));
  const steps = [];
  for (let j = 0; j < n; j++) {
    let u = cols[j];
    for (let i = 0; i < us.length; i++) {
      const c = norm(X.div(dotT(cols[j], us[i]), n2[i]));
      if (c !== X.ZERO) u = u.map((a, k) => norm(X.sub(a, X.mul(c, us[i][k]))));
    }
    const nn = dotT(u, u);
    if (TF.isZero(nn)) {
      steps.push(step("linalg.qr.dependent", `Column ${j + 1} is dependent`, "Its component orthogonal to the previous columns is zero, so it adds no new direction.", null, X.vector(...u)));
      continue;
    }
    us.push(u); n2.push(nn);
    steps.push(step("linalg.qr.gram-schmidt", `Orthogonalise column ${j + 1}`, "Subtract the projections onto the previous orthogonal vectors.", X.vector(...cols[j]), X.vector(...u)));
  }
  const rt = n2.map((v) => Z(X.sqrt(v)));
  const Qc = us.map((u, i) => u.map((a) => norm(X.div(a, rt[i]))));
  const Q = Array.from({ length: m }, (_, r) => Qc.map((q) => q[r]));
  const R = us.map((u, i) => cols.map((c, j) => norm(X.div(dotT(u, c), rt[i]))));
  // R is upper-triangular in the pivot sense; entries below a column's own step are zero
  return { Q, R, rank: us.length, exact: true, approximate: false, steps };
}
export function qrNumeric(A) {
  const M = toFloatMatrix(A);
  const m = M.length, n = M[0].length;
  const Q = [], R = Array.from({ length: n }, () => new Array(n).fill(0));
  const cols = M[0].map((_, j) => M.map((r) => r[j]));
  for (let j = 0; j < n; j++) {
    let v = cols[j].slice();
    for (let i = 0; i < Q.length; i++) {
      const c = Q[i].reduce((s, q, k) => s + q * v[k], 0);
      R[i][j] = c;
      v = v.map((x, k) => x - c * Q[i][k]);
    }
    const nv = Math.hypot(...v);
    R[Q.length][j] = nv;
    if (nv > 1e-12) Q.push(v.map((x) => x / nv));
  }
  return { Q: Array.from({ length: m }, (_, r) => Q.map((q) => q[r])), R: R.slice(0, Q.length), approximate: true, exact: false, method: "modified Gram-Schmidt (double precision)" };
}

// ------------------------------------------------------------------ least squares / projection
export function leastSquares(A, b) {
  A = toMatrix(A);
  const bv = toVector(b);
  const At = transpose(A);
  const AtA = mul(At, A), Atb = mul(At, bv.map((u) => [u])).map((r) => r[0]);
  const s = solve(AtA, Atb);
  const steps = [step("linalg.lsq.normal-equations", "Form the normal equations A^T A x = A^T b", "The least-squares solution minimises |Ax - b| and satisfies the normal equations.", null, X.eq(node(AtA), X.vector(...Atb))), ...s.steps];
  const x = s.solution;
  const residual = x ? mul(A, x.map((u) => [u])).map((r, i) => norm(X.sub(bv[i], r[0]))) : null;
  return { status: s.status, x, params: s.params || [], normal: { AtA, Atb }, residual, steps };
}
// Orthogonal projection of b onto the column space of A.
export function projectOntoColumnSpace(A, b) {
  A = toMatrix(A);
  const bv = toVector(b);
  const B = colsOf(columnSpace(A));
  if (!B[0].length) return bv.map(() => X.ZERO);
  const s = leastSquares(B, bv);
  return mul(B, s.x.map((u) => [u])).map((r) => r[0]);
}
export function projectionMatrix(A) {
  A = toMatrix(A);
  const B = colsOf(columnSpace(A));
  const Bt = transpose(B);
  return mul(mul(B, inv(mul(Bt, B))), Bt);
}

// ------------------------------------------------------------------ vectors
export function dot(u, v) {
  u = toVector(u); v = toVector(v);
  if (u.length !== v.length) throw fail("Quelvra: vectors of different lengths", "DIMENSION");
  return norm(X.add(...u.map((a, i) => X.mul(a, v[i]))));
}
export function cross(u, v) {
  u = toVector(u); v = toVector(v);
  if (u.length !== 3 || v.length !== 3) throw fail("Quelvra: the cross product needs 3-vectors", "DIMENSION");
  const c = (a, b, cc, d) => norm(X.sub(X.mul(a, b), X.mul(cc, d)));
  return [c(u[1], v[2], u[2], v[1]), c(u[2], v[0], u[0], v[2]), c(u[0], v[1], u[1], v[0])];
}
export const vnorm = (v) => Z(X.sqrt(dot(v, v)));
export function angle(u, v) {
  const d = dot(u, v), nu = vnorm(u), nv = vnorm(v);
  if (TF.isZero(nu) || TF.isZero(nv)) throw fail("Quelvra: angle with the zero vector is undefined", "DOMAIN");
  return Z(X.fn("acos", norm(X.div(d, X.mul(nu, nv)))));
}
export function unit(v) {
  v = toVector(v);
  const n = vnorm(v);
  if (TF.isZero(n)) throw fail("Quelvra: the zero vector has no direction", "DOMAIN");
  return v.map((a) => norm(X.div(a, n)));
}
// Projection of u onto v: (u.v / v.v) v
export function projectVector(u, v) {
  u = toVector(u); v = toVector(v);
  const vv = dot(v, v);
  if (TF.isZero(vv)) throw fail("Quelvra: cannot project onto the zero vector", "DOMAIN");
  const c = norm(X.div(dot(u, v), vv));
  return v.map((a) => norm(X.mul(c, a)));
}

// ------------------------------------------------------------------ polynomials over Q (ascending coefficient arrays)
const pTrim = (p) => { p = p.slice(); while (p.length > 1 && N.isZero(p[p.length - 1])) p.pop(); return p; };
const pDeg = (p) => (p.length === 1 && N.isZero(p[0]) ? -1 : p.length - 1);
const pMonic = (p) => { const l = p[p.length - 1]; return p.map((c) => N.div(c, l)); };
function pDivmod(a, b) {
  a = pTrim(a); b = pTrim(b);
  if (pDeg(b) < 0) throw fail("Quelvra: polynomial division by zero", "DOMAIN");
  const q = new Array(Math.max(1, a.length - b.length + 1)).fill(N.ZERO);
  let r = a.slice();
  const lb = b[b.length - 1];
  while (pDeg(r) >= pDeg(b)) {
    const k = r.length - b.length, c = N.div(r[r.length - 1], lb);
    q[k] = c;
    for (let i = 0; i < b.length; i++) r[k + i] = N.sub(r[k + i], N.mul(c, b[i]));
    r = pTrim(r);
    if (pDeg(r) < 0) break;
  }
  return [pTrim(q), r];
}
function pGcd(a, b) {
  a = pTrim(a); b = pTrim(b);
  for (let it = 0; pDeg(b) >= 0; it++) {
    if (it > 1000) throw budget("polynomial gcd");
    [a, b] = [b, pDivmod(a, b)[1]];
  }
  return pDeg(a) < 0 ? a : pMonic(a);
}
const pDeriv = (p) => (p.length === 1 ? [N.ZERO] : p.slice(1).map((c, i) => N.mul(c, N.Q(i + 1))));
const pSub = (a, b) => pTrim(Array.from({ length: Math.max(a.length, b.length) }, (_, i) => N.sub(a[i] || N.ZERO, b[i] || N.ZERO)));
function pToTree(p, x) {
  return Z(X.add(...p.map((c, k) => X.mul(X.num(c), X.pow(x, X.num(k))))));
}
// Square-free decomposition (Yun): returns [[factor, multiplicity], ...] with monic factors.
function squareFree(f) {
  f = pMonic(pTrim(f));
  if (pDeg(f) <= 0) return [];
  const out = [];
  const fp = pDeriv(f);
  const b = pGcd(f, fp);
  let c = pDivmod(f, b)[0], d = pSub(pDivmod(fp, b)[0], pDeriv(c));
  for (let i = 1; pDeg(c) > 0; i++) {
    if (i > 500) throw budget("square-free decomposition");
    const a = pGcd(c, d);
    if (pDeg(a) > 0) out.push([a, i]);
    c = pDivmod(c, a)[0];
    d = pSub(pDivmod(d, a)[0], pDeriv(c));
  }
  return out;
}
function intDivisors(n, cap) {
  n = n < 0n ? -n : n;
  if (n === 0n) return null;
  const { factors, rest } = N.trialFactor(n);
  if (rest !== 1n) return null;
  let ds = [1n];
  for (const [p, e] of factors) {
    const next = [];
    for (const d of ds) { let q = 1n; for (let i = 0n; i <= e; i++) { next.push(d * q); q *= p; } }
    ds = next;
    if (ds.length > cap) return null;
  }
  return ds;
}
// Rational roots of a square-free polynomial with rational coefficients (deflating each root).
function rationalRoots(p) {
  p = pTrim(p);
  const roots = [];
  while (pDeg(p) > 0 && N.isZero(p[0])) { roots.push(N.ZERO); p = p.slice(1); }
  if (pDeg(p) <= 0) return { roots, rest: p };
  let l = 1n;
  for (const c of p) l = (l / N.bgcd(l, c.d)) * c.d;
  const ints = p.map((c) => (c.n * l) / c.d);
  const a0 = ints[0], an = ints[ints.length - 1];
  const P = intDivisors(a0, 4000), Qd = intDivisors(an, 4000);
  let cands = [];
  if (P && Qd && P.length * Qd.length <= 40000) {
    const seen = new Set();
    for (const a of P) for (const b of Qd) for (const s of [1n, -1n]) {
      const r = N.Q(s * a, b), key = N.toString(r);
      if (!seen.has(key)) { seen.add(key); cands.push(r); }
    }
  } else {
    // too many divisors: take candidates from numeric roots, rounded to denominators dividing an
    for (const z of polyRootsNumeric(p.map(N.toFloat))) {
      if (Math.abs(z.im) > 1e-6 * Math.max(1, Math.abs(z.re))) continue;
      const den = Qd || [1n];
      for (const b of den.slice(0, 200)) cands.push(N.Q(BigInt(Math.round(z.re * Number(b))), b));
    }
  }
  for (const r of cands) {
    if (pDeg(p) <= 0) break;
    // exact test: sum a_k r^k
    let v = N.ZERO;
    for (let k = p.length - 1; k >= 0; k--) v = N.add(N.mul(v, r), p[k]);
    if (N.isZero(v)) {
      roots.push(r);
      p = pDivmod(p, [N.neg(r), N.ONE])[0];
    }
  }
  return { roots, rest: p };
}
function quadRoots(c, b, a) {
  // a x^2 + b x + c with trees
  const disc = norm(X.sub(X.mul(b, b), X.mul(X.num(4), a, c)));
  const sq = Z(X.sqrt(disc));
  const den = X.mul(X.TWO, a);
  return [norm(X.div(X.add(X.neg(b), sq), den)), norm(X.div(X.sub(X.neg(b), sq), den))];
}
// Numeric roots of a polynomial with double coefficients (ascending) via the companion matrix.
export function polyRootsNumeric(coeffs) {
  const p = coeffs.slice();
  while (p.length > 1 && p[p.length - 1] === 0) p.pop();
  const n = p.length - 1;
  if (n < 1) return [];
  const lead = p[n];
  const C = Array.from({ length: n }, () => new Array(n).fill(0));
  for (let i = 1; i < n; i++) C[i][i - 1] = 1;
  for (let i = 0; i < n; i++) C[i][n - 1] = -p[i] / lead;
  return hqrEigen(C).values;
}

// ------------------------------------------------------------------ characteristic polynomial / eigen
// charpoly(A, x): det(x I - A). Faddeev-LeVerrier for rational matrices, cofactor expansion otherwise.
export function charpoly(A, x = "lambda") {
  A = toMatrix(A);
  const n = A.length;
  if (n !== A[0].length) throw fail("Quelvra: characteristic polynomial needs a square matrix", "DIMENSION");
  const xs = typeof x === "string" ? X.sym(x) : x;
  if (allNum(A)) {
    const a = A.map((r) => r.map((u) => u.v));
    const c = new Array(n + 1).fill(N.ZERO);
    c[n] = N.ONE;
    let Mk = a.map((r) => r.map(() => N.ZERO));
    for (let k = 1; k <= n; k++) {
      // M_k = A M_{k-1} + c_{n-k+1} I ; c_{n-k} = -tr(A M_k) / k
      const AM = a.map((r) => a.map((_, j) => r.reduce((s, v, t) => N.add(s, N.mul(v, Mk[t][j])), N.ZERO)));
      Mk = AM.map((r, i) => r.map((v, j) => (i === j ? N.add(v, c[n - k + 1]) : v)));
      let tr = N.ZERO;
      for (let i = 0; i < n; i++) for (let t = 0; t < n; t++) tr = N.add(tr, N.mul(a[i][t], Mk[t][i]));
      c[n - k] = N.div(N.neg(tr), N.Q(k));
    }
    const poly = pToTree(c, xs);
    return {
      poly, coeffs: c.map((v) => X.num(v)), rational: c, variable: xs, method: "faddeev-leverrier",
      steps: [step("linalg.charpoly", "Characteristic polynomial det(xI - A)", "Computed exactly with the Faddeev-LeVerrier recurrence M_k = A M_(k-1) + c_(n-k+1) I, c_(n-k) = -tr(A M_k)/k.", node(A), X.eq(X.fn("p", xs), poly))],
    };
  }
  const xI = A.map((r, i) => r.map((u, j) => norm(i === j ? X.sub(xs, u) : X.neg(u))));
  const poly = expand(det(xI), fresh());
  const coeffs = polyCoeffsTree(poly, xs);
  return {
    poly, coeffs, rational: coeffs && coeffs.every((u) => u.k === "num") ? coeffs.map((u) => u.v) : null, variable: xs, method: "cofactor",
    steps: [step("linalg.charpoly", "Characteristic polynomial det(xI - A)", "Symbolic entries: expand det(xI - A) by cofactors.", node(A), X.eq(X.fn("p", xs), poly))],
  };
}
// Coefficients (ascending, trees) of an expanded polynomial in x; null if not polynomial.
export function polyCoeffsTree(u, x) {
  u = expand(u, fresh());
  const out = [];
  const addc = (k, c) => { while (out.length <= k) out.push(X.ZERO); out[k] = norm(X.add(out[k], c)); };
  for (const t of u.k === "add" ? u.args : [u]) {
    const fs = t.k === "mul" ? t.args : [t];
    let k = 0;
    const rest = [];
    for (const f of fs) {
      if (f === x) k += 1;
      else if (f.k === "pow" && f.args[0] === x && X.isInt(f.args[1]) && f.args[1].v.n > 0n) k += Number(f.args[1].v.n);
      else if (X.hasSym(f, x.name)) return null;
      else rest.push(f);
    }
    addc(k, Z(X.mul(...rest)));
  }
  if (!out.length) out.push(X.ZERO);
  return out;
}
function groupRoots(list) {
  const out = [];
  for (const { value, multiplicity } of list) {
    const hit = out.find((o) => TF.isZero(X.sub(o.value, value)));
    if (hit) hit.multiplicity += multiplicity; else out.push({ value, multiplicity });
  }
  return out;
}
function normaliseSolverOutput(r) {
  if (!r) return null;
  if (!Array.isArray(r)) r = r.roots || r.solutions || r.values || null;
  if (!Array.isArray(r)) return null;
  return r.map((e) => (isNode(e) ? { value: norm(e), multiplicity: 1 } : { value: norm(e.value || e.root || e.tree), multiplicity: e.multiplicity || 1 }));
}
// Exact eigenvalues. opts.solvePoly(treePoly, xSym) may be injected for factors of degree > 2.
export function eigenvalues(A, opts = {}) {
  A = toMatrix(A);
  const cp = charpoly(A, opts.variable || "lambda");
  const x = cp.variable;
  const values = [], approx = [], steps = [...cp.steps];
  let complete = true;
  const unresolved = [];
  const tryInjected = (polyTree, mult) => {
    if (typeof opts.solvePoly !== "function") return false;
    let r;
    try { r = normaliseSolverOutput(opts.solvePoly(polyTree, x)); } catch (_) { r = null; }
    if (!r || !r.length) return false;
    for (const e of r) values.push({ value: e.value, multiplicity: e.multiplicity * mult });
    steps.push(step("linalg.eigen.injected-solver", "Solve the remaining factor", "A factor of degree above 2 was handed to the polynomial solver.", X.eq(polyTree, X.ZERO), X.set(...r.map((e) => e.value))));
    return true;
  };
  if (cp.rational) {
    const sf = squareFree(cp.rational);
    for (const [f, mult] of sf) {
      const { roots, rest } = rationalRoots(f);
      for (const r of roots) values.push({ value: X.num(r), multiplicity: mult });
      if (roots.length) steps.push(step("linalg.eigen.rational-roots", "Rational roots", "Candidates p/q with p dividing the constant term and q dividing the leading coefficient were tested exactly.", null, X.set(...roots.map((r) => X.num(r)))));
      const d = pDeg(rest);
      if (d <= 0) continue;
      const T = rest.map((c) => X.num(c));
      if (d === 1) values.push({ value: X.num(N.div(N.neg(rest[0]), rest[1])), multiplicity: mult });
      else if (d === 2) {
        const rs = quadRoots(T[0], T[1], T[2]);
        for (const r of rs) values.push({ value: r, multiplicity: mult });
        steps.push(step("linalg.eigen.quadratic", "Quadratic formula", "The remaining quadratic factor is solved with x = (-b +- sqrt(b^2 - 4ac)) / (2a).", X.eq(pToTree(rest, x), X.ZERO), X.set(...rs)));
      } else if (d === 4 && N.isZero(rest[1]) && N.isZero(rest[3])) {
        const ys = quadRoots(T[0], T[2], T[4]);
        const rs = ys.flatMap((y) => { const s = Z(X.sqrt(y)); return [s, norm(X.neg(s))]; });
        for (const r of rs) values.push({ value: r, multiplicity: mult });
        steps.push(step("linalg.eigen.biquadratic", "Biquadratic factor", "Substitute y = x^2, solve the quadratic in y, then take square roots.", X.eq(pToTree(rest, x), X.ZERO), X.set(...rs)));
      } else if (!tryInjected(pToTree(rest, x), mult)) {
        complete = false;
        unresolved.push({ factor: pToTree(rest, x), multiplicity: mult });
        for (const z of polyRootsNumeric(rest.map(N.toFloat))) approx.push({ re: z.re, im: z.im, multiplicity: mult, approximate: true, method: "companion-matrix QR" });
      }
    }
  } else {
    const c = cp.coeffs;
    if (!c) { complete = false; unresolved.push({ factor: cp.poly, multiplicity: 1 }); }
    else if (c.length - 1 === 1) values.push({ value: norm(X.div(X.neg(c[0]), c[1])), multiplicity: 1 });
    else if (c.length - 1 === 2) {
      const rs = quadRoots(c[0], c[1], c[2]);
      if (TF.isZero(X.sub(rs[0], rs[1]))) values.push({ value: rs[0], multiplicity: 2 });
      else for (const r of rs) values.push({ value: r, multiplicity: 1 });
      steps.push(step("linalg.eigen.quadratic", "Quadratic formula", "The characteristic polynomial is quadratic in the eigenvalue.", X.eq(cp.poly, X.ZERO), X.set(...rs)));
    } else if (!tryInjected(cp.poly, 1)) { complete = false; unresolved.push({ factor: cp.poly, multiplicity: 1 }); }
  }
  return { charpoly: cp.poly, variable: x, values: groupRoots(values), approx, unresolved, complete, steps };
}
// Eigenvectors: basis of the null space of A - lambda I for each exact eigenvalue.
export function eigenvectors(A, opts = {}) {
  A = toMatrix(A);
  const ev = eigenvalues(A, opts);
  const n = A.length;
  const out = ev.values.map(({ value, multiplicity }) => {
    const M = A.map((r, i) => r.map((u, j) => (i === j ? norm(X.sub(u, value)) : u)));
    const vecs = nullSpace(M).map(prettyVector);
    return { value, algebraic: multiplicity, geometric: vecs.length, vectors: vecs };
  });
  void n;
  return { eigen: out, complete: ev.complete, charpoly: ev.charpoly, approx: ev.approx, unresolved: ev.unresolved, steps: ev.steps };
}
// Scale a rational vector to coprime integers (sign: first nonzero positive).
function prettyVector(v) {
  if (!v.every((u) => u.k === "num")) return v;
  let l = 1n, g = 0n;
  for (const u of v) l = (l / N.bgcd(l, u.v.d)) * u.v.d;
  const ints = v.map((u) => (u.v.n * l) / u.v.d);
  for (const k of ints) g = N.bgcd(g, k);
  if (g === 0n) return v;
  const first = ints.find((k) => k !== 0n);
  const s = first < 0n ? -1n : 1n;
  return ints.map((k) => X.num((s * k) / g));
}
export function diagonalize(A, opts = {}) {
  A = toMatrix(A);
  const n = A.length;
  const ev = eigenvectors(A, opts);
  if (!ev.complete) return { diagonalizable: null, reason: "not every eigenvalue could be found exactly", eigen: ev.eigen, approx: ev.approx, steps: ev.steps };
  const defective = ev.eigen.filter((e) => e.geometric < e.algebraic);
  if (defective.length) {
    const d = defective[0];
    return {
      diagonalizable: false, eigen: ev.eigen, steps: ev.steps,
      reason: `eigenvalue ${toText(d.value)} has algebraic multiplicity ${d.algebraic} but geometric multiplicity ${d.geometric}`,
    };
  }
  const vecs = [], diag = [];
  for (const e of ev.eigen) for (const v of e.vectors) { vecs.push(v); diag.push(e.value); }
  if (vecs.length !== n) return { diagonalizable: false, eigen: ev.eigen, reason: "not enough independent eigenvectors", steps: ev.steps };
  const P = colsOf(vecs);
  const D = diag.map((d, i) => diag.map((_, j) => (i === j ? d : X.ZERO)));
  const Pinv = inv(P);
  const verified = equal(mul(mul(P, D), Pinv), A);
  const real = diag.every((d) => !X.contains(d, X.I));
  const steps = [...ev.steps, step("linalg.diagonalize", "A = P D P^-1", "The columns of P are eigenvectors; D holds the matching eigenvalues.", node(A), X.eq(node(A), X.mul(node(P), node(D), X.pow(node(P), X.NEG_ONE))))];
  return { diagonalizable: true, real, P, D, Pinv, verified, eigen: ev.eigen, steps };
}

// ------------------------------------------------------------------ verification
export function verifyInverse(A, Ainv) {
  A = toMatrix(A); Ainv = toMatrix(Ainv);
  if (A.length !== A[0].length || Ainv.length !== A.length || Ainv[0].length !== A.length) return false;
  return equal(mul(A, Ainv), identity(A.length)) && equal(mul(Ainv, A), identity(A.length));
}
export function verifyEigenpair(A, lambda, v) {
  A = toMatrix(A);
  const l = toTree(lambda), vv = toVector(v);
  if (vv.every((u) => TF.isZero(u))) return false;
  const Av = mul(A, vv.map((u) => [u]));
  return Av.every((r, i) => TF.isZero(X.sub(r[0], X.mul(l, vv[i]))));
}

// ------------------------------------------------------------------ numeric algorithms (approximate)
export function evalFloat(u) {
  switch (u.k) {
    case "num": return N.toFloat(u.v);
    case "const":
      if (u.name === "pi") return Math.PI;
      if (u.name === "e") return Math.E;
      if (u.name === "oo") return Infinity;
      throw fail("Quelvra: complex or undefined value in a real numeric evaluation", "DOMAIN");
    case "add": return u.args.reduce((s, a) => s + evalFloat(a), 0);
    case "mul": return u.args.reduce((s, a) => s * evalFloat(a), 1);
    case "pow": {
      const b = evalFloat(u.args[0]), e = evalFloat(u.args[1]);
      if (b < 0 && X.isNum(u.args[1]) && u.args[1].v.d % 2n === 1n) {
        const m = Math.pow(-b, e);
        return u.args[1].v.n % 2n === 0n ? m : -m;
      }
      return Math.pow(b, e);
    }
    case "fn": {
      const a = u.args.map(evalFloat);
      const f = { sin: Math.sin, cos: Math.cos, tan: Math.tan, asin: Math.asin, acos: Math.acos, atan: Math.atan, exp: Math.exp, ln: Math.log, sqrt: Math.sqrt, abs: Math.abs, sinh: Math.sinh, cosh: Math.cosh, tanh: Math.tanh, floor: Math.floor, ceil: Math.ceil }[u.name];
      if (f) return f(a[0]);
      if (u.name === "log") return a.length === 2 ? Math.log(a[1]) / Math.log(a[0]) : Math.log10(a[0]);
      throw fail("Quelvra: cannot evaluate " + u.name + " numerically", "DOMAIN");
    }
    default: throw fail("Quelvra: cannot evaluate a " + u.k + " numerically", "DOMAIN");
  }
}
export function toFloatMatrix(A) {
  if (Array.isArray(A) && Array.isArray(A[0]) && typeof A[0][0] === "number") return A.map((r) => r.slice());
  return toMatrix(A).map((r) => r.map(evalFloat));
}
// Hessenberg reduction (elimination with pivoting) + Francis double-shift QR (EISPACK hqr).
function hqrEigen(A0) {
  const n = A0.length;
  const a = Array.from({ length: n + 1 }, (_, i) => new Array(n + 1).fill(0));
  for (let i = 0; i < n; i++) for (let j = 0; j < n; j++) a[i + 1][j + 1] = A0[i][j];
  // elmhes
  for (let m = 2; m < n; m++) {
    let x = 0, i = m;
    for (let j = m; j <= n; j++) if (Math.abs(a[j][m - 1]) > Math.abs(x)) { x = a[j][m - 1]; i = j; }
    if (i !== m) {
      for (let j = m - 1; j <= n; j++) [a[i][j], a[m][j]] = [a[m][j], a[i][j]];
      for (let j = 1; j <= n; j++) [a[j][i], a[j][m]] = [a[j][m], a[j][i]];
    }
    if (x) {
      for (i = m + 1; i <= n; i++) {
        let y = a[i][m - 1];
        if (y !== 0) {
          y /= x;
          a[i][m - 1] = y;
          for (let j = m; j <= n; j++) a[i][j] -= y * a[m][j];
          for (let j = 1; j <= n; j++) a[j][m] += y * a[j][i];
        }
      }
    }
  }
  for (let i = 1; i <= n; i++) for (let j = 1; j < i - 1; j++) a[i][j] = 0;
  const wr = new Array(n + 1).fill(0), wi = new Array(n + 1).fill(0);
  let anorm = 0;
  for (let i = 1; i <= n; i++) for (let j = Math.max(i - 1, 1); j <= n; j++) anorm += Math.abs(a[i][j]);
  let nn = n, t = 0, total = 0, converged = true;
  let p = 0, q = 0, r = 0, s = 0, w = 0, x = 0, y = 0, z = 0, l = 1, m = 0;
  outer: while (nn >= 1) {
    let its = 0;
    do {
      for (l = nn; l >= 2; l--) {
        s = Math.abs(a[l - 1][l - 1]) + Math.abs(a[l][l]);
        if (s === 0) s = anorm;
        if (Math.abs(a[l][l - 1]) + s === s) { a[l][l - 1] = 0; break; }
      }
      x = a[nn][nn];
      if (l === nn) { wr[nn] = x + t; wi[nn--] = 0; }
      else {
        y = a[nn - 1][nn - 1];
        w = a[nn][nn - 1] * a[nn - 1][nn];
        if (l === nn - 1) {
          p = 0.5 * (y - x);
          q = p * p + w;
          z = Math.sqrt(Math.abs(q));
          x += t;
          if (q >= 0) {
            z = p + (p >= 0 ? Math.abs(z) : -Math.abs(z));
            wr[nn - 1] = wr[nn] = x + z;
            if (z) wr[nn] = x - w / z;
            wi[nn - 1] = wi[nn] = 0;
          } else {
            wr[nn - 1] = wr[nn] = x + p;
            wi[nn - 1] = -(wi[nn] = z);
          }
          nn -= 2;
        } else {
          if (its === 60) { converged = false; break outer; }
          if (its === 10 || its === 20) {
            t += x;
            for (let i = 1; i <= nn; i++) a[i][i] -= x;
            s = Math.abs(a[nn][nn - 1]) + Math.abs(a[nn - 1][nn - 2]);
            y = x = 0.75 * s;
            w = -0.4375 * s * s;
          }
          ++its; ++total;
          for (m = nn - 2; m >= l; m--) {
            z = a[m][m];
            r = x - z;
            s = y - z;
            p = (r * s - w) / a[m + 1][m] + a[m][m + 1];
            q = a[m + 1][m + 1] - z - r - s;
            r = a[m + 2][m + 1];
            s = Math.abs(p) + Math.abs(q) + Math.abs(r);
            p /= s; q /= s; r /= s;
            if (m === l) break;
            const u = Math.abs(a[m][m - 1]) * (Math.abs(q) + Math.abs(r));
            const v = Math.abs(p) * (Math.abs(a[m - 1][m - 1]) + Math.abs(z) + Math.abs(a[m + 1][m + 1]));
            if (u + v === v) break;
          }
          for (let i = m + 2; i <= nn; i++) {
            a[i][i - 2] = 0;
            if (i !== m + 2) a[i][i - 3] = 0;
          }
          for (let k = m; k <= nn - 1; k++) {
            if (k !== m) {
              p = a[k][k - 1];
              q = a[k + 1][k - 1];
              r = 0;
              if (k !== nn - 1) r = a[k + 2][k - 1];
              if ((x = Math.abs(p) + Math.abs(q) + Math.abs(r)) !== 0) { p /= x; q /= x; r /= x; }
            }
            const sq = Math.sqrt(p * p + q * q + r * r);
            if ((s = p >= 0 ? sq : -sq) !== 0) {
              if (k === m) { if (l !== m) a[k][k - 1] = -a[k][k - 1]; }
              else a[k][k - 1] = -s * x;
              p += s;
              x = p / s; y = q / s; z = r / s;
              q /= p; r /= p;
              for (let j = k; j <= nn; j++) {
                p = a[k][j] + q * a[k + 1][j];
                if (k !== nn - 1) { p += r * a[k + 2][j]; a[k + 2][j] -= p * z; }
                a[k + 1][j] -= p * y;
                a[k][j] -= p * x;
              }
              const mmin = nn < k + 3 ? nn : k + 3;
              for (let i = l; i <= mmin; i++) {
                p = x * a[i][k] + y * a[i][k + 1];
                if (k !== nn - 1) { p += z * a[i][k + 2]; a[i][k + 2] -= p * r; }
                a[i][k + 1] -= p * q;
                a[i][k] -= p;
              }
            }
          }
        }
      }
    } while (l < nn - 1);
  }
  const values = [];
  for (let i = 1; i <= n; i++) values.push({ re: wr[i], im: wi[i] });
  values.sort((u, v) => v.re - u.re || v.im - u.im);
  return { values, converged, iterations: total };
}
export function eigenNumeric(A) {
  const M = toFloatMatrix(A);
  if (M.length !== M[0].length) throw fail("Quelvra: eigenvalues need a square matrix", "DIMENSION");
  const r = hqrEigen(M);
  return { ...r, approximate: true, method: "Hessenberg reduction + Francis double-shift QR (double precision)" };
}
// One-sided Jacobi SVD: A = U diag(S) V^T (thin), singular values descending.
export function svdNumeric(A) {
  let M = toFloatMatrix(A);
  let flipped = false;
  if (M.length < M[0].length) { M = M[0].map((_, j) => M.map((r) => r[j])); flipped = true; }
  const m = M.length, n = M[0].length;
  const U = M.map((r) => r.slice());
  const V = Array.from({ length: n }, (_, i) => Array.from({ length: n }, (_, j) => (i === j ? 1 : 0)));
  let sweeps = 0, converged = false;
  for (; sweeps < 80 && !converged; sweeps++) {
    converged = true;
    for (let p = 0; p < n - 1; p++) for (let q = p + 1; q < n; q++) {
      let al = 0, be = 0, ga = 0;
      for (let i = 0; i < m; i++) { al += U[i][p] ** 2; be += U[i][q] ** 2; ga += U[i][p] * U[i][q]; }
      if (Math.abs(ga) <= 1e-15 * Math.sqrt(al * be) || ga === 0) continue;
      converged = false;
      const zeta = (be - al) / (2 * ga);
      const t = (zeta >= 0 ? 1 : -1) / (Math.abs(zeta) + Math.sqrt(1 + zeta * zeta));
      const c = 1 / Math.sqrt(1 + t * t), s = c * t;
      for (let i = 0; i < m; i++) { const a = U[i][p], b = U[i][q]; U[i][p] = c * a - s * b; U[i][q] = s * a + c * b; }
      for (let i = 0; i < n; i++) { const a = V[i][p], b = V[i][q]; V[i][p] = c * a - s * b; V[i][q] = s * a + c * b; }
    }
  }
  const S = [];
  for (let j = 0; j < n; j++) S.push(Math.sqrt(U.reduce((s, r) => s + r[j] ** 2, 0)));
  const order = S.map((s, j) => j).sort((a, b) => S[b] - S[a]);
  const Ss = order.map((j) => S[j]);
  const Uo = U.map((r) => order.map((j) => (S[j] > 1e-300 ? r[j] / S[j] : 0)));
  const Vo = V.map((r) => order.map((j) => r[j]));
  const res = flipped ? { U: Vo, S: Ss, V: Uo } : { U: Uo, S: Ss, V: Vo };
  return { ...res, approximate: true, converged, sweeps, method: "one-sided Jacobi (double precision)" };
}
