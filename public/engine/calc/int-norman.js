// Heuristic Risch-Norman ("parallel integration") for the integrator.
//
// Ansatz: F = sum c_j m_j where the m_j are products of at most two kernels of f (its transcendental and
// algebraic building blocks, closed under d/dx for sin/cos and sinh/cosh pairs) times powers of x. The
// unknown constants solve F' = f; they are fitted by least squares at sample points, recognised as small
// rationals, and the candidate is then accepted ONLY if it passes the integrator's independent check.
// This is a heuristic: failure proves nothing, and success is always verified.

import * as X from "../expr.js";
import * as N from "../num.js";
import { diff } from "./diff.js";
import { canon, evalD, checkAntiderivative } from "./int-util.js";
import { recognizeRational } from "./int-rational.js";

function kernels(f, x) {
  const out = new Set();
  const walk = (w) => {
    if (X.freeOf(w, x)) return;
    if (w.k === "fn") {
      out.add(w);
      const u = w.args[0];
      if (w.name === "sin") out.add(X.fn("cos", u));
      if (w.name === "cos") out.add(X.fn("sin", u));
      if (w.name === "sinh") out.add(X.fn("cosh", u));
      if (w.name === "cosh") out.add(X.fn("sinh", u));
    } else if (w.k === "pow") {
      const [b, e] = w.args;
      if (!X.freeOf(e, x)) out.add(w);
      else if (X.isNum(e) && e.v.d !== 1n) out.add(canon(X.pow(b, X.num(N.Q(1n, e.v.d)))));
    }
    for (const a of w.args) walk(a);
  };
  walk(f);
  return [...out].map((k) => canon(k)).filter((k) => k !== X.UNDEF);
}

function degX(f, x) {
  let d = 0;
  const walk = (w) => {
    if (w.k === "pow" && w.args[0] === x && X.isInt(w.args[1])) d = Math.max(d, Number(w.args[1].v.n));
    else if (w === x) d = Math.max(d, 1);
    for (const a of w.args) walk(a);
  };
  walk(f);
  return d;
}

// least squares A c = b by column-pivoted modified Gram-Schmidt (rank revealing); dependent columns get 0
function lsq(A, b) {
  const m = A.length, n = A[0].length;
  const cols = Array.from({ length: n }, (_, j) => A.map((r) => r[j]));
  const Qs = [], sel = [], Rrows = [];
  const used = new Array(n).fill(false);
  const work = cols.map((c) => c.slice());
  const dot = (u, v) => { let s = 0; for (let k = 0; k < m; k++) s += u[k] * v[k]; return s; };
  for (let step = 0; step < Math.min(m, n); step++) {
    let best = -1, bn = 0;
    for (let j = 0; j < n; j++) if (!used[j]) { const nr = Math.sqrt(dot(work[j], work[j])); if (nr > bn) { bn = nr; best = j; } }
    if (best < 0 || bn < 1e-9) break;
    used[best] = true;
    const q = work[best].map((v) => v / bn);
    // re-orthogonalise for stability
    for (const q2 of Qs) { const s = dot(q, q2); for (let k = 0; k < m; k++) q[k] -= s * q2[k]; }
    const nq = Math.sqrt(dot(q, q));
    for (let k = 0; k < m; k++) q[k] /= nq;
    Qs.push(q); sel.push(best);
    for (let j = 0; j < n; j++) if (!used[j]) { const s = dot(q, work[j]); for (let k = 0; k < m; k++) work[j][k] -= s * q[k]; }
  }
  // R = Q^T A[:, sel] (upper triangular), solve R c = Q^T b
  const r = sel.length;
  for (let i = 0; i < r; i++) Rrows.push(sel.map((j) => dot(Qs[i], cols[j])));
  const qb = Qs.map((q) => dot(q, b));
  const cs = new Array(r).fill(0);
  for (let i = r - 1; i >= 0; i--) { let s = qb[i]; for (let k = i + 1; k < r; k++) s -= Rrows[i][k] * cs[k]; cs[i] = s / Rrows[i][i]; }
  const c = new Array(n).fill(0);
  sel.forEach((j, i) => { c[j] = cs[i]; });
  // residual
  let res = 0, nb = 0;
  for (let k = 0; k < m; k++) { let s = 0; for (let j = 0; j < n; j++) s += A[k][j] * c[j]; res += (s - b[k]) ** 2; nb += b[k] ** 2; }
  if (Math.sqrt(res) > 1e-7 * Math.max(1, Math.sqrt(nb))) return null;
  return c;
}

// continued-fraction rational approximation within a relative tolerance
function ratApprox(v, maxDen, tol) {
  if (!Number.isFinite(v)) return null;
  const sgn = v < 0 ? -1n : 1n;
  let z = Math.abs(v), h0 = 0n, h1 = 1n, k0 = 1n, k1 = 0n;
  for (let i = 0; i < 30; i++) {
    const a = Math.floor(z);
    if (a > 1e12) break;
    const A = BigInt(a);
    [h0, h1] = [h1, A * h1 + h0];
    [k0, k1] = [k1, A * k1 + k0];
    if (k1 > BigInt(maxDen)) return null;
    if (Math.abs(Number(h1) / Number(k1) - Math.abs(v)) <= tol * Math.max(1, Math.abs(v))) return N.Q(sgn * h1, k1);
    const fr = z - a;
    if (fr < 1e-12) break;
    z = 1 / fr;
  }
  return null;
}
void recognizeRational;

export function normanIntegrate(f, x, opts = {}) {
  const ks = kernels(f, x);
  if (!ks.length || ks.length > 7) return null;
  const dmax = Math.min(degX(f, x) + 1, 4);
  const prods = [X.ONE];
  for (let i = 0; i < ks.length; i++) {
    prods.push(ks[i]);
    for (let j = i; j < ks.length; j++) prods.push(canon(X.mul(ks[i], ks[j])));
  }
  const monos = [];
  for (const p of [...new Set(prods)]) for (let d = 0; d <= dmax; d++) {
    const m = canon(X.mul(p, X.pow(x, X.num(d))));
    if (m !== X.ONE && !X.freeOf(m, x)) monos.push(m);
  }
  const uniq = [...new Set(monos)];
  if (typeof process !== "undefined" && process.env && process.env.QV_NORMAN) console.log("kernels", ks.length, "monos", uniq.length);
  if (uniq.length > 90) return null;
  const ders = [];
  for (const m of uniq) {
    if (opts.tick) opts.tick();
    try { ders.push(canon(diff(m, x))); } catch (e) { if (e && e.code) return null; throw e; }
  }
  // sample points where everything is finite
  const pts = [];
  const cand = [];
  for (let i = 0; i < 400; i++) cand.push(-3.1 + 6.2 * ((i * 0.6180339887498949) % 1));
  for (const t of cand) {
    if (pts.length >= uniq.length + 25) break;
    const fv = evalD(f, { [x.name]: t });
    if (!Number.isFinite(fv)) continue;
    const row = ders.map((d) => evalD(d, { [x.name]: t }));
    if (row.some((v) => !Number.isFinite(v))) continue;
    pts.push({ t, fv, row });
  }
  if (pts.length < uniq.length + 5) return null;
  // column scaling for conditioning
  const scale = uniq.map((_, j) => Math.max(1e-300, Math.sqrt(pts.reduce((s, p) => s + p.row[j] * p.row[j], 0))));
  const A = pts.map((p) => p.row.map((v, j) => v / scale[j]));
  const c = lsq(A, pts.map((p) => p.fv));
  if (!c) return null;
  const terms = [];
  const cmax = Math.max(1, ...c.map((v, j) => Math.abs(v / scale[j])));
  for (let j = 0; j < uniq.length; j++) {
    const cj = c[j] / scale[j];
    if (Math.abs(cj) < 1e-6 * cmax) continue;
    const q = ratApprox(cj, 1000, 1e-6);
    if (typeof process !== "undefined" && process.env && process.env.QV_NORMAN) console.log("norman", j, cj, q && N.toString(q));
    if (!q) return null;
    terms.push(X.mul(X.num(q), uniq[j]));
  }
  if (!terms.length) return null;
  const F = canon(X.add(...terms));
  const chk = checkAntiderivative(F, f, x, { points: 8 });
  return chk.ok === true ? F : null;
}
