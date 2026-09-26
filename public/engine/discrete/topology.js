// Simplicial homology over Z and Euler characteristics.
//
//   homology([facet], [facet], ...)       a simplicial complex by its maximal faces
//   homology(vlabel-coded name, facets)   (named surfaces arrive as explicit triangulations)
//   eulerchar(V, E, F)                    V - E + F
//
// H_k = Z^(b_k) ⊕ (torsion) from the Smith normal form of the boundary matrices.
// Independent checks: the boundary of a boundary is zero; Betti numbers from rational ranks
// (Gaussian elimination over Q, not the Smith form); the Euler-Poincare formula
// Σ(-1)^k b_k = Σ(-1)^k f_k; the universal coefficient theorem mod p for small primes and every
// prime in the torsion (dim H_k(X; F_p) = b_k + t_k(p) + t_(k-1)(p), with ranks computed mod p);
// and, for a named surface, the classification of surfaces (every edge in two triangles or on the
// boundary, vertex links are circles or arcs, connectedness, orientability, Euler characteristic).

import { refuse, ansNum, ansText, check, step, N, babs } from "./util.js";
import { intOf, labelOf, listOf, isList } from "./decode.js";

function complexOf(args) {
  const facets = [];
  for (const a of args) {
    if (!isList(a)) throw refuse("give the maximal faces as lists of vertices, for example homology([1,2,3], [2,3,4])");
    const vs = [...new Set(listOf(a).map(labelOf))];
    if (!vs.length) throw refuse("a face needs at least one vertex");
    facets.push(vs);
  }
  if (!facets.length) throw refuse("the complex has no faces");
  const labels = [...new Set(facets.flat())].sort((a, b) => (/^\d+$/.test(a) && /^\d+$/.test(b) ? Number(a) - Number(b) : a < b ? -1 : a > b ? 1 : 0));
  const idx = new Map(labels.map((l, i) => [l, i]));
  const top = Math.max(...facets.map((f) => f.length - 1));
  if (top > 6) throw refuse("complexes up to dimension 6 are supported");
  // all faces by dimension (sorted vertex index tuples)
  const faces = Array.from({ length: top + 1 }, () => new Map());
  let total = 0;
  for (const f of facets) {
    const ids = f.map((l) => idx.get(l)).sort((a, b) => a - b);
    for (let mask = 1; mask < 1 << ids.length; mask++) {
      const s = ids.filter((_, i) => mask & (1 << i));
      const key = s.join(",");
      if (!faces[s.length - 1].has(key)) { faces[s.length - 1].set(key, s); if (++total > 20000) throw refuse("the complex has too many faces"); }
    }
  }
  const lists = faces.map((m) => [...m.values()].sort((a, b) => { for (let i = 0; i < a.length; i++) if (a[i] !== b[i]) return a[i] - b[i]; return 0; }));
  return { labels, facets, top, faces: lists };
}
// boundary matrix d_k : C_k -> C_(k-1), rows = (k-1)-faces, columns = k-faces
function boundary(cx, k) {
  const rows = cx.faces[k - 1], cols = cx.faces[k];
  const ri = new Map(rows.map((s, i) => [s.join(","), i]));
  const M = rows.map(() => Array(cols.length).fill(0n));
  cols.forEach((s, j) => { for (let i = 0; i < s.length; i++) { const f = s.filter((_, t) => t !== i); M[ri.get(f.join(","))][j] += i % 2 ? -1n : 1n; } });
  return M;
}
// Smith normal form diagonal (nonzero invariant factors)
function smith(M0) {
  const M = M0.map((r) => r.slice());
  const m = M.length, n = m ? M[0].length : 0;
  const diag = [];
  let t = 0;
  let guard = 0;
  while (t < m && t < n) {
    // pivot: smallest nonzero |entry| in the remaining block
    let pi = -1, pj = -1, best = 0n;
    for (let i = t; i < m; i++) for (let j = t; j < n; j++) { const v = babs(M[i][j]); if (v && (!best || v < best)) { best = v; pi = i; pj = j; } }
    if (pi < 0) break;
    [M[t], M[pi]] = [M[pi], M[t]];
    for (const r of M) [r[t], r[pj]] = [r[pj], r[t]];
    for (;;) {
      if (++guard > 5e6) throw refuse("the Smith normal form computation is too large");
      let changed = false;
      for (let i = t + 1; i < m; i++) if (M[i][t]) { const q = M[i][t] / M[t][t]; for (let j = t; j < n; j++) M[i][j] -= q * M[t][j]; if (M[i][t]) { [M[t], M[i]] = [M[i], M[t]]; changed = true; } }
      for (let j = t + 1; j < n; j++) if (M[t][j]) { const q = M[t][j] / M[t][t]; for (let i = t; i < m; i++) M[i][j] -= q * M[i][t]; if (M[t][j]) { for (const r of M) [r[t], r[j]] = [r[j], r[t]]; changed = true; } }
      if (changed) continue;
      // divisibility condition: d_t divides every remaining entry
      let bad = -1;
      for (let i = t + 1; i < m && bad < 0; i++) for (let j = t + 1; j < n; j++) if (M[i][j] % M[t][t]) { bad = i; break; }
      if (bad < 0) break;
      for (let j = t; j < n; j++) M[t][j] += M[bad][j];
    }
    diag.push(babs(M[t][t]));
    t++;
  }
  return diag;
}
function rankQ(M) { // rational Gaussian elimination
  const A = M.map((r) => r.map((v) => N.Q(v)));
  let rank = 0; const m = A.length, n = m ? A[0].length : 0;
  for (let c = 0; c < n && rank < m; c++) {
    let p = rank; while (p < m && N.isZero(A[p][c])) p++;
    if (p === m) continue;
    [A[rank], A[p]] = [A[p], A[rank]];
    for (let i = rank + 1; i < m; i++) if (!N.isZero(A[i][c])) { const f = N.div(A[i][c], A[rank][c]); for (let j = c; j < n; j++) A[i][j] = N.sub(A[i][j], N.mul(f, A[rank][j])); }
    rank++;
  }
  return rank;
}
function rankP(M, p) {
  const A = M.map((r) => r.map((v) => ((v % p) + p) % p));
  let rank = 0; const m = A.length, n = m ? A[0].length : 0;
  for (let c = 0; c < n && rank < m; c++) {
    let q = rank; while (q < m && !A[q][c]) q++;
    if (q === m) continue;
    [A[rank], A[q]] = [A[q], A[rank]];
    let inv = 1n; { let b = A[rank][c], e = p - 2n; while (e > 0n) { if (e & 1n) inv = inv * b % p; b = b * b % p; e >>= 1n; } }
    for (let i = rank + 1; i < m; i++) if (A[i][c]) { const f = A[i][c] * inv % p; for (let j = c; j < n; j++) A[i][j] = ((A[i][j] - f * A[rank][j]) % p + p) % p; }
    rank++;
  }
  return rank;
}
const groupText = (b, tors) => { const parts = []; if (b === 1) parts.push("Z"); else if (b > 1) parts.push(`Z^${b}`); for (const d of tors) parts.push(`Z/${d}`); return parts.length ? parts.join(" ⊕ ") : "0"; };
function primeFactors(n) { const out = []; for (let p = 2n; p * p <= n; p++) if (n % p === 0n) { out.push(p); while (n % p === 0n) n /= p; } if (n > 1n) out.push(n); return out; }

// surface recognition (for named spaces)
function surfaceCheck(cx, expect) {
  if (cx.top !== 2) return { ok: false, detail: "not 2-dimensional" };
  const tris = cx.faces[2], edges = cx.faces[1];
  if (cx.facets.some((f) => f.length !== 3)) return { ok: false, detail: "not pure" };
  const edgeTris = new Map(edges.map((e) => [e.join(","), []]));
  tris.forEach((t, i) => { for (const [a, b] of [[t[0], t[1]], [t[1], t[2]], [t[0], t[2]]]) edgeTris.get(`${a},${b}`).push(i); });
  const counts = [...edgeTris.values()].map((l) => l.length);
  if (counts.some((c) => c < 1 || c > 2)) return { ok: false, detail: "some edge is not in one or two triangles" };
  const boundaryEdges = [...edgeTris.entries()].filter(([, l]) => l.length === 1).map(([k]) => k.split(",").map(Number));
  // vertex links: a single cycle (interior) or a single path (boundary)
  for (let v = 0; v < cx.labels.length; v++) {
    const linkEdges = tris.filter((t) => t.includes(v)).map((t) => t.filter((x) => x !== v));
    const deg = new Map(); for (const [a, b] of linkEdges) { deg.set(a, (deg.get(a) || 0) + 1); deg.set(b, (deg.get(b) || 0) + 1); }
    const ends = [...deg.values()].filter((d) => d === 1).length;
    if ([...deg.values()].some((d) => d > 2) || (ends !== 0 && ends !== 2)) return { ok: false, detail: "a vertex link is not a circle or an arc" };
    // connected link
    const adj = new Map(); for (const [a, b] of linkEdges) { (adj.get(a) || adj.set(a, []).get(a)).push(b); (adj.get(b) || adj.set(b, []).get(b)).push(a); }
    const start = linkEdges[0][0]; const seen = new Set([start]); const st = [start];
    while (st.length) { const x = st.pop(); for (const y of adj.get(x)) if (!seen.has(y)) { seen.add(y); st.push(y); } }
    if (seen.size !== deg.size) return { ok: false, detail: "a vertex link is disconnected" };
  }
  // connected, orientable (consistent orientation propagation)
  const orient = Array(tris.length).fill(0); orient[0] = 1; const q = [0]; let orientable = true; let reached = 1;
  const dirEdge = (t, o) => { const [a, b, c] = t; const es = [[a, b], [b, c], [c, a]]; return o === 1 ? es : es.map(([x, y]) => [y, x]); };
  while (q.length) {
    const i = q.shift();
    for (const [x, y] of dirEdge(tris[i], orient[i])) {
      const key = x < y ? `${x},${y}` : `${y},${x}`;
      for (const j of edgeTris.get(key)) {
        if (j === i) continue;
        // neighbour must traverse the edge as (y, x)
        const need = dirEdge(tris[j], 1).some(([u, w]) => u === y && w === x) ? 1 : -1;
        if (!orient[j]) { orient[j] = need; reached++; q.push(j); } else if (orient[j] !== need) orientable = false;
      }
    }
  }
  const V = cx.faces[0].length, E = edges.length, F = tris.length, chi = V - E + F;
  // boundary components = cycles among boundary edges
  const badj = new Map(); for (const [a, b] of boundaryEdges) { (badj.get(a) || badj.set(a, []).get(a)).push(b); (badj.get(b) || badj.set(b, []).get(b)).push(a); }
  let bcomp = 0; const bseen = new Set();
  for (const v of badj.keys()) { if (bseen.has(v)) continue; bcomp++; const st = [v]; bseen.add(v); while (st.length) { const x = st.pop(); for (const y of badj.get(x)) if (!bseen.has(y)) { bseen.add(y); st.push(y); } } }
  const ok = reached === F && orientable === expect.orientable && chi === expect.chi && bcomp === expect.boundary;
  return { ok, detail: `a connected ${orientable ? "orientable" : "non-orientable"} surface with χ = ${chi} and ${bcomp} boundary circle(s), which by the classification of surfaces is the ${expect.name}` };
}
const NAMED = {
  torus: { orientable: true, chi: 0, boundary: 0, name: "torus" }, rp2: { orientable: false, chi: 1, boundary: 0, name: "real projective plane" },
  klein: { orientable: false, chi: 0, boundary: 0, name: "Klein bottle" }, mobius: { orientable: false, chi: 0, boundary: 1, name: "Mobius band" },
  sphere: { orientable: true, chi: 2, boundary: 0, name: "2-sphere" }, disk: { orientable: true, chi: 1, boundary: 1, name: "disk" }, annulus: { orientable: true, chi: 0, boundary: 2, name: "annulus" },
};

function cmdHomology(args) {
  let named = null;
  if (args[0] && args[0].k === "fn" && args[0].name === "vlabel") { named = labelOf(args[0]); args = args.slice(1); }
  const cx = complexOf(args);
  const f = cx.faces.map((l) => l.length);
  const D = [null]; for (let k = 1; k <= cx.top; k++) D.push(boundary(cx, k));
  const snf = D.map((M) => (M ? smith(M) : null));
  const rank = (k) => (k >= 1 && k <= cx.top ? snf[k].length : 0);
  const betti = [], tors = [];
  for (let k = 0; k <= cx.top; k++) { betti.push(f[k] - rank(k) - rank(k + 1)); tors.push(k + 1 <= cx.top ? snf[k + 1].filter((d) => d > 1n) : []); }
  const chi = f.reduce((s, x, k) => s + (k % 2 ? -x : x), 0);
  const answers = [ansText("betti numbers", betti.join(", ")), ansNum("euler characteristic", chi)];
  betti.forEach((b, k) => answers.push(ansText(`H${k}`, groupText(b, tors[k]))));
  answers.push(ansText("face counts", f.map((x, k) => `f${k} = ${x}`).join(", ")));
  return {
    answers,
    steps: [step("top.faces", "List every face of the complex", f.map((x, k) => `${x} face(s) of dimension ${k}`).join(", ") + "."),
      step("top.boundary", "Build the boundary matrices ∂_k with alternating signs", "∂[v0 ... vk] = Σ (-1)^i [v0 ... v̂i ... vk]."),
      step("top.snf", "Smith normal form of each ∂_k", "H_k = Z^(f_k - rank ∂_k - rank ∂_(k+1)) ⊕ (torsion from the invariant factors of ∂_(k+1) greater than 1)."),
      step("top.result", "Homology", betti.map((b, k) => `H${k} = ${groupText(b, tors[k])}`).join(", ") + `; χ = ${chi}.`)],
    checks: () => {
      const cs = [];
      // ∂∂ = 0
      let zero = true;
      for (let k = 2; k <= cx.top; k++) { const A = D[k - 1], B = D[k]; for (let i = 0; i < A.length && zero; i++) for (let j = 0; j < B[0].length; j++) { let s = 0n; for (let t = 0; t < B.length; t++) s += A[i][t] * B[t][j]; if (s) { zero = false; break; } } }
      cs.push(check("∂∂ = 0", zero, "composing consecutive boundary matrices gives zero"));
      const rq = D.map((M) => (M ? rankQ(M) : 0)); rq.push(0);
      const bq = f.map((x, k) => x - (k >= 1 ? rq[k] : 0) - (k + 1 <= cx.top ? rq[k + 1] : 0));
      cs.push(check("rational ranks", bq.every((b, k) => b === betti[k]), `ranks over Q give Betti numbers ${bq.join(", ")}`));
      cs.push(check("Euler-Poincare", betti.reduce((s, b, k) => s + (k % 2 ? -b : b), 0) === chi, `Σ(-1)^k b_k = ${chi} = Σ(-1)^k f_k`));
      const primes = new Set([2n, 3n, 5n, 7n]); tors.flat().forEach((d) => primeFactors(d).forEach((p) => primes.add(p)));
      let uct = true;
      for (const p of primes) {
        const rp = D.map((M) => (M ? rankP(M, p) : 0));
        for (let k = 0; k <= cx.top; k++) {
          const dimP = f[k] - (k >= 1 ? rp[k] : 0) - (k + 1 <= cx.top ? rp[k + 1] : 0);
          const t = (j) => (j >= 0 ? tors[j].filter((d) => d % p === 0n).length : 0);
          if (dimP !== betti[k] + t(k) + t(k - 1)) uct = false;
        }
      }
      cs.push(check("universal coefficients", uct, `homology with F_p coefficients (ranks mod p, p in {${[...primes].join(", ")}}) matches the torsion`));
      if (named && NAMED[named]) { const s = surfaceCheck(cx, NAMED[named]); cs.push(check("surface", s.ok, s.detail)); }
      return cs;
    },
  };
}
function cmdEulerChar(args) {
  const xs = args.map((a) => intOf(a, "a face count"));
  if (!xs.length || xs.some((x) => x < 0n)) throw refuse("face counts must be non-negative integers");
  const chi = xs.reduce((s, x, k) => (k % 2 ? s - x : s + x), 0n);
  return {
    answers: [ansNum("euler characteristic", chi)],
    steps: [step("top.euler", "χ = V - E + F" + (xs.length > 3 ? " - ..." : ""), `${xs.join(" - ").replace(/- (\d+) - (\d+)/, "- $1 + $2")} = ${chi}.`)],
    checks: () => {
      const evens = xs.filter((_, k) => k % 2 === 0).reduce((a, b) => a + b, 0n), odds = xs.filter((_, k) => k % 2 === 1).reduce((a, b) => a + b, 0n);
      return [check("alternating sum", evens - odds === chi, `(sum of even-dimensional counts) - (sum of odd-dimensional counts) = ${evens} - ${odds}`)];
    },
  };
}

export const TOPOLOGY_HANDLERS = { homology: cmdHomology, eulerchar: cmdEulerChar };
