// Graph theory on explicit small graphs.
//
// Graph arguments (canonical call forms written by discrete/lang.js):
//   edgelist([u, v], [u, v, w], ..., vertexset(a, b))   undirected (multi)graph, optional weights
//   arclist(...)                                          directed version
//   adjmatrix([[...]])                                    adjacency / weight matrix (vertices 1..n)
//   completegraph(n) completebipartite(m, n) cyclegraph(n) pathgraph(n) wheelgraph(n) hypercubegraph(d) petersengraph(5, 2)
//
// Every answer carries an independent certificate check:
//   degrees            adjacency-matrix row sums + handshake lemma
//   components         BFS partition vs union-find, and no edge between parts
//   shortest path      path validity + potential (dual) feasibility d(v) <= d(u) + w(u, v)
//   spanning tree      spanning + cycle optimality condition for every non-tree edge (and Prim cross-check)
//   spanning trees     brute-force enumeration (small) or a different cofactor by exact rational elimination
//   bipartite          2-colouring or an odd closed walk
//   Euler              the trail itself, or the parity / connectivity obstruction
//   Hamiltonian        the cycle / path itself, or Held-Karp subset DP (a different algorithm)
//   chromatic          a colouring + P(k - 1) = 0 by Whitney's subgraph expansion (or a clique)
//   chromatic poly     Whitney's expansion vs deletion-contraction, or colour counts at k = 0..n
//   planarity          a genus-0 rotation system (faces traced), or Euler / girth edge bound, or a Kuratowski subdivision
//   max flow           feasible flow + cut of equal capacity
//   topological sort   every arc points forward, or an explicit directed cycle
//   isomorphism        an explicit edge-preserving bijection, or a differing invariant, or brute force over all bijections

import { refuse, budget, ansNum, ansText, ansYes, ansTree, check, step, N, X, qstr } from "./util.js";
import { intOf, ratOf, labelOf, listOf } from "./decode.js";
import { simplify } from "../simplify.js";

const MAXV = 60;

// ---------------------------------------------------------------- building graphs
function mkGraph(directed, labels, edges) {
  const index = new Map(labels.map((l, i) => [l, i]));
  return { directed, V: labels, index, E: edges.map((e, id) => ({ ...e, id })), weighted: edges.some((e) => e.w !== null) };
}
function named(u) {
  const a = u.args.map((t) => Number(intOf(t, "a size")));
  const cap = (n) => { if (!(n >= 1 && n <= MAXV)) throw refuse(`graph size must be between 1 and ${MAXV}`); return n; };
  const L = (i) => String(i);
  const edges = [];
  let labels = [];
  switch (u.name) {
    case "completegraph": { const n = cap(a[0]); labels = Array.from({ length: n }, (_, i) => L(i + 1)); for (let i = 1; i <= n; i++) for (let j = i + 1; j <= n; j++) edges.push({ u: L(i), v: L(j), w: null }); break; }
    case "completebipartite": { const [m, n] = [cap(a[0]), cap(a[1])]; cap(m + n); labels = Array.from({ length: m + n }, (_, i) => L(i + 1)); for (let i = 1; i <= m; i++) for (let j = m + 1; j <= m + n; j++) edges.push({ u: L(i), v: L(j), w: null }); break; }
    case "cyclegraph": { const n = cap(a[0]); if (n < 3) throw refuse("a cycle needs at least 3 vertices"); labels = Array.from({ length: n }, (_, i) => L(i + 1)); for (let i = 1; i <= n; i++) edges.push({ u: L(i), v: L((i % n) + 1), w: null }); break; }
    case "pathgraph": { const n = cap(a[0]); labels = Array.from({ length: n }, (_, i) => L(i + 1)); for (let i = 1; i < n; i++) edges.push({ u: L(i), v: L(i + 1), w: null }); break; }
    case "wheelgraph": { // W_n: an n-cycle plus a hub (n + 1 vertices, Rosen's convention)
      const n = cap(a[0]); if (n < 3) throw refuse("a wheel needs a cycle of at least 3 vertices"); cap(n + 1);
      labels = Array.from({ length: n + 1 }, (_, i) => L(i)); for (let i = 1; i <= n; i++) { edges.push({ u: L(i), v: L((i % n) + 1), w: null }); edges.push({ u: L(0), v: L(i), w: null }); }
      break;
    }
    case "hypercubegraph": { const d = a[0]; if (!(d >= 1 && d <= 5)) throw refuse("hypercube dimension must be 1 to 5"); const n = 1 << d; labels = Array.from({ length: n }, (_, i) => i.toString(2).padStart(d, "0")); for (let i = 0; i < n; i++) for (let b = 0; b < d; b++) { const j = i ^ (1 << b); if (i < j) edges.push({ u: labels[i], v: labels[j], w: null }); } break; }
    case "petersengraph": { // generalized Petersen graph GP(n, k); GP(5, 2) is the Petersen graph
      const [n, k] = [cap(a[0] || 5), a[1] || 2]; cap(2 * n);
      labels = Array.from({ length: 2 * n }, (_, i) => L(i));
      for (let i = 0; i < n; i++) { edges.push({ u: L(i), v: L((i + 1) % n), w: null }); edges.push({ u: L(i), v: L(n + i), w: null }); if (n + i < n + ((i + k) % n)) edges.push({ u: L(n + i), v: L(n + ((i + k) % n)), w: null }); else if (k * 2 !== n) edges.push({ u: L(n + ((i + k) % n)), v: L(n + i), w: null }); }
      // dedupe inner edges
      const seen = new Set(); const out = [];
      for (const e of edges) { const key = [e.u, e.v].sort().join("|"); if (!seen.has(key)) { seen.add(key); out.push(e); } }
      return mkGraph(false, labels, out);
    }
    default: throw refuse(`unknown graph family ${u.name}`);
  }
  return mkGraph(false, labels, edges);
}
export function graphOf(u) {
  if (!u || u.k !== "fn") throw refuse("expected a graph: an edge list such as {1-2, 2-3}, an adjacency matrix, or a named graph such as K5");
  if (["completegraph", "completebipartite", "cyclegraph", "pathgraph", "wheelgraph", "hypercubegraph", "petersengraph"].includes(u.name)) return named(u);
  if (u.name === "adjmatrix") {
    const rows = listOf(u.args[0], "an adjacency matrix").map((r) => listOf(r, "a matrix row").map((c) => ratOf(c)));
    const n = rows.length;
    if (!n || rows.some((r) => r.length !== n || r.some((c) => !c))) throw refuse("the adjacency matrix must be square with numeric entries");
    if (n > MAXV) throw refuse("graph too large");
    const sym = rows.every((r, i) => r.every((c, j) => N.eq(c, rows[j][i])));
    const binary = rows.every((r) => r.every((c) => N.isZero(c) || N.isOne(c)));
    const labels = Array.from({ length: n }, (_, i) => String(i + 1));
    const edges = [];
    for (let i = 0; i < n; i++) for (let j = sym ? i : 0; j < n; j++) {
      const c = rows[i][j];
      if (N.isZero(c)) continue;
      edges.push({ u: labels[i], v: labels[j], w: binary ? null : c });
    }
    return mkGraph(!sym, labels, edges);
  }
  if (u.name !== "edgelist" && u.name !== "arclist") throw refuse("expected a graph");
  const labels = [], edges = [];
  const see = (l) => { if (!labels.includes(l)) labels.push(l); };
  for (const a of u.args) {
    if (a.k === "fn" && a.name === "vertexset") { a.args.forEach((v) => see(labelOf(v))); continue; }
    const parts = listOf(a, "an edge [u, v] or [u, v, weight]");
    if (parts.length !== 2 && parts.length !== 3) throw refuse("an edge is [u, v] or [u, v, weight]");
    const [p, q] = [labelOf(parts[0]), labelOf(parts[1])];
    see(p); see(q);
    let w = null;
    if (parts.length === 3) { w = ratOf(parts[2]); if (!w) throw refuse("edge weights must be numbers"); }
    edges.push({ u: p, v: q, w });
  }
  if (labels.length > MAXV) throw refuse("graph too large");
  if (!labels.length) throw refuse("the graph has no vertices");
  return mkGraph(u.name === "arclist", labels, edges);
}

// ---------------------------------------------------------------- helpers
const W = (e) => (e.w === null ? N.ONE : e.w);
const ix = (G, l) => { const i = G.index.get(l); if (i === undefined) throw refuse(`vertex ${l} is not in the graph`); return i; };
function adjList(G, undirectedView = false) {
  const adj = G.V.map(() => []);
  for (const e of G.E) {
    const a = G.index.get(e.u), b = G.index.get(e.v);
    adj[a].push({ to: b, e });
    if (!G.directed || undirectedView) { if (a !== b || undirectedView) adj[b].push({ to: a, e }); }
  }
  return adj;
}
const simpleEdges = (G) => { const s = new Set(); for (const e of G.E) { const a = G.index.get(e.u), b = G.index.get(e.v); if (a !== b) s.add(a < b ? `${a},${b}` : `${b},${a}`); } return [...s].map((k) => k.split(",").map(Number)); };
const isSimple = (G) => !G.directed && G.E.every((e) => e.u !== e.v) && simpleEdges(G).length === G.E.length;
function bfsComponents(n, edgesIdx) { // independent BFS partition: array comp[v]
  const adj = Array.from({ length: n }, () => []);
  for (const [a, b] of edgesIdx) { adj[a].push(b); adj[b].push(a); }
  const comp = Array(n).fill(-1);
  let c = 0;
  for (let s = 0; s < n; s++) {
    if (comp[s] >= 0) continue;
    const q = [s]; comp[s] = c;
    while (q.length) { const v = q.shift(); for (const w of adj[v]) if (comp[w] < 0) { comp[w] = c; q.push(w); } }
    c++;
  }
  return { comp, count: c };
}
const edgeIdx = (G) => G.E.map((e) => [G.index.get(e.u), G.index.get(e.v)]);
const fmtQ = (q) => qstr(q);
const pathText = (G, vs) => vs.map((i) => G.V[i]).join(" -> ");

// ---------------------------------------------------------------- degrees
function cmdDegrees(args) {
  const G = graphOf(args[0]);
  const n = G.V.length;
  const indeg = Array(n).fill(0), outdeg = Array(n).fill(0), deg = Array(n).fill(0);
  for (const e of G.E) { const a = G.index.get(e.u), b = G.index.get(e.v); outdeg[a]++; indeg[b]++; deg[a]++; deg[b]++; }
  const answers = [];
  if (G.directed) {
    answers.push(ansText("in-degrees", G.V.map((l, i) => `${l}: ${indeg[i]}`).join(", ")), ansText("out-degrees", G.V.map((l, i) => `${l}: ${outdeg[i]}`).join(", ")));
  } else {
    answers.push(ansText("degrees", G.V.map((l, i) => `${l}: ${deg[i]}`).join(", ")), ansText("degree sequence", [...deg].sort((a, b) => b - a).join(", ")));
  }
  answers.push(ansNum("edges", G.E.length));
  return {
    answers, steps: [step("graph.degree", "Count edge endpoints at each vertex", G.directed ? "In-degree counts arcs arriving, out-degree counts arcs leaving." : "A loop adds 2 to the degree of its vertex.")],
    checks: () => {
      // independent: adjacency matrix built from scratch, row / column sums
      const A = Array.from({ length: n }, () => Array(n).fill(0));
      for (const e of G.E) { const a = G.V.indexOf(e.u), b = G.V.indexOf(e.v); A[a][b]++; if (!G.directed) { if (a !== b) A[b][a]++; else A[a][a]++; } }
      const rows = A.map((r) => r.reduce((s, x) => s + x, 0)), cols = A[0].map((_, j) => A.reduce((s, r) => s + r[j], 0));
      const ok1 = G.directed ? rows.every((r, i) => r === outdeg[i]) && cols.every((c, i) => c === indeg[i]) : rows.every((r, i) => r === deg[i]);
      const total = G.directed ? outdeg.reduce((s, x) => s + x, 0) : deg.reduce((s, x) => s + x, 0);
      const ok2 = G.directed ? total === G.E.length && indeg.reduce((s, x) => s + x, 0) === G.E.length : total === 2 * G.E.length;
      return [check("adjacency matrix", ok1, "row sums of the adjacency matrix equal the degrees"), check("handshake lemma", ok2, G.directed ? "in-degrees and out-degrees each sum to the number of arcs" : `the degrees sum to 2|E| = ${2 * G.E.length}`)];
    },
  };
}

// ---------------------------------------------------------------- components
function unionFind(n) { const p = Array.from({ length: n }, (_, i) => i); const f = (x) => (p[x] === x ? x : (p[x] = f(p[x]))); return { find: f, union: (a, b) => { a = f(a); b = f(b); if (a !== b) p[a] = b; return a !== b; } }; }
function cmdComponents(args) {
  const G = graphOf(args[0]);
  const n = G.V.length;
  const uf = unionFind(n);
  for (const [a, b] of edgeIdx(G)) uf.union(a, b);
  const groups = new Map();
  for (let v = 0; v < n; v++) { const r = uf.find(v); if (!groups.has(r)) groups.set(r, []); groups.get(r).push(v); }
  const comps = [...groups.values()];
  const answers = [ansNum("components", comps.length), ansYes("connected", comps.length === 1), ansText("component vertex sets", comps.map((c) => `{${c.map((v) => G.V[v]).join(", ")}}`).join(", "))];
  let scc = null;
  if (G.directed) {
    scc = tarjan(G);
    answers[0].label = "weakly connected components";
    answers[1].label = "weakly connected";
    answers.push(ansNum("strongly connected components", scc.length), ansYes("strongly connected", scc.length === 1));
    answers.push(ansText("strong component vertex sets", scc.map((c) => `{${c.map((v) => G.V[v]).join(", ")}}`).join(", ")));
  }
  return {
    answers, steps: [step("graph.components", "Merge the endpoints of every edge (union-find)", "Vertices end up in the same set exactly when a path joins them.")],
    checks: () => {
      const { comp, count } = bfsComponents(n, edgeIdx(G));
      const same = comps.every((c) => c.every((v) => comp[v] === comp[c[0]])) && count === comps.length;
      const crossing = G.E.some((e) => uf.find(G.index.get(e.u)) !== uf.find(G.index.get(e.v)));
      const cs = [check("BFS partition", same, `breadth-first search finds the same ${count} component(s)`), check("closed parts", !crossing, "no edge joins two different components")];
      if (scc) {
        // reachability matrix by Floyd-Warshall (boolean), mutual reachability = same strong component
        const R = Array.from({ length: n }, (_, i) => Array.from({ length: n }, (_, j) => i === j));
        for (const e of G.E) R[G.index.get(e.u)][G.index.get(e.v)] = true;
        for (let k = 0; k < n; k++) for (let i = 0; i < n; i++) if (R[i][k]) for (let j = 0; j < n; j++) if (R[k][j]) R[i][j] = true;
        const id = Array(n); scc.forEach((c, ci) => c.forEach((v) => { id[v] = ci; }));
        let ok = true;
        for (let i = 0; i < n; i++) for (let j = 0; j < n; j++) if ((R[i][j] && R[j][i]) !== (id[i] === id[j])) ok = false;
        cs.push(check("reachability matrix", ok, "mutual reachability (transitive closure) gives the same strong components"));
      }
      return cs;
    },
  };
}
function tarjan(G) {
  const n = G.V.length, adj = adjList(G);
  let idx = 0; const index = Array(n).fill(-1), low = Array(n).fill(0), on = Array(n).fill(false), st = [], out = [];
  const dfs = (v) => {
    index[v] = low[v] = idx++; st.push(v); on[v] = true;
    for (const { to } of adj[v]) { if (index[to] < 0) { dfs(to); low[v] = Math.min(low[v], low[to]); } else if (on[to]) low[v] = Math.min(low[v], index[to]); }
    if (low[v] === index[v]) { const c = []; let w; do { w = st.pop(); on[w] = false; c.push(w); } while (w !== v); out.push(c.sort((a, b) => a - b)); }
  };
  for (let v = 0; v < n; v++) if (index[v] < 0) dfs(v);
  return out;
}

// ---------------------------------------------------------------- shortest paths
function cmdShortestPath(args) {
  const G = graphOf(args[0]);
  const s = ix(G, labelOf(args[1])), t = ix(G, labelOf(args[2]));
  const n = G.V.length, adj = adjList(G);
  const negative = G.E.some((e) => N.isNeg(W(e)));
  if (negative && !G.directed) throw refuse("an undirected edge with negative weight makes a negative cycle; shortest paths are not defined");
  const dist = Array(n).fill(null), prev = Array(n).fill(-1);
  dist[s] = N.ZERO;
  let method;
  if (!negative) {
    method = "Dijkstra";
    const done = Array(n).fill(false);
    for (;;) {
      let v = -1;
      for (let i = 0; i < n; i++) if (!done[i] && dist[i] && (v < 0 || N.lt(dist[i], dist[v]))) v = i;
      if (v < 0) break;
      done[v] = true;
      for (const { to, e } of adj[v]) { const nd = N.add(dist[v], W(e)); if (!dist[to] || N.lt(nd, dist[to])) { dist[to] = nd; prev[to] = v; } }
    }
  } else {
    method = "Bellman-Ford";
    for (let r = 0; r < n; r++) {
      let changed = false;
      for (let v = 0; v < n; v++) if (dist[v]) for (const { to, e } of adj[v]) { const nd = N.add(dist[v], W(e)); if (!dist[to] || N.lt(nd, dist[to])) { dist[to] = nd; prev[to] = v; changed = true; } }
      if (!changed) break;
      if (r === n - 1 && changed) throw refuse("the graph has a negative cycle reachable from the start, so shortest paths are not defined");
    }
  }
  if (!dist[t]) {
    return {
      answers: [ansText("path", `no path from ${G.V[s]} to ${G.V[t]}`), ansYes("reachable", false)],
      steps: [step("graph.reach", "Search from the start vertex", `${G.V[t]} is never reached.`)],
      checks: () => {
        // independent: the set reachable by BFS is closed under outgoing edges and excludes t
        const seen = new Set([s]); const q = [s];
        while (q.length) { const v = q.shift(); for (const e of G.E) { const a = G.index.get(e.u), b = G.index.get(e.v); for (const [x, y] of G.directed ? [[a, b]] : [[a, b], [b, a]]) if (x === v && !seen.has(y)) { seen.add(y); q.push(y); } } }
        return [check("closed reachable set", !seen.has(t), `the ${seen.size} vertices reachable from ${G.V[s]} have no edge leaving the set and do not include ${G.V[t]}`)];
      },
    };
  }
  const path = [];
  for (let v = t; v >= 0; v = v === s ? -1 : prev[v]) path.unshift(v);
  const D = dist[t];
  return {
    answers: [ansNum("distance", D), ansText("path", pathText(G, path))],
    steps: [step("graph.sp", `${method}'s algorithm from ${G.V[s]}`, negative ? "Negative weights rule out Dijkstra; Bellman-Ford relaxes every edge n - 1 times." : "Repeatedly settle the closest unsettled vertex and relax its edges."),
      step("graph.sp.path", "Follow the predecessor links back from the target", `Distance ${fmtQ(D)} along ${pathText(G, path)}.`)],
    checks: () => {
      // certificate 1: the path exists and has the stated length
      let len = N.ZERO, ok = path[0] === s && path[path.length - 1] === t;
      for (let i = 0; ok && i + 1 < path.length; i++) {
        const cands = G.E.filter((e) => { const a = G.index.get(e.u), b = G.index.get(e.v); return (a === path[i] && b === path[i + 1]) || (!G.directed && b === path[i] && a === path[i + 1]); });
        if (!cands.length) ok = false; else len = N.add(len, cands.map(W).reduce((m, w) => (N.lt(w, m) ? w : m)));
      }
      // certificate 2: potentials satisfy every edge constraint, so no path is shorter than pot(t) - pot(s)
      let feasible = true;
      for (const e of G.E) {
        const a = G.index.get(e.u), b = G.index.get(e.v);
        for (const [x, y] of G.directed ? [[a, b]] : [[a, b], [b, a]]) if (dist[x] && (!dist[y] || N.lt(N.add(dist[x], W(e)), dist[y]))) feasible = false;
      }
      return [check("path", ok && N.eq(len, D), `the path is made of graph edges and has total weight ${fmtQ(len)}`),
        check("dual feasibility", feasible && N.isZero(dist[s]), "the distance labels satisfy d(v) <= d(u) + w(u, v) on every edge, so no path is shorter")];
    },
  };
}

// ---------------------------------------------------------------- minimum spanning tree
function cmdMST(args) {
  const G = graphOf(args[0]);
  if (G.directed) throw refuse("minimum spanning trees are defined for undirected graphs (a directed graph needs an arborescence)");
  const n = G.V.length;
  const order = [...G.E].sort((a, b) => N.cmp(W(a), W(b)) || a.id - b.id);
  const uf = unionFind(n), tree = [];
  for (const e of order) if (uf.union(G.index.get(e.u), G.index.get(e.v))) tree.push(e);
  const total = tree.reduce((s, e) => N.add(s, W(e)), N.ZERO);
  const forest = tree.length < n - 1;
  return {
    answers: [ansNum("total weight", total), ansText(forest ? "minimum spanning forest" : "edges", tree.map((e) => `${e.u}-${e.v}${e.w === null ? "" : ` (${fmtQ(e.w)})`}`).join(", "))],
    note: forest ? "The graph is disconnected, so this is a minimum spanning forest (one tree per component)." : "",
    steps: [step("graph.kruskal", "Kruskal's algorithm", "Take edges in order of weight, skipping any edge that would close a cycle.")],
    checks: () => {
      const cs = [];
      // spanning: same components as G
      const g = bfsComponents(n, edgeIdx(G)), tr = bfsComponents(n, tree.map((e) => [G.index.get(e.u), G.index.get(e.v)]));
      cs.push(check("spanning forest", tree.length === n - g.count && tr.count === g.count, `${tree.length} edges, acyclic, and it connects every component of the graph`));
      // cycle optimality: each non-tree edge is at least as heavy as every tree edge on the tree path between its ends
      const tadj = Array.from({ length: n }, () => []);
      for (const e of tree) { const a = G.index.get(e.u), b = G.index.get(e.v); tadj[a].push([b, W(e)]); tadj[b].push([a, W(e)]); }
      const maxOnPath = (a, b) => {
        const best = Array(n).fill(null), seen = Array(n).fill(false); const st = [[a, null]]; seen[a] = true;
        while (st.length) { const [v, m] = st.pop(); best[v] = m; for (const [w, wt] of tadj[v]) if (!seen[w]) { seen[w] = true; st.push([w, m === null || N.lt(m, wt) ? wt : m]); } }
        return best[b];
      };
      let ok = true;
      const inTree = new Set(tree.map((e) => e.id));
      for (const e of G.E) { if (inTree.has(e.id)) continue; const a = G.index.get(e.u), b = G.index.get(e.v); if (a === b) continue; const m = maxOnPath(a, b); if (m !== null && N.lt(W(e), m)) ok = false; }
      cs.push(check("cycle optimality", ok, "every non-tree edge is at least as heavy as each tree edge on the cycle it would close"));
      // cross-check: Prim's algorithm total
      let primTotal = N.ZERO; const inT = Array(n).fill(false);
      for (let r = 0; r < n; r++) {
        if (inT[r]) continue; inT[r] = true;
        for (;;) { let best = null; for (const e of G.E) { const a = G.index.get(e.u), b = G.index.get(e.v); if (inT[a] !== inT[b] && (!best || N.lt(W(e), W(best)))) best = e; } if (!best) break; inT[G.index.get(best.u)] = inT[G.index.get(best.v)] = true; primTotal = N.add(primTotal, W(best)); }
      }
      cs.push(check("Prim cross-check", N.eq(primTotal, total), `Prim's algorithm also gives total weight ${fmtQ(primTotal)}`));
      return cs;
    },
  };
}

// ---------------------------------------------------------------- matrix-tree theorem
function bareissDet(M) { // integer matrix, fraction-free elimination
  const A = M.map((r) => r.slice()); const n = A.length; let sign = 1n, prev = 1n;
  for (let k = 0; k < n - 1; k++) {
    if (A[k][k] === 0n) { let p = k + 1; while (p < n && A[p][k] === 0n) p++; if (p === n) return 0n; [A[k], A[p]] = [A[p], A[k]]; sign = -sign; }
    for (let i = k + 1; i < n; i++) for (let j = k + 1; j < n; j++) A[i][j] = (A[i][j] * A[k][k] - A[i][k] * A[k][j]) / prev;
    prev = A[k][k];
  }
  return n ? sign * A[n - 1][n - 1] : 1n;
}
function rationalDet(M) { // exact Gaussian elimination over Q (the independent route)
  const A = M.map((r) => r.map((v) => N.Q(v))); const n = A.length; let det = N.ONE;
  for (let k = 0; k < n; k++) {
    let p = k; while (p < n && N.isZero(A[p][k])) p++;
    if (p === n) return N.ZERO;
    if (p !== k) { [A[k], A[p]] = [A[p], A[k]]; det = N.neg(det); }
    det = N.mul(det, A[k][k]);
    for (let i = k + 1; i < n; i++) { const f = N.div(A[i][k], A[k][k]); if (N.isZero(f)) continue; for (let j = k; j < n; j++) A[i][j] = N.sub(A[i][j], N.mul(f, A[k][j])); }
  }
  return det;
}
function laplacian(G) {
  const n = G.V.length; const L = Array.from({ length: n }, () => Array(n).fill(0n));
  for (const e of G.E) { const a = G.index.get(e.u), b = G.index.get(e.v); if (a === b) continue; L[a][a]++; L[b][b]++; L[a][b]--; L[b][a]--; }
  return L;
}
const minor = (L, k) => L.filter((_, i) => i !== k).map((r) => r.filter((_, j) => j !== k));
function cmdSpanningTrees(args) {
  const G = graphOf(args[0]);
  if (G.directed) throw refuse("counting spanning trees is implemented for undirected graphs");
  const n = G.V.length, L = laplacian(G);
  const count = n === 1 ? 1n : bareissDet(minor(L, 0));
  return {
    answers: [ansNum("spanning trees", count)],
    steps: [step("graph.matrixtree", "Kirchhoff's matrix-tree theorem", "The number of spanning trees equals any cofactor of the Laplacian matrix L = D - A."),
      step("graph.matrixtree.det", "Delete the first row and column and take the determinant", `det = ${count}.`)],
    checks: () => {
      const m = G.E.filter((e) => e.u !== e.v).length;
      const combos = binomNum(m, n - 1);
      if (n > 1 && combos <= 300000) {
        // brute force: every (n-1)-edge subset that is acyclic is a spanning tree
        const E = G.E.filter((e) => e.u !== e.v).map((e) => [G.index.get(e.u), G.index.get(e.v)]);
        let cnt = 0n;
        const pick = [];
        const rec = (start) => {
          if (pick.length === n - 1) { const uf = unionFind(n); if (pick.every((i) => uf.union(E[i][0], E[i][1]))) cnt++; return; }
          for (let i = start; i <= E.length - (n - 1 - pick.length); i++) { pick.push(i); rec(i + 1); pick.pop(); }
        };
        rec(0);
        return [check("enumeration", cnt === count, `enumerating all ${combos} sets of ${n - 1} edges finds ${cnt} spanning trees`)];
      }
      const k = n - 1;
      const d2 = n === 1 ? N.ONE : rationalDet(minor(L, k));
      return [check("second cofactor", N.eq(d2, N.Q(count)), `the cofactor for the last vertex, by exact rational elimination, is also ${qstr(d2)}`)];
    },
  };
}
function binomNum(n, k) { if (k < 0 || k > n) return 0; let r = 1; for (let i = 0; i < k; i++) { r = r * (n - i) / (i + 1); if (r > 1e12) return Infinity; } return Math.round(r); }

// ---------------------------------------------------------------- bipartite
function cmdBipartite(args) {
  const G = graphOf(args[0]);
  const n = G.V.length, adj = adjList(G, true);
  const col = Array(n).fill(-1), par = Array(n).fill(-1);
  let odd = null;
  for (let s = 0; s < n && !odd; s++) {
    if (col[s] >= 0) continue;
    col[s] = 0; const q = [s];
    while (q.length && !odd) {
      const v = q.shift();
      for (const { to } of adj[v]) {
        if (col[to] < 0) { col[to] = 1 - col[v]; par[to] = v; q.push(to); }
        else if (col[to] === col[v]) {
          // odd closed walk: v -> root path + to -> root path + edge
          const up = (x) => { const p = [x]; while (par[x] >= 0) { x = par[x]; p.push(x); } return p; };
          const a = up(v), b = up(to);
          odd = [...a.reverse(), ...b.slice(0, -1)];
          break;
        }
      }
    }
  }
  if (odd) {
    // shorten to a closed walk v ... root ... to, v
    const walk = odd;
    return {
      answers: [ansYes("bipartite", false), ansText("odd closed walk", walk.map((v) => G.V[v]).join(" -> ") + " -> " + G.V[walk[0]])],
      steps: [step("graph.bipartite", "Two-colour by breadth-first search", "An edge joins two vertices of the same colour, which closes an odd cycle.")],
      checks: () => {
        const w = [...walk, walk[0]];
        const has = (a, b) => G.E.some((e) => { const x = G.index.get(e.u), y = G.index.get(e.v); return (x === a && y === b) || (x === b && y === a); });
        const edgesOk = w.every((v, i) => i === 0 || has(w[i - 1], v));
        return [check("odd closed walk", edgesOk && (w.length - 1) % 2 === 1, `a closed walk of odd length ${w.length - 1} exists, and a bipartite graph has none`)];
      },
    };
  }
  return {
    answers: [ansYes("bipartite", true), ansText("parts", `{${G.V.filter((_, i) => col[i] === 0).join(", ")}}, {${G.V.filter((_, i) => col[i] === 1).join(", ")}}`)],
    steps: [step("graph.bipartite", "Two-colour by breadth-first search", "No edge joins two vertices of the same colour.")],
    checks: () => [check("2-colouring", G.E.every((e) => col[G.index.get(e.u)] !== col[G.index.get(e.v)]), "every edge joins the two parts")],
  };
}

// ---------------------------------------------------------------- Euler paths and circuits
function cmdEuler(args) {
  const G = graphOf(args[0]);
  const n = G.V.length, m = G.E.length;
  if (!m) throw refuse("the graph has no edges");
  const deg = Array(n).fill(0), indeg = Array(n).fill(0), outdeg = Array(n).fill(0);
  for (const e of G.E) { const a = G.index.get(e.u), b = G.index.get(e.v); deg[a]++; deg[b]++; outdeg[a]++; indeg[b]++; }
  // edges must lie in one (weak) component
  const { comp } = bfsComponents(n, edgeIdx(G));
  const edgeComps = new Set(G.E.map((e) => comp[G.index.get(e.u)]));
  let circuit = false, path = false, start = G.index.get(G.E[0].u), reason = "";
  if (edgeComps.size > 1) reason = "the edges do not all lie in one connected component";
  else if (!G.directed) {
    const odd = deg.map((d, i) => (d % 2 ? i : -1)).filter((i) => i >= 0);
    circuit = odd.length === 0; path = odd.length === 0 || odd.length === 2;
    if (odd.length === 2) start = odd[0];
    reason = circuit ? "" : `${odd.length} vertices have odd degree (${odd.map((i) => G.V[i]).join(", ")})`;
  } else {
    const plus = [], minus = [], bad = [];
    for (let i = 0; i < n; i++) { const d = outdeg[i] - indeg[i]; if (d === 1) plus.push(i); else if (d === -1) minus.push(i); else if (d !== 0) bad.push(i); }
    circuit = !plus.length && !minus.length && !bad.length;
    path = circuit || (plus.length === 1 && minus.length === 1 && !bad.length);
    if (plus.length === 1) start = plus[0];
    reason = circuit ? "" : `in-degree and out-degree differ at ${[...plus, ...minus, ...bad].map((i) => G.V[i]).join(", ")}`;
  }
  let trail = null;
  if (path) {
    // Hierholzer
    const used = Array(m).fill(false), adj = adjList(G), ptr = Array(n).fill(0), st = [[start, -1]], out = [];
    while (st.length) {
      const [v] = st[st.length - 1];
      while (ptr[v] < adj[v].length && used[adj[v][ptr[v]].e.id]) ptr[v]++;
      if (ptr[v] === adj[v].length) { out.push(st.pop()); continue; }
      const { to, e } = adj[v][ptr[v]]; used[e.id] = true; st.push([to, e.id]);
    }
    trail = out.reverse();
  }
  const answers = [ansYes("euler circuit", circuit), ansYes("euler path", path)];
  if (trail) answers.push(ansText(circuit ? "circuit" : "trail", trail.map(([v]) => G.V[v]).join(" -> ")));
  if (!path) answers.push(ansText("reason", reason));
  return {
    answers,
    steps: [step("graph.euler", "Euler's theorem", G.directed ? "A connected digraph has an Euler circuit iff in-degree = out-degree everywhere; an Euler trail iff exactly one vertex has one extra out-arc and one has one extra in-arc." : "A connected graph has an Euler circuit iff every degree is even, and an Euler trail iff exactly 0 or 2 degrees are odd."),
      ...(trail ? [step("graph.hierholzer", "Hierholzer's algorithm builds the trail", "")] : [])],
    checks: () => {
      const cs = [];
      if (trail) {
        const ids = trail.slice(1).map(([, id]) => id);
        const each = ids.length === m && new Set(ids).size === m;
        let consecutive = true;
        for (let i = 1; i < trail.length; i++) { const e = G.E[trail[i][1]]; const a = G.index.get(e.u), b = G.index.get(e.v), p = trail[i - 1][0], q = trail[i][0]; if (!((a === p && b === q) || (!G.directed && a === q && b === p))) consecutive = false; }
        cs.push(check("trail", each && consecutive, `the walk uses each of the ${m} edges exactly once`));
        const closed = trail[0][0] === trail[trail.length - 1][0];
        if (circuit) cs.push(check("closed", closed, "it ends where it starts"));
        else {
          // no circuit: independent parity recount
          let oddCnt = 0; for (let i = 0; i < n; i++) { const d = G.E.reduce((s, e) => s + (e.u === G.V[i]) + (e.v === G.V[i]), 0); if (d % 2) oddCnt++; }
          const dirBad = G.directed && G.V.some((l) => G.E.filter((e) => e.u === l).length !== G.E.filter((e) => e.v === l).length);
          cs.push(check("no circuit", G.directed ? dirBad : oddCnt > 0, G.directed ? "some vertex has in-degree != out-degree, so no Euler circuit exists" : `${oddCnt} odd-degree vertices, so no Euler circuit exists`));
        }
      } else {
        // obstruction recomputed independently
        if (edgeComps.size > 1) {
          const uf = unionFind(n); for (const [a, b] of edgeIdx(G)) uf.union(a, b);
          cs.push(check("disconnected edges", new Set(G.E.map((e) => uf.find(G.index.get(e.u)))).size > 1, "edges in two components cannot be covered by one trail"));
        } else if (!G.directed) {
          let oddCnt = 0; for (const l of G.V) { const d = G.E.reduce((s, e) => s + (e.u === l) + (e.v === l), 0); if (d % 2) oddCnt++; }
          cs.push(check("odd degrees", oddCnt > 2, `${oddCnt} vertices of odd degree; a trail has at most 2 odd-degree vertices (its ends)`));
        } else {
          const imb = G.V.map((l) => G.E.filter((e) => e.u === l).length - G.E.filter((e) => e.v === l).length);
          const pos = imb.filter((d) => d > 0), neg = imb.filter((d) => d < 0);
          cs.push(check("degree imbalance", !(pos.length <= 1 && neg.length <= 1 && pos.every((d) => d === 1) && neg.every((d) => d === -1)), "the in/out-degree imbalance is too large for a single trail"));
        }
      }
      return cs;
    },
  };
}

// ---------------------------------------------------------------- Hamiltonian paths and cycles
function adjMatrixBool(G) { const n = G.V.length; const A = Array.from({ length: n }, () => Array(n).fill(false)); for (const e of G.E) { const a = G.index.get(e.u), b = G.index.get(e.v); if (a === b) continue; A[a][b] = true; if (!G.directed) A[b][a] = true; } return A; }
function hamSearch(A, cycle, limit = 5e6) {
  const n = A.length; const path = [0]; const used = Array(n).fill(false); let steps = 0;
  const starts = cycle ? [0] : [...Array(n).keys()];
  const rec = () => {
    if (++steps > limit) throw budget("Hamiltonian search too large");
    if (path.length === n) return !cycle || A[path[n - 1]][path[0]];
    const v = path[path.length - 1];
    for (let w = 0; w < n; w++) if (A[v][w] && !used[w]) { used[w] = true; path.push(w); if (rec()) return true; path.pop(); used[w] = false; }
    return false;
  };
  for (const s of starts) { path.length = 0; path.push(s); used.fill(false); used[s] = true; if (rec()) return path.slice(); }
  return null;
}
function heldKarp(A, cycle) { // bitmask DP: exists a Hamiltonian path (ending anywhere) / cycle through 0
  const n = A.length; if (n > 18) return null;
  const full = (1 << n) - 1; const dp = new Uint8Array((1 << n) * n);
  for (let v = 0; v < n; v++) if (!cycle || v === 0) dp[(1 << v) * n + v] = 1;
  for (let mask = 1; mask <= full; mask++) for (let v = 0; v < n; v++) {
    if (!dp[mask * n + v]) continue;
    for (let w = 0; w < n; w++) if (!(mask & (1 << w)) && A[v][w]) dp[(mask | (1 << w)) * n + w] = 1;
  }
  for (let v = 0; v < n; v++) if (dp[full * n + v] && (!cycle || A[v][0])) return true;
  return false;
}
function cmdHamilton(args) {
  const G = graphOf(args[0]);
  const n = G.V.length;
  if (n > 16) throw refuse("Hamiltonian questions are decided by exhaustive search, which is limited to 16 vertices");
  const A = adjMatrixBool(G);
  const cyc = n >= 3 || (n === 1) ? hamSearch(A, true) : null;
  const pth = cyc ? cyc : hamSearch(A, false);
  const answers = [ansYes("hamiltonian cycle", !!cyc), ansYes("hamiltonian path", !!pth)];
  if (cyc) answers.push(ansText("cycle", [...cyc, cyc[0]].map((v) => G.V[v]).join(" -> ")));
  else if (pth) answers.push(ansText("path", pth.map((v) => G.V[v]).join(" -> ")));
  return {
    answers,
    steps: [step("graph.hamilton", "Exhaustive backtracking search", "Extend a path one vertex at a time, backing up at dead ends; every possibility is examined.")],
    checks: () => {
      const cs = [];
      const valid = (p, closed) => p && p.length === n && new Set(p).size === n && p.every((v, i) => i === 0 || A[p[i - 1]][v]) && (!closed || A[p[n - 1]][p[0]]);
      if (cyc) cs.push(check("cycle certificate", valid(cyc, true), "the cycle visits every vertex once along graph edges"));
      else {
        const dp = heldKarp(A, true);
        cs.push(check("no cycle (Held-Karp)", dp === false, dp === null ? "too large for the subset DP" : "the subset dynamic programme finds no Hamiltonian cycle either"));
      }
      if (pth) cs.push(check("path certificate", valid(pth, false), "the path visits every vertex once along graph edges"));
      else {
        const dp = heldKarp(A, false);
        cs.push(check("no path (Held-Karp)", dp === false, dp === null ? "too large for the subset DP" : "the subset dynamic programme finds no Hamiltonian path either"));
      }
      return cs;
    },
  };
}

// ---------------------------------------------------------------- colouring
function simpleUndirected(G, what) {
  if (G.directed) throw refuse(`${what} is defined for undirected graphs`);
  if (G.E.some((e) => e.u === e.v)) throw refuse(`the graph has a loop, so it has no proper colouring`);
  return simpleEdges(G);
}
// deletion-contraction with memo: returns coefficient array (index = power of k) of BigInt
function chromPolyDC(n, edges) {
  const memo = new Map(); let calls = 0;
  const polyMul = (a, b) => { const r = Array(a.length + b.length - 1).fill(0n); a.forEach((x, i) => b.forEach((y, j) => { r[i + j] += x * y; })); return r; };
  const rec = (vs, es) => {
    if (++calls > 2e6) throw budget("chromatic polynomial too large");
    if (!es.length) { const r = Array(vs + 1).fill(0n); r[vs] = 1n; return r; }
    const key = vs + "|" + es.map(([a, b]) => a * 64 + b).sort((x, y) => x - y).join(",");
    if (memo.has(key)) return memo.get(key);
    // complete graph shortcut
    if (es.length === vs * (vs - 1) / 2) { let r = [1n]; for (let i = 0; i < vs; i++) r = polyMul(r, [-BigInt(i), 1n]); memo.set(key, r); return r; }
    const [a, b] = es[0];
    const rest = es.slice(1);
    const del = rec(vs, rest);
    // contract b into a, renumber vertices > b down by one
    const ren = (x) => (x === b ? a : x) > b ? (x === b ? a : x) - 1 : (x === b ? a : x);
    const set = new Set();
    for (const [x, y] of rest) { let p = ren(x), q = ren(y); if (p === q) continue; if (p > q) [p, q] = [q, p]; set.add(p * 64 + q); }
    const con = rec(vs - 1, [...set].map((k) => [Math.floor(k / 64), k % 64]));
    const r = del.map((c, i) => c - (con[i] || 0n));
    memo.set(key, r);
    return r;
  };
  const norm = edges.map(([a, b]) => (a < b ? [a, b] : [b, a]));
  return rec(n, norm);
}
// Whitney: P(k) = sum over edge subsets S of (-1)^|S| k^{c(S)}; returns coefficients
function chromPolyWhitney(n, edges) {
  const m = edges.length; if (m > 22) return null;
  const coef = Array(n + 1).fill(0n);
  for (let S = 0; S < (1 << m); S++) {
    const p = Array.from({ length: n }, (_, i) => i); const f = (x) => (p[x] === x ? x : (p[x] = f(p[x])));
    let c = n, bits = 0;
    for (let j = 0; j < m; j++) if (S & (1 << j)) { bits++; const a = f(edges[j][0]), b = f(edges[j][1]); if (a !== b) { p[a] = b; c--; } }
    coef[c] += bits % 2 ? -1n : 1n;
  }
  return coef;
}
const evalPoly = (cs, k) => cs.reduce((s, c, i) => s + c * BigInt(k) ** BigInt(i), 0n);
function countColourings(n, edges, k, limit = 2e7) { // backtracking count (independent of the polynomial code)
  const adj = Array.from({ length: n }, () => []); for (const [a, b] of edges) { adj[a].push(b); adj[b].push(a); }
  const col = Array(n).fill(-1); let steps = 0;
  const rec = (v) => { if (++steps > limit) throw budget("too many colourings to count"); if (v === n) return 1n; let s = 0n; for (let c = 0; c < k; c++) { if (adj[v].some((w) => w < v && col[w] === c)) continue; col[v] = c; s += rec(v + 1); } col[v] = -1; return s; };
  return rec(0);
}
function colourWith(n, edges, k, limit = 5e6) { // DSATUR-ordered backtracking; returns colouring or null
  const adj = Array.from({ length: n }, () => new Set()); for (const [a, b] of edges) { adj[a].add(b); adj[b].add(a); }
  const col = Array(n).fill(-1); let steps = 0;
  const pick = () => { let best = -1, bs = -1, bd = -1; for (let v = 0; v < n; v++) { if (col[v] >= 0) continue; const s = new Set([...adj[v]].map((w) => col[w]).filter((c) => c >= 0)).size; if (s > bs || (s === bs && adj[v].size > bd)) { best = v; bs = s; bd = adj[v].size; } } return best; };
  const rec = (done, maxUsed) => {
    if (++steps > limit) throw budget("colouring search too large");
    if (done === n) return true;
    const v = pick();
    for (let c = 0; c < Math.min(k, maxUsed + 2); c++) { if ([...adj[v]].some((w) => col[w] === c)) continue; col[v] = c; if (rec(done + 1, Math.max(maxUsed, c))) return true; col[v] = -1; }
    return false;
  };
  return rec(0, -1) ? col.slice() : null;
}
function maxClique(n, edges) {
  const adj = Array.from({ length: n }, () => new Set()); for (const [a, b] of edges) { adj[a].add(b); adj[b].add(a); }
  let best = [];
  const rec = (R, P) => { if (R.length > best.length) best = R.slice(); for (let i = 0; i < P.length; i++) { if (R.length + P.length - i <= best.length) return; const v = P[i]; rec([...R, v], P.slice(i + 1).filter((w) => adj[v].has(w))); } };
  if (n <= 40) rec([], [...Array(n).keys()]);
  return best;
}
function cmdChromaticNumber(args) {
  const G = graphOf(args[0]);
  const edges = simpleUndirected(G, "the chromatic number");
  const n = G.V.length;
  if (n > 40) throw refuse("chromatic number search is limited to 40 vertices");
  let k = 1, col = null;
  for (; k <= n; k++) { col = colourWith(n, edges, k); if (col) break; }
  if (!edges.length) { k = 1; col = Array(n).fill(0); }
  const classes = [...Array(k).keys()].map((c) => G.V.filter((_, i) => col[i] === c));
  return {
    answers: [ansNum("chromatic number", k), ansText("colouring", classes.map((c, i) => `colour ${i + 1}: {${c.join(", ")}}`).join("; "))],
    steps: [step("graph.colour", "Search for colourings with 1, 2, 3, ... colours", `The first k that works is k = ${k}.`)],
    checks: () => {
      const cs = [check("colouring certificate", col.every((c) => c >= 0 && c < k) && edges.every(([a, b]) => col[a] !== col[b]), `a proper colouring with ${k} colours exists`)];
      if (k <= 1) return cs;
      const clique = maxClique(n, edges);
      if (clique.length >= k) {
        const ok = clique.every((a, i) => clique.every((b, j) => i === j || edges.some(([x, y]) => (x === a && y === b) || (x === b && y === a))));
        cs.push(check("clique lower bound", ok, `the vertices {${clique.map((v) => G.V[v]).join(", ")}} form a clique of size ${clique.length}, so at least ${k} colours are needed`));
        return cs;
      }
      const P = chromPolyWhitney(n, edges);
      if (P) { const v = evalPoly(P, k - 1); cs.push(check("no smaller colouring", v === 0n, `Whitney's expansion gives P(${k - 1}) = ${v} proper ${k - 1}-colourings`)); return cs; }
      const c = countColourings(n, edges, k - 1);
      cs.push(check("no smaller colouring", c === 0n, `counting ${k - 1}-colourings directly finds ${c}`));
      return cs;
    },
  };
}
export function polyTreeK(cs, v = "k") {
  const terms = [];
  cs.forEach((c, i) => { if (c !== 0n) terms.push(X.mul(X.num(c), X.pow(X.sym(v), X.num(i)))); });
  return terms.length ? X.add(...terms.reverse()) : X.ZERO;
}
function cmdChromaticPoly(args) {
  const G = graphOf(args[0]);
  const edges = simpleUndirected(G, "the chromatic polynomial");
  const n = G.V.length;
  if (n > 20) throw refuse("the chromatic polynomial is computed for graphs with at most 20 vertices");
  const P = chromPolyDC(n, edges);
  const tree = simplify(polyTreeK(P));
  return {
    answers: [ansTree("chromatic polynomial", tree)],
    steps: [step("graph.chrompoly", "Deletion-contraction", "P(G, k) = P(G - e, k) - P(G / e, k); a graph with no edges on n vertices gives k^n.")],
    checks: () => {
      const Wh = chromPolyWhitney(n, edges);
      if (Wh) return [check("Whitney expansion", Wh.length === P.length && Wh.every((c, i) => c === P[i]), `summing (-1)^|S| k^c(S) over all ${2 ** edges.length} edge subsets gives the same polynomial`)];
      // degree-n polynomial is fixed by its values at k = 0..n: count colourings directly
      let ok = true;
      for (let k = 0; k <= n && ok; k++) if (countColourings(n, edges, k) !== evalPoly(P, k)) ok = false;
      return [check("colour counts", ok, `direct counts of proper k-colourings for k = 0..${n} match, which determines the degree-${n} polynomial`)];
    },
  };
}

// ---------------------------------------------------------------- planarity
function girth(n, edges) {
  const adj = Array.from({ length: n }, () => []); for (const [a, b] of edges) { adj[a].push(b); adj[b].push(a); }
  let g = Infinity;
  for (let s = 0; s < n; s++) {
    const d = Array(n).fill(-1), p = Array(n).fill(-1); d[s] = 0; const q = [s];
    while (q.length) { const v = q.shift(); for (const w of adj[v]) { if (d[w] < 0) { d[w] = d[v] + 1; p[w] = v; q.push(w); } else if (p[v] !== w) g = Math.min(g, d[v] + d[w] + 1); } }
  }
  return g;
}
// search for a genus-0 rotation system; returns rotation (array of neighbour orders) or null
function planarEmbedding(n, edges, limit = 3e5) {
  const adj = Array.from({ length: n }, () => []); for (const [a, b] of edges) { adj[a].push(b); adj[b].push(a); }
  const m = edges.length;
  const comps = bfsComponents(n, edges).count;
  const target = n - m + comps + 1 - 0; // faces needed: V - E + F = 1 + C  => F = 1 + C - V + E
  const need = 1 + comps - n + m;
  void target;
  // rotations: fix the first neighbour, permute the rest
  const perms = (arr) => { if (arr.length <= 1) return [arr]; const out = []; arr.forEach((x, i) => perms([...arr.slice(0, i), ...arr.slice(i + 1)]).forEach((p) => out.push([x, ...p]))); return out; };
  const options = adj.map((ns) => (ns.length <= 2 ? [ns] : perms(ns.slice(1)).map((p) => [ns[0], ...p])));
  let total = 1; for (const o of options) { total *= o.length; if (total > limit) return undefined; }
  const rot = options.map((o) => o[0]);
  const faces = () => {
    const succ = rot.map((ns) => { const mp = new Map(); ns.forEach((w, i) => mp.set(w, ns[(i + 1) % ns.length])); return mp; });
    const seen = new Set(); let f = 0;
    for (let v = 0; v < n; v++) for (const w of adj[v]) {
      if (seen.has(v * 1000 + w)) continue; f++;
      let a = v, b = w;
      while (!seen.has(a * 1000 + b)) { seen.add(a * 1000 + b); const c = succ[b].get(a); a = b; b = c; }
    }
    return f;
  };
  const idx = Array(n).fill(0);
  for (let it = 0; it < total; it++) {
    if (faces() === need) return rot.map((r) => r.slice());
    for (let v = 0; v < n; v++) { idx[v]++; if (idx[v] < options[v].length) { rot[v] = options[v][idx[v]]; break; } idx[v] = 0; rot[v] = options[v][0]; }
  }
  return null;
}
function traceFaces(n, edges, rot) { // independent face tracer: returns number of faces or -1 when rot is not a rotation system of the graph
  const nbr = Array.from({ length: n }, () => []); for (const [a, b] of edges) { nbr[a].push(b); nbr[b].push(a); }
  for (let v = 0; v < n; v++) { const x = [...rot[v]].sort((p, q) => p - q), y = [...nbr[v]].sort((p, q) => p - q); if (x.length !== y.length || x.some((t, i) => t !== y[i])) return -1; }
  const darts = new Set(); for (let v = 0; v < n; v++) for (const w of nbr[v]) darts.add(`${v}>${w}`);
  let faces = 0;
  while (darts.size) {
    const first = darts.values().next().value; faces++;
    let [a, b] = first.split(">").map(Number);
    for (let guard = 0; guard < 4 * edges.length + 4; guard++) {
      const key = `${a}>${b}`; if (!darts.has(key)) break; darts.delete(key);
      const r = rot[b]; const c = r[(r.indexOf(a) + 1) % r.length]; a = b; b = c;
    }
  }
  return faces;
}
function kuratowski(n, edges, limit) { // minimal non-planar subgraph by edge deletion, then smoothing
  let es = edges.slice();
  for (let i = 0; i < es.length; ) {
    const trial = es.filter((_, j) => j !== i);
    const emb = planarEmbedding(n, trial, limit);
    if (emb === undefined) return null;
    if (emb === null) es = trial; else i++;
  }
  return es;
}
function smoothIsKuratowski(n, es) { // independent check: smooth degree-2 vertices, drop isolated, compare with K5 / K3,3
  let E = es.map((e) => e.slice());
  for (;;) {
    const deg = new Map(); for (const [a, b] of E) { deg.set(a, (deg.get(a) || 0) + 1); deg.set(b, (deg.get(b) || 0) + 1); }
    const v = [...deg.entries()].find(([, d]) => d === 2);
    if (!v) break;
    const inc = E.filter(([a, b]) => a === v[0] || b === v[0]);
    const ends = inc.map(([a, b]) => (a === v[0] ? b : a));
    if (ends[0] === ends[1]) return null;
    E = E.filter(([a, b]) => a !== v[0] && b !== v[0]);
    if (E.some(([a, b]) => (a === ends[0] && b === ends[1]) || (a === ends[1] && b === ends[0]))) return null; // would create a multi-edge
    E.push([ends[0], ends[1]]);
  }
  const vs = [...new Set(E.flat())];
  const has = (a, b) => E.some(([x, y]) => (x === a && y === b) || (x === b && y === a));
  if (vs.length === 5 && E.length === 10 && vs.every((a) => vs.every((b) => a === b || has(a, b)))) return "K5";
  if (vs.length === 6 && E.length === 9) {
    for (let mask = 0; mask < 64; mask++) {
      const A = vs.filter((_, i) => mask & (1 << i)), B = vs.filter((_, i) => !(mask & (1 << i)));
      if (A.length === 3 && A.every((a) => B.every((b) => has(a, b)))) return "K3,3";
    }
  }
  return null;
}
function cmdPlanar(args) {
  const G = graphOf(args[0]);
  if (G.directed) throw refuse("planarity is a property of the underlying undirected graph; give it undirected");
  const edges = simpleEdges(G); // loops and parallel edges never affect planarity
  const n = G.V.length, m = edges.length;
  if (n > 30) throw refuse("planarity is decided here for graphs with at most 30 vertices");
  const comps = bfsComponents(n, edges).count;
  // edge-count bounds (valid for simple graphs): m <= 3n - 6, girth g: m <= g (n - 2) / (g - 2)
  const g = girth(n, edges);
  const boundFails = n >= 3 && (m > 3 * n - 6 || (Number.isFinite(g) && g > 3 && m * (g - 2) > g * (n - 2)));
  if (boundFails) {
    return {
      answers: [ansYes("planar", false), ansText("reason", m > 3 * n - 6 ? `${m} edges > 3n - 6 = ${3 * n - 6}` : `girth ${g} and ${m} edges > g(n - 2)/(g - 2) = ${qstr(N.Q(BigInt(g * (n - 2)), BigInt(g - 2)))}`)],
      steps: [step("graph.planar.bound", "Euler's formula edge bound", "A simple planar graph with n >= 3 vertices and girth g has at most g(n - 2)/(g - 2) edges (3n - 6 when g = 3).")],
      checks: () => {
        const g2 = girthByCycleSearch(n, edges);
        const ok = m > 3 * n - 6 || (g2 > 3 && m * (g2 - 2) > g2 * (n - 2));
        return [check("edge bound", ok, `recount: n = ${n}, m = ${m}, girth ${g2}; the planar edge bound is exceeded`)];
      },
    };
  }
  const emb = planarEmbedding(n, edges);
  if (emb === undefined) throw refuse("the embedding search is too large for this graph");
  if (emb) {
    const need = 1 + comps - n + m;
    return {
      answers: [ansYes("planar", true), ansNum("faces", need)],
      steps: [step("graph.planar.embed", "Find a rotation system of genus 0", `Tracing faces gives F = ${need}, and V - E + F = ${n - m + need} = 1 + (number of components).`)],
      checks: () => { const f = traceFaces(n, edges, emb); return [check("embedding", f === need && n - m + f === 1 + comps, `face tracing of the rotation system gives ${f} faces, so V - E + F = ${n - m + f}: a plane embedding`)]; },
    };
  }
  const sub = kuratowski(n, edges, 3e5);
  return {
    answers: [ansYes("planar", false)],
    steps: [step("graph.planar.search", "No rotation system has genus 0", "Every rotation system was examined.")],
    checks: () => {
      const kind = sub ? smoothIsKuratowski(n, sub) : null;
      return [check("Kuratowski subgraph", !!kind && sub.every(([a, b]) => edges.some(([x, y]) => (x === a && y === b) || (x === b && y === a))), kind ? `the graph contains a subdivision of ${kind}` : "no Kuratowski subgraph could be exhibited")];
    },
  };
}
function girthByCycleSearch(n, edges) { // independent girth: shortest cycle through each edge via BFS avoiding it
  let best = Infinity;
  for (let i = 0; i < edges.length; i++) {
    const [a, b] = edges[i];
    const adj = Array.from({ length: n }, () => []); edges.forEach(([x, y], j) => { if (j !== i) { adj[x].push(y); adj[y].push(x); } });
    const d = Array(n).fill(-1); d[a] = 0; const q = [a];
    while (q.length) { const v = q.shift(); for (const w of adj[v]) if (d[w] < 0) { d[w] = d[v] + 1; q.push(w); } }
    if (d[b] >= 0) best = Math.min(best, d[b] + 1);
  }
  return best;
}

// ---------------------------------------------------------------- max flow / min cut
function cmdMaxFlow(args) {
  const G = graphOf(args[0]);
  const s = ix(G, labelOf(args[1])), t = ix(G, labelOf(args[2]));
  if (s === t) throw refuse("the source and sink must differ");
  const n = G.V.length;
  if (G.E.some((e) => e.w !== null && N.isNeg(e.w))) throw refuse("capacities must be non-negative");
  // arcs: directed as given; an undirected edge is two opposite arcs
  const arcs = [];
  for (const e of G.E) { const a = G.index.get(e.u), b = G.index.get(e.v); if (a === b) continue; arcs.push({ a, b, cap: W(e), e }); if (!G.directed) arcs.push({ a: b, b: a, cap: W(e), e }); }
  const flow = arcs.map(() => N.ZERO);
  // residual graph with explicit reverse arcs (Edmonds-Karp)
  for (let iter = 0; iter < 100000; iter++) {
    const prev = Array(n).fill(null); prev[s] = { arc: -1 }; const q = [s];
    while (q.length && !prev[t]) {
      const v = q.shift();
      arcs.forEach((r, i) => {
        if (r.a === v && !prev[r.b] && N.lt(flow[i], r.cap)) { prev[r.b] = { arc: i, fwd: true }; q.push(r.b); }
        if (r.b === v && !prev[r.a] && N.isPos(flow[i])) { prev[r.a] = { arc: i, fwd: false }; q.push(r.a); }
      });
    }
    if (!prev[t]) break;
    let aug = null;
    for (let v = t; v !== s;) { const p = prev[v]; const r = arcs[p.arc]; const room = p.fwd ? N.sub(r.cap, flow[p.arc]) : flow[p.arc]; aug = aug === null || N.lt(room, aug) ? room : aug; v = p.fwd ? r.a : r.b; }
    for (let v = t; v !== s;) { const p = prev[v]; const r = arcs[p.arc]; flow[p.arc] = p.fwd ? N.add(flow[p.arc], aug) : N.sub(flow[p.arc], aug); v = p.fwd ? r.a : r.b; }
  }
  // cut: vertices reachable in the residual graph
  const S = new Set([s]); const q = [s];
  while (q.length) { const v = q.shift(); arcs.forEach((r, i) => { if (r.a === v && !S.has(r.b) && N.lt(flow[i], r.cap)) { S.add(r.b); q.push(r.b); } if (r.b === v && !S.has(r.a) && N.isPos(flow[i])) { S.add(r.a); q.push(r.a); } }); }
  const value = arcs.reduce((acc, r, i) => (r.a === s ? N.add(acc, flow[i]) : r.b === s ? N.sub(acc, flow[i]) : acc), N.ZERO);
  const cutArcs = arcs.filter((r) => S.has(r.a) && !S.has(r.b));
  const flowText = arcs.map((r, i) => (N.isZero(flow[i]) ? null : `${G.V[r.a]}->${G.V[r.b]}: ${qstr(flow[i])}`)).filter(Boolean).join(", ");
  return {
    answers: [ansNum("max flow", value), ansText("min cut", `S = {${[...S].sort((a, b) => a - b).map((v) => G.V[v]).join(", ")}}, cut arcs ${cutArcs.map((r) => `${G.V[r.a]}->${G.V[r.b]}`).join(", ")}`), ansText("flow", flowText || "zero flow")],
    steps: [step("graph.flow", "Edmonds-Karp: augment along shortest residual paths", "Stop when the sink is unreachable in the residual network."),
      step("graph.flow.cut", "Read off the minimum cut", "S is the set of vertices still reachable from the source; the arcs leaving S are saturated.")],
    checks: () => {
      const cap = arcs.every((r, i) => !N.isNeg(flow[i]) && !N.lt(r.cap, flow[i]));
      let cons = true;
      for (let v = 0; v < n; v++) { if (v === s || v === t) continue; let bal = N.ZERO; arcs.forEach((r, i) => { if (r.b === v) bal = N.add(bal, flow[i]); if (r.a === v) bal = N.sub(bal, flow[i]); }); if (!N.isZero(bal)) cons = false; }
      const cutCap = cutArcs.reduce((acc, r) => N.add(acc, r.cap), N.ZERO);
      return [check("feasible flow", cap && cons, "0 <= flow <= capacity on every arc, and flow is conserved at every vertex other than s and t"),
        check("cut certificate", S.has(s) && !S.has(t) && N.eq(cutCap, value), `the cut separating s from t has capacity ${qstr(cutCap)} = flow value, so both are optimal (weak duality)`)];
    },
  };
}

// ---------------------------------------------------------------- topological sort
function cmdTopo(args) {
  const G = graphOf(args[0]);
  if (!G.directed) throw refuse("a topological order needs a directed graph (write arcs as u->v)");
  const n = G.V.length, indeg = Array(n).fill(0);
  for (const e of G.E) indeg[G.index.get(e.v)]++;
  const q = [...Array(n).keys()].filter((v) => indeg[v] === 0), order = [];
  const d = indeg.slice();
  while (q.length) { q.sort((a, b) => a - b); const v = q.shift(); order.push(v); for (const e of G.E) if (G.index.get(e.u) === v) { const w = G.index.get(e.v); if (--d[w] === 0) q.push(w); } }
  if (order.length === n) {
    return {
      answers: [ansYes("acyclic", true), ansText("topological order", order.map((v) => G.V[v]).join(", "))],
      steps: [step("graph.kahn", "Kahn's algorithm", "Repeatedly output a vertex with no remaining incoming arcs.")],
      checks: () => { const pos = new Map(order.map((v, i) => [v, i])); return [check("order", pos.size === n && G.E.every((e) => pos.get(G.index.get(e.u)) < pos.get(G.index.get(e.v))), "every arc points from an earlier to a later vertex")]; },
    };
  }
  // find a directed cycle among the remaining vertices
  const rem = new Set([...Array(n).keys()].filter((v) => !order.includes(v)));
  let v = [...rem][0]; const seenAt = new Map(); const walk = [];
  while (!seenAt.has(v)) { seenAt.set(v, walk.length); walk.push(v); const e = G.E.find((x) => G.index.get(x.u) === v && rem.has(G.index.get(x.v))); v = G.index.get(e.v); }
  const cycle = walk.slice(seenAt.get(v));
  return {
    answers: [ansYes("acyclic", false), ansText("directed cycle", [...cycle, cycle[0]].map((x) => G.V[x]).join(" -> "))],
    steps: [step("graph.kahn", "Kahn's algorithm gets stuck", "Every remaining vertex has an incoming arc, which forces a directed cycle.")],
    checks: () => { const c = [...cycle, cycle[0]]; return [check("cycle", c.every((x, i) => i === 0 || G.E.some((e) => G.index.get(e.u) === c[i - 1] && G.index.get(e.v) === x)), "the directed cycle exists, so no topological order exists")]; },
  };
}

// ---------------------------------------------------------------- isomorphism
function invariants(G) {
  const n = G.V.length, A = adjMatrixBool(G);
  const deg = A.map((r) => r.filter(Boolean).length).sort((a, b) => a - b);
  let tri = 0; for (let i = 0; i < n; i++) for (let j = i + 1; j < n; j++) if (A[i][j]) for (let k = j + 1; k < n; k++) if (A[j][k] && A[i][k]) tri++;
  const comps = bfsComponents(n, simpleEdges(G)).comp; const sizes = Object.values(comps.reduce((m, c) => { m[c] = (m[c] || 0) + 1; return m; }, {})).sort((a, b) => a - b);
  return { vertices: n, edges: simpleEdges(G).length, degrees: deg.join(","), triangles: tri, components: sizes.join(",") };
}
function cmdIsomorphic(args) {
  const G = graphOf(args[0]), H = graphOf(args[1]);
  if (G.directed || H.directed) throw refuse("isomorphism is implemented for undirected graphs");
  if (!isSimple(G) || !isSimple(H)) throw refuse("isomorphism is implemented for simple graphs (no loops or repeated edges)");
  const n = G.V.length;
  if (n > 40) throw refuse("isomorphism search is limited to 40 vertices");
  const A = adjMatrixBool(G), B = adjMatrixBool(H);
  let map = null;
  if (n === H.V.length && simpleEdges(G).length === simpleEdges(H).length) {
    const dg = A.map((r) => r.filter(Boolean).length), dh = B.map((r) => r.filter(Boolean).length);
    const f = Array(n).fill(-1), used = Array(n).fill(false); let steps = 0;
    const order = [...Array(n).keys()].sort((a, b) => dg[b] - dg[a]);
    const rec = (k) => {
      if (++steps > 5e6) throw budget("isomorphism search too large");
      if (k === n) return true;
      const v = order[k];
      for (let w = 0; w < n; w++) {
        if (used[w] || dh[w] !== dg[v]) continue;
        if (order.slice(0, k).some((u) => A[u][v] !== B[f[u]][w])) continue;
        f[v] = w; used[w] = true; if (rec(k + 1)) return true; used[w] = false; f[v] = -1;
      }
      return false;
    };
    if (rec(0)) map = f.slice();
  }
  if (map) {
    return {
      answers: [ansYes("isomorphic", true), ansText("isomorphism", G.V.map((l, i) => `${l} -> ${H.V[map[i]]}`).join(", "))],
      steps: [step("graph.iso", "Backtracking search for an edge-preserving bijection", "Vertices are matched degree by degree.")],
      checks: () => {
        const bij = new Set(map).size === n;
        let ok = bij;
        for (let i = 0; i < n && ok; i++) for (let j = 0; j < n; j++) if (A[i][j] !== B[map[i]][map[j]]) { ok = false; break; }
        return [check("bijection", ok, "the map is a bijection that sends edges to edges and non-edges to non-edges")];
      },
    };
  }
  const iG = invariants(G), iH = invariants(H);
  const diff = Object.keys(iG).find((k) => iG[k] !== iH[k]);
  return {
    answers: [ansYes("isomorphic", false), ...(diff ? [ansText("reason", `different ${diff}: ${iG[diff]} vs ${iH[diff]}`)] : [])],
    steps: [step("graph.iso", "Exhaustive search finds no edge-preserving bijection", diff ? `The graphs differ in ${diff}.` : "")],
    checks: () => {
      if (diff) return [check("invariant", iG[diff] !== iH[diff], `an isomorphism preserves the ${diff}, which differ (${iG[diff]} vs ${iH[diff]})`)];
      if (n > 8) return [check("brute force", false, "no distinguishing invariant, and too many vertices for a brute-force check")];
      // brute force over all n! bijections
      const perm = [...Array(n).keys()]; let found = false;
      const rec = (k) => { if (found) return; if (k === n) { let ok = true; for (let i = 0; i < n && ok; i++) for (let j = 0; j < n; j++) if (A[i][j] !== B[perm[i]][perm[j]]) { ok = false; break; } if (ok) found = true; return; } for (let i = k; i < n; i++) { [perm[k], perm[i]] = [perm[i], perm[k]]; rec(k + 1); [perm[k], perm[i]] = [perm[i], perm[k]]; } };
      rec(0);
      return [check("brute force", !found, `none of the ${n}! bijections preserves edges`)];
    },
  };
}

export const GRAPH_HANDLERS = {
  graphdegrees: cmdDegrees, graphcomponents: cmdComponents, shortestpath: cmdShortestPath, minspantree: cmdMST, countspanningtrees: cmdSpanningTrees,
  isbipartite: cmdBipartite, eulerpath: cmdEuler, hamiltonpath: cmdHamilton, chromaticnumber: cmdChromaticNumber, chromaticpoly: cmdChromaticPoly,
  isplanar: cmdPlanar, maxflow: cmdMaxFlow, toposort: cmdTopo, isisomorphic: cmdIsomorphic,
};
