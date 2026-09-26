// Linear and integer programming, zero-sum matrix games and bimatrix Nash equilibria, in exact
// rational arithmetic.
//
//   linprog(objmax(f) | objmin(f), constraint, ...)   constraints: linear <=, >=, = (variables are free
//                                                    unless a constraint such as x >= 0 bounds them)
//   intprog(objmax(f) | objmin(f), constraint, ...)   all variables integer
//   matrixgame(A)                                    row player maximises
//   nashequilibria(A, B)                             A: row player's payoffs, B: column player's
//
// Certificates (checked by plain arithmetic, independent of the simplex internals):
//   optimal     a feasible x and a dual vector y with the right signs, Aᵀy = c and b·y = c·x
//   unbounded   a feasible x and a ray d (a·d <= 0 / >= 0 / = 0 on the rows) with c·d > 0
//   infeasible  a Farkas vector y with the dual signs, Aᵀy = 0 and b·y < 0
//   integer     exhaustive enumeration of every integer point in the box the LP relaxation bounds
//   games       the optimal strategies guarantee the value against every pure reply; each Nash
//               equilibrium passes the best-response test for both players

import { refuse, ansText, ansNum, check, step, N, X, qstr } from "./util.js";
import { ratOf, listOf } from "./decode.js";

// ---------------------------------------------------------------- linear expressions
function linOf(u) { // -> Map(var -> Rational), with key "" for the constant
  const out = new Map();
  const addTo = (m, k, v) => { const s = N.add(m.get(k) || N.ZERO, v); if (N.isZero(s)) m.delete(k); else m.set(k, s); };
  const go = (w, scale) => {
    const r = ratOf(w);
    if (r) { addTo(out, "", N.mul(scale, r)); return; }
    if (w.k === "sym") { addTo(out, w.name, scale); return; }
    if (w.k === "add") { w.args.forEach((a) => go(a, scale)); return; }
    if (w.k === "mul") {
      let c = scale; let rest = null;
      for (const a of w.args) { const q = ratOf(a); if (q) c = N.mul(c, q); else if (!rest) rest = a; else throw refuse("the objective and constraints must be linear"); }
      if (!rest) { addTo(out, "", c); return; }
      go(rest, c); return;
    }
    throw refuse("the objective and constraints must be linear");
  };
  go(u, N.ONE);
  return out;
}
function readProblem(args) {
  const objNode = args[0];
  if (!objNode || objNode.k !== "fn" || (objNode.name !== "objmax" && objNode.name !== "objmin")) throw refuse("start with maximize or minimize");
  const sense = objNode.name === "objmax" ? "max" : "min";
  const obj = linOf(objNode.args[0]);
  const rows = [];
  for (const a of args.slice(1)) {
    let op;
    if (a.k === "eq") op = "=";
    else if (a.k === "rel" && (a.op === "<=" || a.op === "≤")) op = "<=";
    else if (a.k === "rel" && (a.op === ">=" || a.op === "≥")) op = ">=";
    else if (a.k === "rel") throw refuse("strict inequalities are not allowed in a linear program");
    else throw refuse("each constraint must be a linear equation or inequality");
    const l = linOf(a.args[0]), r = linOf(a.args[1]);
    const coef = new Map(l);
    for (const [k, v] of r) coef.set(k, N.sub(coef.get(k) || N.ZERO, v));
    const b = N.neg(coef.get("") || N.ZERO); coef.delete("");
    for (const [k, v] of [...coef]) if (N.isZero(v)) coef.delete(k);
    rows.push({ coef, op, b, text: null });
  }
  const vars = [...new Set([...obj.keys(), ...rows.flatMap((r) => [...r.coef.keys()])])].filter((v) => v !== "").sort();
  if (!vars.length) throw refuse("the problem has no variables");
  if (vars.length > 12 || rows.length > 40) throw refuse("the problem is too large (at most 12 variables and 40 constraints)");
  const c = vars.map((v) => obj.get(v) || N.ZERO);
  const A = rows.map((r) => vars.map((v) => r.coef.get(v) || N.ZERO));
  return { sense, vars, c, c0: obj.get("") || N.ZERO, A, ops: rows.map((r) => r.op), b: rows.map((r) => r.b) };
}

// ---------------------------------------------------------------- exact two-phase simplex (Bland's rule)
// maximise c·x subject to rows A x (op) b with every x free; returns { status, x }
export function lpSolve(c, A, ops, b) {
  const n = c.length, m = A.length;
  // columns: u_j (j < n), v_j (n + j), then slacks / surpluses, then artificials
  const rows = []; const kinds = [];
  for (let i = 0; i < m; i++) {
    let a = [...A[i], ...A[i].map(N.neg)], rhs = b[i], op = ops[i];
    if (N.isNeg(rhs)) { a = a.map(N.neg); rhs = N.neg(rhs); op = op === "<=" ? ">=" : op === ">=" ? "<=" : "="; }
    rows.push({ a, rhs, op }); kinds.push(op);
  }
  const nSlack = rows.filter((r) => r.op !== "=").length;
  const nArt = rows.filter((r) => r.op !== "<=").length;
  const W = 2 * n + nSlack + nArt;
  const T = []; const basis = []; const artCols = new Set();
  let s = 2 * n, t = 2 * n + nSlack;
  for (const r of rows) {
    const row = Array(W + 1).fill(N.ZERO);
    r.a.forEach((v, j) => { row[j] = v; });
    row[W] = r.rhs;
    if (r.op === "<=") { row[s] = N.ONE; basis.push(s); s++; }
    else if (r.op === ">=") { row[s] = N.NEG_ONE; s++; row[t] = N.ONE; basis.push(t); artCols.add(t); t++; }
    else { row[t] = N.ONE; basis.push(t); artCols.add(t); t++; }
    T.push(row);
  }
  let steps = 0;
  const run = (cost, allowed) => {
    for (;;) {
      if (++steps > 20000) throw refuse("the simplex method did not finish");
      let enter = -1;
      for (let j = 0; j < W && enter < 0; j++) {
        if (!allowed(j) || basis.includes(j)) continue;
        let z = N.neg(cost[j]);
        for (let i = 0; i < T.length; i++) if (!N.isZero(T[i][j])) z = N.add(z, N.mul(cost[basis[i]], T[i][j]));
        if (N.isNeg(z)) enter = j;
      }
      if (enter < 0) return "optimal";
      let leave = -1, best = null;
      for (let i = 0; i < T.length; i++) {
        if (!N.isPos(T[i][enter])) continue;
        const ratio = N.div(T[i][W], T[i][enter]);
        if (best === null || N.lt(ratio, best) || (N.eq(ratio, best) && basis[i] < basis[leave])) { best = ratio; leave = i; }
      }
      if (leave < 0) return { unbounded: enter };
      pivot(leave, enter);
    }
  };
  const pivot = (r, col) => {
    const pv = T[r][col];
    T[r] = T[r].map((v) => N.div(v, pv));
    for (let i = 0; i < T.length; i++) if (i !== r && !N.isZero(T[i][col])) { const f = T[i][col]; T[i] = T[i].map((v, j) => N.sub(v, N.mul(f, T[r][j]))); }
    basis[r] = col;
  };
  // phase 1
  const cost1 = Array(W).fill(N.ZERO); for (const j of artCols) cost1[j] = N.NEG_ONE;
  run(cost1, () => true);
  const infeas = T.some((row, i) => artCols.has(basis[i]) && !N.isZero(row[W]));
  if (infeas) return { status: "infeasible" };
  // drive zero-level artificials out of the basis
  for (let i = T.length - 1; i >= 0; i--) {
    if (!artCols.has(basis[i])) continue;
    const j = T[i].findIndex((v, jj) => jj < W && !artCols.has(jj) && !N.isZero(v));
    if (j >= 0) pivot(i, j); else { T.splice(i, 1); basis.splice(i, 1); }
  }
  const read = () => { const x = Array(W).fill(N.ZERO); basis.forEach((j, i) => { x[j] = T[i][W]; }); return c.map((_, j) => N.sub(x[j], x[n + j])); };
  const feasible = read();
  const cost2 = Array(W).fill(N.ZERO); c.forEach((v, j) => { cost2[j] = v; cost2[n + j] = N.neg(v); });
  const r2 = run(cost2, (j) => !artCols.has(j));
  if (r2 !== "optimal") return { status: "unbounded", feasible };
  const x = read();
  return { status: "optimal", x, value: dot(c, x), feasible };
}
const dot = (a, b) => a.reduce((s, v, i) => N.add(s, N.mul(v, b[i])), N.ZERO);
const opOk = (lhs, op, b) => (op === "<=" ? !N.lt(b, lhs) : op === ">=" ? !N.lt(lhs, b) : N.eq(lhs, b));
const feasibleAt = (A, ops, b, x) => A.every((row, i) => opOk(dot(row, x), ops[i], b[i]));
const transpose = (A, n) => Array.from({ length: n }, (_, j) => A.map((r) => r[j]));
// dual / Farkas sign rows for y: <= rows y >= 0, >= rows y <= 0, = rows free
function signRows(ops) { const m = ops.length; const rows = [], rops = [], rb = []; ops.forEach((op, i) => { if (op === "=") return; const r = Array(m).fill(N.ZERO); r[i] = N.ONE; rows.push(r); rops.push(op === "<=" ? ">=" : "<="); rb.push(N.ZERO); }); return { rows, rops, rb }; }
const signOk = (ops, y) => ops.every((op, i) => (op === "<=" ? !N.isNeg(y[i]) : op === ">=" ? !N.isPos(y[i]) : true));

function certificate(P, res) {
  const { c, A, ops, b } = P; const n = c.length, m = A.length;
  const At = transpose(A, n);
  if (res.status === "optimal") {
    // dual: minimise b·y  s.t. Aᵀ y = c, sign rows
    const s = signRows(ops);
    const d = lpSolve(b.map(N.neg), [...At, ...s.rows], [...At.map(() => "="), ...s.rops], [...c, ...s.rb]);
    if (d.status !== "optimal") return { ok: false, detail: "no dual certificate was found" };
    const y = d.x;
    const ok = feasibleAt(A, ops, b, res.x) && signOk(ops, y) && At.every((col, j) => N.eq(dot(col, y), c[j])) && N.eq(dot(b, y), dot(c, res.x));
    return { ok, y, detail: `dual y = (${y.map(qstr).join(", ")}): signs match the constraints, Aᵀy = c, and b·y = ${qstr(dot(b, y))} = c·x, so no feasible point does better (weak duality)` };
  }
  if (res.status === "unbounded") {
    const cap = [...c]; // c·d <= 1
    const rec = lpSolve(c, [...A, cap], [...ops, "<="], [...b.map(() => N.ZERO), N.ONE]);
    if (rec.status !== "optimal" || !N.isPos(rec.value)) return { ok: false, detail: "no improving ray was found" };
    const dd = rec.x;
    const ok = feasibleAt(A, ops, b, res.feasible) && A.every((row, i) => opOk(dot(row, dd), ops[i], N.ZERO)) && N.isPos(dot(c, dd));
    return { ok, detail: `x0 = (${res.feasible.map(qstr).join(", ")}) is feasible and the ray d = (${dd.map(qstr).join(", ")}) keeps every constraint while c·d = ${qstr(dot(c, dd))} > 0, so the objective grows without bound` };
  }
  const s = signRows(ops); // Farkas: Aᵀ y = 0, b·y >= -1, minimise b·y
  const f = lpSolve(b.map(N.neg), [...At, ...s.rows, b], [...At.map(() => "="), ...s.rops, ">="], [...c.map(() => N.ZERO), ...s.rb, N.NEG_ONE]);
  if (f.status !== "optimal") return { ok: false, detail: "no Farkas certificate was found" };
  const y = f.x;
  const ok = signOk(ops, y) && At.every((col) => N.isZero(dot(col, y))) && N.isNeg(dot(b, y));
  void m;
  return { ok, detail: `y = (${y.map(qstr).join(", ")}) has the dual signs, Aᵀy = 0 and b·y = ${qstr(dot(b, y))} < 0; adding the constraints with these weights gives 0 < 0 (Farkas)` };
}
const pointText = (vars, x) => vars.map((v, i) => `${v} = ${qstr(x[i])}`).join(", ");

function cmdLinprog(args) {
  const P = readProblem(args);
  const c = P.sense === "max" ? P.c : P.c.map(N.neg);
  const res = lpSolve(c, P.A, P.ops, P.b);
  const answers = [ansText("status", res.status)];
  let value = null;
  if (res.status === "optimal") {
    value = N.add(P.sense === "max" ? res.value : N.neg(res.value), P.c0);
    answers.unshift({ kind: "exact", label: "optimal value", tree: X.num(value) });
    answers.push(ansText("optimal point", pointText(P.vars, res.x)));
  }
  const Q = { ...P, c };
  return {
    answers,
    steps: [step("lp.simplex", "Two-phase simplex in exact rational arithmetic", `Phase 1 finds a feasible vertex (or shows there is none); phase 2 improves the objective with Bland's rule.`),
      step("lp.result", res.status === "optimal" ? "Optimum" : res.status === "unbounded" ? "Unbounded" : "Infeasible", res.status === "optimal" ? `${P.sense === "max" ? "Maximum" : "Minimum"} ${qstr(value)} at ${pointText(P.vars, res.x)}.` : res.status === "unbounded" ? "The objective can be improved without limit." : "No point satisfies all the constraints.")],
    checks: () => { const ct = certificate(Q, res); return [check(res.status === "optimal" ? "dual certificate" : res.status === "unbounded" ? "ray certificate" : "Farkas certificate", ct.ok, ct.detail)]; },
  };
}

// ---------------------------------------------------------------- integer programming
function cmdIntprog(args) {
  const P = readProblem(args);
  const n = P.vars.length;
  const c = P.sense === "max" ? P.c : P.c.map(N.neg);
  let best = null, nodes = 0;
  const bb = (A, ops, b) => {
    if (++nodes > 20000) throw refuse("branch and bound needed too many nodes");
    const r = lpSolve(c, A, ops, b);
    if (r.status === "infeasible") return;
    if (r.status === "unbounded") throw refuse("the LP relaxation is unbounded, so branch and bound cannot certify an integer optimum");
    if (best && !N.lt(best.value, r.value)) return;
    const j = r.x.findIndex((v) => v.d !== 1n);
    if (j < 0) { best = { x: r.x, value: r.value }; return; }
    const row = Array(n).fill(N.ZERO); row[j] = N.ONE;
    bb([...A, row], [...ops, "<="], [...b, N.Q(N.floor(r.x[j]))]);
    bb([...A, row], [...ops, ">="], [...b, N.Q(N.ceil(r.x[j]))]);
  };
  bb(P.A, P.ops, P.b);
  const answers = [];
  let value = null;
  if (best) { value = N.add(P.sense === "max" ? best.value : N.neg(best.value), P.c0); answers.push({ kind: "exact", label: "optimal value", tree: X.num(value) }, ansText("optimal point", pointText(P.vars, best.x)), ansText("status", "optimal")); }
  else answers.push(ansText("status", "infeasible"));
  return {
    answers,
    steps: [step("ilp.bb", "Branch and bound", "Solve the LP relaxation; when a variable is fractional, split into x <= floor and x >= ceil and keep the best integer solution."),
      step("ilp.result", best ? "Integer optimum" : "No integer point", best ? `${qstr(value)} at ${pointText(P.vars, best.x)} (${nodes} subproblems).` : "Every branch is infeasible.")],
    checks: () => {
      // box from the LP relaxation, then every integer point in it
      const lo = [], hi = [];
      for (let j = 0; j < n; j++) {
        const e = Array(n).fill(N.ZERO); e[j] = N.ONE;
        const mx = lpSolve(e, P.A, P.ops, P.b), mn = lpSolve(e.map(N.neg), P.A, P.ops, P.b);
        if (mx.status === "infeasible") return [check("exhaustive", !best, "the LP relaxation is infeasible, so there is no integer point")];
        if (mx.status !== "optimal" || mn.status !== "optimal") return [check("exhaustive", false, "the feasible region is unbounded, so exhaustive search is impossible")];
        lo.push(N.ceil(mn.x[j])); hi.push(N.floor(mx.x[j]));
      }
      let count = 1n; for (let j = 0; j < n; j++) count *= hi[j] >= lo[j] ? hi[j] - lo[j] + 1n : 0n;
      if (count > 2000000n) return [check("exhaustive", false, `${count} integer points in the bounding box is too many to enumerate`)];
      let bestV = null; const x = lo.slice(); let feasibleCount = 0;
      const rec = (j) => {
        if (j === n) { const xq = x.map((v) => N.Q(v)); if (feasibleAt(P.A, P.ops, P.b, xq)) { feasibleCount++; const v = dot(c, xq); if (bestV === null || N.lt(bestV, v)) bestV = v; } return; }
        for (let v = lo[j]; v <= hi[j]; v++) { x[j] = v; rec(j + 1); }
      };
      if (count > 0n) rec(0);
      if (!best) return [check("exhaustive", bestV === null, `none of the ${count} integer points in the bounding box is feasible`)];
      return [check("exhaustive", bestV !== null && N.eq(bestV, best.value), `all ${count} integer points in the bounding box were checked (${feasibleCount} feasible); the best objective is ${bestV === null ? "none" : qstr(P.sense === "max" ? N.add(bestV, P.c0) : N.add(N.neg(bestV), P.c0))}`)];
    },
  };
}

// ---------------------------------------------------------------- games
function matrixOf(u, what) {
  const rows = listOf(u, what).map((r) => listOf(r, "a matrix row").map((v) => { const q = ratOf(v); if (!q) throw refuse("payoffs must be numbers"); return q; }));
  if (!rows.length || rows.some((r) => r.length !== rows[0].length)) throw refuse("the payoff matrix must be rectangular");
  if (rows.length > 8 || rows[0].length > 8) throw refuse("games up to 8 x 8 are supported");
  return rows;
}
const vecText = (v) => `(${v.map(qstr).join(", ")})`;
function cmdMatrixGame(args) {
  if (args.length !== 1) throw refuse("matrixgame(A)");
  const A = matrixOf(args[0], "a payoff matrix");
  const m = A.length, n = A[0].length;
  // row player: max v s.t. sum_i p_i A_ij >= v, sum p = 1, p >= 0  (variables p_1..p_m, v)
  const rows = [], ops = [], b = [];
  for (let j = 0; j < n; j++) { rows.push([...A.map((r) => r[j]), N.NEG_ONE]); ops.push(">="); b.push(N.ZERO); }
  rows.push([...Array(m).fill(N.ONE), N.ZERO]); ops.push("="); b.push(N.ONE);
  for (let i = 0; i < m; i++) { const r = Array(m + 1).fill(N.ZERO); r[i] = N.ONE; rows.push(r); ops.push(">="); b.push(N.ZERO); }
  const cR = [...Array(m).fill(N.ZERO), N.ONE];
  const R = lpSolve(cR, rows, ops, b);
  // column player: min w s.t. sum_j A_ij q_j <= w
  const rows2 = [], ops2 = [], b2 = [];
  for (let i = 0; i < m; i++) { rows2.push([...A[i], N.NEG_ONE]); ops2.push("<="); b2.push(N.ZERO); }
  rows2.push([...Array(n).fill(N.ONE), N.ZERO]); ops2.push("="); b2.push(N.ONE);
  for (let j = 0; j < n; j++) { const r = Array(n + 1).fill(N.ZERO); r[j] = N.ONE; rows2.push(r); ops2.push(">="); b2.push(N.ZERO); }
  const C = lpSolve([...Array(n).fill(N.ZERO), N.NEG_ONE], rows2, ops2, b2);
  if (R.status !== "optimal" || C.status !== "optimal") throw refuse("the game LP did not solve");
  const p = R.x.slice(0, m), v = R.x[m], q = C.x.slice(0, n);
  // pure saddle points
  const saddles = [];
  for (let i = 0; i < m; i++) for (let j = 0; j < n; j++) if (A[i].every((x) => !N.lt(x, A[i][j])) && A.every((r) => !N.lt(A[i][j], r[j]))) saddles.push(`(R${i + 1}, C${j + 1})`);
  return {
    answers: [{ kind: "exact", label: "value", tree: X.num(v) }, ansText("row strategy", vecText(p)), ansText("column strategy", vecText(q)), ansText("saddle points", saddles.length ? saddles.join(", ") : "none (mixed strategies are needed)")],
    steps: [step("game.lp", "Solve the row player's linear program", "Maximise v subject to every column giving the row player at least v, with probabilities summing to 1."), step("game.dual", "Solve the column player's program", "Minimise w subject to every row giving the row player at most w; by the minimax theorem v = w.")],
    checks: () => {
      const guaranteeRow = Array.from({ length: n }, (_, j) => dot(p, A.map((r) => r[j])));
      const guaranteeCol = A.map((r) => dot(r, q));
      const minRow = guaranteeRow.reduce((a, x) => (N.lt(x, a) ? x : a));
      const maxCol = guaranteeCol.reduce((a, x) => (N.lt(a, x) ? x : a));
      const probs = (w) => w.every((x) => !N.isNeg(x)) && N.eq(w.reduce(N.add, N.ZERO), N.ONE);
      return [check("row guarantee", probs(p) && N.eq(minRow, v), `against every pure column the row strategy earns at least ${qstr(minRow)}`), check("column guarantee", probs(q) && N.eq(maxCol, v), `against every pure row the column strategy concedes at most ${qstr(maxCol)}`)];
    },
  };
}
function solveLinear(M, rhs) { // exact Gauss; unique solution or null
  const k = M.length, w = M[0].length;
  if (k !== w) return null;
  const T = M.map((r, i) => [...r, rhs[i]]);
  for (let c = 0; c < w; c++) {
    let r = c; while (r < k && N.isZero(T[r][c])) r++;
    if (r === k) return null;
    [T[c], T[r]] = [T[r], T[c]];
    const pv = T[c][c]; T[c] = T[c].map((v) => N.div(v, pv));
    for (let i = 0; i < k; i++) if (i !== c && !N.isZero(T[i][c])) { const f = T[i][c]; T[i] = T[i].map((v, j) => N.sub(v, N.mul(f, T[c][j]))); }
  }
  return T.map((r) => r[w]);
}
function subsets(n, k) { const out = []; const rec = (s, cur) => { if (cur.length === k) { out.push(cur.slice()); return; } for (let i = s; i < n; i++) { cur.push(i); rec(i + 1, cur); cur.pop(); } }; rec(0, []); return out; }
function isNash(A, B, p, q) {
  const m = A.length, n = A[0].length;
  const u = A.map((r) => dot(r, q)), w = Array.from({ length: n }, (_, j) => dot(p, B.map((r) => r[j])));
  const pu = dot(p, u), qw = dot(q, w);
  return u.every((x) => !N.lt(pu, x)) && w.every((x) => !N.lt(qw, x)) && [p, q].every((v) => v.every((x) => !N.isNeg(x)) && N.eq(v.reduce(N.add, N.ZERO), N.ONE)) && m > 0;
}
function cmdNash(args) {
  if (args.length !== 2) throw refuse("nashequilibria(A, B)");
  const A = matrixOf(args[0], "the row player's payoffs"), B = matrixOf(args[1], "the column player's payoffs");
  const m = A.length, n = A[0].length;
  if (B.length !== m || B[0].length !== n) throw refuse("the two payoff matrices must have the same shape");
  if (m > 5 || n > 5) throw refuse("support enumeration is limited to 5 x 5 games");
  // pure equilibria: mutual best responses
  const pure = [];
  for (let i = 0; i < m; i++) for (let j = 0; j < n; j++) if (A.every((r) => !N.lt(A[i][j], r[j])) && B[i].every((x) => !N.lt(B[i][j], x))) pure.push([i, j]);
  // support enumeration (equal-size supports, k >= 2)
  const mixed = []; const seen = new Set();
  for (let k = 2; k <= Math.min(m, n); k++) for (const I of subsets(m, k)) for (const J of subsets(n, k)) {
    // q on J: A_I,J q = u 1, sum q = 1 ; unknowns q_J, u
    const Mq = [...I.map((i) => [...J.map((j) => A[i][j]), N.NEG_ONE]), [...J.map(() => N.ONE), N.ZERO]];
    const sq = solveLinear(Mq, [...I.map(() => N.ZERO), N.ONE]);
    const Mp = [...J.map((j) => [...I.map((i) => B[i][j]), N.NEG_ONE]), [...I.map(() => N.ONE), N.ZERO]];
    const sp = solveLinear(Mp, [...J.map(() => N.ZERO), N.ONE]);
    if (!sq || !sp) continue;
    const q = Array(n).fill(N.ZERO), p = Array(m).fill(N.ZERO);
    J.forEach((j, t) => { q[j] = sq[t]; }); I.forEach((i, t) => { p[i] = sp[t]; });
    if (![...p, ...q].every((x) => !N.isNeg(x))) continue;
    if (!I.every((i) => N.isPos(p[i])) || !J.every((j) => N.isPos(q[j]))) continue;
    if (!isNash(A, B, p, q)) continue;
    const key = vecText(p) + vecText(q);
    if (!seen.has(key)) { seen.add(key); mixed.push({ p, q }); }
  }
  const answers = [ansNum("number of pure equilibria", pure.length), ansText("pure equilibria", pure.length ? `{${pure.map(([i, j]) => `(R${i + 1}, C${j + 1})`).join(", ")}}` : "{}")];
  if (mixed.length) answers.push(ansText("mixed equilibrium", `row ${vecText(mixed[0].p)}, column ${vecText(mixed[0].q)}`));
  if (mixed.length > 1) answers.push(ansText("mixed equilibria", mixed.map((e) => `row ${vecText(e.p)}, column ${vecText(e.q)}`).join("; ")));
  return {
    answers,
    steps: [step("nash.pure", "Pure equilibria: cells where each payoff is a best response to the other player's choice", pure.length ? pure.map(([i, j]) => `(R${i + 1}, C${j + 1})`).join(", ") : "none"),
      step("nash.support", "Mixed equilibria by support enumeration", "For each pair of equal-size supports, make the opponent indifferent across the support and check that no pure strategy outside it does better.")],
    checks: () => {
      // pure: recompute best-response sets per column (row player) and per row (column player)
      const brRow = Array.from({ length: n }, (_, j) => { const mx = A.map((r) => r[j]).reduce((a, x) => (N.lt(a, x) ? x : a)); return new Set(A.map((r, i) => (N.eq(r[j], mx) ? i : -1)).filter((i) => i >= 0)); });
      const brCol = B.map((r) => { const mx = r.reduce((a, x) => (N.lt(a, x) ? x : a)); return new Set(r.map((x, j) => (N.eq(x, mx) ? j : -1)).filter((j) => j >= 0)); });
      const pure2 = []; for (let i = 0; i < m; i++) for (let j = 0; j < n; j++) if (brRow[j].has(i) && brCol[i].has(j)) pure2.push(`${i},${j}`);
      const cs = [check("best responses", pure2.length === pure.length && pure.every(([i, j]) => pure2.includes(`${i},${j}`)), "intersecting the best-response sets of both players gives the same pure equilibria")];
      if (mixed.length) cs.push(check("mixed equilibria", mixed.every((e) => isNash(A, B, e.p, e.q)), "no pure deviation improves either player's expected payoff"));
      return cs;
    },
  };
}

export const LP_HANDLERS = { linprog: cmdLinprog, intprog: cmdIntprog, matrixgame: cmdMatrixGame, nashequilibria: cmdNash };

// used by the recogniser: true when the call's objective and constraints are all linear
export function isLinearProblem(node) {
  try { readProblem(node.args); return true; } catch (_) { return false; }
}
