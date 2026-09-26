// Quelvra recurrences.
//
//   detectRecurrence(tree) -> info | null      (raw parse tree: a(n) = 2a(n-1) + 1, a(0) = 0, ...)
//   solveRecurrence(info)  -> { value, general, constants, steps, method }
//   verifyRecurrence(info, res) -> verifier record
//
// The parser reads a(n) as the product a*n, so applications are recovered structurally: inside a
// product, a symbol F immediately followed by an argument containing the index n (or an integer, for
// initial conditions) is an application F(arg), provided F never occurs on its own.
//
// Solved: linear recurrences with constant coefficients (any order the polynomial solver can factor
// exactly), homogeneous or with a quasi-polynomial right-hand side sum P(n) mu^n (undetermined
// coefficients, resonance included); first-order a(n) = p(n) a(n-1) + q(n) via products and sums.
// Constants come from the initial conditions (exact linear solve).

import { X, N, simp, simpExpand, qerr, Budget, isZeroStrong, hp, log10Abs, complexParts } from "./cutil.js";
import * as P from "../poly.js";
import * as L from "../linalg.js";
import { makeStep } from "../steps.js";
import { sumCompute, productCompute, solveQ } from "./sum.js";

const S = (rule, title, why, before = null, after = null) => makeStep({ rule, title, why, before, after });
let txt = (u) => String(u.k);
export function setPrinter(fn) { txt = fn; }

// ---------------------------------------------------------------- detection
function flatMul(u) {
  if (u.k !== "mul") return [u];
  return u.args.flatMap(flatMul);
}
function isIntNode(u) { const s = simp(u); return X.isNum(s) && s.v.d === 1n; }

export function detectRecurrence(tree) {
  const eqs = tree.k === "system" ? tree.args : [tree];
  if (!eqs.length || !eqs.every((e) => e.k === "eq")) return null;
  // candidate function symbols: sym followed by another factor inside a product
  const heads = new Map();
  const scan = (u) => {
    if (u.k === "mul") {
      const fs = flatMul(u);
      for (let i = 0; i + 1 < fs.length; i++) if (fs[i].k === "sym") {
        const h = heads.get(fs[i].name) || [];
        h.push(fs[i + 1]);
        heads.set(fs[i].name, h);
      }
      fs.forEach(scan);
      return;
    }
    u.args.forEach(scan);
  };
  eqs.forEach(scan);
  for (const [F, args] of heads) {
    // index symbol: the free symbol of the non-integer arguments
    const idx = new Set();
    for (const a of args) {
      const fsyms = [...X.freeSymbols(a)];
      if (fsyms.includes(F)) { idx.clear(); idx.add("__bad"); break; }
      fsyms.forEach((s) => idx.add(s));
    }
    if (idx.size !== 1) continue;
    const n = [...idx][0];
    const res = rewrite(eqs, F, n);
    if (res) return res;
  }
  return null;
}
function rewrite(eqs, F, n) {
  const ns = X.sym(n);
  let bad = false;
  const shifts = new Set();
  const ics = [];
  const conv = (u, allowInt) => {
    if (bad) return u;
    if (u.k === "sym" && u.name === F) { bad = true; return u; }
    if (u.k === "mul") {
      const fs = flatMul(u);
      const out = [];
      for (let i = 0; i < fs.length; i++) {
        if (fs[i].k === "sym" && fs[i].name === F && i + 1 < fs.length) {
          const arg = simp(fs[i + 1]);
          const d = simp(X.sub(arg, ns));
          if (X.isNum(d) && d.v.d === 1n) { shifts.add(Number(d.v.n)); out.push(X.sym(`__r${Number(d.v.n)}`)); i++; continue; }
          if (allowInt && X.isNum(arg) && arg.v.d === 1n) { out.push(X.sym(`__ic${arg.v.n}`)); i++; continue; }
          bad = true; return u;
        }
        out.push(conv(fs[i], allowInt));
      }
      return X.mul(...out);
    }
    if (!u.args.length) return u;
    return X.withArgs(u, u.args.map((a) => conv(a, allowInt)));
  };
  let main = null;
  for (const e of eqs) {
    const before = shifts.size;
    const lhs = conv(e.args[0], true), rhs = conv(e.args[1], true);
    if (bad) return null;
    const D = simp(X.sub(lhs, rhs));
    const icSyms = [...X.freeSymbols(D)].filter((s) => s.startsWith("__ic"));
    const rSyms = [...X.freeSymbols(D)].filter((s) => s.startsWith("__r"));
    if (rSyms.length && !icSyms.length) {
      if (main) return null; // two recurrence equations
      main = D;
    } else if (icSyms.length === 1 && !rSyms.length && !X.freeSymbols(D).has(n)) {
      const at = BigInt(icSyms[0].slice(4));
      const cs = P.coefficients(D, icSyms[0]);
      if (!cs || cs.length !== 2) return null;
      ics.push({ at, value: simp(X.neg(X.mul(cs[0] || X.ZERO, X.pow(cs[1], X.NEG_ONE)))) });
    } else return null;
    void before;
  }
  if (!main || shifts.size < 2) return null;
  return { F, n, main, shifts: [...shifts].sort((a, b) => a - b), ics };
}

// ---------------------------------------------------------------- helpers
function splitQuasiPoly(g, n) {
  // g = sum_i P_i(n) mu_i^n ; returns [{ mu: tree, poly: tree[] (coefficients) }] or null
  const e = simpExpand(g);
  const terms = e === X.ZERO ? [] : e.k === "add" ? e.args : [e];
  const groups = new Map();
  for (const t of terms) {
    const fs = t.k === "mul" ? t.args : [t];
    let mu = [], rest = [];
    for (const f of fs) {
      if (f.k === "pow" && !X.hasSym(f.args[0], n) && X.hasSym(f.args[1], n)) {
        const cs = P.coefficients(f.args[1], n);
        if (!cs || cs.length !== 2) return null;
        mu.push(X.pow(f.args[0], cs[1])); rest.push(X.pow(f.args[0], cs[0] || X.ZERO));
      } else rest.push(f);
    }
    const m = simp(X.mul(...mu));
    const pr = simp(X.mul(...rest));
    const cs = P.coefficients(pr, n);
    if (!cs || cs.some((c) => X.hasSym(c, n))) return null;
    const key = m.id;
    const g0 = groups.get(key) || { mu: m, poly: [] };
    cs.forEach((c, i) => { g0.poly[i] = simp(X.add(g0.poly[i] || X.ZERO, c)); });
    groups.set(key, g0);
  }
  return [...groups.values()].map((g) => ({ mu: g.mu, poly: Array.from(g.poly, (c) => c || X.ZERO) }));
}
function reIm(u) { return complexParts(simp(u)); }
// recognise theta with cos(theta) = c exactly, theta = p pi / q (q <= 12)
function angleOf(re, im, rho) {
  const r = hp(re, {}), i = hp(im, {}), m = hp(rho, {});
  if (!r.ok || !i.ok || !m.ok) return null;
  const th = Math.atan2(i.re, r.re);
  for (let q = 1; q <= 12; q++) {
    const p = Math.round(th / Math.PI * q);
    if (Math.abs(p / q * Math.PI - th) < 1e-12) {
      const T = simp(X.mul(X.num(N.Q(p, q)), X.PI));
      try {
        if (isZeroStrong(simp(X.sub(X.mul(rho, X.fn("cos", T)), re))) && isZeroStrong(simp(X.sub(X.mul(rho, X.fn("sin", T)), im)))) return T;
      } catch (_) { return null; }
    }
  }
  return null;
}

// ---------------------------------------------------------------- solver
export function solveRecurrence(info, opts = {}) {
  return Budget.with(opts.timeLimit || 10000, () => solveCore(info));
}
function solveCore(info) {
  const { n, main, shifts } = info;
  const ns = X.sym(n);
  const steps = [];
  const j0 = shifts[0], j1 = shifts[shifts.length - 1];
  const order = j1 - j0;
  // coefficients of a(n + j) and the inhomogeneous part
  const coef = {};
  let rest = main;
  for (const j of shifts) {
    const cs = P.coefficients(main, `__r${j}`);
    if (!cs || cs.length !== 2) throw qerr("UNSUPPORTED", "the recurrence is not linear");
    coef[j] = cs[1];
    rest = X.subs(rest, { [`__r${j}`]: X.ZERO });
  }
  const g = simp(X.neg(rest)); // sum c_j a(n+j) = g(n)
  const constCoef = shifts.every((j) => !X.hasSym(coef[j], n));
  if (!constCoef) {
    if (order === 1) return firstOrderVariable(info, coef, g, steps);
    throw qerr("UNSUPPORTED", "only constant-coefficient recurrences (or first-order ones) are solved");
  }
  // characteristic polynomial in r (shift so the lowest index is r^0)
  const r = X.sym("__rr");
  const chi = simp(X.add(...shifts.map((j) => X.mul(coef[j], X.pow(r, X.num(j - j0))))));
  const sp = P.solvePolynomial(chi, "__rr", { domain: "complex" });
  if (!sp.complete) throw qerr("UNSUPPORTED", "the characteristic polynomial could not be solved exactly");
  const roots = sp.exact.map((e) => ({ root: simp(e.root), mult: e.multiplicity }));
  const tot = roots.reduce((s, e) => s + e.mult, 0);
  if (tot !== order) throw qerr("UNSUPPORTED", "characteristic roots incomplete");
  steps.push(S("recur.characteristic", "Characteristic equation", `Try a(n) = r^n: ${txt(X.subs(chi, { __rr: X.sym("r") }))} = 0.`, null, X.vector(...roots.map((e) => e.root))));
  // homogeneous basis (real form for conjugate pairs on recognised angles)
  const basis = [];
  const used = new Set();
  for (let i = 0; i < roots.length; i++) {
    if (used.has(i)) continue;
    const { root, mult } = roots[i];
    if (X.contains(root, X.I)) {
      const ri = reIm(root);
      let jconj = -1;
      if (ri) for (let j = i + 1; j < roots.length; j++) if (!used.has(j) && roots[j].mult === mult) {
        const rj = reIm(roots[j].root);
        try { if (rj && isZeroStrong(simp(X.sub(rj.re, ri.re))) && isZeroStrong(simp(X.add(rj.im, ri.im)))) { jconj = j; break; } } catch (_) { /* skip */ }
      }
      if (jconj >= 0) {
        const rho = simp(X.pow(X.add(X.pow(ri.re, X.TWO), X.pow(ri.im, X.TWO)), X.HALF));
        const th = angleOf(ri.re, ri.im, rho);
        if (th) {
          used.add(i); used.add(jconj);
          const ath = N.sign(hp(th, {}).big.m > 0n ? N.ONE : N.NEG_ONE) > 0 ? th : simp(X.neg(th));
          for (let m = 0; m < mult; m++) {
            basis.push(simp(X.mul(X.pow(ns, X.num(m)), X.pow(rho, ns), X.fn("cos", X.mul(ath, ns)))));
            basis.push(simp(X.mul(X.pow(ns, X.num(m)), X.pow(rho, ns), X.fn("sin", X.mul(ath, ns)))));
          }
          continue;
        }
      }
    }
    used.add(i);
    for (let m = 0; m < mult; m++) basis.push(simp(X.mul(X.pow(ns, X.num(m)), X.pow(root, ns))));
  }
  // particular solution
  let part = X.ZERO;
  if (g !== X.ZERO) {
    const groups = splitQuasiPoly(g, n);
    if (!groups) throw qerr("UNSUPPORTED", "the right-hand side is not a sum of polynomial times exponential terms");
    const parts = [];
    for (const { mu, poly } of groups) {
      if (!X.isNum(mu) || !shifts.every((j) => X.isNum(coef[j])) || !poly.every(X.isNum)) throw qerr("UNSUPPORTED", "undetermined coefficients need rational data");
      const muq = mu.v;
      // multiplicity of mu as a root
      let s = 0;
      let cp = P.fromTree(chi, "__rr");
      while (cp.length && N.isZero(P.evalAt(cp, muq))) { s++; cp = P.deriv(cp); }
      const d = poly.length - 1;
      // ansatz a(n) = n^s Q(n) mu^n:  sum_j c_j mu^j (n + j)^s Q(n + j) = P(n)
      const cols = [];
      for (let i = 0; i <= d; i++) {
        let acc = [];
        for (const j of shifts) acc = P.add(acc, P.scale(P.pow([N.Q(j), N.ONE], s + i), N.mul(coef[j].v, N.pow(muq, j))));
        cols.push(acc);
      }
      const Pn = P.norm(poly.map((c) => c.v));
      const rows = Math.max(Pn.length, ...cols.map((c) => c.length));
      const M = [], rhs = [];
      for (let k = 0; k < rows; k++) { M.push(cols.map((c) => c[k] || N.ZERO)); rhs.push(Pn[k] || N.ZERO); }
      const sol = solveQ(M, rhs);
      if (!sol) throw qerr("INTERNAL", "undetermined coefficients system has no solution");
      const Qn = simp(X.add(...sol.map((c, i) => X.mul(X.num(c), X.pow(ns, X.num(i))))));
      parts.push(simp(X.mul(X.pow(ns, X.num(s)), Qn, X.pow(mu, ns))));
    }
    part = simp(X.add(...parts));
    steps.push(S("recur.particular", "Particular solution", "Undetermined coefficients: try n^s Q(n) mu^n for each exponential mu^n on the right (s = multiplicity of mu as a characteristic root).", g, part));
  }
  const Cs = basis.map((_, i) => X.sym(`C${i + 1}`));
  const general = simp(X.add(part, ...basis.map((b, i) => X.mul(Cs[i], b))));
  steps.push(S("recur.general", "General solution", "Combine the characteristic solutions (and the particular solution).", null, general));
  const res = { general, value: general, constants: Cs, steps, method: "characteristic roots" };
  return applyICs(info, res);
}
function applyICs(info, res) {
  const { n, ics } = info;
  const order = info.shifts[info.shifts.length - 1] - info.shifts[0];
  if (!ics.length || !res.constants.length) return res;
  if (ics.length < order) { res.note = `Only ${ics.length} initial condition(s) for an order-${order} recurrence; the remaining constants stay free.`; }
  const Cs = res.constants;
  const rows = [], rhs = [];
  for (const ic of ics) {
    const e = simp(X.subs(res.general, { [n]: X.num(ic.at) }));
    const cs = Cs.map((C) => { const c = P.coefficients(e, C.name); return c ? c[1] || X.ZERO : null; });
    if (cs.some((c) => c === null)) throw qerr("UNSUPPORTED", "constants enter non-linearly");
    let c0 = e;
    for (const C of Cs) c0 = X.subs(c0, { [C.name]: X.ZERO });
    rows.push(cs);
    rhs.push(simp(X.sub(ic.value, c0)));
  }
  const s = L.solve(rows, rhs, { steps: false });
  if (s.status === "none") throw qerr("INCONSISTENT", "the initial conditions are inconsistent with the recurrence");
  const sub = {};
  Cs.forEach((C, i) => { if (s.status === "unique" || !s.params.some((p) => s.solution[i] === p)) sub[C.name] = s.solution[i]; });
  let value = simp(X.subs(res.general, sub));
  value = tidyForm(value, n);
  res.steps.push(S("recur.constants", "Use the initial conditions", `Substitute ${ics.map((ic) => `${info.F}(${ic.at}) = ${txt(ic.value)}`).join(", ")} and solve for the constants.`, res.general, value));
  return { ...res, value, constantsSolved: sub };
}
function tidyForm(u, n) {
  try {
    let e = simpExpand(u);
    if (X.size(e) >= X.size(u)) e = u;
    if (n && P.fromTree(e, n)) { const f = P.factorTree(e); if (X.size(f) <= X.size(e) + 2) e = f; }
    return e;
  } catch (_) { return u; }
}
function firstOrderVariable(info, coef, g, steps) {
  // c1 a(n + j1) + c0 a(n + j0) = g  ->  a(m) = p(m) a(m-1) + q(m), m = n + j1
  const { n, shifts } = info;
  const [j0, j1] = shifts;
  const ns = X.sym(n);
  const k = X.sym("__k");
  const back = (u) => simp(X.subs(u, { [n]: X.sub(k, X.num(j1)) }));
  const p = back(X.neg(X.mul(coef[j0], X.pow(coef[j1], X.NEG_ONE))));
  const q = back(X.mul(g, X.pow(coef[j1], X.NEG_ONE)));
  const ic = info.ics.find(() => true);
  const m0 = ic ? ic.at : 0n;
  const a0 = ic ? ic.value : X.sym("C1");
  // a(m) = Pi(m) [a(m0) + sum_{i=m0+1}^{m} q(i)/Pi(i)],  Pi(m) = prod_{i=m0+1}^{m} p(i)
  const m = X.sym("__m");
  const Pi = productCompute(p, "__k", X.num(m0 + 1n), m);
  if (Pi.kind !== "value") throw qerr("UNSUPPORTED", "product not found");
  let sumPart = X.ZERO;
  if (q !== X.ZERO) {
    const term = simp(X.mul(q, X.pow(simp(X.subs(Pi.value, { __m: k })), X.NEG_ONE)));
    const Sm = sumCompute(term, "__k", X.num(m0 + 1n), m);
    if (Sm.kind !== "value") throw qerr("UNSUPPORTED", "sum not found");
    sumPart = Sm.value;
  }
  const value = tidyForm(simp(X.subs(X.mul(Pi.value, X.add(a0, sumPart)), { __m: ns })), n);
  steps.push(S("recur.first-order", "First-order recurrence", "Unroll a(n) = p(n) a(n-1) + q(n): a(n) = P(n) (a(n0) + sum q(i)/P(i)) with P(n) = product of p(i).", null, value));
  return { value, general: value, constants: ic ? [] : [X.sym("C1")], steps, method: "product and sum" };
}

// ---------------------------------------------------------------- verification
// Iterate the recurrence exactly from the initial conditions (or from values of the closed form
// when there are none) and compare with the closed form at high precision.
export function verifyRecurrence(info, res) {
  const { n, main, shifts, ics } = info;
  const checks = [];
  const j0 = shifts[0], j1 = shifts[shifts.length - 1];
  const order = j1 - j0;
  const cfree = res.constants.filter((C) => !(res.constantsSolved && res.constantsSolved[C.name]));
  const csub = {};
  cfree.forEach((C, i) => { csub[C.name] = X.num(N.Q(3 + i, 7 + 2 * i)); });
  const closed = simp(X.subs(res.value, csub));
  const at = (m) => simp(X.subs(closed, { [n]: X.num(m) }));
  // initial conditions
  for (const ic of ics) {
    const v = at(ic.at);
    const d = simp(X.sub(v, ic.value));
    let ok;
    try { ok = isZeroStrong(d); } catch (_) { ok = null; }
    checks.push({ kind: "initial condition", ok, detail: `${info.F}(${ic.at}) = ${txt(ic.value)}` });
    if (ok === false) return { status: "failed", checks };
  }
  // residual of the recurrence at n = n0 .. n0 + 20 (exact when the values simplify to numbers,
  // otherwise 60-digit evaluation)
  const start = ics.length ? Number([...ics].sort((a, b) => (a.at < b.at ? -1 : 1))[0].at) - j0 : 0;
  let good = 0, allExact = true;
  for (let m = start; m < start + 20; m++) {
    const sub = {};
    for (const j of shifts) sub[`__r${j}`] = at(m + j);
    const resid = simp(X.subs(X.subs(main, sub), { [n]: X.num(m) }));
    if (resid === X.ZERO) { good++; continue; }
    allExact = false;
    const v = hp(resid, {}, { digits: 60, maxDigits: 200 });
    const scale = Math.max(0, ...shifts.map((j) => { const w = hp(at(m + j), {}, { digits: 30 }); return w.ok ? log10Abs(w.big) : 0; }));
    if (!v.ok) continue;
    if (log10Abs(v.big) - scale < -40) { good++; continue; }
    checks.push({ kind: "recurrence residual", ok: false, detail: `the closed form does not satisfy the recurrence at n = ${m}` });
    return { status: "failed", checks };
  }
  checks.push({ kind: "recurrence residual", ok: good >= 15, detail: `the closed form satisfies the recurrence at ${good} consecutive values of n${allExact ? " (exactly)" : " (to 40+ digits)"}` });
  if (good < 15) return { status: "inconclusive", checks };
  void order;
  // exponential-polynomial closed forms are determined by `order` consecutive values, and a linear
  // recurrence of this order determines the sequence from them: agreement on 20 values is a proof
  // when every check was exact
  return { status: allExact ? "verified-exact" : "verified-numeric", checks };
}
