// Quelvra ordinary differential equations.
//
//   detectODE(tree)            -> info | null   (raw parse tree; y', y'', dy/dx, d^2y/dx^2, f'(x),
//                                               diff(y, x), y(x), initial conditions y(0) = 1, y'(0) = 0)
//   solveODE(info, {log})      -> { solutions: [{ kind: "explicit"|"implicit", dep, tree }], general,
//                                   constants, method, steps, conditions, approximate? }
//   verifyODE(info, res)       -> verifier record (substitution into the ORIGINAL equation, symbolic
//                                   then 60-digit numeric; initial conditions; independence of the basis)
//
// Methods: first order - separable, linear (integrating factor), exact (with integrating factors
// mu(x) or mu(y)), Bernoulli, homogeneous y/x; linear with constant coefficients of any order the
// polynomial solver can factor exactly (real distinct / repeated / complex roots in real form),
// undetermined coefficients for quasi-polynomial forcing (resonance included, via the exponential
// shift rule), variation of parameters for other forcing; Cauchy-Euler (x = e^t); first-order
// constant-matrix linear systems via eigenvectors. Initial value problems solve for the constants
// exactly. When no symbolic method applies to an IVP, a Dormand-Prince numeric solution is
// returned, labelled approximate.

import { X, N, simp, simpExpand, qerr, Budget, isZeroStrong, hp, log10Abs, complexParts } from "./cutil.js";
import * as P from "../poly.js";
import * as L from "../linalg.js";
import * as NU from "../numeric.js";
import { diff } from "./diff.js";
import { makeStep } from "../steps.js";
import { together, numerDenom, makeCtx } from "../simplify.js";

let INTEGRATE = null;
try { INTEGRATE = (await import("./integrate.js")).integrate; } catch (_) { INTEGRATE = null; }

const S = (rule, title, why, before = null, after = null) => makeStep({ rule, title, why, before, after });
let txt = (u) => String(u.k);
export function setPrinter(fn) { txt = fn; }
const dsym = (dep, m) => (m === 0 ? X.sym(dep) : X.sym(`__D${m}_${dep}`));
const derivInfo = (name) => { const m = /^__D(\d+)_(.+)$/.exec(name); return m ? { m: Number(m[1]), dep: m[2] } : null; };

// ---------------------------------------------------------------- detection
function flatMul(u) { return u.k === "mul" ? u.args.flatMap(flatMul) : [u]; }
function primeDepth(u) { let m = 0; while (u.k === "fn" && u.name === "prime" && u.args.length === 1) { u = u.args[0]; m++; } return { m, base: u }; }

export function detectODE(tree) {
  const eqs = tree.k === "system" ? tree.args : [tree];
  if (!eqs.length || !eqs.every((e) => e.k === "eq")) return null;
  const deps = new Set();
  let xname = null;
  let hasDeriv = false;
  // pass 1: dependent names and the independent variable
  const scan = (u) => {
    if (u.k === "fn" && u.name === "prime") {
      const { m, base } = primeDepth(u);
      if (base.k === "sym") { deps.add(base.name); hasDeriv = true; }
      else if (base.k === "fn" && base.args.length === 1) { deps.add(base.name); hasDeriv = true; if (base.args[0].k === "sym") xname = xname || base.args[0].name; }
      void m;
      return;
    }
    if (u.k === "deriv") {
      const [f, v] = u.args;
      if (f.k === "sym") deps.add(f.name);
      else if (f.k === "fn" && f.args.length === 1) deps.add(f.name);
      if (v.k === "sym") xname = xname || v.name;
      hasDeriv = true;
      return;
    }
    if (u.k === "mul") {
      const fs = flatMul(u);
      for (let i = 0; i + 3 < fs.length; i++) {
        const lb = leibniz(fs, i);
        if (lb) { deps.add(lb.dep); xname = xname || lb.x; hasDeriv = true; }
      }
    }
    u.args.forEach(scan);
  };
  eqs.forEach(scan);
  if (!hasDeriv || !deps.size) return null;
  // applications Y(t): a dependent (or its derivative) followed by a symbol
  if (!xname) {
    const seen = new Set();
    const app = (u) => {
      if (u.k === "mul") {
        const fs = flatMul(u);
        for (let i = 0; i + 1 < fs.length; i++) {
          const b = primeDepth(fs[i]).base;
          if (b.k === "sym" && deps.has(b.name) && fs[i + 1].k === "sym" && !deps.has(fs[i + 1].name)) seen.add(fs[i + 1].name);
        }
      }
      u.args.forEach(app);
    };
    eqs.forEach(app);
    if (seen.size === 1) xname = [...seen][0];
  }
  if (!xname) {
    const free = new Set();
    eqs.forEach((e) => X.freeSymbols(e).forEach((s) => free.add(s)));
    for (const d of deps) free.delete(d);
    free.delete("d");
    if (free.has("x") && !deps.has("x")) xname = "x";
    else if (free.has("t")) xname = "t";
    else if (!deps.has("x") && free.size === 0) xname = "x";
    else if (deps.has("x")) xname = "t";
    else if (free.size === 1) xname = [...free][0];
    else xname = "x";
  }
  if (deps.has(xname)) return null;
  // pass 2: rewrite
  const odes = [], ics = [];
  for (const e of eqs) {
    const ic = asIC(e, deps, xname);
    if (ic) { ics.push(ic); continue; }
    const lhs = rw(e.args[0], deps, xname), rhs = rw(e.args[1], deps, xname);
    if (!lhs || !rhs) return null;
    odes.push({ lhs: simp(lhs), rhs: simp(rhs), F: simp(X.sub(lhs, rhs)) });
  }
  if (!odes.length) return null;
  const order = {};
  for (const d of deps) order[d] = 0;
  for (const o of odes) for (const s of X.freeSymbols(o.F)) { const di = derivInfo(s); if (di && deps.has(di.dep)) order[di.dep] = Math.max(order[di.dep], di.m); }
  if (!Object.values(order).some((m) => m > 0)) return null;
  return { deps: [...deps], x: xname, odes, ics, order };
}
function leibniz(fs, i) {
  // [d^m, Y, d^-1, x^m]
  const dpow = (u) => (u.k === "sym" && u.name === "d" ? 1 : u.k === "pow" && u.args[0].k === "sym" && u.args[0].name === "d" && X.isInt(u.args[1]) ? Number(u.args[1].v.n) : 0);
  const m = dpow(fs[i]);
  if (m < 1) return null;
  const Y = fs[i + 1];
  if (Y.k !== "sym" || Y.name === "d") return null;
  if (dpow(fs[i + 2]) !== -1) return null;
  const xf = fs[i + 3];
  const xm = xf.k === "sym" ? [xf.name, 1] : xf.k === "pow" && xf.args[0].k === "sym" && X.isInt(xf.args[1]) ? [xf.args[0].name, Number(xf.args[1].v.n)] : null;
  if (!xm || xm[1] !== m) return null;
  return { dep: Y.name, x: xm[0], m };
}
function depOf(u, deps) {
  // Y, Y', f(x), f'(x) -> { dep, m, arg? }
  const { m, base } = primeDepth(u);
  if (base.k === "sym" && deps.has(base.name)) return { dep: base.name, m };
  if (base.k === "fn" && deps.has(base.name) && base.args.length === 1) return { dep: base.name, m, arg: base.args[0] };
  if (u.k === "deriv") {
    const [f, v, k] = u.args;
    const mm = k ? Number(simp(k).v.n) : 1;
    if (f.k === "sym" && deps.has(f.name)) return { dep: f.name, m: mm, arg: null, wrt: v };
    if (f.k === "fn" && deps.has(f.name)) return { dep: f.name, m: mm, arg: f.args[0], wrt: v };
  }
  return null;
}
function rw(u, deps, xn) {
  let bad = false;
  const go = (w) => {
    if (bad) return w;
    const d = depOf(w, deps);
    if (d) {
      if (d.arg && !(d.arg.k === "sym" && d.arg.name === xn)) { bad = true; return w; }
      return dsym(d.dep, d.m);
    }
    if (w.k === "mul") {
      const fs = flatMul(w);
      const out = [];
      for (let i = 0; i < fs.length; i++) {
        if (i + 3 < fs.length) {
          const lb = leibniz(fs, i);
          if (lb && deps.has(lb.dep)) { out.push(dsym(lb.dep, lb.m)); i += 3; continue; }
        }
        const dd = depOf(fs[i], deps);
        if (dd && !dd.arg && i + 1 < fs.length && fs[i + 1].k === "sym" && fs[i + 1].name === xn) { out.push(dsym(dd.dep, dd.m)); i++; continue; }
        out.push(go(fs[i]));
      }
      return X.mul(...out);
    }
    if (!w.args.length) return w;
    return X.withArgs(w, w.args.map(go));
  };
  const r = go(u);
  if (bad) return null;
  // leftover d symbols mean an unrecognised Leibniz form
  if (X.freeSymbols(r).has("d")) return null;
  return r;
}
function asIC(e, deps, xn) {
  const [l, r] = e.args;
  if (X.freeSymbols(r).size && [...X.freeSymbols(r)].some((s) => deps.has(s) || s === xn)) return null;
  let d = null, at = null;
  const direct = depOf(l, deps);
  if (direct && direct.arg && !X.hasSym(direct.arg, xn)) { d = direct; at = direct.arg; }
  else if (l.k === "deriv" && l.args[0].k === "fn" && deps.has(l.args[0].name)) {
    // f'(0) parses as deriv(f(0), 0, 1)
    d = { dep: l.args[0].name, m: l.args[2] ? Number(simp(l.args[2]).v.n) : 1 }; at = l.args[0].args[0];
  } else if (l.k === "mul") {
    const fs = flatMul(l);
    if (fs.length === 2) {
      const dd = depOf(fs[0], deps);
      if (dd && !dd.arg && !X.hasSym(fs[1], xn) && ![...X.freeSymbols(fs[1])].some((s) => deps.has(s))) { d = dd; at = fs[1]; }
    }
  }
  if (!d) return null;
  if (X.hasSym(at, xn) || [...X.freeSymbols(at)].some((s) => deps.has(s))) return null;
  return { dep: d.dep, m: d.m, at: simp(at), value: simp(r) };
}

// ---------------------------------------------------------------- integration
function integ(f, xn) {
  f = simp(f);
  if (f === X.ZERO) return X.ZERO;
  if (!X.hasSym(f, xn)) return simp(X.mul(f, X.sym(xn)));
  let firstErr = null;
  if (INTEGRATE) {
    try { return simp(INTEGRATE(f, X.sym(xn)).F); } catch (e) { if (e && e.code === "TIMEOUT") throw e; firstErr = e; }
  }
  const q = quasiIntegrate(f, xn);
  if (q) return q;
  throw qerr("NOINTEGRAL", firstErr && firstErr.code === "NONELEMENTARY" ? firstErr.message : `could not integrate ${txt(f)}`);
}
// integral of a quasi-polynomial (sums of c x^j e^(lambda x) after writing sin/cos as exponentials)
function quasiIntegrate(f, xn) {
  const terms = quasiTerms(expForm(f), xn);
  if (!terms) return null;
  const x = X.sym(xn);
  const parts = [];
  for (const { c, j, lam } of terms) {
    if (lam === X.ZERO) { parts.push(X.mul(c, X.pow(x, X.num(j + 1)), X.num(N.Q(1, j + 1)))); continue; }
    // int x^j e^(lam x) = e^(lam x) sum_i (-1)^i j!/(j-i)! x^(j-i) / lam^(i+1)
    const inner = [];
    let fall = 1n;
    for (let i = 0; i <= j; i++) {
      if (i > 0) fall *= BigInt(j - i + 1);
      inner.push(X.mul(X.num(N.Q((i % 2 ? -1n : 1n) * fall)), X.pow(x, X.num(j - i)), X.pow(lam, X.num(-(i + 1)))));
    }
    parts.push(X.mul(c, X.exp(X.mul(lam, x)), X.add(...inner)));
  }
  const r = realify(simp(X.add(...parts)));
  return r;
}

// ---------------------------------------------------------------- complex-exponential machinery
function expForm(g) {
  const r = X.mapTree(g, (w) => {
    if (w.k !== "fn" || w.args.length !== 1) return w;
    const u = w.args[0];
    const eP = (s) => X.exp(X.mul(X.I, s, u)), eN = X.exp(X.neg(X.mul(X.I, u)));
    switch (w.name) {
      case "sin": return X.mul(X.add(X.exp(X.mul(X.I, u)), X.neg(eN)), X.pow(X.mul(X.TWO, X.I), X.NEG_ONE));
      case "cos": return X.mul(X.add(X.exp(X.mul(X.I, u)), eN), X.HALF);
      case "sinh": return X.mul(X.add(X.exp(u), X.neg(X.exp(X.neg(u)))), X.HALF);
      case "cosh": return X.mul(X.add(X.exp(u), X.exp(X.neg(u))), X.HALF);
      case "exp": return X.exp(u);
      default: void eP; return w;
    }
  });
  return simpExpand(r);
}
// c x^j e^(lam x) terms (c, lam free of x; lam may be complex)
function quasiTerms(e, xn) {
  const terms = e === X.ZERO ? [] : e.k === "add" ? e.args : [e];
  const out = [];
  for (const t of terms) {
    const fs = t.k === "mul" ? t.args : [t];
    let c = [], j = 0, lam = [];
    for (const f of fs) {
      if (!X.hasSym(f, xn)) { c.push(f); continue; }
      if (f.k === "sym") { j += 1; continue; }
      if (f.k === "pow" && f.args[0].k === "sym" && f.args[0].name === xn && X.isInt(f.args[1]) && f.args[1].v.n > 0n) { j += Number(f.args[1].v.n); continue; }
      if (f.k === "pow" && f.args[0] === X.E) {
        const cs = P.coefficients(f.args[1], xn);
        if (!cs || cs.length > 2 || cs.some((q) => X.hasSym(q, xn))) return null;
        lam.push(cs[1] || X.ZERO);
        if (cs[0] && cs[0] !== X.ZERO) c.push(X.exp(cs[0]));
        continue;
      }
      return null;
    }
    out.push({ c: simp(X.mul(...c)), j, lam: simp(X.add(...lam)) });
  }
  return out;
}
function realify(u) {
  if (!X.contains(u, X.I)) return u;
  const p = complexParts(u);
  if (!p) throw qerr("UNSUPPORTED", "could not separate real and imaginary parts");
  return simp(p.re);
}

// ---------------------------------------------------------------- linear structure
// F = sum_i a_i(x) D_i + b(x) with D_0 = y, D_i = y^(i); returns { a: [...], g: -b } or null
function linearForm(F, dep, n, xn) {
  const a = [];
  let rest = F;
  for (let i = 0; i <= n; i++) {
    const s = dsym(dep, i).name;
    const cs = P.coefficients(rest, s);
    if (!cs || cs.length > 2) return null;
    a[i] = cs[1] ? simp(cs[1]) : X.ZERO;
    rest = cs[0] || X.ZERO;
  }
  for (let i = 0; i <= n; i++) if ([...X.freeSymbols(a[i])].some((s) => s === dep || derivInfo(s))) return null;
  if ([...X.freeSymbols(rest)].some((s) => s === dep || derivInfo(s))) return null;
  return { a, g: simp(X.neg(rest)) };
}

// ---------------------------------------------------------------- constant coefficients
function charRoots(chi, rn) {
  const sp = P.solvePolynomial(chi, rn, { domain: "complex" });
  if (!sp.complete) throw qerr("UNSUPPORTED", "the characteristic polynomial could not be solved exactly");
  return sp.exact.map((e) => ({ root: simp(e.root), mult: e.multiplicity }));
}
// basis functions for roots (real form); mk(root, j) builds x^j e^(root x) style terms
function realBasis(roots, x, kind) {
  const basis = [];
  const used = new Set();
  const xs = X.sym(x);
  const powx = (j) => (kind === "euler" ? X.pow(X.fn("ln", xs), X.num(j)) : X.pow(xs, X.num(j)));
  const expo = (r) => (kind === "euler" ? X.pow(xs, r) : X.exp(X.mul(r, xs)));
  const trig = (f, b) => (kind === "euler" ? X.fn(f, X.mul(b, X.fn("ln", xs))) : X.fn(f, X.mul(b, xs)));
  for (let i = 0; i < roots.length; i++) {
    if (used.has(i)) continue;
    const { root, mult } = roots[i];
    if (X.contains(root, X.I)) {
      const pi = complexParts(root);
      let jc = -1;
      if (pi) for (let j = i + 1; j < roots.length; j++) {
        if (used.has(j) || roots[j].mult !== mult) continue;
        const pj = complexParts(roots[j].root);
        try { if (pj && isZeroStrong(simp(X.sub(pj.re, pi.re))) && isZeroStrong(simp(X.add(pj.im, pi.im)))) { jc = j; break; } } catch (_) { /* skip */ }
      }
      if (jc < 0) throw qerr("UNSUPPORTED", "complex roots without conjugates");
      used.add(i); used.add(jc);
      let b = pi.im;
      try { const v = hp(b, {}); if (v.ok && v.re < 0) b = simp(X.neg(b)); } catch (_) { /* keep */ }
      for (let j = 0; j < mult; j++) {
        basis.push(simp(X.mul(powx(j), expo(pi.re), trig("cos", b))));
        basis.push(simp(X.mul(powx(j), expo(pi.re), trig("sin", b))));
      }
      continue;
    }
    used.add(i);
    for (let j = 0; j < mult; j++) basis.push(simp(X.mul(powx(j), expo(root))));
  }
  return basis;
}
// particular solution of p(D) y = g for quasi-polynomial g (exponential shift rule)
function undetermined(pcoef, g, xn) {
  const terms = quasiTerms(expForm(g), xn);
  if (!terms) return null;
  const x = X.sym(xn);
  const groups = new Map();
  for (const t of terms) {
    const k = t.lam.id;
    const gr = groups.get(k) || { lam: t.lam, poly: [] };
    gr.poly[t.j] = gr.poly[t.j] ? simp(X.add(gr.poly[t.j], t.c)) : t.c;
    groups.set(k, gr);
  }
  const n = pcoef.length - 1;
  const r = X.sym("__r");
  const chi = simp(X.add(...pcoef.map((c, i) => X.mul(c, X.pow(r, X.num(i))))));
  const derivs = [chi];
  for (let k = 1; k <= n; k++) derivs.push(simp(diff(derivs[k - 1], r)));
  const parts = [];
  for (const { lam, poly } of groups.values()) {
    const pv = derivs.map((d) => simp(X.subs(d, { __r: lam })));
    let s = 0;
    while (s <= n && isZeroStrong(pv[s])) s++;
    if (s > n) throw qerr("INTERNAL", "zero operator");
    const d = poly.length - 1;
    // unknown R(x) = sum_{i<=d} r_i x^i; L[x^(s+i) e^(lam x)] = e^(lam x) sum_k p^(k)(lam)/k! D^k x^(s+i)
    const rows = [];
    for (let m = 0; m <= s + d; m++) rows.push(new Array(d + 1).fill(X.ZERO));
    for (let i = 0; i <= d; i++) {
      const e = s + i;
      let fall = 1n, kf = 1n;
      for (let k = 0; k <= Math.min(e, n); k++) {
        if (k > 0) { fall *= BigInt(e - k + 1); kf *= BigInt(k); }
        const coef = simp(X.mul(pv[k], X.num(N.Q(fall, kf))));
        rows[e - k][i] = simp(X.add(rows[e - k][i], coef));
      }
    }
    const rhs = rows.map((_, m) => (m <= d && poly[m] ? poly[m] : X.ZERO));
    // equations for powers x^0 .. x^(s+d); the ones below s are identically 0 = 0 for i-columns? keep all
    const sol = L.solve(rows, rhs, { steps: false });
    if (sol.status !== "unique") throw qerr("INTERNAL", "undetermined coefficients system is singular");
    const R = simp(X.add(...sol.solution.map((c, i) => X.mul(c, X.pow(x, X.num(i))))));
    parts.push(simp(X.mul(X.pow(x, X.num(s)), R, X.exp(X.mul(lam, x)))));
  }
  return realify(simp(X.add(...parts)));
}
function wronskian(fs, xn) {
  const n = fs.length;
  const rows = [];
  let cur = fs.slice();
  for (let i = 0; i < n; i++) { rows.push(cur); cur = cur.map((f) => simp(diff(f, X.sym(xn)))); }
  return rows;
}
function variationOfParameters(basis, g, an, xn, steps) {
  // W u' = (0, ..., 0, g / a_n), y_p = sum u_i y_i
  const n = basis.length;
  const W = wronskian(basis, xn);
  const rhs = new Array(n).fill(X.ZERO);
  rhs[n - 1] = simp(X.mul(g, X.pow(an, X.NEG_ONE)));
  let up;
  if (n === 2) {
    const [y1, y2] = basis, [d1, d2] = W[1];
    const Wd = simpExpand(X.sub(X.mul(y1, d2), X.mul(y2, d1)));
    const Wt = tryTrig(Wd);
    up = [simp(X.mul(X.neg(y2), rhs[1], X.pow(Wt, X.NEG_ONE))), simp(X.mul(y1, rhs[1], X.pow(Wt, X.NEG_ONE)))];
  } else {
    const s = L.solve(W, rhs, { steps: false });
    if (s.status !== "unique") throw qerr("UNSUPPORTED", "singular Wronskian system");
    up = s.solution;
  }
  const u = up.map((f) => integ(tryTrig(simpExpand(f)), xn));
  steps.push(S("ode.variation", "Variation of parameters", "Look for y_p = u1 y1 + ... with u' solving W u' = (0, ..., g/a_n), where W is the Wronskian matrix of the homogeneous solutions; integrate each u_i'."));
  return simp(X.add(...u.map((ui, i) => X.mul(ui, basis[i]))));
}
function tryTrig(u) {
  // sin^2 + cos^2 -> 1 style cleanup via the rules module when available
  if (!TRIGSIMP) return u;
  try { const v = TRIGSIMP(u); return v && X.size(v) <= X.size(u) ? v : u; } catch (_) { return u; }
}
let TRIGSIMP = null;
try { const R = await import("../rules.js"); TRIGSIMP = R.trigsimp ? (u) => { const r = R.trigsimp(u); return r && r.result ? r.result : r; } : null; } catch (_) { TRIGSIMP = null; }

function constCoeffSolve(a, g, xn, steps, kind = "const") {
  // a: coefficients (constants) of y, y', ..., y^(n) (for "euler": of the indicial operator)
  const n = a.length - 1;
  const r = X.sym("__r");
  const chi = simp(X.add(...a.map((c, i) => X.mul(c, X.pow(r, X.num(i))))));
  const roots = charRoots(chi, "__r");
  const tot = roots.reduce((s, e) => s + e.mult, 0);
  if (tot !== n) throw qerr("UNSUPPORTED", "characteristic roots incomplete");
  steps.push(S("ode.characteristic", kind === "euler" ? "Indicial equation" : "Characteristic equation", kind === "euler" ? `Try y = x^r: ${txt(X.subs(chi, { __r: X.sym("r") }))} = 0.` : `Try y = e^(r x): ${txt(X.subs(chi, { __r: X.sym("r") }))} = 0.`, null, X.vector(...roots.map((e) => e.root))));
  const tvar = kind === "euler" ? "__t" : xn;
  const basis = realBasis(roots, kind === "euler" ? xn : xn, kind);
  let part = X.ZERO;
  if (g !== X.ZERO) {
    if (kind === "euler") {
      // particular solution in t = ln x: p(D_t) u = g(e^t)
      const G = simp(X.subs(g, { [xn]: X.exp(X.sym(tvar)) }));
      let pt = null;
      try { pt = undetermined(a, G, tvar); } catch (e) { if (e.code === "TIMEOUT") throw e; pt = null; }
      if (pt) {
        part = simp(X.subs(pt, { [tvar]: X.fn("ln", X.sym(xn)) }));
        steps.push(S("ode.undetermined", "Particular solution", "With x = e^t the equation has constant coefficients; undetermined coefficients in t, then t = ln x.", null, part));
      } else throw qerr("UNSUPPORTED", "forcing term not handled for Cauchy-Euler equations");
    } else {
      let pt = null;
      try { pt = undetermined(a, g, xn); } catch (e) { if (e.code === "TIMEOUT") throw e; pt = null; }
      if (pt !== null) {
        part = pt;
        steps.push(S("ode.undetermined", "Undetermined coefficients", "The forcing is a sum of polynomial times exponential (sine, cosine) terms; try x^s R(x) e^(lambda x) with s the multiplicity of lambda as a characteristic root (resonance).", g, part));
      } else part = variationOfParameters(basis, g, a[n], xn, steps);
    }
  }
  return { basis, part };
}

// ---------------------------------------------------------------- first order
function splitSeparable(g, xn, yn) {
  // g = X(x) * Y(y)
  const fs0 = g.k === "mul" ? g.args : [g];
  const fs = [];
  for (const f of fs0) {
    if (f.k === "pow" && f.args[0] === X.E && f.args[1].k === "add") f.args[1].args.forEach((t) => fs.push(X.exp(t)));
    else fs.push(f);
  }
  const Xs = [], Ys = [];
  for (const f of fs) {
    const hx = X.hasSym(f, xn), hy = X.hasSym(f, yn);
    if (hx && hy) {
      // try factoring the mixed factor
      const ff = factorMixed(f, xn, yn);
      if (!ff) return null;
      Xs.push(ff[0]); Ys.push(ff[1]);
    } else if (hy) Ys.push(f); else Xs.push(f);
  }
  return [simp(X.mul(...Xs)), simp(X.mul(...Ys))];
}
function factorMixed(f, xn, yn) {
  try {
    const t = P.factorTree(f);
    if (t === f) return null;
    const s = splitSeparable(t, xn, yn);
    return s;
  } catch (_) { return null; }
}
function invertH(H, rhs, yn) {
  // solve H(y) = rhs for y in simple cases; returns tree or null
  const y = X.sym(yn);
  H = simp(H);
  const cs = P.coefficients(H, yn);
  if (cs && cs.length === 2 && !X.hasSym(cs[1], yn)) return simp(X.mul(X.sub(rhs, cs[0] || X.ZERO), X.pow(cs[1], X.NEG_ONE)));
  // c * ln|y| or c * ln(y)
  const lnMatch = (h) => {
    const fs = h.k === "mul" ? h.args : [h];
    const c = fs.filter((f) => !X.hasSym(f, yn));
    const r = fs.filter((f) => X.hasSym(f, yn));
    if (r.length === 1 && r[0].k === "fn" && r[0].name === "ln") {
      const a = r[0].args[0];
      const inner = a.k === "fn" && a.name === "abs" ? a.args[0] : a;
      return { c: simp(X.mul(...c)), inner };
    }
    return null;
  };
  const lm = lnMatch(H);
  if (lm) {
    const inner = simp(X.exp(X.mul(rhs, X.pow(lm.c, X.NEG_ONE))));
    return invertH(lm.inner, inner, yn);
  }
  // c * y^k
  const fs = H.k === "mul" ? H.args : [H];
  const c = fs.filter((f) => !X.hasSym(f, yn)), r = fs.filter((f) => X.hasSym(f, yn));
  if (r.length === 1 && r[0].k === "pow" && r[0].args[0] === y && X.isNum(r[0].args[1])) {
    const k = r[0].args[1];
    if (!N.isZero(k.v)) return simp(X.pow(X.mul(rhs, X.pow(X.mul(...c), X.NEG_ONE)), X.pow(k, X.NEG_ONE)));
  }
  if (r.length === 1 && r[0].k === "fn" && r[0].name === "atan" && r[0].args[0] === y) return simp(X.fn("tan", X.mul(rhs, X.pow(X.mul(...c), X.NEG_ONE))));
  return null;
}
function absorbConstant(u, C) {
  // e^(stuff + C1) -> C1 * e^(stuff) style: rename exp(C1) as a new constant (sign included)
  const r = X.mapTree(u, (w) => {
    if (w.k === "pow" && w.args[0] === X.E && w.args[1].k === "add" && w.args[1].args.includes(C)) {
      const rest = w.args[1].args.filter((a) => a !== C);
      return X.mul(C, X.exp(X.add(...rest)));
    }
    return w;
  });
  return simp(r);
}
function firstOrder(F, dep, xn, steps) {
  const y = X.sym(dep), p = dsym(dep, 1), x = X.sym(xn);
  const C1 = X.sym("C1");
  const cs = P.coefficients(F, p.name);
  if (!cs || cs.length !== 2 || [...X.freeSymbols(cs[1])].some((s) => derivInfo(s))) throw qerr("UNSUPPORTED", "the equation is not linear in y' (not solved for the derivative)");
  const M = cs[0] || X.ZERO, Nn = cs[1];
  const g = simp(X.mul(X.neg(M), X.pow(Nn, X.NEG_ONE)));
  const out = (sols, method, extra = {}) => ({ solutions: sols, method, constants: [C1], ...extra });
  // y' = g(x)
  if (!X.hasSym(g, dep)) {
    const G = integ(g, xn);
    steps.push(S("ode.direct", "Integrate directly", "The right-hand side does not involve y, so y = integral of it plus a constant.", g, G));
    return out([{ kind: "explicit", dep, tree: simp(X.add(G, C1)) }], "direct integration");
  }
  // linear
  let lc = P.coefficients(g, dep);
  if (!lc || lc.length > 2) { try { lc = P.coefficients(simpExpand(g), dep); } catch (_) { lc = null; } }
  if (lc && lc.length === 2 && !X.hasSym(lc[1], dep) && !X.hasSym(lc[0] || X.ZERO, dep)) {
    const A = lc[1], Bq = lc[0] || X.ZERO;
    const mu = dropAbs(simp(X.exp(X.neg(integ(A, xn)))));
    const I = Bq === X.ZERO ? X.ZERO : integ(simpExpand(X.mul(mu, Bq)), xn);
    const sol = simp(X.mul(X.add(I, C1), X.pow(mu, X.NEG_ONE)));
    const solE = pick(sol);
    steps.push(S("ode.linear", "Linear first-order equation", `Write y' + P y = Q with P = ${txt(simp(X.neg(A)))}, Q = ${txt(Bq)}; the integrating factor mu = e^(integral P dx) = ${txt(mu)} gives (mu y)' = mu Q.`, null, solE));
    return out([{ kind: "explicit", dep, tree: solE }], "linear (integrating factor)");
  }
  // separable
  const sep = splitSeparable(simp(g), xn, dep);
  if (sep) {
    const [Xf, Yf] = sep;
    const H = integ(simp(X.pow(Yf, X.NEG_ONE)), dep);
    const A = integ(Xf, xn);
    const rhs = simp(X.add(A, C1));
    let expl = invertH(H, rhs, dep);
    const sols = [];
    if (expl) { expl = absorbConstant(expl, C1); for (const b of branches(pick(expl))) sols.push({ kind: "explicit", dep, tree: b }); }
    else sols.push({ kind: "implicit", dep, tree: X.eq(simp(X.sub(H, A)), C1) });
    // constant (singular) solutions: roots of Y(y)
    const singular = [];
    let sp = null;
    try { sp = P.fromTree(Yf, dep) ? P.solvePolynomial(Yf, dep, { domain: "real" }) : null; } catch (_) { sp = null; }
    if (sp) for (const e of sp.exact) singular.push(e.root);
    else { try { if (simp(X.subs(Yf, { [dep]: X.ZERO })) === X.ZERO) singular.push(X.ZERO); } catch (_) { /* undefined at 0 */ } }
    steps.push(S("ode.separable", "Separate the variables", `dy/dx = ${txt(Xf)} * ${txt(Yf)}: integrate dy/(${txt(Yf)}) = ${txt(Xf)} dx.`, null, sols[0].tree));
    for (const r0 of singular) {
      // is it already covered by some value of C1?
      if (expl && coveredBy(expl, dep, r0)) continue;
      sols.push({ kind: "explicit", dep, tree: r0, singular: true });
    }
    return out(sols, "separable", { implicitForm: X.eq(simp(X.sub(H, A)), C1) });
  }
  // Bernoulli: g = A y + B y^m
  const ber = bernoulliSplit(g, dep);
  if (ber) {
    const { A, Bq, m } = ber;
    const k1 = N.sub(N.ONE, m);
    const vp = X.sym("__v");
    const lin = linearFirst(simp(X.mul(X.num(k1), A)), simp(X.mul(X.num(k1), Bq)), xn);
    const v = lin;
    const sol = pick(simp(X.pow(v, X.num(N.inv(k1)))));
    steps.push(S("ode.bernoulli", "Bernoulli equation", `y' = A y + B y^${N.toString(m)}; with v = y^(${N.toString(k1)}) the equation becomes linear: v' = ${N.toString(k1)}(A v + B).`, null, sol));
    void vp;
    const sols = branches(sol).map((b) => ({ kind: "explicit", dep, tree: b }));
    if (N.cmp(m, N.ZERO) > 0) sols.push({ kind: "explicit", dep, tree: X.ZERO, singular: true });
    return out(sols, "Bernoulli");
  }
  let ex0 = null;
  try { ex0 = exactSolve(M, Nn, xn, dep, steps, false); } catch (e) { if (e.code === "TIMEOUT") throw e; ex0 = null; }
  if (ex0) return out([ex0], "exact");
  // homogeneous: g(x, v x) free of x
  const vs = X.sym("__v");
  const h = simp(X.subs(g, { [dep]: X.mul(vs, x) }));
  if (!X.hasSym(h, xn) || isFreeNumeric(h, xn)) {
    const hv = simp(X.subs(h, { [xn]: X.ONE }));
    // x v' = h(v) - v
    const den = simp(together(simp(X.sub(hv, vs)), makeCtx({ budget: { ops: 200000 } })));
    let H = null;
    if (den !== X.ZERO) { try { H = integ(simp(together(simp(X.pow(den, X.NEG_ONE)), makeCtx({ budget: { ops: 200000 } }))), "__v"); } catch (e) { if (e.code === "TIMEOUT") throw e; H = null; } }
    if (H) {
      const rhs = simp(X.add(X.fn("ln", X.fn("abs", x)), C1));
      const vexpl = invertH(H, rhs, "__v");
      steps.push(S("ode.homogeneous", "Homogeneous equation", "The right-hand side depends only on y/x; with y = v x the equation separates: x v' = h(v) - v."));
      if (vexpl) return out([{ kind: "explicit", dep, tree: pick(absorbConstant(simp(X.mul(vexpl, x)), C1)) }], "homogeneous");
      return out([{ kind: "implicit", dep, tree: X.eq(simp(X.sub(X.subs(H, { __v: X.mul(X.sym(dep), X.pow(x, X.NEG_ONE)) }), X.fn("ln", X.fn("abs", x)))), C1) }], "homogeneous");
    }
  }
  // exact (with integrating factors)
  const ex = exactSolve(M, Nn, xn, dep, steps);
  if (ex) return out([ex], "exact");
  throw qerr("UNSUPPORTED", "no first-order method applies (not separable, linear, Bernoulli, homogeneous or exact)");
}
function isFreeNumeric(h, xn) {
  try { return isZeroStrong(simp(diff(h, X.sym(xn))), { __v: [0.37, 1.3, 2.1, 0.8] }); } catch (_) { return false; }
}
function coveredBy(expl, dep, r0) {
  // does expl(C1) equal r0 for C1 = 0?
  try { return isZeroStrong(simp(X.sub(X.subs(expl, { C1: X.ZERO }), r0))); } catch (_) { return false; }
}
// any nonzero multiple of an integrating factor works, and |u|^k = +-u^k piecewise, so the absolute
// values produced by integrating 1/u can be dropped (the result is re-verified by substitution)
function dropAbs(u) { return simp(X.mapTree(u, (w) => (w.k === "fn" && w.name === "abs" ? w.args[0] : w))); }
function linearFirst(A, Bq, xn) {
  // v' = A v + B general solution with C1
  const mu = dropAbs(simp(X.exp(X.neg(integ(A, xn)))));
  const I = Bq === X.ZERO ? X.ZERO : integ(simpExpand(X.mul(mu, Bq)), xn);
  return simp(X.mul(X.add(I, X.sym("C1")), X.pow(mu, X.NEG_ONE)));
}
function bernoulliSplit(g, yn) {
  const e = simpExpand(g);
  const terms = e.k === "add" ? e.args : [e];
  let A = [], Bq = [], m = null;
  for (const t of terms) {
    const fs = t.k === "mul" ? t.args : [t];
    let ex = N.ZERO; const rest = [];
    for (const f of fs) {
      if (f === X.sym(yn)) ex = N.add(ex, N.ONE);
      else if (f.k === "pow" && f.args[0] === X.sym(yn) && X.isNum(f.args[1])) ex = N.add(ex, f.args[1].v);
      else if (X.hasSym(f, yn)) return null;
      else rest.push(f);
    }
    if (N.eq(ex, N.ONE)) A.push(X.mul(...rest));
    else if (!N.isZero(ex)) { if (m && !N.eq(m, ex)) return null; m = ex; Bq.push(X.mul(...rest)); }
    else return null;
  }
  if (!m) return null;
  return { A: simp(X.add(...A)), Bq: simp(X.add(...Bq)), m };
}
function exactSolve(M, Nn, xn, yn, steps, allowMu = true) {
  const x = X.sym(xn), y = X.sym(yn);
  const isZ = (u) => { try { return isZeroStrong(simp(u)); } catch (_) { return false; } };
  let mu = X.ONE;
  let My = simp(diff(M, y)), Nx = simp(diff(Nn, x));
  if (!isZ(X.sub(My, Nx))) {
    if (!allowMu) return null;
    const fx = simp(X.mul(X.sub(My, Nx), X.pow(Nn, X.NEG_ONE)));
    const fy = simp(X.mul(X.sub(Nx, My), X.pow(M, X.NEG_ONE)));
    if (!X.hasSym(fx, yn)) mu = simp(X.exp(integ(fx, xn)));
    else if (!X.hasSym(fy, xn)) mu = simp(X.exp(integ(fy, yn)));
    else return null;
    M = simp(X.mul(mu, M)); Nn = simp(X.mul(mu, Nn));
    My = simp(diff(M, y)); Nx = simp(diff(Nn, x));
    if (!isZ(X.sub(My, Nx))) return null;
  }
  const Phi0 = integ(M, xn);
  const hp_ = simp(X.sub(Nn, diff(Phi0, y)));
  if (X.hasSym(simpExpand(hp_), xn) && !isZ(diff(hp_, x))) return null;
  const hy = integ(X.hasSym(simpExpand(hp_), xn) ? hp_ : simpExpand(hp_), yn);
  const Phi = simp(X.add(Phi0, hy));
  steps.push(S("ode.exact", mu === X.ONE ? "Exact equation" : "Exact after an integrating factor", `${mu === X.ONE ? "" : `Multiplying by ${txt(mu)} makes the equation exact. `}M dx + N dy = 0 with dM/dy = dN/dx; the potential is Phi = ${txt(Phi)}, and the solutions are its level curves.`, null, X.eq(Phi, X.sym("C1"))));
  const expl = invertH(Phi, X.sym("C1"), yn);
  if (expl) return { kind: "explicit", dep: yn, tree: expl };
  return { kind: "implicit", dep: yn, tree: X.eq(Phi, X.sym("C1")) };
}
// an even root u^(p/q) (q even) has a second real branch -u^(p/q)
function branches(u) {
  if (u.k === "pow" && X.isNum(u.args[1]) && u.args[1].v.d % 2n === 0n) return [u, simp(X.neg(u))];
  if (u.k === "mul") {
    const ev = u.args.find((f) => f.k === "pow" && X.isNum(f.args[1]) && f.args[1].v.d % 2n === 0n);
    if (ev) return [u, simp(X.neg(u))];
  }
  return [u];
}
function pick(u) {
  let best = u;
  const consider = (f) => { try { const v = f(); if (v && X.size(v) < X.size(best)) best = v; } catch (e) { if (e && e.code === "TIMEOUT") throw e; } };
  consider(() => simpExpand(u));
  consider(() => {
    const [nu, de] = numerDenom(u);
    if (de === X.ONE) return null;
    return simp(X.mul(simpExpand(X.neg(nu)), X.pow(simpExpand(X.neg(de)), X.NEG_ONE)));
  });
  return best;
}

// ---------------------------------------------------------------- systems
function systemSolve(info, steps) {
  const { deps, odes, x: tn } = info;
  if (odes.length !== deps.length || deps.some((d) => info.order[d] !== 1)) throw qerr("UNSUPPORTED", "only first-order systems with one equation per unknown are solved");
  const n = deps.length;
  const A = [], forcing = [];
  for (const o of odes) {
    // solve o.F for exactly one derivative
    const ds = deps.filter((d) => X.hasSym(o.F, dsym(d, 1).name));
    if (ds.length !== 1) throw qerr("UNSUPPORTED", "each equation must contain exactly one derivative");
    const cs = P.coefficients(o.F, dsym(ds[0], 1).name);
    if (!cs || cs.length !== 2 || X.freeSymbols(cs[1]).size) throw qerr("UNSUPPORTED", "system not in standard form");
    const rhs = simpExpand(X.mul(X.neg(cs[0] || X.ZERO), X.pow(cs[1], X.NEG_ONE)));
    const row = [];
    let rest = rhs;
    for (const d of deps) {
      const c = P.coefficients(rest, d);
      if (!c || c.length > 2 || (c[1] && X.freeSymbols(c[1]).size)) throw qerr("UNSUPPORTED", "only constant-coefficient linear systems are solved");
      row.push(c[1] || X.ZERO);
      rest = c[0] || X.ZERO;
    }
    if (rest !== X.ZERO) throw qerr("UNSUPPORTED", "only homogeneous systems are solved");
    A[deps.indexOf(ds[0])] = row;
    forcing.push(rest);
  }
  const ev = L.eigenvectors(A, { solvePoly: (pt, xs) => P.solvePolynomial(pt, xs.name || xs, { domain: "complex" }).exact.map((e) => ({ value: e.root, multiplicity: e.multiplicity })) });
  const t = X.sym(tn);
  const sols = deps.map(() => []);
  let ci = 0;
  const Cs = [];
  const eig = ev.eigen || [];
  if (eig.reduce((s, e) => s + (e.geometric || e.vectors.length), 0) !== n) throw qerr("UNSUPPORTED", "the matrix is not diagonalisable (defective eigenvalues)");
  const done = new Set();
  for (let i = 0; i < eig.length; i++) {
    if (done.has(i)) continue;
    const e = eig[i];
    const lam = simp(e.value);
    if (X.contains(lam, X.I)) {
      // pair with its conjugate: real and imaginary parts of e^(lam t) v
      const pl = complexParts(lam);
      let j = -1;
      for (let k = i + 1; k < eig.length; k++) {
        const pk = complexParts(simp(eig[k].value));
        try { if (pk && isZeroStrong(simp(X.sub(pk.re, pl.re))) && isZeroStrong(simp(X.add(pk.im, pl.im)))) { j = k; break; } } catch (_) { /* skip */ }
      }
      if (j < 0) throw qerr("UNSUPPORTED", "complex eigenvalue without conjugate");
      done.add(i); done.add(j);
      for (const v of e.vectors) {
        const z = v.map((c) => simp(X.mul(c, X.exp(X.mul(lam, t)))));
        const parts = z.map((c) => complexParts(c));
        if (parts.some((q) => !q)) throw qerr("UNSUPPORTED", "complex parts");
        const C1 = X.sym(`C${++ci}`), C2 = X.sym(`C${++ci}`);
        Cs.push(C1, C2);
        parts.forEach((q, r) => { sols[r].push(X.mul(C1, q.re), X.mul(C2, q.im)); });
      }
      continue;
    }
    done.add(i);
    for (const v of e.vectors) {
      const C = X.sym(`C${++ci}`);
      Cs.push(C);
      v.forEach((c, r) => sols[r].push(X.mul(C, c, X.exp(X.mul(lam, t)))));
    }
  }
  const trees = sols.map((s) => simp(X.add(...s)));
  steps.push(S("ode.system", "Eigenvalues and eigenvectors", "For X' = A X, each eigenpair (lambda, v) gives the solution e^(lambda t) v; complex pairs give real solutions from the real and imaginary parts.", X.matrix(A.map((r) => X.tuple(...r))), X.vector(...trees)));
  return { solutions: deps.map((d, i) => ({ kind: "explicit", dep: d, tree: trees[i] })), constants: Cs, method: "eigenvectors" };
}

// ---------------------------------------------------------------- main solver
export function solveODE(info, opts = {}) {
  const steps = [];
  const run = () => {
    let res;
    try { res = solveSymbolic(info, steps); }
    catch (e) {
      if (e.code === "TIMEOUT" || e.code === "INCONSISTENT") throw e;
      const nres = numericFallback(info, steps, e);
      if (nres) return nres;
      throw e;
    }
    if (info.ics.length) res = applyICs(info, res, steps);
    return { ...res, steps, conditions: res.conditions || [] };
  };
  return opts.deadline ? Budget.withDeadline(opts.deadline, run) : Budget.with(opts.timeLimit || 15000, run);
}
function solveSymbolic(info, steps) {
  if (info.deps.length > 1 || info.odes.length > 1) return systemSolve(info, steps);
  const dep = info.deps[0], xn = info.x;
  const F = info.odes[0].F;
  const n = info.order[dep];
  if (n === 1) {
    try { return firstOrder(F, dep, xn, steps); }
    catch (e) { if (e.code !== "UNSUPPORTED" && e.code !== "NOINTEGRAL") throw e; const lf = linearForm(F, dep, 1, xn); if (!lf) throw e; }
  }
  const lf = linearForm(F, dep, n, xn);
  if (!lf) throw qerr("UNSUPPORTED", "the equation is not linear in y and its derivatives");
  const { a, g } = lf;
  const x = X.sym(xn);
  const Cs = Array.from({ length: n }, (_, i) => X.sym(`C${i + 1}`));
  // constant coefficients
  if (a.every((c) => !X.hasSym(c, xn))) {
    const { basis, part } = constCoeffSolve(a, g, xn, steps);
    const general = simp(X.add(part, ...basis.map((b, i) => X.mul(Cs[i], b))));
    steps.push(S("ode.general", "General solution", "y = y_p + C1 y1 + ... + Cn yn.", null, general));
    return { solutions: [{ kind: "explicit", dep, tree: general }], constants: Cs, basis, method: "constant coefficients" + (g === X.ZERO ? "" : " + particular solution") };
  }
  // Cauchy-Euler: a_i = b_i x^i
  const b = a.map((c, i) => simp(X.mul(c, X.pow(x, X.num(-i)))));
  if (b.every((c) => !X.hasSym(c, xn))) {
    // indicial operator: sum b_i r(r-1)...(r-i+1) -> coefficients of the constant-coefficient operator in t
    const r = X.sym("__r");
    const ind = simpExpand(X.add(...b.map((c, i) => { let f = X.ONE; for (let j = 0; j < i; j++) f = X.mul(f, X.sub(r, X.num(j))); return X.mul(c, f); })));
    const cs = P.coefficients(ind, "__r");
    const { basis, part } = constCoeffSolve(cs.map((c) => simp(c)), g, xn, steps, "euler");
    const general = simp(X.add(part, ...basis.map((bb, i) => X.mul(Cs[i], bb))));
    steps.push(S("ode.euler", "Cauchy-Euler equation", "Coefficients a_i x^i: substitute y = x^r (equivalently x = e^t) to get constant coefficients; valid for x > 0.", null, general));
    return { solutions: [{ kind: "explicit", dep, tree: general }], constants: Cs, basis, method: "Cauchy-Euler", conditions: [X.rel(">", x, X.ZERO)] };
  }
  throw qerr("UNSUPPORTED", "linear equation with variable coefficients (not Cauchy-Euler)");
}

// ---------------------------------------------------------------- initial conditions
function applyICs(info, res, steps) {
  const xn = info.x;
  const x = X.sym(xn);
  const Cs = res.constants;
  const eqs = [];
  const viaImplicit = !!(res.implicitForm && Cs.length === 1 && info.ics.length === 1 && info.ics[0].m === 0);
  if (!viaImplicit) for (const ic of info.ics) {
    const sol = res.solutions.find((s) => s.dep === ic.dep && !s.singular);
    if (!sol) throw qerr("UNSUPPORTED", "initial condition for an unknown function");
    if (sol.kind === "implicit") {
      if (ic.m !== 0 || res.solutions.length !== 1) throw qerr("UNSUPPORTED", "derivative conditions with implicit solutions");
      const [lhs] = sol.tree.args;
      const val = simp(X.subs(lhs, { [xn]: ic.at, [ic.dep]: ic.value }));
      eqs.push({ direct: val });
      continue;
    }
    let d = sol.tree;
    for (let k = 0; k < ic.m; k++) d = simp(diff(d, x));
    eqs.push({ e: simp(X.sub(X.subs(d, { [xn]: ic.at }), ic.value)) });
  }
  let sub = {};
  let branchFilter = false;
  if (viaImplicit) {
    // separable: H(y) - A(x) = C1 is linear in C1; keep only the explicit branches through the point
    const ic = info.ics[0];
    sub.C1 = simp(X.subs(res.implicitForm.args[0], { [xn]: ic.at, [ic.dep]: ic.value }));
    branchFilter = true;
    if (hasBad(sub.C1)) {
      // the point lies on no member of the family: only constant (singular) solutions can pass through it
      const sing = res.solutions.filter((q) => q.singular && q.dep === ic.dep && isZeroStrongSafe(X.sub(q.tree, ic.value)));
      if (!sing.length) throw qerr("INCONSISTENT", "no solution passes through the initial point");
      steps.push(S("ode.ivp", "Use the initial condition", `The point (${txt(ic.at)}, ${txt(ic.value)}) lies on none of the non-constant solutions; the constant solution ${ic.dep} = ${txt(sing[0].tree)} passes through it.`, null, sing[0].tree));
      return { ...res, solutions: sing.map((q) => ({ ...q, singular: false })), constants: [], constantsSolved: {}, general: res.solutions };
    }
  } else if (eqs.length === 1 && eqs[0].direct) sub.C1 = eqs[0].direct;
  else {
    const rows = [], rhs = [];
    let linear = true;
    for (const q of eqs) {
      if (q.direct) { linear = false; break; }
      const row = [];
      let rest = q.e;
      for (const C of Cs) {
        const c = P.coefficients(rest, C.name);
        if (!c || c.length > 2 || (c[1] && Cs.some((D) => X.hasSym(c[1], D.name)))) { linear = false; break; }
        row.push(c[1] || X.ZERO);
        rest = c[0] || X.ZERO;
      }
      if (!linear) break;
      rows.push(row); rhs.push(simp(X.neg(rest)));
    }
    if (linear) {
      const s = L.solve(rows, rhs, { steps: false });
      if (s.status === "none") throw qerr("INCONSISTENT", "the initial conditions cannot be satisfied");
      Cs.forEach((C, i) => { if (!(s.params || []).includes(s.solution[i])) sub[C.name] = s.solution[i]; });
    } else if (Cs.length === 1 && eqs.length === 1) {
      // one constant entering non-linearly: numerator linear in C1
      const t = together(eqs[0].e, makeCtx({ budget: { ops: 400000 } }));
      const [nu] = numerDenom(t);
      const c = P.coefficients(nu, "C1");
      if (!c || c.length !== 2 || X.hasSym(c[1], "C1")) throw qerr("UNSUPPORTED", "could not solve for the constant");
      sub.C1 = simp(X.mul(X.neg(c[0] || X.ZERO), X.pow(c[1], X.NEG_ONE)));
    } else throw qerr("UNSUPPORTED", "constants enter non-linearly");
  }
  const sols = res.solutions.filter((s) => !s.singular).map((s) => {
    let t = s.kind === "implicit" ? X.eq(s.tree.args[0], simp(X.subs(s.tree.args[1], sub))) : simp(X.subs(s.tree, sub));
    if (s.kind === "implicit") {
      const ex = invertH(t.args[0], t.args[1], s.dep);
      if (ex) return { kind: "explicit", dep: s.dep, tree: pick(ex), branchCheck: true };
      return { ...s, tree: t };
    }
    return { ...s, tree: pick(t) };
  });
  if (branchFilter) {
    const ic = info.ics[0];
    const keep = sols.filter((q) => q.kind !== "explicit" || isZeroStrongSafe(X.sub(X.subs(q.tree, { [xn]: ic.at }), ic.value)));
    const expl = keep.filter((q) => q.kind === "explicit");
    sols.length = 0;
    if (expl.length) sols.push(...expl);
    else sols.push({ kind: "implicit", dep: ic.dep, tree: X.eq(res.implicitForm.args[0], sub.C1) });
  }
  // singular solutions that satisfy the IC are also answers
  for (const s of res.solutions.filter((q) => q.singular)) {
    const ok = info.ics.every((ic) => ic.dep !== s.dep || (ic.m === 0 && isZeroStrongSafe(X.sub(s.tree, ic.value))));
    if (ok && info.ics.some((ic) => ic.dep === s.dep)) sols.push(s);
  }
  steps.push(S("ode.ivp", "Use the initial conditions", `Substitute ${info.ics.map((ic) => `${ic.dep}${"'".repeat(ic.m)}(${txt(ic.at)}) = ${txt(ic.value)}`).join(", ")} and solve for the constants: ${Object.entries(sub).map(([k, v]) => `${k} = ${txt(v)}`).join(", ")}.`, null, sols.length === 1 ? sols[0].tree : null));
  return { ...res, solutions: sols, constantsSolved: sub, general: res.solutions };
}
function hasBad(u) { return X.contains(u, X.UNDEF) || X.contains(u, X.OO); }
function isZeroStrongSafe(u) { try { return isZeroStrong(simp(u)); } catch (_) { return false; } }

// ---------------------------------------------------------------- numeric fallback
function numericFallback(info, steps, why) {
  if (info.deps.length !== 1 || info.odes.length !== 1 || !info.ics.length) return null;
  const dep = info.deps[0], n = info.order[dep], xn = info.x;
  const F = info.odes[0].F;
  const top = dsym(dep, n).name;
  const cs = P.coefficients(F, top);
  if (!cs || cs.length !== 2 || X.hasSym(cs[1], top)) return null;
  const rhs = simp(X.mul(X.neg(cs[0] || X.ZERO), X.pow(cs[1], X.NEG_ONE)));
  const at = info.ics.map((ic) => ic.at);
  if (!at.every((a) => a === at[0])) return null;
  const t0v = hp(at[0], {});
  if (!t0v.ok) return null;
  const y0 = [];
  for (let k = 0; k < n; k++) {
    const ic = info.ics.find((q) => q.m === k);
    if (!ic) return null;
    const v = hp(ic.value, {});
    if (!v.ok || [...X.freeSymbols(ic.value)].length) return null;
    y0.push(v.re);
  }
  // state (y, y', ..., y^(n-1)); rhs trees in x and state symbols
  const names = Array.from({ length: n }, (_, k) => dsym(dep, k).name);
  const sys = [];
  for (let k = 0; k < n - 1; k++) sys.push(X.sym(names[k + 1]));
  sys.push(rhs);
  const t1 = t0v.re + 1;
  let r;
  try { r = NU.solveODE(sys, xn, names, t0v.re, y0, t1, { rtol: 1e-12, atol: 1e-14, samples: 11 }); } catch (e) { return null; }
  if (!r || !r.converged) return null;
  const table = r.t.map((tv, i) => [tv, r.y[i][0]]);
  steps.push(S("ode.numeric", "Numeric solution (approximate)", `No symbolic method applied (${why.message}). The initial value problem was integrated numerically with an adaptive Dormand-Prince 5(4) method (relative tolerance 1e-12).`));
  return { approximate: true, table, final: table[table.length - 1][1], finalText: r.final && r.final[0] ? r.final[0].value : null, t1, solutions: [], constants: [], method: "numeric (Dormand-Prince)", steps, conditions: [], ode: { sys, names, t0: t0v.re, y0 } };
}

// ---------------------------------------------------------------- verification
function residualOf(F, subsMap) { return simp(X.subs(F, subsMap)); }
function numZero(u, envs, scaleTerms) {
  // relative residual test at the given points: true / false / null
  let good = 0, tried = 0;
  for (const env of envs) {
    const v = hp(u, env, { digits: 50, maxDigits: 200 });
    if (!v.ok) continue;
    let scale = 0;
    for (const t of scaleTerms) { const w = hp(t, env, { digits: 30, maxDigits: 60 }); if (w.ok) scale = Math.max(scale, log10Abs(w.big)); }
    tried++;
    const mag = log10Abs(v.big);
    if (mag - scale > -12) return false;
    if (mag - scale < -30) good++;
  }
  if (tried >= 3 && good === tried) return true;
  return null;
}
export function verifyODE(info, res) {
  const checks = [];
  const xn = info.x;
  const x = X.sym(xn);
  if (res.approximate) {
    // independent check: re-integrate with a looser tolerance and a different step control
    const r2 = NU.solveODE(res.ode.sys, xn, res.ode.names, res.ode.t0, res.ode.y0, res.t1, { rtol: 1e-9, atol: 1e-11, h0: 1e-3, samples: 11 });
    const a = res.final, b = r2.y[r2.y.length - 1][0];
    const ok = Math.abs(a - b) <= 1e-6 * Math.max(1, Math.abs(a));
    checks.push({ kind: "re-integration", ok, detail: `a second integration with different tolerances gives ${b.toPrecision(10)} at x = ${res.t1}` });
    return { status: ok ? "verified-numeric" : "failed", checks };
  }
  const baseC = {};
  (res.constants || []).forEach((C, i) => { if (!res.constantsSolved || !(C.name in res.constantsSolved)) baseC[C.name] = X.num(N.Q(5 + 3 * i, 7 + i)); });
  const xpts = info.odes.some((o) => res.method === "Cauchy-Euler") || (res.conditions || []).length ? [0.63, 1.37, 2.11, 2.9] : [0.41, 0.83, 1.29, 1.71];
  let exactAll = true;
  for (const o of info.odes) {
    const F = o.F;
    // substitute every dependent (explicit solutions only)
    const sub = {};
    let implicitSol = null;
    for (const dep of info.deps) {
      const sol = res.solutions.find((s) => s.dep === dep && !s.singular);
      if (!sol) return { status: "inconclusive", checks };
      if (sol.kind === "implicit") { implicitSol = sol; continue; }
      let d = simp(X.subs(sol.tree, baseC));
      for (let k = 0; k <= Math.max(info.order[dep], 1); k++) { sub[dsym(dep, k).name] = d; d = simp(diff(d, x)); }
    }
    if (implicitSol) {
      // y' = -Phi_x / Phi_y on the level curves; check F at random (x, y)
      const Phi = simp(X.sub(implicitSol.tree.args[0], implicitSol.tree.args[1]));
      const dep = implicitSol.dep;
      const yp = simp(X.mul(X.neg(diff(Phi, x)), X.pow(diff(Phi, X.sym(dep)), X.NEG_ONE)));
      const resid = simp(X.subs(F, { [dsym(dep, 1).name]: yp }));
      const envs = xpts.map((xv, i) => ({ [xn]: xv, [dep]: 0.3 + 0.45 * i }));
      const terms = (F.k === "add" ? F.args : [F]).map((t) => simp(X.subs(t, { [dsym(dep, 1).name]: yp })));
      const ok = resid === X.ZERO ? true : numZero(resid, envs, terms);
      if (resid !== X.ZERO) exactAll = false;
      checks.push({ kind: "implicit differentiation", ok, detail: ok ? "differentiating the implicit solution implicitly satisfies the equation" : "the implicit solution does not satisfy the equation" });
      if (ok === false) return { status: "failed", checks };
      if (ok === null) return { status: "inconclusive", checks };
      continue;
    }
    let resid = residualOf(F, sub);
    if (resid !== X.ZERO) { try { resid = simpExpand(resid); } catch (_) { /* keep */ } }
    if (resid !== X.ZERO) resid = tryTrig(resid);
    if (resid === X.ZERO) { checks.push({ kind: "substitution", ok: true, detail: "substituting the solution into the original equation gives 0 exactly" }); continue; }
    exactAll = false;
    const params = [...X.freeSymbols(resid)].filter((s) => s !== xn);
    const envs = xpts.map((xv) => { const e = { [xn]: xv }; params.forEach((p, i) => { e[p] = 0.7 + 0.31 * i; }); return e; });
    const terms = (F.k === "add" ? F.args : [F]).map((t) => residualOf(t, sub));
    const ok = numZero(resid, envs, terms);
    checks.push({ kind: "substitution", ok, detail: ok ? "the residual after substitution vanishes to 30+ digits at 4 points" : ok === false ? "substituting the solution leaves a nonzero residual" : "the residual could not be evaluated reliably" });
    if (ok === false) return { status: "failed", checks };
    if (ok === null) return { status: "inconclusive", checks };
  }
  // singular solutions
  for (const s of res.solutions.filter((q) => q.singular)) {
    const dep = s.dep;
    const sub = { [dep]: s.tree };
    for (let k = 1; k <= info.order[dep]; k++) sub[dsym(dep, k).name] = X.ZERO;
    const r = residualOf(info.odes[0].F, sub);
    const ok = r === X.ZERO || isZeroStrongSafe(r);
    checks.push({ kind: "constant solution", ok, detail: `${dep} = ${txt(s.tree)} satisfies the equation` });
    if (!ok) return { status: "failed", checks };
  }
  // initial conditions
  for (const ic of info.ics) {
    for (const sol of res.solutions.filter((s) => s.dep === ic.dep && s.kind === "implicit" && ic.m === 0)) {
      const v = simp(X.subs(X.sub(sol.tree.args[0], sol.tree.args[1]), { [xn]: ic.at, [ic.dep]: ic.value }));
      const ok = isZeroStrongSafe(v);
      checks.push({ kind: "initial condition", ok, detail: `the implicit solution passes through (${txt(ic.at)}, ${txt(ic.value)})` });
      if (!ok) return { status: "failed", checks };
    }
    const sols = res.solutions.filter((s) => s.dep === ic.dep && s.kind === "explicit");
    for (const sol of sols) {
      let d = sol.tree;
      for (let k = 0; k < ic.m; k++) d = simp(diff(d, x));
      const v = simp(X.sub(X.subs(d, { [xn]: ic.at }), ic.value));
      const ok = isZeroStrongSafe(v);
      checks.push({ kind: "initial condition", ok, detail: `${ic.dep}${"'".repeat(ic.m)}(${txt(ic.at)}) = ${txt(ic.value)}` });
      if (!ok) return { status: "failed", checks };
      if (v !== X.ZERO) exactAll = false;
    }
  }
  // independence of the homogeneous basis (general solution has n genuine constants)
  if (res.basis && res.basis.length > 1) {
    const W = wronskian(res.basis, xn);
    const Wn = W.map((row) => row.map((f) => { const v = hp(f, { [xn]: 0.77 }, { digits: 30 }); return v.ok ? v.re : NaN; }));
    const det = detNum(Wn);
    const ok = Number.isFinite(det) && Math.abs(det) > 1e-12;
    checks.push({ kind: "independence", ok, detail: `Wronskian of the basis at x = 0.77 is ${Number.isFinite(det) ? det.toPrecision(6) : "undefined"}` });
    if (!ok) return { status: "failed", checks };
  }
  return { status: exactAll ? "verified-exact" : "verified-numeric", checks };
}
function detNum(M) {
  const n = M.length;
  const A = M.map((r) => r.slice());
  let det = 1;
  for (let c = 0; c < n; c++) {
    let p = c;
    for (let r = c + 1; r < n; r++) if (Math.abs(A[r][c]) > Math.abs(A[p][c])) p = r;
    if (!(Math.abs(A[p][c]) > 0)) return 0;
    if (p !== c) { [A[p], A[c]] = [A[c], A[p]]; det = -det; }
    det *= A[c][c];
    for (let r = c + 1; r < n; r++) { const f = A[r][c] / A[c][c]; for (let j = c; j < n; j++) A[r][j] -= f * A[c][j]; }
  }
  return det;
}
