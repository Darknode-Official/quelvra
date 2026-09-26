// Quelvra function analysis: shared helpers.
//
// Points on the real line are { tree, v } (exact tree plus its double value) or
// { tree, v, approx } for certified numeric points. Sets of reals are lists of intervals
// { lo, hi, loOpen, hiOpen } with tree ends (null means -oo / +oo).
//
// Numeric checks in this directory always evaluate the ORIGINAL expression with the verifier's
// own evaluator (verify.js evalC / evalReal / definedAt), never with the symbolic engines that
// produced the answer.

import * as X from "../expr.js";
import * as Q from "../num.js";
import { simplify, makeCtx, expand } from "../simplify.js";
import { toText } from "../print.js";
import { evalC, evalReal, definedAt } from "../verify.js";
import { C, safe, cval, signConst, cmpConst, tidy, hp, nearZero, isZeroExact, decimalTree, rationalBetween, approxRec } from "../solve/util.js";
import { solveCore } from "../solve/core.js";

export { X, Q, toText, C, safe, cval, signConst, cmpConst, tidy, hp, nearZero, isZeroExact, decimalTree, rationalBetween, approxRec, evalReal, definedAt, evalC };

export const NOLOG = { steps: [], add() { return null; }, group: (h, f) => f(null), get length() { return 0; } };

export function fail(message) { const e = new Error(message); e.code = "UNSUPPORTED"; return e; }

// Real double value of a constant tree (NaN when undefined / not real).
export function dv(t) {
  if (t === null || t === undefined) return NaN;
  if (t === X.OO) return Infinity;
  if (t.k === "mul" && t.args.length === 2 && X.isNum(t.args[0]) && t.args[0].v.n < 0n && t.args[1] === X.OO) return -Infinity;
  const v = evalReal(t, {});
  if (Number.isFinite(v)) return v;
  const h = safe(() => hp(t, 30));
  return h && h.ok && Math.abs(h.im) < 1e-20 ? h.re : NaN;
}
export const pt = (tree) => ({ tree, v: dv(tree) });

// f evaluated at a double with the verifier's evaluator (NaN when undefined).
export const fAt = (f, x, t) => evalReal(f, { [x]: t });
export const definedNum = (f, x, t) => definedAt(f, { [x]: t }) && Number.isFinite(fAt(f, x, t));

// Exact value of f at an exact point: simplified tree, or null when f is undefined there.
// Every subexpression containing x is checked (x/x at 0 is undefined even though it "simplifies").
export function valueAt(f, x, tree) {
  const env = { [x]: tree };
  let ok = true;
  const walk = (w) => {
    if (!ok || X.freeOf(w, x)) return;
    if (w.k === "sym") return;
    const s = safe(() => C(X.subs(w, env)));
    if (!s || X.contains(s, X.UNDEF) || X.contains(s, X.OO)) { ok = false; return; }
    if (X.freeSymbols(s).size === 0) {
      const c = evalC(s, {}, "complex");
      if (Number.isFinite(c.re) && Math.abs(c.im) > 1e-9 * Math.max(1, Math.abs(c.re))) { ok = false; return; }
      if (!Number.isFinite(c.re) || !Number.isFinite(c.im)) {
        const h = safe(() => hp(s, 30));
        if (!h || !h.ok) { ok = false; return; }
        if (Math.abs(h.im) > Math.max(1e-25, 4 * h.err)) { ok = false; return; }
      }
    }
    for (const a of w.args || []) walk(a);
  };
  walk(f);
  if (!ok) return null;
  const v = safe(() => tidy(C(X.subs(f, env))));
  if (!v || X.contains(v, X.UNDEF) || X.contains(v, X.I)) return null;
  return v;
}

// Compare two exact points: -1, 0, 1 (null when undecidable).
export function cmpPt(a, b) {
  if (a.tree === b.tree) return 0;
  if (Number.isFinite(a.v) && Number.isFinite(b.v) && Math.abs(a.v - b.v) > 1e-9 * Math.max(1, Math.abs(a.v), Math.abs(b.v))) return a.v < b.v ? -1 : 1;
  if (a.approx || b.approx) return Math.abs(a.v - b.v) <= 1e-12 * Math.max(1, Math.abs(a.v)) ? 0 : a.v < b.v ? -1 : 1;
  const s = safe(() => cmpConst(a.tree, b.tree));
  if (s !== null && s !== undefined) return s;
  if (safe(() => nearZero(X.sub(a.tree, b.tree), 50))) return 0;
  return null;
}
export function sortUniq(points) {
  const ps = points.filter((p) => Number.isFinite(p.v)).sort((a, b) => a.v - b.v);
  const out = [];
  for (const p of ps) {
    const q = out[out.length - 1];
    if (q && cmpPt(p, q) === 0) { if (q.approx && !p.approx) out[out.length - 1] = p; continue; }
    out.push(p);
  }
  return out;
}

// A rational test point strictly between two doubles (either may be infinite).
export function testPoint(lo, hi) {
  if (!Number.isFinite(lo) && !Number.isFinite(hi)) return X.ZERO;
  if (!Number.isFinite(lo)) return X.num(Q.Q(BigInt(Math.floor(hi) - 1)));
  if (!Number.isFinite(hi)) return X.num(Q.Q(BigInt(Math.ceil(lo) + 1)));
  return X.num(rationalBetween(lo, hi));
}

// Exact sign of g at an exact point: 1, -1, 0 or null.
export function signAt(g, x, tree) {
  const s = safe(() => C(X.subs(g, { [x]: tree })));
  if (!s || s === X.UNDEF || X.contains(s, X.UNDEF)) return null;
  return safe(() => signConst(s));
}

// Real zeros of e(x) (exact, certified numeric, periodic families). Throws when the search is not complete.
export function zerosOf(e, x, env, { allowFamilies = true, allowNumeric = true } = {}) {
  const S = { x, topVar: x, log: NOLOG, domain: "real", digits: env.digits || 20, checkTime: env.checkTime, allowNumeric, depth: 0 };
  const e0 = C(e);
  if (X.freeOf(e0, x)) return { points: [], families: [], all: e0 === X.ZERO, complete: true };
  let sol = solveCore(e0, S);
  if (!sol.complete || (sol.regions && sol.regions.length)) {
    const e1 = dropExpFactors(e0, x);
    if (e1 !== e0) { const s1 = safe(() => solveCore(e1, S)); if (s1 && s1.complete) sol = s1; }
  }
  if (sol.regions && sol.regions.length) throw fail(`${toText(e0)} = 0 on a whole interval; this case is not supported`);
  if (!sol.complete) throw fail(`the solutions of ${toText(e0)} = 0 could not all be found`);
  if (sol.general.length && !allowFamilies) throw fail(`${toText(e0)} = 0 has infinitely many solutions`);
  const points = [];
  for (const r of sol.exact) {
    const c = cval(r.tree);
    if (!Number.isFinite(c.re) || Math.abs(c.im) > 1e-12 * Math.max(1, Math.abs(c.re))) continue;
    if (hasW(r.tree)) { const t = decimalTree(c.re.toPrecision(16)); if (t) points.push({ tree: t, v: c.re, approx: { value: c.re.toPrecision(16), digits: 15, method: "Lambert W" } }); continue; }
    const t = tidy(r.tree);
    points.push({ tree: t, v: dv(t), mult: r.multiplicity || 1 });
  }
  for (const a of sol.approx) {
    if (a.complex) continue;
    const t = decimalTree(a.approx.value);
    if (!t) continue;
    points.push({ tree: t, v: parseFloat(a.approx.value), approx: a.approx });
  }
  const families = mergeFamilies(sol.general.map((f) => ({ offset: tidy(f.offset), period: tidy(f.period), o: dv(f.offset), p: Math.abs(dv(f.period)) }))
    .filter((f) => Number.isFinite(f.o) && f.p > 0));
  return { points: sortUniq(points), families, all: !!sol.all, complete: true };
}

// e^u is never 0 (and is defined wherever u is), so an exp factor common to every term of e can be divided out
function dropExpFactors(e, x) {
  const isExp = (u) => u.k === "pow" && u.args[0] === X.E && !X.freeOf(u.args[1], x);
  if (e.k === "mul") { const keep = e.args.filter((a) => !isExp(a)); return keep.length < e.args.length ? C(X.mul(...keep)) : e; }
  if (e.k !== "add") return e;
  const first = e.args[0];
  const cands = (first.k === "mul" ? first.args : [first]).filter(isExp);
  for (const c of cands) {
    const r = safe(() => C(expand(C(X.mul(e, X.exp(X.neg(c.args[1])))))));
    if (r && X.size(r) < X.size(e)) return r;
  }
  return e;
}
const hasW = (u) => (u.k === "fn" && u.name === "W") || (u.args || []).some(hasW);
// Merge families of one period whose offsets are equally spaced (pi/2 + 2k pi and -pi/2 + 2k pi -> pi/2 + k pi).
export function mergeFamilies(fams) {
  let list = fams.slice();
  const norm = (o, p) => { let r = o - p * Math.floor(o / p); if (p - r < 1e-9 * p) r = 0; return r; };
  // drop duplicates
  const out0 = [];
  for (const f of list) if (!out0.some((g) => Math.abs(g.p - f.p) < 1e-12 * f.p && Math.abs(norm(f.o - g.o, g.p)) < 1e-9)) out0.push(f);
  list = out0;
  for (let changed = true; changed;) {
    changed = false;
    for (const f of list) {
      const same = list.filter((g) => Math.abs(g.p - f.p) < 1e-12 * f.p);
      for (let n = same.length; n >= 2; n--) {
        const step = f.p / n;
        const members = [];
        for (let j = 0; j < n; j++) { const m = same.find((g) => Math.abs(norm(g.o - f.o - j * step, f.p)) < 1e-9 || Math.abs(norm(g.o - f.o - j * step, f.p) - f.p) < 1e-9); if (!m) break; members.push(m); }
        if (members.length !== n) continue;
        const best = members.reduce((a, b) => (Math.abs(b.o) < Math.abs(a.o) - 1e-12 || (Math.abs(Math.abs(b.o) - Math.abs(a.o)) < 1e-12 && b.o > a.o) ? b : a));
        const period = tidy(C(X.div(best.period, X.num(Q.Q(BigInt(n))))));
        let offset = best.offset, o = best.o;
        const k = Math.floor(o / step + 1e-9);
        if (k !== 0 && Math.abs(o) > step / 2 + 1e-12) { offset = tidy(C(X.sub(offset, X.mul(X.num(Q.Q(BigInt(k))), period)))); o = dv(offset); }
        list = [...list.filter((g) => !members.includes(g)), { offset, period, o, p: step }];
        changed = true;
        break;
      }
      if (changed) break;
    }
  }
  return list.sort((a, b) => a.o - b.o);
}
// Members of periodic families inside [lo, hi] (doubles), as exact points.
export function familyMembers(families, lo, hi, limit = 400) {
  const out = [];
  for (const f of families) {
    const k0 = Math.ceil((lo - f.o) / f.p - 1e-9), k1 = Math.floor((hi - f.o) / f.p + 1e-9);
    if (k1 - k0 > limit) throw fail("too many periodic points in the window");
    for (let k = k0; k <= k1; k++) {
      const t = tidy(C(X.add(f.offset, X.mul(X.num(Q.Q(BigInt(k))), f.period))));
      const v = dv(t);
      if (v >= lo - 1e-9 && v <= hi + 1e-9) out.push({ tree: t, v });
    }
  }
  return out;
}

// Periodicity: every occurrence of x inside sin/cos/tan/... of a*x + b (a rational), none outside.
// Returns the period as a tree (q * pi) or null.
const TRIG2 = new Set(["sin", "cos", "sec", "csc"]);
const TRIG1 = new Set(["tan", "cot"]);
export function periodOf(f, x) {
  const periods = [];
  let ok = true;
  const walk = (w) => {
    if (!ok || X.freeOf(w, x)) return;
    if (w.k === "sym") { ok = false; return; }
    if (w.k === "fn" && (TRIG2.has(w.name) || TRIG1.has(w.name))) {
      const a = safe(() => C(X.subs(X.sub(X.subs(w.args[0], { [x]: X.ONE }), X.subs(w.args[0], { [x]: X.ZERO })), {})));
      const lin = a && X.isNum(a) && a.v.n !== 0n && safe(() => C(X.sub(w.args[0], X.mul(a, X.sym(x))))) ;
      if (!lin || !X.freeOf(lin, x)) { ok = false; return; }
      const base = TRIG2.has(w.name) ? Q.Q(2n) : Q.Q(1n);
      periods.push(Q.div(base, Q.abs(a.v)));
      return;
    }
    for (const c of w.args || []) walk(c);
  };
  walk(f);
  if (!ok || !periods.length) return null;
  // lcm of rationals n_i / d_i = lcm(n_i) / gcd(d_i)
  const gcd = (a, b) => { a = a < 0n ? -a : a; b = b < 0n ? -b : b; while (b) [a, b] = [b, a % b]; return a; };
  let n = periods[0].n, d = periods[0].d;
  for (const p of periods.slice(1)) { n = (n * p.n) / gcd(n, p.n); d = gcd(d, p.d); }
  return C(X.mul(X.num(Q.Q(n, d)), X.PI));
}

// Functions whose sign charts would not be justified (discontinuous inside their domain).
const DISC = new Set(["floor", "ceil", "round", "sign", "mod", "factorial", "gamma", "max", "min", "re", "im", "arg", "conj"]);
export function assertElementary(f, x) {
  let bad = null;
  const walk = (w) => {
    if (bad) return;
    if (w.k === "fn" && DISC.has(w.name) && !X.freeOf(w, x)) bad = w.name;
    if (w.k === "piecewise" || w.k === "integral" || w.k === "sum" || w.k === "deriv" || w.k === "limit") bad = w.k;
    for (const a of w.args || []) walk(a);
  };
  walk(f);
  if (bad) throw fail(`functions with ${bad} are not supported by this command (they can jump inside their domain)`);
}

// Interval-set -> relation tree in variable v (mirrors the inequality solver's output shape).
export function setTree(ivs, v, { contractNe = true } = {}) {
  const V = typeof v === "string" ? X.sym(v) : v;
  if (!ivs.length) return X.FALSE;
  const parts = ivs.map(({ lo, hi, loOpen, hiOpen }) => {
    if (lo === null && hi === null) return X.TRUE;
    if (lo !== null && hi !== null && lo === hi) return X.eq(V, lo);
    const cs = [];
    if (lo !== null) cs.push(X.rel(loOpen ? "<" : "<=", lo, V));
    if (hi !== null) cs.push(X.rel(hiOpen ? "<" : "<=", V, hi));
    return cs.length === 1 ? cs[0] : X.and(...cs);
  });
  if (parts.includes(X.TRUE)) return X.TRUE;
  if (contractNe && ivs.length === 2 && ivs[0].lo === null && ivs[1].hi === null && ivs[0].hiOpen && ivs[1].loOpen && ivs[0].hi === ivs[1].lo) return X.rel("!=", V, ivs[0].hi);
  return parts.length === 1 ? parts[0] : X.or(...parts);
}
export const ivOut = (ivs) => ivs.map(({ lo, hi, loOpen, hiOpen }) => ({ lo, hi, loOpen: lo === null ? true : !!loOpen, hiOpen: hi === null ? true : !!hiOpen }));
export function ivText(iv) {
  if (iv.lo !== null && iv.hi !== null && iv.lo === iv.hi) return `{${toText(iv.lo)}}`;
  return `${iv.lo === null || iv.loOpen ? "(" : "["}${iv.lo === null ? "-oo" : toText(iv.lo)}, ${iv.hi === null ? "oo" : toText(iv.hi)}${iv.hi === null || iv.hiOpen ? ")" : "]"}`;
}
export const ivsText = (ivs) => (ivs.length ? ivs.map(ivText).join(" U ") : "the empty set");
// Double-valued membership in an interval set (with a relative tolerance at the ends).
export function inIvs(ivs, t, tol = 0) {
  for (const iv of ivs) {
    const lo = iv.lo === null ? -Infinity : dv(iv.lo), hi = iv.hi === null ? Infinity : dv(iv.hi);
    const e = tol * Math.max(1, Math.abs(t));
    const okLo = iv.loOpen ? t > lo - e : t >= lo - e;
    const okHi = iv.hiOpen ? t < hi + e : t <= hi + e;
    if (okLo && okHi) return true;
  }
  return false;
}

// Probe points around a set of boundaries plus a coarse grid.
export function probeGrid(bounds, span = 30, n = 240) {
  const pts = new Set();
  for (let i = 0; i <= n; i++) pts.add(-span + (2 * span * i) / n + 0.00731);
  const bs = bounds.filter(Number.isFinite).sort((a, b) => a - b);
  for (const b of bs) for (const e of [1e-6, 1e-3, 0.05, 0.37]) { const h = e * Math.max(1, Math.abs(b)); pts.add(b - h); pts.add(b + h); }
  for (let i = 0; i + 1 < bs.length; i++) pts.add((bs[i] + bs[i + 1]) / 2);
  return [...pts].sort((a, b) => a - b);
}

// Verification record helpers (verify.js status names, mapped by toContractVerification).
export const pass = (kind, detail, numeric = true) => ({ status: numeric ? "verified-numeric" : "verified-exact", checks: [{ kind, ok: true, detail }] });
export const bad = (kind, detail) => ({ status: "failed", checks: [{ kind, ok: false, detail }] });
export const open = (kind, detail) => ({ status: "inconclusive", checks: [{ kind, ok: null, detail }] });
export const fmt = (v) => (Number.isFinite(v) ? String(+v.toPrecision(10)) : v > 0 ? "oo" : v < 0 ? "-oo" : "undefined");
export const ptText = (p) => (p.approx ? `~${String(p.approx.value).slice(0, 14)}` : toText(p.tree));

// Independent adaptive Gauss-Legendre quadrature on [a, b] with the verifier's evaluator.
// Nodes never touch the ends (integrable end singularities are fine). Returns { value, err, ok }.
const GL_X = [0, 0.5384693101056831, 0.906179845938664], GL_W = [0.5688888888888889, 0.47862867049936647, 0.23692688505618908];
function gl5(g, a, b) {
  const c = (a + b) / 2, h = (b - a) / 2;
  let s = GL_W[0] * g(c);
  for (let i = 1; i < 3; i++) s += GL_W[i] * (g(c - h * GL_X[i]) + g(c + h * GL_X[i]));
  return s * h;
}
export function quadrature(g, a, b, tol = 1e-11, maxSeg = 4000) {
  if (!(b > a)) return { value: 0, err: 0, ok: a === b };
  let segs = [{ a, b, v: gl5(g, a, b) }];
  segs[0].e = Infinity;
  const refine = (s) => {
    const m = (s.a + s.b) / 2;
    const l = { a: s.a, b: m, v: gl5(g, s.a, m) }, r = { a: m, b: s.b, v: gl5(g, m, s.b) };
    const e = Math.abs(l.v + r.v - s.v);
    l.e = r.e = e / 2;
    return [l, r];
  };
  segs = refine(segs[0]);
  for (let it = 0; it < maxSeg; it++) {
    let tot = 0, err = 0, wi = 0;
    for (let i = 0; i < segs.length; i++) { tot += segs[i].v; err += segs[i].e; if (segs[i].e > segs[wi].e) wi = i; }
    if (!Number.isFinite(tot)) return { value: NaN, err: Infinity, ok: false };
    if (err <= tol * Math.max(1, Math.abs(tot))) return { value: tot, err, ok: true };
    segs.splice(wi, 1, ...refine(segs[wi]));
  }
  let tot = 0, err = 0;
  for (const s of segs) { tot += s.v; err += s.e; }
  return { value: tot, err, ok: Number.isFinite(tot) && err <= 1e-7 * Math.max(1, Math.abs(tot)) };
}

// Command argument helpers ------------------------------------------------------------
export function fnAndVar(args, name, { allowEq = true } = {}) {
  let f = args[0];
  if (!f) throw fail(`${name} needs a function, for example ${name}(x^2 - 1, x)`);
  if (allowEq && f.k === "eq" && f.args[0].k === "sym" && !X.freeOf(f.args[1], f.args[0])) throw fail(`${name} needs an expression, not an equation`);
  if (allowEq && f.k === "eq" && f.args[0].k === "sym") f = f.args[1]; // y = f(x)
  if (f.k === "eq" || f.k === "rel" || f.k === "system" || f.k === "and" || f.k === "or") throw fail(`${name} needs an expression f(x), not a relation`);
  let x = args[1] && args[1].k === "sym" ? args[1].name : null;
  const syms = [...X.freeSymbols(f)];
  if (!x) x = syms.length === 1 ? syms[0] : syms.includes("x") ? "x" : null;
  if (!x) throw fail(`${name} needs the variable, for example ${name}(f, x)`);
  const others = syms.filter((s) => s !== x);
  if (others.length) throw fail(`${name} works with one variable; ${others.join(", ")} would have to be given a value`);
  return { f, x, rest: args.slice(args[1] && args[1].k === "sym" ? 2 : 1) };
}
export function constArg(u, what) {
  if (!u) throw fail(`missing ${what}`);
  const s = C(u);
  if (X.freeSymbols(s).size) throw fail(`${what} must be a number, got ${toText(s)}`);
  const v = dv(s);
  if (!Number.isFinite(v)) throw fail(`${what} must be a real number, got ${toText(s)}`);
  return { tree: tidy(s), v };
}
export { simplify, makeCtx };
