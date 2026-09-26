// Quelvra solvers: Groebner bases over Q (Buchberger's algorithm, lex order).
//
// Polynomials are sparse maps  key "e1,e2,...,en" -> Rational  over a fixed variable list; the
// variable order is the lex order (vars[0] is the largest). The algorithm uses Buchberger's two
// criteria to skip useless S-pairs (coprime leading monomials; the chain criterion), the normal
// selection strategy (smallest lcm first), and finally returns the reduced Groebner basis
// (monic, no leading monomial divisible by another, fully inter-reduced).

import * as Q from "../num.js";
import * as X from "../expr.js";
import * as P from "../poly.js";

const key = (e) => e.join(",");
const unkey = (k) => k.split(",").map(Number);

export class GPoly {
  constructor(n, terms) { this.n = n; this.terms = terms || new Map(); } // Map key -> Rational
  static fromMPoly(p, vars) {
    const q = P.mReorder(p, vars);
    const t = new Map();
    for (const [k, c] of q.terms) t.set(key(P.expsOf(k, vars.length)), c);
    return new GPoly(vars.length, t);
  }
  isZero() { return this.terms.size === 0; }
  lead() {
    let best = null, bk = null;
    for (const k of this.terms.keys()) { const e = unkey(k); if (!best || lexCmp(e, best) > 0) { best = e; bk = k; } }
    return best ? { e: best, c: this.terms.get(bk) } : null;
  }
  scaleMono(c, e) { // c * x^e * this
    const t = new Map();
    for (const [k, v] of this.terms) { const f = unkey(k); t.set(key(f.map((a, i) => a + e[i])), Q.mul(v, c)); }
    return new GPoly(this.n, t);
  }
  sub(o) {
    const t = new Map(this.terms);
    for (const [k, v] of o.terms) { const s = t.has(k) ? Q.sub(t.get(k), v) : Q.neg(v); if (s.n === 0n) t.delete(k); else t.set(k, s); }
    return new GPoly(this.n, t);
  }
  monic() { const l = this.lead(); if (!l) return this; const inv = Q.inv(l.c); const t = new Map(); for (const [k, v] of this.terms) t.set(k, Q.mul(v, inv)); return new GPoly(this.n, t); }
  toTree(vars) {
    const terms = [];
    for (const [k, c] of this.terms) { const e = unkey(k); terms.push(X.mul(X.num(c), ...e.map((a, j) => (a ? X.pow(X.sym(vars[j]), X.num(a)) : X.ONE)))); }
    return terms.length ? X.add(...terms) : X.ZERO;
  }
  equals(o) { if (this.terms.size !== o.terms.size) return false; for (const [k, v] of this.terms) { const w = o.terms.get(k); if (!w || !Q.eq(v, w)) return false; } return true; }
}
export function lexCmp(a, b) { for (let i = 0; i < a.length; i++) if (a[i] !== b[i]) return a[i] > b[i] ? 1 : -1; return 0; }
const divides = (a, b) => a.every((x, i) => x <= b[i]);
const lcm = (a, b) => a.map((x, i) => Math.max(x, b[i]));
const coprime = (a, b) => a.every((x, i) => x === 0 || b[i] === 0);
const deg = (e) => e.reduce((s, x) => s + x, 0);

// full reduction of f modulo G (list of GPoly with cached leads)
export function reduce(f, G, tick) {
  let r = new GPoly(f.n), p = f;
  while (!p.isZero()) {
    tick && tick();
    const lt = p.lead();
    let done = false;
    for (const g of G) {
      const lg = g._lead || (g._lead = g.lead());
      if (divides(lg.e, lt.e)) {
        const c = Q.div(lt.c, lg.c);
        p = p.sub(g.scaleMono(c, lt.e.map((x, i) => x - lg.e[i])));
        done = true;
        break;
      }
    }
    if (!done) {
      const k = key(lt.e);
      r.terms.set(k, lt.c);
      const t = new Map(p.terms); t.delete(k); p = new GPoly(p.n, t);
    }
  }
  return r;
}
function spoly(f, g) {
  const lf = f._lead || (f._lead = f.lead()), lg = g._lead || (g._lead = g.lead());
  const L = lcm(lf.e, lg.e);
  return f.scaleMono(Q.inv(lf.c), L.map((x, i) => x - lf.e[i])).sub(g.scaleMono(Q.inv(lg.c), L.map((x, i) => x - lg.e[i])));
}

// Reduced Groebner basis. opts: { maxSteps, checkTime }
export function groebner(F, opts = {}) {
  const maxSteps = opts.maxSteps || 200000;
  let steps = 0;
  const tick = () => { if (++steps > maxSteps) { const e = new Error("Groebner basis computation exceeded its budget"); e.code = "BUDGET"; throw e; } if (opts.checkTime && steps % 500 === 0) opts.checkTime(); };
  const G = [];
  for (const f of F) if (!f.isZero()) { const m = f.monic(); m._lead = m.lead(); G.push(m); }
  if (!G.length) return { basis: [], steps };
  const pairs = [];
  const done = new Set();
  const addPairs = (j) => { for (let i = 0; i < j; i++) pairs.push([i, j]); };
  for (let j = 1; j < G.length; j++) addPairs(j);
  let stats = { pairs: 0, criterion1: 0, criterion2: 0, reductions: 0 };
  while (pairs.length) {
    // normal strategy: smallest lcm in total degree, then lex
    let bi = 0;
    for (let t = 1; t < pairs.length; t++) {
      const a = lcm(G[pairs[t][0]]._lead.e, G[pairs[t][1]]._lead.e), b = lcm(G[pairs[bi][0]]._lead.e, G[pairs[bi][1]]._lead.e);
      if (deg(a) < deg(b) || (deg(a) === deg(b) && lexCmp(a, b) < 0)) bi = t;
    }
    const [i, j] = pairs.splice(bi, 1)[0];
    done.add(i + "," + j);
    stats.pairs++;
    const li = G[i]._lead.e, lj = G[j]._lead.e;
    if (coprime(li, lj)) { stats.criterion1++; continue; } // Buchberger's first criterion
    const L = lcm(li, lj);
    // chain criterion: some k with LM(k) | lcm and pairs (i,k), (j,k) already treated
    let chain = false;
    for (let k = 0; k < G.length && !chain; k++) {
      if (k === i || k === j) continue;
      if (!divides(G[k]._lead.e, L)) continue;
      const pk = (a, b) => (a < b ? a + "," + b : b + "," + a);
      if (done.has(pk(i, k)) && done.has(pk(j, k))) chain = true;
    }
    if (chain) { stats.criterion2++; continue; }
    const s = spoly(G[i], G[j]);
    const r = reduce(s, G, tick);
    stats.reductions++;
    if (!r.isZero()) {
      const m = r.monic(); m._lead = m.lead();
      G.push(m);
      addPairs(G.length - 1);
      if (deg(m._lead.e) === 0) break; // 1 in the ideal
    }
  }
  return { basis: reduced(G, tick), steps, stats };
}
function reduced(G, tick) {
  // minimal: drop polynomials whose leading monomial is divisible by another's
  let M = G.slice();
  if (M.some((g) => deg(g._lead.e) === 0)) { const one = new GPoly(M[0].n, new Map([[key(new Array(M[0].n).fill(0)), Q.Q(1n)]])); one._lead = one.lead(); return [one]; }
  M = M.filter((g, i) => !M.some((h, j) => j !== i && divides(h._lead.e, g._lead.e) && (lexCmp(h._lead.e, g._lead.e) !== 0 || j < i)));
  // inter-reduce
  const out = [];
  for (let i = 0; i < M.length; i++) {
    const others = M.filter((_, j) => j !== i);
    const r = reduce(M[i], others, tick).monic();
    r._lead = r.lead();
    out.push(r);
  }
  out.sort((a, b) => lexCmp(b._lead.e, a._lead.e));
  return out;
}
// zero-dimensional: every variable has a pure power among the leading monomials
export function isZeroDimensional(basis, n) {
  for (let v = 0; v < n; v++) if (!basis.some((g) => g._lead.e.every((x, i) => (i === v ? x > 0 : x === 0)))) return false;
  return true;
}
