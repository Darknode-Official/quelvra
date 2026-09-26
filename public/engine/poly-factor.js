// Quelvra polynomial factorisation over Q.
//
//   univariate: content -> x^k -> square-free (Yun) -> Zassenhaus on each square-free part:
//     distinct-degree + equal-degree (Cantor-Zassenhaus) factorisation modulo a good prime p,
//     multifactor linear Hensel lifting to p^k > 2 |lc| 2^n ||f||_2 (Mignotte-type bound),
//     recombination of lifted factors by subsets with the trailing-coefficient test and exact
//     trial division over Z. Every result is verified by exact multiplication.
//   multivariate: numeric + monomial content -> content with respect to a main variable
//     (recursive) -> square-free decomposition (Yun over Q[others][x]) -> Kronecker substitution
//     x_j -> t^(w_j) with exact trial division of every candidate. Verified by multiplication;
//     on any doubt the unfactored polynomial is returned (never a wrong factorisation).

import * as N from "./num.js";
import * as X from "./expr.js";
import { together, makeCtx } from "./simplify.js";
import { toText } from "./print.js";
import * as C from "./poly-core.js";

const { tick, guard, budgetError, canon } = C;

// numerator / denominator split without touching simplify's shared default budget
export function numDen(u) {
  if (u.k === "pow" && X.isNum(u.args[1]) && N.isNeg(u.args[1].v)) return [X.ONE, canon(X.pow(u.args[0], X.num(N.neg(u.args[1].v))))];
  if (u.k === "num") return [X.num(u.v.n), X.num(u.v.d)];
  if (u.k === "mul") {
    const n = [], d = [];
    for (const f of u.args) { const [a, b] = numDen(f); if (!X.isOne(a)) n.push(a); if (!X.isOne(b)) d.push(b); }
    return [canon(X.mul(...n)), canon(X.mul(...d))];
  }
  return [u, X.ONE];
}
const Q0 = N.ZERO, Q1 = N.ONE;

// ---------------------------------------------------------------- arithmetic mod p (Number)
// p < 2^26 so every product of two residues is an exact double.
const md = (a, p) => { a %= p; return a < 0 ? a + p : a; };
function pNorm(a) { let n = a.length; while (n > 0 && a[n - 1] === 0) n--; return n === a.length ? a : a.slice(0, n); }
function invMod(a, p) {
  let [r0, r1, s0, s1] = [md(a, p), p, 1, 0];
  while (r1) { const q = Math.floor(r0 / r1); [r0, r1] = [r1, r0 - q * r1]; [s0, s1] = [s1, s0 - q * s1]; }
  if (r0 !== 1) throw new Error("Quelvra: internal error (non-invertible residue)");
  return md(s0, p);
}
function pAdd(a, b, p) { const n = Math.max(a.length, b.length), o = new Array(n); for (let i = 0; i < n; i++) o[i] = ((a[i] || 0) + (b[i] || 0)) % p; return pNorm(o); }
function pSub(a, b, p) { const n = Math.max(a.length, b.length), o = new Array(n); for (let i = 0; i < n; i++) o[i] = md((a[i] || 0) - (b[i] || 0), p); return pNorm(o); }
function pScale(a, k, p) { k = md(k, p); return k ? pNorm(a.map((v) => (v * k) % p)) : []; }
function pMul(a, b, p) {
  if (!a.length || !b.length) return [];
  const o = new Array(a.length + b.length - 1).fill(0);
  for (let i = 0; i < a.length; i++) { const ai = a[i]; if (!ai) continue; for (let j = 0; j < b.length; j++) o[i + j] = (o[i + j] + ai * b[j]) % p; }
  return pNorm(o);
}
function pDivmod(a, b, p) {
  const db = b.length - 1;
  if (db < 0) throw new RangeError("Quelvra: division by zero mod p");
  if (a.length - 1 < db) return { q: [], r: a };
  const r = a.slice(), q = new Array(a.length - db).fill(0), inv = invMod(b[db], p);
  for (let i = a.length - 1; i >= db; i--) {
    const c = r[i];
    if (!c) continue;
    const t = (c * inv) % p;
    q[i - db] = t;
    for (let j = 0; j <= db; j++) r[i - db + j] = md(r[i - db + j] - t * b[j], p);
  }
  return { q: pNorm(q), r: pNorm(r.slice(0, db)) };
}
const pRem = (a, b, p) => pDivmod(a, b, p).r;
const pMonic = (a, p) => (a.length ? pScale(a, invMod(a[a.length - 1], p), p) : a);
function pGcd(a, b, p) {
  for (let g = a.length + b.length + 2; b.length; ) { if (--g < 0) throw budgetError("gcd mod p"); [a, b] = [b, pRem(a, b, p)]; }
  return pMonic(a, p);
}
function pXgcd(a, b, p) {
  let r0 = a, r1 = b, s0 = [1], s1 = [], t0 = [], t1 = [1];
  for (let g = a.length + b.length + 2; r1.length; ) {
    if (--g < 0) throw budgetError("xgcd mod p");
    const { q, r } = pDivmod(r0, r1, p);
    [r0, r1] = [r1, r];
    [s0, s1] = [s1, pSub(s0, pMul(q, s1, p), p)];
    [t0, t1] = [t1, pSub(t0, pMul(q, t1, p), p)];
  }
  const k = invMod(r0[r0.length - 1], p);
  return { g: pScale(r0, k, p), s: pScale(s0, k, p), t: pScale(t0, k, p) };
}
function pPowMod(base, e, m, p) {
  let r = [1], b = pRem(base, m, p);
  e = BigInt(e);
  while (e > 0n) { tick(); if (e & 1n) r = pRem(pMul(r, b, p), m, p); e >>= 1n; if (e) b = pRem(pMul(b, b, p), m, p); }
  return r;
}
const pDeriv = (a, p) => pNorm(a.slice(1).map((v, i) => (v * ((i + 1) % p)) % p));

// deterministic pseudo-random residues (xorshift) for Cantor-Zassenhaus
function prng(seed) {
  let s = seed >>> 0 || 0x9e3779b9;
  return (m) => { s ^= s << 13; s >>>= 0; s ^= s >>> 17; s ^= s << 5; s >>>= 0; return s % m; };
}
function edf(g, d, p, rnd) {
  const n = g.length - 1;
  if (n === d) return [g];
  const e = (BigInt(p) ** BigInt(d) - 1n) / 2n;
  for (let tries = 0; tries < 400; tries++) {
    tick();
    const a = [];
    for (let i = 0; i < n; i++) a.push(rnd(p));
    const ap = pNorm(a);
    if (ap.length < 2) continue;
    const b = pSub(pPowMod(ap, e, g, p), [1], p);
    const h = pGcd(g, b, p);
    if (h.length > 1 && h.length < g.length) return [...edf(h, d, p, rnd), ...edf(pMonic(pDivmod(g, h, p).q, p), d, p, rnd)];
  }
  throw budgetError("equal-degree factorisation");
}
// Monic irreducible factors of a monic square-free f mod p (p odd prime).
function czFactor(f, p) {
  const rnd = prng(1234567 + p);
  const out = [];
  let fr = f, h = [0, 1];
  for (let i = 1; fr.length - 1 >= 2 * i; i++) {
    tick();
    h = pPowMod(h, p, fr, p);
    const g = pGcd(fr, pSub(h, [0, 1], p), p);
    if (g.length > 1) {
      out.push(...edf(g, i, p, rnd));
      fr = pMonic(pDivmod(fr, g, p).q, p);
      h = pRem(h, fr, p);
    }
  }
  if (fr.length > 1) out.push(fr);
  return out;
}

// Public Z_p factorisation (Cantor-Zassenhaus). coeffs: integers low -> high; p an odd prime
// below 2^26. Returns { lc, factors: [monic residue arrays] } with f = lc * prod factors (mod p).
// The input must be square-free modulo p (RangeError otherwise).
export function factorModP(coeffs, p, opts) {
  return guard(opts, () => {
    if (!Number.isInteger(p) || p < 3 || p >= 2 ** 26 || !PRIMES.includes(p) && !isPrimeSmall(p)) throw new RangeError("Quelvra: p must be an odd prime below 2^26");
    const P = BigInt(p);
    const f = pNorm(coeffs.map((c) => Number(((BigInt(c) % P) + P) % P)));
    if (f.length <= 1) return { lc: f.length ? f[0] : 0, factors: [] };
    if (pGcd(f, pDeriv(f, p), p).length > 1) throw new RangeError("Quelvra: polynomial is not square-free modulo p");
    const fs = czFactor(pMonic(f, p), p);
    fs.sort((a, b) => a.length - b.length || (a.join(",") < b.join(",") ? -1 : 1));
    return { lc: f[f.length - 1], factors: fs };
  });
}
function isPrimeSmall(n) { if (n % 2 === 0) return false; for (let d = 3; d * d <= n; d += 2) if (n % d === 0) return false; return true; }

const PRIMES = (() => {
  const out = [], lim = 60000, s = new Uint8Array(lim + 1);
  for (let i = 2; i <= lim; i++) if (!s[i]) { out.push(i); for (let j = i * i; j <= lim; j += i) s[j] = 1; }
  return out.slice(1); // odd primes only
})();

// ---------------------------------------------------------------- Hensel lifting
function modSym(v, M) { let r = v % M; if (r < 0n) r += M; if (r > M / 2n) r -= M; return r; }
function henselLift(f, gs, p, k) {
  const P = BigInt(p), r = gs.length;
  const lcf = f[f.length - 1];
  const lcInv = invMod(Number(((lcf % P) + P) % P), p);
  // t_i = inverse of prod_{j != i} g_j modulo g_i
  const ts = gs.map((gi, i) => {
    let hat = [1];
    for (let j = 0; j < r; j++) if (j !== i) hat = pMul(hat, gs[j], p);
    const { s } = pXgcd(pRem(hat, gi, p), gi, p);
    return s;
  });
  const G = gs.map((g) => g.map(BigInt));
  let pj = P;
  for (let j = 1; j < k; j++) {
    tick(r);
    const M = pj * P;
    let prod = [lcf % M];
    for (const g of G) prod = C.zMul(prod, g).map((v) => v % M);
    const e = [];
    for (let i = 0; i < f.length; i++) {
      let c = ((f[i] - (prod[i] || 0n)) % M + M) % M;
      if (c % pj !== 0n) throw new Error("Quelvra: internal error (Hensel invariant)");
      e.push(Number((c / pj) % P));
    }
    const ep = pScale(pNorm(e), lcInv, p);
    if (ep.length) {
      for (let i = 0; i < r; i++) {
        const delta = pRem(pMul(ep, ts[i], p), gs[i], p);
        for (let t = 0; t < delta.length; t++) G[i][t] = (G[i][t] + pj * BigInt(delta[t])) % M;
      }
    }
    pj = M;
  }
  return { G, M: pj };
}

// ---------------------------------------------------------------- Zassenhaus
function sqrtCeil(n) { const [r, ex] = N.iroot(n, 2); return ex ? r : r + 1n; }
function mignotteModulusBound(f) {
  const n = f.length - 1;
  let s = 0n;
  for (const c of f) s += c * c;
  const lcf = f[n] < 0n ? -f[n] : f[n];
  return 2n * lcf * (1n << BigInt(n)) * sqrtCeil(s) + 1n;
}
function quadraticFactor(f) {
  const [c, b, a] = f;
  const D = b * b - 4n * a * c;
  if (D < 0n) return [f];
  const [s, ex] = N.iroot(D, 2);
  if (!ex) return [f];
  const g1 = C.zPrimitive([b - s, 2n * a]), g2 = C.zPrimitive([b + s, 2n * a]);
  if (C.zEq(C.zMul(g1, g2), f)) return [g1, g2];
  return [f];
}
// f: square-free, primitive, lc > 0, f(0) != 0, degree >= 1. Returns irreducible factors.
function zassenhaus(f, stats) {
  const n = f.length - 1;
  if (n <= 1) return [f];
  if (n === 2) return quadraticFactor(f);
  const lcf = f[n];
  let best = null, good = 0;
  for (let pi = 0; pi < PRIMES.length && pi < 400; pi++) {
    const p = PRIMES[pi], P = BigInt(p);
    if (lcf % P === 0n) continue;
    const fp = pNorm(f.map((c) => Number(((c % P) + P) % P)));
    if (pGcd(fp, pDeriv(fp, p), p).length > 1) continue;
    tick(n);
    const fs = czFactor(pMonic(fp, p), p);
    if (!best || fs.length < best.fs.length) best = { p, fs };
    if (fs.length === 1) return [f];
    if (++good >= 6) break;
  }
  if (!best) throw budgetError("no good prime");
  if (stats) { stats.prime = best.p; stats.modFactors = best.fs.length; }
  const { p, fs } = best;
  const bound = mignotteModulusBound(f);
  let k = 1, pk = BigInt(p);
  while (pk <= bound) { pk *= BigInt(p); k++; }
  const { G, M } = henselLift(f, fs, p, k);
  // recombination
  let cur = f, rem = G.map((g, i) => i);
  const out = [];
  let s = 1;
  let combos = 0;
  outer: while (2 * s <= rem.length) {
    const idx = Array.from({ length: s }, (_, i) => i);
    for (;;) {
      if (++combos > 300000) throw budgetError("Zassenhaus recombination");
      tick();
      const lcc = cur[cur.length - 1];
      let g = [lcc % M];
      for (const i of idx) g = C.zMul(g, G[rem[i]]).map((v) => v % M);
      g = C.zNorm(g.map((v) => modSym(v, M)));
      const c0 = lcc * cur[0];
      if (g.length > 1 && g[0] !== 0n && c0 % g[0] === 0n) {
        const h = C.zPrimitive(g);
        const q = C.zDivExact(cur, h);
        if (q) {
          out.push(h);
          cur = C.zPrimitive(q);
          const used = new Set(idx.map((i) => rem[i]));
          rem = rem.filter((x) => !used.has(x));
          continue outer;
        }
      }
      // next combination
      let t = s - 1;
      while (t >= 0 && idx[t] === rem.length - s + t) t--;
      if (t < 0) break;
      idx[t]++;
      for (let u = t + 1; u < s; u++) idx[u] = idx[u - 1] + 1;
    }
    s++;
  }
  if (cur.length > 1) out.push(cur);
  return out;
}

function zCmp(a, b) {
  if (a.length !== b.length) return a.length - b.length;
  for (let i = a.length - 1; i >= 0; i--) if (a[i] !== b[i]) return a[i] < b[i] ? -1 : 1;
  return 0;
}
// Factor an integer polynomial: f = unit * prod poly^mult, polys primitive irreducible, lc > 0.
export function factorZ(f, opts) {
  return guard(opts, () => {
    f = C.zNorm(f.map(BigInt));
    if (!f.length) return { unit: 0n, factors: [], verified: true };
    if (f.length === 1) return { unit: f[0], factors: [], verified: true };
    let unit = C.zContent(f);
    if (f[f.length - 1] < 0n) unit = -unit;
    const g = f.map((v) => v / unit);
    const factors = [];
    let k = 0;
    while (g[k] === 0n) k++;
    if (k) factors.push({ poly: [0n, 1n], mult: k });
    const h = g.slice(k);
    if (h.length > 1) {
      const sf = C.squareFree(C.fromZ(h));
      for (const { poly, mult } of sf.factors) {
        const z = C.toZ(poly).z;
        for (const q of zassenhaus(z)) factors.push({ poly: q, mult });
      }
    }
    factors.sort((a, b) => zCmp(a.poly, b.poly) || a.mult - b.mult);
    // exact verification
    let prod = [unit];
    for (const { poly, mult } of factors) prod = C.zMul(prod, C.zPow(poly, mult));
    if (!C.zEq(prod, f)) return { unit, factors: [{ poly: g, mult: 1 }], verified: false };
    return { unit, factors, verified: true };
  });
}
// Factor a UPoly over Q: p = unit * prod poly^mult with poly integer primitive, lc > 0.
export function factorQ(p, opts) {
  return guard(opts, () => {
    p = C.norm(p);
    if (p.length <= 1) return { unit: C.lc(p), factors: [], verified: true };
    const { c, z } = C.toZ(p);
    const r = factorZ(z);
    return { unit: N.mul(c, N.Q(r.unit)), factors: r.factors.map(({ poly, mult }) => ({ poly: C.fromZ(poly), mult })), verified: r.verified };
  });
}
export function isIrreducible(p, opts) {
  const r = factorQ(p, opts);
  return r.factors.length === 1 && r.factors[0].mult === 1;
}

// ---------------------------------------------------------------- multivariate
function monomialContent(p) {
  const nv = p.vars.length;
  let mins = null;
  for (const k of p.terms.keys()) {
    const e = C.expsOf(k, nv);
    mins = mins ? mins.map((m, i) => Math.min(m, e[i])) : e;
  }
  return mins || p.vars.map(() => 0);
}
function divMonomial(p, e) {
  const nv = p.vars.length;
  return C.mpoly(p.vars, [...p.terms].map(([k, c]) => [C.expsOf(k, nv).map((x, i) => x - e[i]), c]));
}
const MAX_KRON_DEG = 260, MAX_KRON_FACTORS = 16;
function kronecker(f, used) {
  const vars = f.vars, nv = vars.length;
  const idx = used.map((v) => vars.indexOf(v));
  const degs = used.map((v) => C.mDegree(f, v));
  const w = [1];
  for (let j = 1; j < used.length; j++) w.push(w[j - 1] * (degs[j - 1] + 1));
  const D = degs.reduce((s, d, j) => s + d * w[j], 0);
  if (D > MAX_KRON_DEG) return { factors: [f], complete: false };
  const u = new Array(D + 1).fill(0n);
  for (const [k, c] of f.terms) {
    const e = C.expsOf(k, nv);
    let t = 0;
    for (let j = 0; j < idx.length; j++) t += e[idx[j]] * w[j];
    u[t] += c.n;
  }
  const fz = factorZ(u);
  if (!fz.verified) return { factors: [f], complete: false };
  const list = [];
  for (const { poly, mult } of fz.factors) for (let i = 0; i < mult; i++) list.push(poly);
  if (list.length > MAX_KRON_FACTORS) return { factors: [f], complete: false };
  const invMap = (h) => {
    const entries = [];
    for (let i = 0; i < h.length; i++) {
      if (h[i] === 0n) continue;
      let r = i;
      const e = new Array(nv).fill(0);
      for (let j = idx.length - 1; j >= 0; j--) {
        const dj = Math.floor(r / w[j]);
        if (dj > degs[j]) return null;
        e[idx[j]] = dj;
        r -= dj * w[j];
      }
      entries.push([e, N.Q(h[i])]);
    }
    return C.mpoly(vars, entries);
  };
  let cur = f, rem = list.map((_, i) => i);
  const out = [];
  let s = 1, combos = 0;
  outer: while (2 * s <= rem.length) {
    const ix = Array.from({ length: s }, (_, i) => i);
    for (;;) {
      if (++combos > 20000) return { factors: [...out, cur], complete: false };
      tick();
      let h = [1n];
      for (const i of ix) h = C.zMul(h, list[rem[i]]);
      const H = invMap(h);
      if (H && C.mUsedVars(H).length) {
        const q = C.mDivExact(cur, H);
        if (q) {
          out.push(C.mNormalize(H).p);
          cur = C.mNormalize(q).p;
          const usedIdx = new Set(ix.map((i) => rem[i]));
          rem = rem.filter((x) => !usedIdx.has(x));
          continue outer;
        }
      }
      let t = s - 1;
      while (t >= 0 && ix[t] === rem.length - s + t) t--;
      if (t < 0) break;
      ix[t]++;
      for (let v = t + 1; v < s; v++) ix[v] = ix[v - 1] + 1;
    }
    s++;
  }
  if (C.mUsedVars(cur).length) out.push(cur);
  return { factors: out, complete: true };
}
function mSortKey(p) {
  return [C.mTotalDegree(p), [...p.terms].map(([k, c]) => k + ":" + c.n + "/" + c.d).sort().join(";")];
}
// Factor an MPoly over Q: p = unit * prod poly^mult; each poly integer primitive with positive
// lex-leading coefficient (in p.vars order). complete=false when a size limit stopped the search
// (the returned product is still exactly p).
export function mFactor(p, opts) {
  return guard(opts, () => {
    const vars = p.vars;
    if (C.mIsZero(p)) return { unit: Q0, factors: [], complete: true, verified: true };
    const { unit: u0, p: prim } = C.mNormalize(p);
    const out = [];
    let complete = true;
    const mc = monomialContent(prim);
    mc.forEach((e, i) => { if (e) out.push({ poly: C.mVar(vars, vars[i]), mult: e }); });
    const rec = (q, mult, depth) => {
      if (depth > 64) throw budgetError("multivariate factorisation depth");
      q = C.mNormalize(q).p;
      const used = C.mUsedVars(q);
      if (!used.length) return;
      if (used.length === 1) {
        const fq = factorQ(C.mToU(q, used[0]));
        if (!fq.verified) complete = false;
        for (const f of fq.factors) out.push({ poly: C.mFromU(f.poly, vars, used[0]), mult: f.mult * mult });
        return;
      }
      let v = used[0];
      for (const w of used) if (C.mDegree(q, w) < C.mDegree(q, v)) v = w;
      const cont = C.mContentIn(q, v);
      if (C.mUsedVars(cont).length) {
        rec(cont, mult, depth + 1);
        const rest = C.mDivExact(q, cont);
        if (!rest) throw new Error("Quelvra: internal error (content)");
        rec(rest, mult, depth + 1);
        return;
      }
      const order = [v, ...used.filter((w) => w !== v)];
      const R = C._rec.mToRec(q, order);
      const parts = C._rec.rYun(R, order.length);
      for (const { p: part, mult: m } of parts) {
        const P = C.mNormalize(C._rec.rToM(part, order, vars)).p;
        const k = kronecker(P, C.mUsedVars(P));
        if (!k.complete) complete = false;
        for (const f of k.factors) out.push({ poly: f, mult: m * mult });
      }
    };
    rec(divMonomial(prim, mc), 1, 0);
    // merge equal factors, sort
    const merged = [];
    for (const f of out) {
      const g = merged.find((h) => C.mEq(h.poly, f.poly));
      if (g) g.mult += f.mult; else merged.push({ poly: f.poly, mult: f.mult });
    }
    merged.sort((a, b) => { const ka = mSortKey(a.poly), kb = mSortKey(b.poly); return ka[0] - kb[0] || (ka[1] < kb[1] ? -1 : ka[1] > kb[1] ? 1 : 0); });
    // unit from lex-leading coefficients, then exact verification
    let unit = N.mul(u0, Q1);
    let prod = C.mConst(vars, unit);
    for (const { poly, mult } of merged) prod = C.mMul(prod, C.mPow(poly, mult));
    if (!C.mEq(prod, p)) {
      const lp = C.mLeadTerm(p).coeff, lq = C.mLeadTerm(prod).coeff;
      unit = N.mul(unit, N.div(lp, lq));
      prod = C.mScale(prod, N.div(lp, lq));
      if (!C.mEq(prod, p)) return { unit: u0, factors: [{ poly: prim, mult: 1 }], complete: false, verified: false };
    }
    return { unit, factors: merged, complete, verified: true };
  });
}

// ---------------------------------------------------------------- trees
// Replace non-polynomial kernels (functions, radicals, constants) by fresh symbols.
function kernelize(u) {
  const map = new Map(), back = new Map();
  let n = 0;
  const go = (w) => {
    switch (w.k) {
      case "num": case "sym": return w;
      case "add": case "mul": return X.withArgs(w, w.args.map(go));
      case "pow":
        if (X.isInt(w.args[1])) return X.withArgs(w, [go(w.args[0]), w.args[1]]);
      // fallthrough
      default: {
        if (w === X.UNDEF || w === X.OO) throw Object.assign(new Error("not factorable"), { code: "NOTPOLY" });
        if (!map.has(w)) { const s = X.sym("\u0001k" + n++); map.set(w, s); back.set(s.name, w); }
        return map.get(w);
      }
    }
  };
  return { node: go(u), back };
}
function assemble(unit, factors, back) {
  const t = canon(X.mul(X.num(unit), ...factors.map(({ poly, mult }) => X.pow(C.toTree(poly), X.num(mult)))));
  return back && back.size ? canon(X.subs(t, back)) : t;
}
function prepare(node) {
  const u = canon(node);
  if (u.k !== "add" && u.k !== "mul" && u.k !== "pow") return null;
  const { node: k, back } = kernelize(u);
  const vars = [...X.freeSymbols(k)].sort();
  if (!vars.length) return null;
  const m = C.fromTree(k, vars);
  return m ? { m, back, vars } : null;
}
// Factor an expression tree over Q. Rational expressions are factored as numerator/denominator.
export function factorTree(node, opts) {
  return guard(opts, () => {
    let u = canon(node);
    if (u.k === "eq" || u.k === "rel") return X.withArgs(u, u.args.map((a) => factorTree(a)));
    if (u.k === "add") u = together(u, makeCtx());
    const [nu, de] = numDen(u);
    if (!X.isOne(de)) return canon(C.RB.div(factorTree(nu), factorTree(de)));
    let pr;
    try { pr = prepare(u); } catch (e) { if (e.code === "NOTPOLY") return u; throw e; }
    if (!pr) return u;
    try {
      const f = mFactor(pr.m);
      return assemble(f.unit, f.factors, pr.back);
    } catch (e) {
      if (e && e.code === "BUDGET") return u;
      throw e;
    }
  });
}

// ---------------------------------------------------------------- factoring with steps
// Rule ids: factor.common, factor.diff-squares, factor.sum-cubes, factor.diff-cubes,
// factor.perfect-square, factor.trinomial, factor.trinomial-ac, factor.grouping,
// factor.rational-root, factor.square-free, factor.zassenhaus, factor.kronecker, factor.complete.
const txt = (t) => toText(t);
function ratSqrt(r) {
  if (N.isNeg(r)) return null;
  const [a, ea] = N.iroot(r.n, 2), [b, eb] = N.iroot(r.d, 2);
  return ea && eb ? N.Q(a, b) : null;
}
function ratCbrt(r) {
  const [a, ea] = N.iroot(r.n, 3), [b, eb] = N.iroot(r.d, 3);
  return ea && eb ? N.Q(a, b) : null;
}
const termsOf = (m) => [...m.terms].map(([k, c]) => ({ e: C.expsOf(k, m.vars.length), c }));
const monoTree = (vars, e) => canon(X.mul(...e.map((x, j) => (x ? X.pow(X.sym(vars[j]), X.num(x)) : X.ONE))));
const fromTerms = (vars, ts) => C.mpoly(vars, ts.map((t) => [t.e, t.c]));

function tryBinomial(m) {
  const ts = termsOf(m);
  if (ts.length !== 2) return null;
  let [a, b] = ts[0].c.n > 0n ? [ts[0], ts[1]] : [ts[1], ts[0]];
  if (N.isNeg(a.c)) return null;
  const vars = m.vars;
  // difference of squares
  if (N.isNeg(b.c) && a.e.every((x) => x % 2 === 0) && b.e.every((x) => x % 2 === 0)) {
    const sa = ratSqrt(a.c), sb = ratSqrt(N.neg(b.c));
    if (sa && sb) {
      const A = { e: a.e.map((x) => x / 2), c: sa }, B = { e: b.e.map((x) => x / 2), c: sb };
      const f1 = fromTerms(vars, [A, { e: B.e, c: N.neg(B.c) }]), f2 = fromTerms(vars, [A, B]);
      const At = canon(X.mul(X.num(A.c), monoTree(vars, A.e))), Bt = canon(X.mul(X.num(B.c), monoTree(vars, B.e)));
      return { rule: "factor.diff-squares", title: "Difference of squares", parts: [f1, f2],
        why: `${txt(C.toTree(m))} = (${txt(At)})^2 - (${txt(Bt)})^2, and A^2 - B^2 = (A - B)(A + B).` };
    }
  }
  // sum / difference of cubes
  if (a.e.every((x) => x % 3 === 0) && b.e.every((x) => x % 3 === 0)) {
    const ca = ratCbrt(a.c), cb = ratCbrt(b.c);
    if (ca && cb) {
      const A = { e: a.e.map((x) => x / 3), c: ca }, B = { e: b.e.map((x) => x / 3), c: cb };
      const Am = fromTerms(vars, [A]), Bm = fromTerms(vars, [B]);
      const lin = C.mAdd(Am, Bm);
      const quad = C.mAdd(C.mSub(C.mMul(Am, Am), C.mMul(Am, Bm)), C.mMul(Bm, Bm));
      const isSum = !N.isNeg(b.c);
      const At = C.toTree(Am), Bt = C.toTree(isSum ? Bm : C.mNeg(Bm));
      return { rule: isSum ? "factor.sum-cubes" : "factor.diff-cubes", title: isSum ? "Sum of cubes" : "Difference of cubes", parts: [lin, quad],
        why: isSum ? `${txt(C.toTree(m))} = (${txt(At)})^3 + (${txt(Bt)})^3, and A^3 + B^3 = (A + B)(A^2 - AB + B^2).`
          : `${txt(C.toTree(m))} = (${txt(At)})^3 - (${txt(Bt)})^3, and A^3 - B^3 = (A - B)(A^2 + AB + B^2).` };
    }
  }
  return null;
}
function lexDesc(ts) { return ts.slice().sort((x, y) => { for (let i = 0; i < x.e.length; i++) if (x.e[i] !== y.e[i]) return y.e[i] - x.e[i]; return 0; }); }
function tryTrinomial(m) {
  const ts = termsOf(m);
  if (ts.length !== 3) return null;
  const [t1, t2, t3] = lexDesc(ts);
  if (!t1.e.every((x) => x % 2 === 0) || !t3.e.every((x) => x % 2 === 0)) return null;
  const U = t1.e.map((x) => x / 2), W = t3.e.map((x) => x / 2);
  if (!t2.e.every((x, i) => x === U[i] + W[i])) return null;
  if (!ts.every((t) => t.c.d === 1n)) return null;
  const a = t1.c.n, b = t2.c.n, c = t3.c.n;
  const D = b * b - 4n * a * c;
  if (D < 0n) return null;
  const [s, ex] = N.iroot(D, 2);
  if (!ex) return null;
  const vars = m.vars;
  const mk = (p, q) => C.mNormalize(fromTerms(vars, [{ e: U, c: N.Q(p) }, { e: W, c: N.Q(q) }])).p;
  const s1 = (b - s) / 2n, s2 = (b + s) / 2n; // s1 + s2 = b, s1 s2 = ac
  const f1 = mk(a, s1), f2 = mk(a, s2);
  const ut = monoTree(vars, U), wt = monoTree(vars, W);
  const orig = txt(C.toTree(m));
  if (D === 0n) {
    return { rule: "factor.perfect-square", title: "Perfect square trinomial", parts: [f1, f2],
      why: `${orig} has the form A^2 + 2AB + B^2 (discriminant b^2 - 4ac = 0), so it is a square.` };
  }
  if (a === 1n) {
    return { rule: "factor.trinomial", title: "Factor the trinomial", parts: [f1, f2],
      why: `Find two numbers whose product is ${c} and whose sum is ${b}: ${s1} and ${s2}. So ${orig} = (${txt(ut)} + ${s1}${X.isOne(wt) ? "" : "*" + txt(wt)})(${txt(ut)} + ${s2}${X.isOne(wt) ? "" : "*" + txt(wt)}).`.replace(/\+ -/g, "- ") };
  }
  return { rule: "factor.trinomial-ac", title: "Factor by the ac-method", parts: [f1, f2],
    why: `a*c = ${a * c}; the numbers ${s1} and ${s2} multiply to ${a * c} and add to ${b}. Split the middle term and group the pairs.` };
}
function tryGrouping(m) {
  const ts = termsOf(m);
  if (ts.length !== 4) return null;
  const vars = m.vars;
  const sorted = lexDesc(ts);
  const pairings = [[[0, 1], [2, 3]], [[0, 2], [1, 3]], [[0, 3], [1, 2]]];
  for (const [g1, g2] of pairings) {
    const P1 = fromTerms(vars, g1.map((i) => sorted[i])), P2 = fromTerms(vars, g2.map((i) => sorted[i]));
    const split = (P) => {
      const mc = monomialContent(P);
      const { unit, p } = C.mNormalize(divMonomial(P, mc));
      return { g: C.mpoly(vars, [[mc, unit]]), r: p };
    };
    const A = split(P1), B = split(P2);
    if (C.mEq(A.r, B.r) && C.mUsedVars(A.r).length) {
      const other = C.mAdd(A.g, B.g);
      if (!C.mUsedVars(other).length) continue;
      return { rule: "factor.grouping", title: "Factor by grouping", parts: [C.mNormalize(other).p, A.r],
        why: `Group as (${txt(C.toTree(P1))}) + (${txt(C.toTree(P2))}) = ${txt(C.toTree(A.g))}(${txt(C.toTree(A.r))}) + ${txt(C.toTree(B.g))}(${txt(C.toTree(B.r))}); both groups share the factor ${txt(C.toTree(A.r))}.`.replace(/\+ -/g, "- ") };
    }
  }
  return null;
}
function tryRationalRoot(m) {
  const used = C.mUsedVars(m);
  if (used.length !== 1) return null;
  const x = used[0];
  const u = C.mToU(m, x);
  if (u.length - 1 < 2) return null;
  const roots = C.rationalRoots(u);
  if (!roots.length) return null;
  const r = roots[0];
  const lin = [N.Q(-r.n), N.Q(r.d)]; // d x - n
  const { q, rem } = C.syntheticDivide(u, r);
  if (rem.n !== 0n) return null;
  const vars = m.vars;
  return { rule: "factor.rational-root", title: "Rational root and synthetic division", parts: [C.mFromU(lin, vars, x), C.mFromU(C.scale(q, N.inv(N.Q(r.d))), vars, x)],
    why: `By the rational root theorem the candidates are ±p/q with p | ${C.toZ(u).z[0]} and q | ${C.toZ(u).z[u.length - 1]}. Substituting ${x} = ${N.toString(r)} gives 0, so (${txt(C.toTree(C.mFromU(lin, vars, x)))}) is a factor; synthetic division gives the quotient.` };
}

// Factor with an explanation. Returns { result: tree, steps: [StepRecord], complete }.
export function factorSteps(node, opts) {
  return guard(opts, () => {
    const u = canon(node);
    const steps = [];
    const final = factorTree(u);
    let pr = null;
    try { pr = prepare(u); } catch (e) { if (e.code !== "NOTPOLY") throw e; }
    if (!pr || C.mIsZero(pr.m)) return { result: final, steps, complete: true };
    const vars = pr.m.vars;
    let unit = Q1;
    let items = [];
    const treeNow = () => assemble(unit, items.map((it) => ({ poly: it.poly, mult: it.mult })), pr.back);
    const record = (rule, title, why, before) => {
      const after = treeNow();
      if (after !== before) steps.push({ rule, title, why, before, after, conditions: [], kind: "equivalent" });
    };
    // start from the expanded form
    const expanded = pr.back.size ? canon(X.subs(C.toTree(pr.m), pr.back)) : C.toTree(pr.m);
    if (expanded !== u) steps.push({ rule: "factor.expand", title: "Expand", why: "Multiply out so that every term is visible.", before: u, after: expanded, conditions: [], kind: "equivalent" });
    const before0 = expanded;
    const { unit: cu, p: prim } = C.mNormalize(pr.m);
    unit = cu;
    const mc = monomialContent(prim);
    mc.forEach((e, i) => { if (e) items.push({ poly: C.mVar(vars, vars[i]), mult: e, done: true }); });
    const rest = divMonomial(prim, mc);
    if (C.mUsedVars(rest).length) items.push({ poly: rest, mult: 1, done: false });
    else unit = N.mul(unit, [...rest.terms.values()][0] || Q1);
    const gcfTree = canon(X.mul(X.num(cu), monoTree(vars, mc)));
    const k0 = pr.back.size ? canon(X.subs(gcfTree, pr.back)) : gcfTree;
    if (!N.isOne(cu) || mc.some((e) => e)) record("factor.common", N.eq(cu, N.NEG_ONE) && mc.every((e) => !e) ? "Factor out -1" : "Factor out the greatest common factor",
      `Every term is divisible by ${txt(k0)}.`, before0);
    for (let guardN = 0; guardN < 200; guardN++) {
      tick();
      const i = items.findIndex((it) => !it.done);
      if (i < 0) break;
      const it = items[i];
      const m = it.poly;
      const before = treeNow();
      let r = tryBinomial(m) || tryTrinomial(m) || tryGrouping(m);
      if (!r) {
        // repeated factors
        const used = C.mUsedVars(m);
        if (used.length === 1) {
          const uq = C.mToU(m, used[0]);
          const sf = C.squareFree(uq);
          if (sf.factors.length > 1 || (sf.factors.length === 1 && sf.factors[0].mult > 1)) {
            unit = N.mul(unit, N.pow(sf.unit, it.mult));
            items.splice(i, 1, ...sf.factors.map((f) => ({ poly: C.mFromU(f.poly, vars, used[0]), mult: f.mult * it.mult, done: false })));
            record("factor.square-free", "Separate repeated factors", "gcd(p, p') is not constant, so p has repeated factors; Yun's algorithm splits p into square-free parts.", before);
            continue;
          }
          r = tryRationalRoot(m);
          if (!r) {
            const fq = factorQ(uq);
            if (fq.factors.length > 1 || (fq.factors[0] && fq.factors[0].mult > 1)) {
              unit = N.mul(unit, N.pow(fq.unit, it.mult));
              items.splice(i, 1, ...fq.factors.map((f) => ({ poly: C.mFromU(f.poly, vars, used[0]), mult: f.mult * it.mult, done: true })));
              record("factor.zassenhaus", "Factor over the rationals (Zassenhaus)", "No rational roots remain; factoring modulo a prime, Hensel lifting and recombining the lifted factors gives the irreducible factors over Q.", before);
              continue;
            }
            it.done = true;
            continue;
          }
        } else {
          const mf = mFactor(m);
          if (mf.factors.length > 1 || (mf.factors[0] && mf.factors[0].mult > 1)) {
            unit = N.mul(unit, N.pow(mf.unit, it.mult));
            items.splice(i, 1, ...mf.factors.map((f) => ({ poly: f.poly, mult: f.mult * it.mult, done: true })));
            record("factor.kronecker", "Factor the multivariate polynomial", "Separate the content and repeated factors, then use Kronecker's substitution with exact trial division to find the irreducible factors.", before);
            continue;
          }
          it.done = true;
          continue;
        }
      }
      // apply pattern result: normalise parts
      const newItems = [];
      let prod = C.mConst(vars, Q1);
      for (const part of r.parts) {
        const { unit: pu, p } = C.mNormalize(part);
        unit = N.mul(unit, N.pow(pu, it.mult));
        prod = C.mMul(prod, part);
        const used = C.mUsedVars(p).length;
        if (used) newItems.push({ poly: p, mult: it.mult, done: false });
      }
      if (!C.mEq(prod, m)) throw new Error("Quelvra: internal error (factor step " + r.rule + ")");
      items.splice(i, 1, ...newItems);
      record(r.rule, r.title, r.why, before);
    }
    const now = treeNow();
    if (now !== final) {
      steps.push({ rule: "factor.complete", title: "Finish the factorisation", why: "Combine repeated factors and factor any remaining parts over Q.", before: now, after: final, conditions: [], kind: "equivalent" });
    }
    return { result: final, steps, complete: true };
  });
}
