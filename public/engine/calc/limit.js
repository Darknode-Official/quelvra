// Quelvra limits.
//
//   limit(expr, x, to, dir)        -> { value: tree | null, status: "exact" | "dne" | "unknown", reason,
//                                       method, result, steps }
//   limitDetailed(expr, x, to, dir, {log}) -> internal result { k: "fin"|"inf"|"dne"|"undef", ... }
//   verifyLimit(expr, x, to, dir, result) -> verifier result (verified-numeric | failed | inconclusive)
//
// Layers (each proves its answer; none guesses):
//   1. continuity: direct substitution where every sub-expression is continuous at the point
//   2. series: expansion in t -> 0+ with x = a +- t (or x = 1/t at infinity), leading term c t^e;
//      handles cancellation, rationalisation, standard limits, Puiseux terms and ln-factors
//   3. Gruntz: most-rapidly-varying subexpressions, rewrite in omega, leading term, recursion
//   4. oscillation: squeeze (bounded trig factors times vanishing coefficients) or two sequences
//      along which the function tends to different values (proof that the limit does not exist)
//   5. L'Hopital for quotients (bounded depth) when the expansion methods do not apply
// One-sided limits are computed separately; a two-sided limit exists only when both agree.

import { X, N, simp, tidy, simpExpand, qerr, Budget, isZeroStrong, constSign, hp, log10Abs, bigSign, NEG_OO, isNegInf, now } from "./cutil.js";
import { leading, LSYM } from "./series.js";
import { diff } from "./diff.js";
import { evalC } from "../verify.js";
import { coefficients } from "../poly.js";
import * as B from "../bigfloat.js";

const T = X.sym("__t");
const W = X.sym("__w");
const NOLOG = { add() {}, group(h, f) { return f(null); } };

// ---------------------------------------------------------------- preparation
const HYP = {
  sinh: (u) => X.mul(X.HALF, X.add(X.exp(u), X.neg(X.exp(X.neg(u))))),
  cosh: (u) => X.mul(X.HALF, X.add(X.exp(u), X.exp(X.neg(u)))),
  tanh: (u) => X.mul(X.add(X.exp(u), X.neg(X.exp(X.neg(u)))), X.pow(X.add(X.exp(u), X.exp(X.neg(u))), X.NEG_ONE)),
  coth: (u) => X.mul(X.add(X.exp(u), X.exp(X.neg(u))), X.pow(X.add(X.exp(u), X.neg(X.exp(X.neg(u)))), X.NEG_ONE)),
  sech: (u) => X.mul(X.TWO, X.pow(X.add(X.exp(u), X.exp(X.neg(u))), X.NEG_ONE)),
  csch: (u) => X.mul(X.TWO, X.pow(X.add(X.exp(u), X.neg(X.exp(X.neg(u)))), X.NEG_ONE)),
};
// Rewrite into the forms the series / Gruntz machinery understands (x-dependent exponents become
// exp(v ln b), hyperbolic functions become exponentials, log_b becomes ln / ln b).
function gprep(u, x) {
  const r = X.mapTree(u, (w) => {
    if (w.k === "pow" && w.args[0] !== X.E && X.hasSym(w.args[1], x.name) && X.hasSym(w.args[0], x.name))
      return X.pow(X.E, X.mul(w.args[1], X.fn("ln", w.args[0])));
    if (w.k === "pow" && w.args[0] !== X.E && X.hasSym(w.args[1], x.name))
      return X.pow(X.E, X.mul(w.args[1], X.fn("ln", w.args[0])));
    if (w.k === "fn") {
      if (HYP[w.name] && X.hasSym(w, x.name)) return HYP[w.name](w.args[0]);
      if (w.name === "log") return w.args.length === 2 ? X.mul(X.fn("ln", w.args[1]), X.pow(X.fn("ln", w.args[0]), X.NEG_ONE)) : X.mul(X.fn("ln", w.args[0]), X.pow(X.fn("ln", X.num(10)), X.NEG_ONE));
      if (w.name === "exp") return X.pow(X.E, w.args[0]);
      if (w.name === "sec") return X.pow(X.fn("cos", w.args[0]), X.NEG_ONE);
      if (w.name === "csc") return X.pow(X.fn("sin", w.args[0]), X.NEG_ONE);
      if (w.name === "cot") return X.mul(X.fn("cos", w.args[0]), X.pow(X.fn("sin", w.args[0]), X.NEG_ONE));
      if (w.name === "sqrt") return X.pow(w.args[0], X.HALF);
    }
    return w;
  });
  return simp(r);
}
const isInfTree = (u) => u === X.OO || isNegInf(u);

// ---------------------------------------------------------------- results
const FIN = (v) => ({ k: "fin", v });
const INF = (s) => ({ k: "inf", s });
export function resultTree(r) {
  if (r.k === "fin") return r.v;
  if (r.k === "inf") return r.s > 0 ? X.OO : NEG_OO;
  return null;
}
function showR(r, toText) {
  if (r.k === "fin") return toText(r.v);
  if (r.k === "inf") return r.s > 0 ? "oo" : "-oo";
  if (r.k === "undef") return "undefined";
  return "does not exist";
}
function sameResult(a, b) {
  if (a.k !== b.k) return false;
  if (a.k === "inf") return a.s === b.s;
  if (a.k === "fin") {
    if (a.v === b.v) return true;
    try { return isZeroStrong(simp(X.sub(a.v, b.v))); } catch (_) { return false; }
  }
  return false;
}

// ---------------------------------------------------------------- continuity
function dval(u, x, a) {
  const v = evalC(u, { [x.name]: a }, "real");
  return v;
}
// Returns the value tree when u is provably continuous at x = a (a finite), else null.
function contAt(u, x, a) {
  if (X.contains(u, X.OO)) return null;
  const v = simp(X.subs(u, { [x.name]: a }));
  if (v === X.UNDEF || X.contains(v, X.OO) || X.contains(v, X.I)) return null;
  const av = evalC(a, {}, "real");
  if (!Number.isFinite(av.re) || av.im) return null;
  const at = (w) => dval(w, x, av.re);
  const far = (z, lim = 1e-9) => Number.isFinite(z.re) && Math.abs(z.im) < 1e-12 && Math.abs(z.re) > lim;
  let ok = true;
  const walk = (w) => {
    if (!ok || !X.hasSym(w, x.name)) return;
    switch (w.k) {
      case "sym": case "add": case "mul": break;
      case "pow": {
        const [b, e] = w.args;
        const bv = at(b);
        if (!Number.isFinite(bv.re) || Math.abs(bv.im) > 1e-12) { ok = false; break; }
        if (X.hasSym(e, x.name) || !X.isNum(e)) { if (b !== X.E && !(bv.re > 1e-9)) ok = false; break; }
        const q = e.v;
        if (q.d === 1n) { if (q.n < 0n && !far(bv)) ok = false; }
        else if (q.d % 2n === 0n) { if (!(bv.re > 1e-9)) ok = false; }
        else if (q.n < 0n && !far(bv)) ok = false;
        break;
      }
      case "fn": {
        const n = w.name, z = at(w.args[w.args.length - 1]);
        if (!Number.isFinite(z.re) || Math.abs(z.im) > 1e-12) { ok = false; break; }
        const y = z.re;
        if (n === "ln" || n === "log") { if (!(y > 1e-9)) ok = false; if (n === "log" && w.args.length === 2) { const b = at(w.args[0]); if (!(b.re > 1e-9) || Math.abs(b.re - 1) < 1e-9) ok = false; } }
        else if (["sin", "cos", "exp", "atan", "sinh", "cosh", "tanh", "asinh", "abs", "erf", "acot"].includes(n)) { /* continuous everywhere */ }
        else if (n === "tan" || n === "sec") { if (!(Math.abs(Math.cos(y)) > 1e-9)) ok = false; }
        else if (n === "cot" || n === "csc") { if (!(Math.abs(Math.sin(y)) > 1e-9)) ok = false; }
        else if (n === "asin" || n === "acos") { if (!(Math.abs(y) < 1 - 1e-9)) ok = false; }
        else if (n === "acosh") { if (!(y > 1 + 1e-9)) ok = false; }
        else if (n === "atanh") { if (!(Math.abs(y) < 1 - 1e-9)) ok = false; }
        else if (n === "sqrt") { if (!(y > 1e-9)) ok = false; }
        else if (n === "floor" || n === "ceil" || n === "sign" || n === "round") {
          const s = simp(X.subs(w.args[0], { [x.name]: a }));
          if (!(X.isNum(s) && s.v.d !== 1n) && !(n === "sign" && Math.abs(y) > 1e-9)) ok = false;
        } else if (n === "gamma" || n === "factorial") { const yy = n === "gamma" ? y : y + 1; if (!(yy > 1e-9 || Math.abs(yy - Math.round(yy)) > 1e-9)) ok = false; }
        else ok = false;
        break;
      }
      default: ok = false;
    }
    if (ok) w.args.forEach(walk);
  };
  walk(u);
  return ok ? v : null;
}

// ---------------------------------------------------------------- Gruntz
class Gruntz {
  constructor(x, log) {
    this.x = x;
    this.log = log || NOLOG;
    this.limMemo = new Map();
    this.mrvMemo = new Map();
    this.depth = 0;
  }
  guard() {
    Budget.check();
    if (this.depth > 60) throw qerr("BUDGET", "limit recursion too deep");
  }
  lim(e) {
    // limit as x -> +oo: { k: "fin", v } | { k: "inf", s }
    const x = this.x;
    if (!X.hasSym(e, x.name)) {
      if (e === X.UNDEF) throw qerr("UNDEFINED", "undefined");
      return FIN(e);
    }
    if (e === x) return INF(1);
    const hit = this.limMemo.get(e);
    if (hit) return hit;
    this.guard();
    this.depth++;
    try {
      const ep = gprep(e, x);
      const { c, e0 } = this.leadterm(ep);
      if (X.contains(c, X.I)) throw qerr("UNDEFINED", "the function is not real near the point");
      let r;
      if (e0 === null) r = FIN(X.ZERO);
      else if (N.cmp(e0, N.ZERO) > 0) r = FIN(X.ZERO);
      else if (N.cmp(e0, N.ZERO) < 0) r = INF(this.sign(c));
      else r = this.lim(c);
      if (r.k === "fin") r = FIN(simp(r.v));
      if (r.k === "fin" && (X.contains(r.v, X.I) || r.v === X.UNDEF)) throw qerr("UNDEFINED", "the function is not real near the point");
      this.limMemo.set(e, r);
      return r;
    } finally { this.depth--; }
  }
  sign(e) {
    const x = this.x;
    if (!X.hasSym(e, x.name)) {
      const s = constSign(e);
      if (s === 0) throw qerr("INTERNAL", "zero leading coefficient");
      return s;
    }
    if (e === x) return 1;
    this.guard();
    if (e.k === "pow") {
      const [b, p] = e.args;
      if (b === X.E) return 1;
      if (X.isNum(p)) {
        const q = p.v;
        if (q.d % 2n === 0n) return 1;
        if (q.n % 2n === 0n) return 1;
        return this.sign(b);
      }
      return 1;
    }
    if (e.k === "mul") return e.args.reduce((s, f) => s * this.sign(f), 1);
    if (e.k === "fn" && e.name === "abs") return 1;
    this.depth++;
    try {
      const { c, e0 } = this.leadterm(gprep(e, x));
      if (e0 === null) throw qerr("INTERNAL", "sign of zero");
      return this.sign(c);
    } finally { this.depth--; }
  }
  mrv(e) {
    const x = this.x;
    if (!X.hasSym(e, x.name)) return [];
    if (e === x) return [x];
    const hit = this.mrvMemo.get(e);
    if (hit) return hit;
    this.guard();
    let r;
    switch (e.k) {
      case "add": case "mul": {
        r = [];
        for (const a of e.args) r = this.mrvMax(r, this.mrv(a));
        break;
      }
      case "pow": {
        const [b, p] = e.args;
        if (b === X.E) {
          const L = this.lim(p);
          r = L.k === "inf" ? this.mrvMax([e], this.mrv(p)) : this.mrv(p);
        } else if (!X.hasSym(p, x.name)) r = this.mrv(b);
        else throw qerr("INTERNAL", "unprepared power");
        break;
      }
      case "fn": {
        r = [];
        for (const a of e.args) r = this.mrvMax(r, this.mrv(a));
        break;
      }
      default: throw qerr("UNSUPPORTED", `limits of ${e.k} nodes are not supported`);
    }
    this.mrvMemo.set(e, r);
    return r;
  }
  mrvMax(A, B2) {
    if (!A.length) return B2;
    if (!B2.length) return A;
    if (A.some((a) => B2.includes(a))) return [...new Set([...A, ...B2])];
    // an exponential whose exponent tends to +-oo varies at least as fast as x (exp of logs are
    // simplified away before this point), so x never joins a set of exponentials
    if (B2.includes(this.x)) return A;
    if (A.includes(this.x)) return B2;
    const c = this.compare(A[0], B2[0]);
    if (c > 0) return A;
    if (c < 0) return B2;
    return [...new Set([...A, ...B2])];
  }
  compare(a, b) {
    const x = this.x;
    const la = a === x ? X.fn("ln", x) : a.args[1];
    const lb = b === x ? X.fn("ln", x) : b.args[1];
    const c = this.lim(simp(X.mul(la, X.pow(lb, X.NEG_ONE))));
    if (c.k === "inf") return 1;
    if (c.v === X.ZERO) return -1;
    return 0;
  }
  leadterm(e) {
    // leading term of e in the most rapidly varying scale: { c (tree in x), e0 (Rational | null) }
    const x = this.x;
    let cur = e;
    for (let up = 0; up < 8; up++) {
      this.guard();
      const Om = this.mrv(cur);
      if (!Om.length) return { c: cur, e0: N.ZERO };
      if (Om.includes(x)) {
        // move up: x -> e^x (the limit at infinity is unchanged)
        cur = gprep(simp(X.subs(cur, { [x.name]: X.exp(x) })), x);
        continue;
      }
      return this.rewriteLead(cur, Om);
    }
    throw qerr("BUDGET", "too many move-up steps");
  }
  rewriteLead(e, Om) {
    const x = this.x;
    const sorted = Om.slice().sort((a, b) => X.size(a) - X.size(b));
    const g = sorted[0];
    const h = g.args[1];
    const Lh = this.lim(h);
    if (Lh.k !== "inf") throw qerr("INTERNAL", "mrv element without infinite exponent");
    const logw = Lh.s < 0 ? h : simp(X.neg(h));
    const map = new Map();
    const rep = (u) => (map.has(u) ? map.get(u) : u.args.length ? X.withArgs(u, u.args.map(rep)) : u);
    for (const f of sorted) {
      const s = f.args[1];
      const cl = this.lim(simp(X.mul(s, X.pow(logw, X.NEG_ONE))));
      if (cl.k !== "fin" || !X.isNum(cl.v) || X.isZero(cl.v)) throw qerr("UNSUPPORTED", "non-rational comparability exponent");
      const s2 = rep(s);
      const A = simp(X.pow(X.E, simpExpand(X.sub(s2, X.mul(cl.v, logw)))));
      map.set(f, simp(X.mul(A, X.pow(W, cl.v))));
    }
    const e2 = simp(rep(e));
    if (X.hasSym(e2, x.name) && Om.some((f) => X.contains(e2, f))) throw qerr("INTERNAL", "rewrite incomplete");
    const special = { [x.name]: [9.3, 14.7, 23.1, 37.9], [LSYM.name]: null };
    const subsL = (c) => simp(X.subs(c, { [LSYM.name]: logw }));
    const zeroSpecial = { [x.name]: special[x.name] };
    const opts = {
      special: zeroSpecial,
      zeroFn: (c) => zeroTestX(subsL(c), x, special[x.name]),
      signFn: (c) => this.sign(subsL(c)),
      Lval: logw,
    };
    const L = leadingG(e2, opts);
    if (L.zero) return { c: X.ZERO, e0: null };
    return { c: subsL(L.c), e0: L.e };
  }
}
// Zero test for coefficients that depend on x (large). Products of manifestly nonzero factors are
// nonzero; otherwise the value is compared with the size of its addends (relative cancellation).
function nonzeroStruct(c, xn) {
  if (X.isNum(c)) return !X.isZero(c);
  if (c.k === "sym") return c.name === xn;
  if (c.k === "const") return c === X.PI || c === X.E;
  if (c.k === "pow") return c.args[0] === X.E ? !X.contains(c.args[1], X.UNDEF) : nonzeroStruct(c.args[0], xn);
  if (c.k === "mul") return c.args.every((a) => nonzeroStruct(a, xn));
  if (c.k === "fn" && c.name === "ln") return c.args[0].k === "sym" && c.args[0].name === xn;
  return false;
}
function zeroTestX(c, x, xs) {
  const s = simp(c);
  if (s === X.ZERO) return true;
  if (!X.hasSym(s, x.name) && !X.freeSymbols(s).size) return isZeroStrong(s);
  if (nonzeroStruct(s, x.name)) return false;
  const e = X.size(s) < 300 ? simpExpand(s) : s;
  if (e === X.ZERO) return true;
  if (nonzeroStruct(e, x.name)) return false;
  const addends = e.k === "add" ? e.args : [e];
  let zeros = 0, tried = 0;
  for (const xv of xs) {
    const env = { ...Object.fromEntries([...X.freeSymbols(e)].map((n, i) => [n, 0.7310585786 + 0.3 * i])), [x.name]: xv };
    const v = hp(e, env, { digits: 50, maxDigits: 200 });
    if (!v.ok) continue;
    let scale = -Infinity;
    for (const a of addends) { const w = hp(a, env, { digits: 30, maxDigits: 60 }); if (w.ok) scale = Math.max(scale, log10Abs(w.big), w.bigIm ? log10Abs(w.bigIm) : -Infinity); }
    if (scale === -Infinity) continue;
    tried++;
    const mag = Math.max(log10Abs(v.big), v.bigIm ? log10Abs(v.bigIm) : -Infinity);
    if (mag - scale > -20) return false;
    if (mag - scale < -35) zeros++;
  }
  if (tried >= 2 && zeros === tried) return true;
  throw qerr("UNDECIDABLE", "cannot decide whether a coefficient is zero");
}
// leading() with a custom zero test (coefficients depend on x; __L means ln(omega))
function leadingG(u, opts) {
  return leading(u, W, { special: { ...opts.special, [LSYM.name]: [-9.3, -14.7, -23.1, -37.9] }, signFn: opts.signFn, zeroFn: opts.zeroFn, Lval: opts.Lval });
}

// ---------------------------------------------------------------- Stirling (multiplicative factors only)
// n! = sqrt(2 pi n) (n/e)^n (1 + o(1)). Replacing a factor f by f~ with f/f~ -> 1 does not change the
// limit of a product, so only factorial / gamma factors of the top-level product are replaced.
function stirling(u, x, G) {
  const fs = u.k === "mul" ? u.args : [u];
  let changed = false;
  const out = fs.map((f) => {
    const [b, e] = f.k === "pow" && !X.hasSym(f.args[1], x.name) ? f.args : [f, X.ONE];
    if (b.k === "fn" && (b.name === "factorial" || b.name === "gamma") && X.hasSym(b, x.name)) {
      const a = b.args[0];
      let L;
      try { L = G.lim(a); } catch (_) { return f; }
      if (L.k !== "inf" || L.s < 0) return f;
      changed = true;
      const n = b.name === "factorial" ? a : a;
      const base = b.name === "factorial"
        ? X.mul(X.pow(X.mul(X.TWO, X.PI, n), X.HALF), X.pow(n, n), X.exp(X.neg(n)))
        : X.mul(X.pow(X.mul(X.TWO, X.PI, X.pow(n, X.NEG_ONE)), X.HALF), X.pow(n, n), X.exp(X.neg(n)));
      return X.pow(base, e);
    }
    return f;
  });
  return changed ? simp(X.mul(...out)) : null;
}

// ---------------------------------------------------------------- series layer
function seriesSide(w, info) {
  // w: tree in T (t -> 0+). Returns a result or throws.
  const L = leading(w, T);
  if (L.zero) return FIN(X.ZERO);
  const { c, e } = L;
  if (X.contains(c, X.I)) throw qerr("UNDEFINED", "the function is not real near the point");
  if (X.hasSym(c, LSYM.name)) {
    const cs = coefficients(c, LSYM.name);
    if (!cs || cs.some((k) => X.freeSymbols(k).has(LSYM.name))) throw qerr("UNSUPPORTED", "non-polynomial logarithmic coefficient");
    const d = cs.length - 1;
    if (N.cmp(e, N.ZERO) > 0) return FIN(X.ZERO);
    const lc = cs[d];
    const s = constSignP(lc) * (d % 2 ? -1 : 1);
    if (N.cmp(e, N.ZERO) < 0 || d > 0) return INF(s);
    return FIN(simp(cs[0]));
  }
  if (N.cmp(e, N.ZERO) > 0) return FIN(X.ZERO);
  if (N.isZero(e)) { info.leading = { c, e }; return FIN(c); }
  info.leading = { c, e };
  return INF(constSignP(c));
}
function constSignP(c) {
  // sign of a (possibly parameter-dependent) coefficient; parameters make it undecidable
  return constSign(c);
}

// ---------------------------------------------------------------- oscillation
const OSC_FNS = new Set(["sin", "cos"]);
function oscillation(u, x, where, ctx) {
  // where: { inf: true } (x -> +oo) or { a, s }
  const cand = new Map();
  const walk = (w) => {
    if (!X.hasSym(w, x.name)) return;
    if (w.k === "fn" && OSC_FNS.has(w.name) && !cand.has(w.args[0])) cand.set(w.args[0], null);
    w.args.forEach(walk);
  };
  walk(u);
  const osc = [];
  for (const arg of cand.keys()) {
    let r;
    try { r = limWhere(arg, x, where, ctx); } catch (_) { continue; }
    if (r.k === "inf") osc.push(arg);
  }
  if (osc.length !== 1) return null;
  const arg = osc[0];
  const S = X.sym("__s"), C = X.sym("__c");
  const F = simp(X.replace(X.replace(u, X.fn("sin", arg), S), X.fn("cos", arg), C));
  // (a) squeeze: F = B + sum A_m S^i C^j with every A_m -> 0
  try {
    const cs = coefficients(F, "__s");
    if (cs) {
      const mons = [];
      let Bpart = null;
      cs.forEach((ci, i) => {
        const cc = coefficients(ci, "__c");
        if (!cc) throw qerr("NOPOLY", "");
        cc.forEach((cij, j) => { if (cij === X.ZERO) return; if (i === 0 && j === 0) Bpart = cij; else mons.push(cij); });
      });
      if (mons.length) {
        const allZero = mons.every((A) => { const r = limWhere(A, x, where, ctx); return r.k === "fin" && r.v === X.ZERO; });
        if (allZero) {
          const rb = Bpart ? limWhere(Bpart, x, where, ctx) : FIN(X.ZERO);
          if (rb.k === "fin" || rb.k === "inf") return { ...rb, method: "squeeze", osc: { arg } };
        }
      }
    }
  } catch (e) { if (e.code === "TIMEOUT") throw e; }
  // (b) sequences with arg = theta + 2 pi n
  const thetas = [[X.ZERO, "0"], [X.mul(X.HALF, X.PI), "pi/2"], [X.PI, "pi"], [X.mul(X.num(3, 2), X.PI), "3pi/2"]];
  const got = [];
  for (const [th, label] of thetas) {
    const Ft = simp(X.subs(F, { __s: simp(X.fn("sin", th)), __c: simp(X.fn("cos", th)) }));
    let r;
    try { r = limWhere(Ft, x, where, ctx); } catch (e) { if (e.code === "TIMEOUT") throw e; continue; }
    if (r.k !== "fin" && r.k !== "inf") continue;
    for (const [r2, l2] of got) {
      if (!sameResult(r, r2)) {
        return { k: "dne", method: "oscillation", osc: { arg, values: [[l2, r2], [label, r]] }, reason: null };
      }
    }
    got.push([r, label]);
  }
  return null;
}

// ---------------------------------------------------------------- L'Hopital (quotients, bounded)
function lhopital(u, x, where, ctx, depth = 0) {
  if (depth > 3 || u.k !== "mul") return null;
  const num = [], den = [];
  for (const f of u.args) {
    if (f.k === "pow" && X.isNum(f.args[1]) && N.isNeg(f.args[1].v)) den.push(X.pow(f.args[0], X.num(N.neg(f.args[1].v))));
    else num.push(f);
  }
  if (!den.length) return null;
  const f = simp(X.mul(...num)), g = simp(X.mul(...den));
  const rf = limWhere(f, x, where, ctx), rg = limWhere(g, x, where, ctx);
  const zz = rf.k === "fin" && rf.v === X.ZERO && rg.k === "fin" && rg.v === X.ZERO;
  const ii = rf.k === "inf" && rg.k === "inf";
  if (!zz && !ii) return null;
  const q = simp(X.mul(diff(f, x), X.pow(diff(g, x), X.NEG_ONE)));
  const r = limWhere(q, x, where, ctx, depth + 1);
  if (r.k === "fin" || r.k === "inf") return { ...r, method: "lhopital" };
  return null;
}

// ---------------------------------------------------------------- one side / infinity
function limWhere(u, x, where, ctx, lhDepth = 0) {
  ctx.depth = (ctx.depth || 0) + 1;
  if (ctx.depth > 25) { ctx.depth--; throw qerr("BUDGET", "limit recursion too deep"); }
  try {
    return where.inf ? limInf(u, x, ctx, lhDepth) : limSide(u, x, where.a, where.s, ctx, lhDepth);
  } finally { ctx.depth--; }
}
const SOFT = new Set(["OSCILLATES", "DIVERGENT", "UNSUPPORTED", "UNDECIDABLE", "NEEDMORE", "SINGULAR", "INTERNAL", "COMPLEX", "BUDGET", "NOPOLY"]);
function soft(e) { if (!e || !e.code || !SOFT.has(e.code)) throw e; return e; }

function limSide(u, x, a, s, ctx, lhDepth = 0) {
  Budget.check();
  u = simp(u);
  if (!X.hasSym(u, x.name)) return FIN(u);
  const v = contAt(u, x, a);
  if (v) return { ...FIN(v), method: "continuity" };
  const errs = [];
  let undef = null;
  // series in t
  try {
    const w = simp(X.subs(u, { [x.name]: s > 0 ? X.add(a, T) : X.sub(a, T) }));
    const info = {};
    const r = seriesSide(gprepSeries(w), info);
    return { ...r, method: "series", info };
  } catch (e) { if (e.code === "UNDEFINED") undef = e; else errs.push(soft(e)); }
  // Gruntz at infinity with x = a +- 1/x
  if (!undef) try {
    const w = simp(X.subs(u, { [x.name]: s > 0 ? X.add(a, X.pow(x, X.NEG_ONE)) : X.sub(a, X.pow(x, X.NEG_ONE)) }));
    const G = new Gruntz(x, ctx.log);
    const r = G.lim(w);
    return { ...r, method: "gruntz" };
  } catch (e) { if (e.code === "UNDEFINED") undef = undef || e; else errs.push(soft(e)); }
  if (undef && definedNear(u, x, { a, s }) === false) return { k: "undef", reason: "not defined (as a real number) on this side of the point", method: "domain" };
  const o = oscillation(u, x, { a, s }, ctx);
  if (o) return o;
  const l = lhopital(u, x, { a, s }, ctx, lhDepth);
  if (l) return l;
  throw qerr("UNKNOWN", reasonOf(errs, undef));
}
function limInf(u, x, ctx, lhDepth = 0) {
  Budget.check();
  u = simp(u);
  if (!X.hasSym(u, x.name)) return FIN(u);
  const errs = [];
  let undef = null;
  const G = new Gruntz(x, ctx.log);
  let work = u;
  try {
    const st = stirling(gprep(u, x), x, G);
    if (st) { work = st; ctx.notes && ctx.notes.push("stirling"); }
  } catch (e) { soft(e); }
  try {
    const w = simp(X.subs(work, { [x.name]: X.pow(T, X.NEG_ONE) }));
    const info = {};
    const r = seriesSide(gprepSeries(w), info);
    return { ...r, method: "series", info };
  } catch (e) { if (e.code === "UNDEFINED") undef = e; else errs.push(soft(e)); }
  if (!undef) try {
    const r = G.lim(work);
    return { ...r, method: "gruntz" };
  } catch (e) { if (e.code === "UNDEFINED") undef = undef || e; else errs.push(soft(e)); }
  if (undef && definedNear(u, x, { inf: true }) === false) return { k: "undef", reason: "not defined (as a real number) for large x", method: "domain" };
  const o = oscillation(u, x, { inf: true }, ctx);
  if (o) return o;
  const l = lhopital(u, x, { inf: true }, ctx, lhDepth);
  if (l) return l;
  throw qerr("UNKNOWN", reasonOf(errs, undef));
}
function gprepSeries(w) { return gprep(w, T); }
function reasonOf(errs, undef) {
  if (undef) return "the function is not defined as a real number near the point";
  const m = errs.find((e) => e.code === "OSCILLATES" || e.code === "DIVERGENT") || errs[0];
  return m ? m.message : "no method applies";
}
// Is u undefined (not real) at every sample point near the side? false = undefined everywhere sampled.
function definedNear(u, x, where) {
  let defined = 0, tried = 0;
  const hs = [1e-3, 3e-4, 1e-4, 1e-5, 1e-6, 1e-8];
  for (const h of hs) {
    let xv;
    if (where.inf) xv = 1 / h;
    else { const av = evalC(where.a, paramEnv(where.a, x.name), "real").re; xv = av + where.s * h; }
    const v = evalC(u, { ...paramEnv(u, x.name), [x.name]: xv }, "real");
    tried++;
    if (Number.isFinite(v.re) && Math.abs(v.im) < 1e-12 * Math.max(1, Math.abs(v.re))) defined++;
  }
  return defined > 0;
}

// ---------------------------------------------------------------- public entry
export function limitDetailed(expr, x, to, dir = "", opts = {}) {
  const xs = typeof x === "string" ? X.sym(x) : x;
  const log = opts.log || NOLOG;
  const ctx = { log, depth: 0, notes: [] };
  const run = () => {
    const u = simp(expr);
    const target = simp(to);
    if (target === X.OO) return withNotes(limWhere(u, xs, { inf: true }, ctx), ctx);
    if (isNegInf(target)) return withNotes(limWhere(simp(X.subs(u, { [xs.name]: X.neg(xs) })), xs, { inf: true }, ctx), ctx);
    if (X.hasSym(target, xs.name) || X.contains(target, X.OO)) throw qerr("UNSUPPORTED", "unsupported limit point");
    if (dir === "+" || dir === "-") return withNotes(limWhere(u, xs, { a: target, s: dir === "+" ? 1 : -1 }, ctx), ctx);
    // two-sided
    let left, right;
    try { left = limWhere(u, xs, { a: target, s: -1 }, ctx); } catch (e) { if (e.code === "TIMEOUT") throw e; left = { k: "unknown", reason: e.message }; }
    try { right = limWhere(u, xs, { a: target, s: 1 }, ctx); } catch (e) { if (e.code === "TIMEOUT") throw e; right = { k: "unknown", reason: e.message }; }
    if (left.k === "unknown" || right.k === "unknown") {
      // a single known side that proves non-existence is enough
      const known = left.k !== "unknown" ? left : right.k !== "unknown" ? right : null;
      if (known && known.k === "dne") return withNotes({ k: "dne", method: known.method, sides: [left, right], osc: known.osc, which: left.k !== "unknown" ? "left" : "right" }, ctx);
      throw qerr("UNKNOWN", left.k === "unknown" ? left.reason : right.reason);
    }
    if (left.k === "undef" && right.k === "undef") return withNotes({ k: "undef", reason: "the function is not defined (as a real number) near the point", sides: [left, right] }, ctx);
    // domain convention (as in most CAS and textbooks for x^x, x ln x, ...): when the function is not
    // real on one side, the limit is taken through its domain, i.e. it is the other one-sided limit
    if (left.k === "undef" && (right.k === "fin" || right.k === "inf")) { ctx.notes.push(`The function is only defined (as a real number) to the right of the point, so this is the limit through its domain (the right-hand limit).`); return withNotes({ ...right, sides: [left, right], domainSide: "right" }, ctx); }
    if (right.k === "undef" && (left.k === "fin" || left.k === "inf")) { ctx.notes.push(`The function is only defined (as a real number) to the left of the point, so this is the limit through its domain (the left-hand limit).`); return withNotes({ ...left, sides: [left, right], domainSide: "left" }, ctx); }
    if (sameResult(left, right)) return withNotes({ ...right, method: right.method === left.method ? right.method : `${left.method}+${right.method}`, sides: [left, right], twoSided: true }, ctx);
    return withNotes({ k: "dne", method: "one-sided", sides: [left, right] }, ctx);
  };
  const ms = opts.timeLimit || 6000;
  return opts.deadline ? Budget.withDeadline(opts.deadline, run) : Budget.with(ms, run);
}
function withNotes(r, ctx) { return ctx.notes.length ? { ...r, notes: ctx.notes.slice() } : r; }

// Simple API for other engines: { value, status: "exact" | "dne" | "unknown", reason }
export function limit(expr, x, to, dir = "", opts = {}) {
  try {
    const r = limitDetailed(expr, x, to, dir, opts);
    if (r.k === "fin" || r.k === "inf") return { value: resultTree(r), status: "exact", reason: "", method: r.method, result: r };
    return { value: null, status: "dne", reason: describe(r, x, to), method: r.method, result: r };
  } catch (e) {
    if (e && e.code === "UNKNOWN") return { value: null, status: "unknown", reason: e.message };
    if (e && ["TIMEOUT", "BUDGET", "UNSUPPORTED", "UNDECIDABLE", "INTERNAL", "NEEDMORE", "UNDEFINED", "SINGULAR", "OSCILLATES", "DIVERGENT", "COMPLEX"].includes(e.code)) return { value: null, status: "unknown", reason: e.message };
    throw e;
  }
}

const per = (l) => (l === "0" ? "2 pi n" : `${l} + 2 pi n`);
// Human-readable reason for a non-existent limit.
export function describe(r, x, to, toText = defaultText) {
  const xn = typeof x === "string" ? x : x.name;
  if (r.k === "undef") return r.reason || "The function is not defined near the point.";
  if (r.method === "oscillation" && r.osc) {
    const [[l1, r1], [l2, r2]] = r.osc.values;
    return `The function oscillates: ${toText(r.osc.arg)} grows without bound, and along points where ${toText(r.osc.arg)} = ${per(l1)} the values tend to ${showR(r1, toText)}, while where ${toText(r.osc.arg)} = ${per(l2)} they tend to ${showR(r2, toText)}.`;
  }
  if (r.sides) {
    const [L, Rr] = r.sides;
    const pt = toText(to);
    if (L.k === "undef" && Rr.k !== "undef") return `The function is not defined (as a real number) to the left of ${xn} = ${pt}, so the two-sided limit does not exist; the right-hand limit is ${showR(Rr, toText)}.`;
    if (Rr.k === "undef" && L.k !== "undef") return `The function is not defined (as a real number) to the right of ${xn} = ${pt}, so the two-sided limit does not exist; the left-hand limit is ${showR(L, toText)}.`;
    if (L.k === "dne" || Rr.k === "dne") {
      const side = L.k === "dne" ? L : Rr;
      return `${L.k === "dne" ? "The left-hand" : "The right-hand"} limit does not exist. ` + describe(side, x, to, toText);
    }
    return `The left-hand limit is ${showR(L, toText)} but the right-hand limit is ${showR(Rr, toText)}.`;
  }
  return "The limit does not exist.";
}
let defaultText = (u) => String(u.k);
export function setPrinter(fn) { defaultText = fn; }

// ---------------------------------------------------------------- numeric verification
// Evaluate the ORIGINAL expression along sequences approaching the point (high precision with
// precision agreement) and check consistency with the claimed result.
function paramEnv(u, xn) {
  const env = {};
  [...X.freeSymbols(u)].filter((v) => v !== xn).forEach((p, i) => { env[p] = 0.7310585786 + 0.4142135624 * i; });
  return env;
}
function expArgsTooBig(u, env) {
  let big = false;
  const walk = (w) => {
    if (big) return;
    if (w.k === "pow" && w.args[0] === X.E) {
      const v = evalC(w.args[1], env, "real");
      if (!Number.isFinite(v.re) || Math.abs(v.re) > 2e5) { big = true; return; }
    }
    if (w.k === "pow" && w.args[0] !== X.E && X.freeSymbols(w.args[1]).size) {
      const b = evalC(w.args[0], env, "real"), e = evalC(w.args[1], env, "real");
      const m = Math.abs(e.re) * Math.log(Math.max(1e-300, Math.abs(b.re)));
      if (!Number.isFinite(m) || Math.abs(m) > 2e5) { big = true; return; }
    }
    if (w.k === "fn" && (w.name === "factorial" || w.name === "gamma")) {
      const v = evalC(w.args[0], env, "real");
      if (!Number.isFinite(v.re) || Math.abs(v.re) > 1e5) { big = true; return; }
    }
    if (w.k === "fn" && (w.name === "sinh" || w.name === "cosh" || w.name === "exp")) {
      const v = evalC(w.args[0], env, "real");
      if (!Number.isFinite(v.re) || Math.abs(v.re) > 2e5) { big = true; return; }
    }
    w.args.forEach(walk);
  };
  walk(u);
  return big;
}
const H_FIN = ["1e-1", "1e-2", "1e-3", "1e-4", "1e-6", "1e-8", "1e-12", "1e-16", "1e-24", "1e-32", "1e-48", "1e-64"];
const X_INF = ["10", "100", "1000", "10000", "30000", "100000", "1e6", "1e8", "1e12", "1e16", "1e24", "1e32", "1e48", "1e64", "1e100", "1e300", "1e1000", "1e3000", "1e10000"];
// Decimal digits needed to see through cancellation: the largest exponential scale inside u
// (|exp argument| / ln 10) plus the number of digits in the offset h.
function digitsNeeded(u, env, hDigits) {
  let m = 0;
  const walk = (w, inAdd) => {
    if (w.k === "add") inAdd = true;
    if (!inAdd) { w.args.forEach((a) => walk(a, inAdd)); return; }
    if (w.k === "pow" && w.args[0] === X.E) {
      const v = evalC(w.args[1], env, "real");
      m = Math.max(m, Number.isFinite(v.re) ? Math.abs(v.re) / 2.302585 : Infinity);
    }
    if (w.k === "fn" && (w.name === "sinh" || w.name === "cosh" || w.name === "tanh" || w.name === "exp")) {
      const v = evalC(w.args[0], env, "real");
      m = Math.max(m, Number.isFinite(v.re) ? Math.abs(v.re) / 2.302585 : Infinity);
    }
    w.args.forEach((a) => walk(a, inAdd));
  };
  walk(u, false);
  return 40 + Math.ceil(m) + 3 * hDigits;
}
function sequenceValues(u, xn, where, penv) {
  const out = [];
  let abig = null;
  if (!where.inf) {
    const a = hp(where.a, penv, { digits: 150, maxDigits: 150 });
    if (!a.ok) return out;
    abig = a.big;
  }
  const list = where.inf ? X_INF : H_FIN;
  const t0 = now();
  for (const s of list) {
    if (now() - t0 > 2500) break;
    const hv = B.fromString(s, 256);
    let xv;
    if (where.inf) xv = where.neg ? B.neg(hv) : hv;
    else xv = B.add(abig, where.s > 0 ? hv : B.neg(hv), 600);
    const xd = B.toNumber(xv);
    if (expArgsTooBig(u, { ...penv, [xn]: xd })) break;
    const hDigits = Math.abs(Math.round(log10Abs(hv)));
    const need = digitsNeeded(u, { ...penv, [xn]: Number.isFinite(xd) ? xd : 1e300 }, hDigits);
    if (need > 1200) break;
    const v = hp(u, { ...penv, [xn]: xv }, { digits: need, maxDigits: Math.max(700, 2 * need) });
    if (!v.ok) { out.push({ h: s, ok: false }); continue; }
    if (v.bigIm && v.bigIm.m !== 0n && log10Abs(v.bigIm) > log10Abs(v.big) - 20) { out.push({ h: s, ok: false, complex: true }); continue; }
    out.push({ h: s, ok: true, big: v.big, lg: log10Abs(v.big), sg: bigSign(v.big) });
  }
  return out;
}
function judgeFinite(vals, Lbig) {
  const ok = vals.filter((v) => v.ok);
  if (ok.length < 3) return { status: "inconclusive", detail: "too few points where the function could be evaluated" };
  const scale = Math.max(0, log10Abs(Lbig));
  const d = ok.map((v) => { const df = B.sub(v.big, Lbig, 256); return log10Abs(df) - scale; });
  const last = d[d.length - 1];
  if (last < -8) return { status: "verified-numeric", detail: `at ${ok.length} points approaching the limit point the values approach the answer (last difference 1e${Math.round(last)})` };
  const tail = d.slice(-3);
  if (last < -1.3 && tail[0] > tail[1] && tail[1] > tail[2] && last < d[0] - 0.7) return { status: "verified-numeric", detail: `the difference from the answer decreases steadily (to 1e${last.toFixed(1)}) along the sequence` };
  // converged elsewhere?
  const lastVals = ok.slice(-3);
  const agree = lastVals.every((v) => { const df = B.sub(v.big, lastVals[2].big, 256); return log10Abs(df) - Math.max(0, lastVals[2].lg) < -10; });
  if (agree && last > -6) return { status: "failed", detail: `the function values settle near ${B.toString(lastVals[2].big, 12)}, not the claimed answer` };
  if (last > 0.5 && tail[2] > tail[1] && tail[1] > tail[0]) return { status: "failed", detail: "the function values move away from the claimed answer" };
  return { status: "inconclusive", detail: "numeric evidence is not conclusive" };
}
function judgeInfinite(vals, s) {
  const ok = vals.filter((v) => v.ok);
  if (ok.length < 3) return { status: "inconclusive", detail: "too few points where the function could be evaluated" };
  const tail = ok.slice(-3);
  if (tail.slice(-2).some((v) => v.sg !== s)) return { status: "failed", detail: `the function values have the wrong sign for a limit of ${s > 0 ? "+" : "-"}infinity` };
  const inc = tail[0].lg < tail[1].lg && tail[1].lg < tail[2].lg;
  const agree = tail.every((v) => { const df = B.sub(v.big, tail[2].big, 256); return log10Abs(df) - Math.max(0, tail[2].lg) < -10; });
  if (agree) return { status: "failed", detail: `the function values settle near ${B.toString(tail[2].big, 12)}` };
  if (inc && tail[2].lg > 1) return { status: "verified-numeric", detail: `the values grow without bound (|f| reaches 1e${Math.round(tail[2].lg)}) with the right sign` };
  return { status: "inconclusive", detail: "growth is not clearly visible numerically" };
}
function spreadCheck(u, xn, where, penv, gap) {
  // oscillation: in shrinking windows the values keep a spread comparable to the proven gap
  const windows = where.inf ? [[1e3, 2e3], [1e6, 2e6]] : [[1e-3, 2e-3], [1e-6, 2e-6]];
  const av = where.inf ? 0 : evalC(where.a, penv, "real").re;
  const res = [];
  for (const [lo, hi] of windows) {
    let mn = Infinity, mx = -Infinity;
    for (let i = 0; i < 97; i++) {
      const h = lo * Math.pow(hi / lo, (i + 0.5) / 97);
      const xv = where.inf ? (where.neg ? -h : h) : av + where.s * h;
      const v = hp(u, { ...penv, [xn]: xv }, { digits: 30, maxDigits: 120 });
      if (!v.ok) continue;
      const n = B.toNumber(v.big);
      if (Number.isFinite(n)) { mn = Math.min(mn, n); mx = Math.max(mx, n); }
    }
    res.push(mx - mn);
  }
  const need = Number.isFinite(gap) ? 0.25 * gap : 10;
  return res.every((s) => s >= need) ? { status: "verified-numeric", detail: `in shrinking windows near the point the values keep spreading over an interval of length >= ${need.toPrecision(3)}` }
    : { status: "inconclusive", detail: "oscillation not visible numerically" };
}
function verifySide(u, xn, where, r, penv) {
  if (r.k === "undef") {
    const vals = sequenceValues(u, xn, where, penv).slice(0, 6);
    const bad = vals.filter((v) => !v.ok).length;
    return bad >= Math.max(3, vals.length - 0) ? { status: "verified-numeric", detail: "the function is undefined at every test point on this side" } : { status: "failed", detail: "the function is defined at test points on this side" };
  }
  if (r.k === "fin") {
    const Lv = hp(r.v, penv, { digits: 60, maxDigits: 300 });
    if (!Lv.ok) return { status: "inconclusive", detail: "the answer could not be evaluated" };
    return judgeFinite(sequenceValues(u, xn, where, penv), Lv.big);
  }
  if (r.k === "inf") return judgeInfinite(sequenceValues(u, xn, where, penv), r.s);
  if (r.k === "dne" && r.osc) {
    const [[, r1], [, r2]] = r.osc.values;
    let gap = Infinity;
    if (r1.k === "fin" && r2.k === "fin") {
      const a = hp(r1.v, penv), b = hp(r2.v, penv);
      gap = a.ok && b.ok ? Math.abs(a.re - b.re) : Infinity;
    }
    return spreadCheck(u, xn, where, penv, gap);
  }
  return { status: "inconclusive", detail: "no numeric test for this case" };
}
export function verifyLimit(expr, x, to, dir, r) {
  const xn = typeof x === "string" ? x : x.name;
  const u = expr;
  const penv = paramEnv(u, xn);
  const target = simp(to);
  const checks = [];
  const add = (name, res) => checks.push({ kind: name, ok: res.status === "failed" ? false : res.status === "inconclusive" ? null : true, detail: res.detail });
  let statuses = [];
  const run = (where, res, name) => { const v = verifySide(u, xn, where, res, penv); add(name, v); statuses.push(v.status); };
  try {
    return Budget.with(8000, () => {
      if (target === X.OO) run({ inf: true }, r, "sequence x -> oo");
      else if (isNegInf(target)) run({ inf: true, neg: true }, r, "sequence x -> -oo");
      else if (dir === "+" || dir === "-") run({ a: target, s: dir === "+" ? 1 : -1 }, r, `sequence x -> ${dir === "+" ? "right" : "left"}`);
      else if (r.sides) {
        run({ a: target, s: -1 }, r.sides[0], "sequence from the left");
        run({ a: target, s: 1 }, r.sides[1], "sequence from the right");
        if (r.k === "dne" && !r.osc && r.sides.every((sd) => sd.k === "fin" || sd.k === "inf") && sameResult(r.sides[0], r.sides[1])) statuses.push("failed");
      } else run({ a: target, s: 1 }, r, "sequence");
      const status = statuses.includes("failed") ? "failed" : statuses.every((s) => s === "verified-numeric") ? "verified-numeric" : "inconclusive";
      return { status, checks };
    });
  } catch (e) {
    if (e.code === "TIMEOUT") return { status: "inconclusive", checks: [...checks, { kind: "sequence", ok: null, detail: "numeric check ran out of time" }] };
    throw e;
  }
}

export { gprep, contAt, Gruntz };
