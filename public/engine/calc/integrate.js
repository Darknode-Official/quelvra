// Quelvra symbolic integration.
//
//   integrate(f, x, {steps, ctx, budget, timeLimit, assume}) -> { F, method, steps, conditions, special, note }
//   throws { code: "NONELEMENTARY" | "UNSUPPORTED" | "BUDGET" | "TIMEOUT", message, proof? }
//
// Layers (each bounded, every transformation recorded as a step):
//   int.table      standard forms, including linear arguments f(ax + b), ln|u| in the real domain
//   int.linear     split sums, take constants out
//   int.poly       polynomials (expanded when cheap)
//   int.partial    rational functions: Hermite reduction + Rothstein-Trager / real splitting (int-rational.js)
//   int.usub       derivative-divides substitution u = g(x), with inverse substitution when g is invertible
//   int.parts      integration by parts (LIATE), including the cyclic case (e^x sin x) solved as an equation
//   int.trig       powers and products of trig functions (odd-power substitution, half-angle, reduction
//                  formulas, products to sums, Bioche substitutions)
//   int.trigsub    sqrt(a^2 - u^2) by u = a sin t, back-substituted to x
//   int.weierstrass  t = tan(u/2) for rational functions of sin and cos
//   int.euler      Euler substitution for R(x, sqrt(x^2 + b x + c))
//   int.risch      exponential polynomials: the Risch differential equation y' + q' y = p decides
//                  elementarity exactly (and proves NONELEMENTARY when it has no solution)
//   int.special    classic non-elementary integrals expressed with erf, erfi, Si, Ci, Shi, Chi, Ei, li,
//                  FresnelS, FresnelC
// Every candidate antiderivative is checked independently (d/dx F == f numerically on the real domain of f,
// and F must be defined wherever f is) before it is returned. A candidate that fails is never returned.

import * as X from "../expr.js";
import * as N from "../num.js";
import { makeCtx, simplify } from "../simplify.js";
import { toText } from "../print.js";
import { diff } from "./diff.js";
import { StepLog, NO_STEPS } from "../steps.js";
import * as P from "../poly.js";
import { verifyAntiderivative } from "../verify.js";
import { canon, expandC, linearCoeffs, polyCoeffs, checkAntiderivative, usesSpecial, evalD, togetherND } from "./int-util.js";
import { integrateRationalQ, setPrinter } from "./int-rational.js";
import { specialIntegral, expPolyRisch, setShow } from "./int-special.js";
import { normanIntegrate } from "./int-norman.js";

setPrinter(toText);
setShow(toText);

const { ZERO, ONE, TWO, NEG_ONE, HALF, E, PI } = X;
const now = () => (typeof performance !== "undefined" ? performance.now() : Date.now());
const T = (u) => toText(u);

export function intError(code, message, extra = {}) { return Object.assign(new Error(message), { code, ...extra }); }

const TRIG = new Set(["sin", "cos", "tan", "cot", "sec", "csc"]);
const HYP = new Set(["sinh", "cosh", "tanh", "coth", "sech", "csch"]);
const INV = new Set(["asin", "acos", "atan", "acot", "asec", "acsc", "asinh", "acosh", "atanh"]);

// ---------------------------------------------------------------- small tree helpers
const isNumNode = (u) => u.k === "num";
const D = (u, x) => diff(u, x, { ctx: makeCtx({ budget: { ops: 200000 } }) });
function splitConst(f, x) {
  if (f.k !== "mul") return X.freeOf(f, x) ? [f, ONE] : [ONE, f];
  const c = [], v = [];
  for (const a of f.args) (X.freeOf(a, x) ? c : v).push(a);
  return [c.length ? canon(X.mul(...c)) : ONE, v.length ? (v.length === 1 ? v[0] : X.mul(...v)) : ONE];
}
function freshSym(f, base = "u") {
  const used = X.freeSymbols(f);
  for (const n of [base, "v", "w", "t", "s", "z"]) if (!used.has(n)) return X.sym(n);
  for (let i = 1; ; i++) if (!used.has(base + i)) return X.sym(base + i);
}
function collect(u, pred, out = []) {
  if (pred(u) && !out.includes(u)) out.push(u);
  for (const a of u.args) collect(a, pred, out);
  return out;
}
// replace every occurrence of `from` (structurally) - also inside larger products/sums
function replaceAll(u, from, to) { return X.replace(u, from, to); }
// Rewrite compositions that appear after back-substitution: cos(asin z) = sqrt(1 - z^2), ...
export function backSimp(u) {
  return canon(X.mapTree(u, (w) => {
    if (w.k !== "fn" || w.args.length !== 1) return w;
    const a = w.args[0];
    if (w.name === "Ei" && a.k === "fn" && a.name === "ln" && a.args.length === 1) return X.fn("li", a.args[0]); // Ei(ln z) = li(z), z > 0
    if (a.k !== "fn" || a.args.length !== 1) return w;
    const z = a.args[0];
    const s1mz2 = X.sqrt(X.sub(ONE, X.pow(z, TWO))), s1pz2 = X.sqrt(X.add(ONE, X.pow(z, TWO))), sz2m1 = X.sqrt(X.sub(X.pow(z, TWO), ONE));
    const key = w.name + "(" + a.name + ")";
    switch (key) {
      case "sin(asin)": case "cos(acos)": case "tan(atan)": case "sinh(asinh)": case "cosh(acosh)": case "tanh(atanh)": return z;
      case "cos(asin)": case "sin(acos)": return canon(s1mz2);
      case "tan(asin)": return canon(X.div(z, s1mz2));
      case "sec(asin)": return canon(X.recip(s1mz2));
      case "cot(asin)": return canon(X.div(s1mz2, z));
      case "csc(asin)": return canon(X.recip(z));
      case "sin(atan)": return canon(X.div(z, s1pz2));
      case "cos(atan)": return canon(X.recip(s1pz2));
      case "sec(atan)": return canon(s1pz2);
      case "csc(atan)": return canon(X.div(s1pz2, z));
      case "cot(atan)": return canon(X.recip(z));
      case "cosh(asinh)": return canon(s1pz2);
      case "sinh(acosh)": return canon(sz2m1);
      case "atan(tan)": return z; // valid antiderivative piece: same derivative, and continuous
      default: return w;
    }
  }));
}

// replace powers of base0 (= Qd/k up to canon) by powers of Qd: base0^p -> Qd^p * k^(-p)
function rebaseRadical(u, base0, Qd, k) {
  const b0 = canon(base0);
  return canon(X.mapTree(u, (w) => (w.k === "pow" && w.args[0] === b0 && X.isNum(w.args[1]) ? X.mul(X.pow(Qd, w.args[1]), X.pow(X.num(k), X.neg(w.args[1]))) : w)));
}

// sin(n u), cos(n u) -> polynomials in sin u, cos u (for back-substitution)
function expandMultiAngle(u) {
  return canon(X.mapTree(u, (w) => {
    if (w.k !== "fn" || (w.name !== "sin" && w.name !== "cos")) return w;
    const a = w.args[0];
    if (a.k !== "mul" || !X.isInt(a.args[0])) return w;
    const n = Number(a.args[0].v.n);
    if (n < 2 || n > 8) return w;
    const t = canon(X.mul(...a.args.slice(1)));
    const s = X.fn("sin", t), c = X.fn("cos", t);
    // de Moivre: cos(n t) + i sin(n t) = (c + i s)^n
    const re = [], im = [];
    for (let k = 0; k <= n; k++) {
      const term = X.mul(X.num(N.binom(BigInt(n), BigInt(k))), X.pow(c, X.num(n - k)), X.pow(s, X.num(k)));
      const r = k % 4;
      if (r === 0) re.push(term); else if (r === 1) im.push(term); else if (r === 2) re.push(X.neg(term)); else im.push(X.neg(term));
    }
    return canon(w.name === "cos" ? X.add(...re) : X.add(...im));
  }));
}

// ---------------------------------------------------------------- the engine
class Engine {
  constructor(opts) {
    this.log = opts.steps || NO_STEPS;
    this.ops = opts.budget && opts.budget.calls ? opts.budget.calls : 4000;
    this.deadline = now() + (opts.timeLimit || 6000);
    this.memo = new Map();
    this.active = new Set();
    this.depth = 0;
    this.maxDepth = opts.maxDepth || 14;
    this.conditions = [];
    this.special = false;
    this.nonelementary = null; // proof text when a sub-integral is proven non-elementary
    this.assume = opts.assume || null;
    this.positive = opts.positive || [];
    this.rejected = [];
    this.neProofs = new Map();
  }
  tick() {
    if (--this.ops < 0) throw intError("BUDGET", "Quelvra: integration budget exhausted");
    if (now() > this.deadline) throw intError("TIMEOUT", "Quelvra: integration time limit reached");
  }
  step(s) { this.log.add(s); }
  // steps read top-down: the step for a rule comes first and the integrals it needed (logged after
  // `mark`) become its sub-steps
  mark() { return this.log.cur ? this.log.cur.length : 0; }
  stepAdopt(mark, s) {
    const cur = this.log.cur;
    const kids = cur && cur.length > mark ? cur.splice(mark) : [];
    this.log.add({ ...s, sub: [...kids, ...(s.sub || [])] });
  }
  // a proof of non-elementarity is only about the integrand it was made for (a sub-integral being
  // non-elementary says nothing about a sum it came from), so it is keyed by that integrand
  noteNonelementary(f, proof) { this.neProofs.set(f, proof); }
  // cheap independent check of a candidate for a sub-integral (false only on a definite failure)
  quickCheck(G, f, x) {
    if (G === X.UNDEF || X.contains(G, X.UNDEF)) return false;
    const r = checkAntiderivative(backSimp(G), f, x, { points: 5, positive: this.positive });
    if (r.ok === false) { this.rejected.push({ F: G, f, reason: r.detail }); return false; }
    return true;
  }
  // run fn with a private step log; keep its steps only if it succeeds
  attempt(fn) {
    const saved = this.log;
    const tmp = saved === NO_STEPS ? NO_STEPS : new StepLog();
    this.log = tmp;
    let r = null;
    try { r = fn(); } finally { this.log = saved; }
    if (r && tmp !== NO_STEPS) for (const s of tmp.steps) saved.add(s);
    return r;
  }

  // integral of f dx, or null. f canonical.
  I(f, x) {
    this.tick();
    if (X.freeOf(f, x)) return canon(X.mul(f, x));
    const key = f.id + ":" + x.name;
    if (this.memo.has(key)) {
      const hit = this.memo.get(key);
      if (hit) this.step({ rule: "int.table", title: "Known integral", why: "This integral was already computed above.", before: X.integral(f, x), after: hit });
      return hit;
    }
    if (this.active.has(key) || this.depth >= this.maxDepth) return null;
    this.active.add(key);
    this.depth++;
    let r = null;
    try { r = this.dispatch(f, x); } finally { this.depth--; this.active.delete(key); }
    if (r) r = canon(r);
    this.memo.set(key, r);
    return r;
  }

  dispatch(f, x) {
    const before = X.integral(f, x);
    // 1 table
    let r = this.table(f, x);
    if (r) { this.step({ rule: "int.table", title: "Standard integral", why: this.tableWhy || "A standard antiderivative from the table.", before, after: r }); return r; }
    // 2 linearity
    if (f.k === "mul") {
      const [c, rest] = splitConst(f, x);
      if (c !== ONE) {
        const g = canon(rest);
        const s = this.attempt(() => {
          const m = this.mark();
          const G = this.I(g, x);
          if (!G) return null;
          const res = canon(X.mul(c, G));
          this.stepAdopt(m, { rule: "int.linear", title: "Constant multiple", why: `${T(c)} does not depend on ${x.name}, so it moves outside the integral.`, before, after: res, sub: [] });
          return res;
        });
        if (s) return s;
        if (this.neProofs.has(g)) this.neProofs.set(f, this.neProofs.get(g)); // c g is elementary iff g is
        return null;
      }
    }
    if (f.k === "add") {
      const s = this.attempt(() => {
        const m = this.mark(), parts = [];
        // integrate the terms in the order they are written
        const ft = T(f), pos = (t) => { const i = ft.indexOf(T(t).replace(/^-/, "")); return i < 0 ? Infinity : i; };
        for (const t of [...f.args].sort((a, b) => pos(a) - pos(b))) { const G = this.I(t, x); if (!G) return null; parts.push(G); }
        const res = canon(X.add(...parts));
        this.stepAdopt(m, { rule: "int.linear", title: "Integrate term by term", why: "The integral of a sum is the sum of the integrals.", before, after: res });
        return res;
      });
      if (s) return s;
    }
    // a sum whose terms are not separately integrable: try the Risch-Norman ansatz early
    if (f.k === "add" && this.depth <= 2) {
      const r0 = this.attempt(() => { try { return this.norman(f, x); } catch (e) { if (e && e.code === "UNSUPPORTED") return null; throw e; } });
      if (r0) return r0;
    }
    // remaining layers, each validated independently before it is accepted
    const layers = [
      ["poly", () => this.polynomial(f, x)],
      ["rational", () => this.rational(f, x)],
      ["exp-risch", () => this.expPoly(f, x)],
      ["trig", () => this.trig(f, x)],
      ["usub", () => this.usub(f, x)],
      ["expand", () => this.expandFirst(f, x)],
      ["radical", () => this.radicalQuadratic(f, x)],
      ["parts", () => this.parts(f, x)],
      ["hyperbolic", () => this.hyperbolic(f, x)],
      ["norman", () => this.norman(f, x)],
      ["special", () => this.specialFn(f, x)],
    ];
    for (const [, run] of layers) {
      const res = this.attempt(() => {
        let G = null;
        try { G = run(); } catch (e) {
          if (e && (e.code === "UNSUPPORTED" || e.code === "NONELEMENTARY")) return null;
          if (e instanceof RangeError && /call stack/i.test(e.message)) return null; // simplifier recursion (reported bug)
          throw e;
        }
        if (!G) return null;
        return this.quickCheck(canon(G), f, x) ? G : null;
      });
      if (res) return res;
    }
    return null;
  }

  // ------------------------------------------------ layer 1: table
  table(f, x) {
    this.tableWhy = "";
    const why = (s) => { this.tableWhy = s; };
    if (f === x) { why("x^n dx = x^(n+1)/(n+1) with n = 1."); return canon(X.mul(HALF, X.pow(x, TWO))); }
    const lin = (u) => (u === x ? [ONE, ZERO] : linearCoeffs(u, x));
    if (f.k === "pow") {
      const [b, e] = f.args;
      if (X.freeOf(e, x)) {
        const L = lin(b);
        if (L) {
          const a = L[0];
          if (e === NEG_ONE) {
            why(b === x ? "The integral of 1/x is ln|x| (the absolute value keeps it valid for x < 0)." : `The integral of 1/(a x + b) is ln|a x + b|/a with a = ${T(a)}.`);
            return canon(X.div(X.fn("ln", X.fn("abs", b)), a));
          }
          const e1 = canon(X.add(e, ONE));
          if (!X.isNum(e1)) this.conditions.push(X.rel("!=", e1, ZERO));
          why(b === x ? `Power rule: x^n dx = x^(n+1)/(n+1) with n = ${T(e)}.` : `Power rule with a linear inside: (a x + b)^n dx = (a x + b)^(n+1)/(a (n+1)) with a = ${T(a)}, n = ${T(e)}.`);
          return canon(X.div(X.pow(b, e1), X.mul(a, e1)));
        }
        // sec^2, csc^2, sech^2, csch^2, tan^2, cot^2 of a linear argument
        if (b.k === "fn" && b.args.length === 1 && e === TWO) {
          const La = lin(b.args[0]);
          if (La) {
            const u = b.args[0], a = La[0];
            const T2 = {
              sec: () => X.fn("tan", u), csc: () => X.neg(X.fn("cot", u)), sech: () => X.fn("tanh", u), csch: () => X.neg(X.fn("coth", u)),
              tan: () => X.sub(X.fn("tan", u), u), cot: () => X.sub(X.neg(X.fn("cot", u)), u),
              tanh: () => X.sub(u, X.fn("tanh", u)), coth: () => X.sub(u, X.fn("coth", u)),
            }[b.name];
            if (T2) { why(`Standard integral of ${b.name}^2.`); return canon(X.div(T2(), a)); }
          }
        }
      }
      if (X.freeOf(b, x)) {
        const L = lin(e);
        if (L) {
          const a = L[0];
          if (b === E) { why(e === x ? "The exponential e^x is its own antiderivative." : `e^(a x + b) dx = e^(a x + b)/a with a = ${T(a)}.`); return canon(X.div(f, a)); }
          if (X.isNum(b) && !N.isPos(b.v)) return null;
          if (!X.isNum(b) && !X.isConstantExpr(b)) this.conditions.push(X.rel(">", b, ZERO), X.rel("!=", b, ONE));
          why(`a^u du = a^u / ln(a) with a = ${T(b)}.`);
          return canon(X.div(f, X.mul(a, X.fn("ln", b))));
        }
      }
      return null;
    }
    if (f.k === "fn" && f.args.length === 1) {
      const u = f.args[0];
      const L = lin(u);
      if (!L) return null;
      const a = L[0];
      const s = (v) => canon(X.div(v, a));
      const lnAbs = (v) => X.fn("ln", X.fn("abs", v));
      const sq = (v) => X.pow(v, TWO);
      const res = {
        sin: () => X.neg(X.fn("cos", u)), cos: () => X.fn("sin", u),
        tan: () => X.neg(lnAbs(X.fn("cos", u))), cot: () => lnAbs(X.fn("sin", u)),
        sec: () => lnAbs(X.add(X.fn("sec", u), X.fn("tan", u))), csc: () => X.neg(lnAbs(X.add(X.fn("csc", u), X.fn("cot", u)))),
        sinh: () => X.fn("cosh", u), cosh: () => X.fn("sinh", u), tanh: () => X.fn("ln", X.fn("cosh", u)),
        coth: () => lnAbs(X.fn("sinh", u)), sech: () => X.fn("atan", X.fn("sinh", u)), csch: () => lnAbs(X.fn("tanh", X.mul(HALF, u))),
        ln: () => X.sub(X.mul(u, X.fn("ln", u)), u),
        asin: () => X.add(X.mul(u, X.fn("asin", u)), X.sqrt(X.sub(ONE, sq(u)))),
        acos: () => X.sub(X.mul(u, X.fn("acos", u)), X.sqrt(X.sub(ONE, sq(u)))),
        atan: () => X.sub(X.mul(u, X.fn("atan", u)), X.mul(HALF, X.fn("ln", X.add(ONE, sq(u))))),
        acot: () => X.add(X.mul(u, X.fn("acot", u)), X.mul(HALF, X.fn("ln", X.add(ONE, sq(u))))),
        asinh: () => X.sub(X.mul(u, X.fn("asinh", u)), X.sqrt(X.add(sq(u), ONE))),
        acosh: () => X.sub(X.mul(u, X.fn("acosh", u)), X.sqrt(X.sub(sq(u), ONE))),
        atanh: () => X.add(X.mul(u, X.fn("atanh", u)), X.mul(HALF, X.fn("ln", X.sub(ONE, sq(u))))),
        abs: () => X.mul(HALF, u, X.fn("abs", u)),
        sign: () => X.fn("abs", u),
        erf: () => X.add(X.mul(u, X.fn("erf", u)), X.div(X.exp(X.neg(sq(u))), X.sqrt(PI))),
      }[f.name];
      if (!res) return null;
      why(u === x ? `Standard integral of ${f.name}(x).` : `Standard integral of ${f.name}(u) with the linear inside u = ${T(u)}; divide by its slope ${T(a)}.`);
      return s(res());
    }
    if (f.k === "fn" && f.name === "log" && f.args.length === 2 && X.freeOf(f.args[0], x)) {
      const inner = this.table(X.fn("ln", f.args[1]), x);
      if (inner) { why("log_b(u) = ln(u)/ln(b)."); return canon(X.div(inner, X.fn("ln", f.args[0]))); }
      return null;
    }
    if (f.k === "mul" && f.args.length === 2) {
      const [p, q] = f.args;
      const pairs = { sec: ["tan", (u) => X.fn("sec", u)], csc: ["cot", (u) => X.neg(X.fn("csc", u))], sech: ["tanh", (u) => X.neg(X.fn("sech", u))], csch: ["coth", (u) => X.neg(X.fn("csch", u))] };
      for (const [A, Bn] of [[p, q], [q, p]]) {
        if (A.k === "fn" && Bn.k === "fn" && pairs[A.name] && pairs[A.name][0] === Bn.name && A.args[0] === Bn.args[0]) {
          const L = lin(A.args[0]);
          if (L) { why(`Standard integral of ${A.name}(u) ${Bn.name}(u).`); return canon(X.div(pairs[A.name][1](A.args[0]), L[0])); }
        }
      }
    }
    return null;
  }

  // ------------------------------------------------ layer 3: polynomials
  polynomial(f, x) {
    if (f.k !== "add" && f.k !== "mul" && f.k !== "pow") return null;
    if (collect(f, (w) => w.k === "fn" || (w.k === "pow" && !X.freeOf(w.args[1], x))).some((w) => !X.freeOf(w, x))) return null;
    const c = polyCoeffs(f, x);
    if (!c || c.length > 60) return null;
    const terms = c.map((ci, i) => X.mul(ci, X.num(1, i + 1), X.pow(x, X.num(i + 1))));
    const res = canon(X.add(...terms));
    this.step({ rule: "int.poly", title: "Integrate the polynomial", why: "Expand and apply the power rule to each term: x^n dx = x^(n+1)/(n+1).", before: X.integral(f, x), after: res });
    return res;
  }

  // ------------------------------------------------ layer 4: rational functions
  rational(f, x) {
    // x^k R(x^(k+1)): substitute first (a much simpler answer than partial fractions of the expanded form)
    for (const w of f.k === "mul" ? f.args : []) {
      const k = w === x ? 1n : w.k === "pow" && w.args[0] === x && X.isInt(w.args[1]) && w.args[1].v.n >= 1n ? w.args[1].v.n : 0n;
      if (!k) continue;
      const r = this.attempt(() => this.trySub(f, x, X.pow(x, X.num(N.Q(k + 1n))), false));
      if (r) return r;
    }
    if (collect(f, (w) => w.k === "fn" || w.k === "const" && w.name !== "pi" && w.name !== "e" || (w.k === "pow" && !X.isInt(w.args[1]))).some((w) => !X.freeOf(w, x))) return null;
    const [nt, dt] = P.numDen(f.k === "add" ? canon(expandTogether(f)) : f);
    if (X.freeOf(dt, x)) return null;
    let n, d;
    try { n = P.fromTree(nt, x.name); d = P.fromTree(dt, x.name); } catch (e) { if (e && e.code === "BUDGET") return null; throw e; }
    if (!n || !d) return this.rationalParam(f, x, nt, dt);
    const res = integrateRationalQ(n, d, x, this.log);
    if (!res) return null;
    this.step({ rule: "int.partial", title: "Integrate the rational function", why: "Polynomial part by the power rule, repeated factors by Hermite reduction, the rest as logarithms and arctangents over the real irreducible factors of the denominator.", before: X.integral(f, x), after: res });
    return res;
  }
  // rational functions with symbolic parameters: only linear and simple quadratic denominators
  rationalParam(f, x, nt, dt) {
    const cd = polyCoeffs(dt, x), cn = polyCoeffs(nt, x);
    if (!cd || !cn || cd.length > 3 || cn.length >= cd.length) return null;
    if (cd.length === 3 && cn.length <= 2) {
      // (B x + C)/(a x^2 + b x + c) with parameters: require known sign of 4ac - b^2
      const [c0, b0, a0] = cd;
      const disc = canon(X.sub(X.mul(X.num(4), a0, c0), X.pow(b0, TWO)));
      const sgn = constSign(disc, this.assume);
      if (sgn !== 1) return null;
      const B = cn[1] || ZERO, Cc = cn[0] || ZERO;
      const sd = canon(X.sqrt(disc));
      const res = canon(X.add(
        X.mul(B, X.pow(X.mul(TWO, a0), NEG_ONE), X.fn("ln", X.fn("abs", dt))),
        X.mul(X.sub(X.mul(TWO, a0, Cc), X.mul(B, b0)), X.pow(X.mul(a0, sd), NEG_ONE), X.fn("atan", X.div(X.add(X.mul(TWO, a0, x), b0), sd)))));
      this.conditions.push(X.rel("!=", a0, ZERO));
      this.step({ rule: "int.partial", title: "Complete the square", why: `The denominator has no real roots because 4ac - b^2 = ${T(disc)} > 0; the integral splits into a logarithm and an arctangent.`, before: X.integral(f, x), after: res });
      return res;
    }
    return null;
  }

  // ------------------------------------------------ exponential polynomials (Risch DE)
  expPoly(f, x) {
    const r = expPolyRisch(f, x, this);
    if (!r) return null;
    if (r.nonelementary) { this.noteNonelementary(f, r.proof); if (!r.F) return null; }
    if (r.F) {
      if (r.special) this.special = true;
      this.step({ rule: r.special ? "int.special" : "int.risch", title: r.title, why: r.why, before: X.integral(f, x), after: r.F });
      return r.F;
    }
    return null;
  }

  // ------------------------------------------------ layer 5: substitution
  usub(f, x) {
    const cands = [];
    const walk = (w) => {
      if (w === x || X.freeOf(w, x)) return;
      if (w.k === "fn") { for (const a of w.args) if (a !== x && !X.freeOf(a, x)) cands.push(a); cands.push(w); }
      else if (w.k === "pow") {
        const [b, e] = w.args;
        if (b !== x && !X.freeOf(b, x)) cands.push(b);
        if (!X.freeOf(e, x)) { cands.push(e); cands.push(w); }
        else if (!X.isInt(e)) cands.push(w);
        else if (b !== x && X.isInt(e) && e.v.n > 1n) cands.push(w);
        else if (b === x && X.isInt(e) && e.v.n >= 2n) cands.push(w);
      }
      for (const a of w.args) walk(a);
    };
    walk(f);
    // a factor x^k suggests u = x^(k+1) (its derivative up to a constant)
    for (const w of f.k === "mul" ? f.args : [f]) {
      if (w === x) cands.push(X.pow(x, TWO));
      else if (w.k === "pow" && w.args[0] === x && X.isInt(w.args[1]) && w.args[1].v.n >= 1n) cands.push(X.pow(x, X.num(N.add(w.args[1].v, N.Q(1)))));
    }
    // polynomial numerator p(x): u = antiderivative of p (derivative-divides for p(x) R(u))
    try {
      const [nt] = P.numDen(f);
      const pn = nt !== f ? P.fromTree(nt, x.name) : null;
      if (pn && pn.length >= 2 && pn.length <= 8) {
        const ip = [N.ZERO, ...pn.map((c, i) => N.div(c, N.Q(i + 1)))];
        cands.push(P.toTree(ip, x.name));
      }
    } catch (e) { if (!e || e.code !== "BUDGET") throw e; }
    let list = [...new Set(cands)].filter((g) => g !== x && g !== f);
    // linear candidates only help when they occur inside non-trivial structure; keep them last
    const isLin = (g) => !!linearCoeffs(g, x);
    list.sort((a, b) => (isLin(a) - isLin(b)) || X.size(a) - X.size(b));
    list = list.slice(0, 14);
    // pass 1: pure derivative-divides substitutions; pass 2: with inverse substitution
    for (const allowInverse of [false, true]) {
      for (const g of list) {
        this.tick();
        const res = this.attempt(() => this.trySub(f, x, g, allowInverse));
        if (res) return res;
      }
    }
    return null;
  }
  // x as a function of t when g is invertible in closed form; positive: range of g is t > 0 / t >= 0
  inverse(g, x, t) {
    const L = linearCoeffs(g, x);
    if (L) return { x: canon(X.div(X.sub(t, L[1]), L[0])), positive: false };
    if (g.k === "pow") {
      const [b, e] = g.args;
      if (X.freeOf(e, x) && X.isNum(e)) {
        const Lb = b === x ? [ONE, ZERO] : linearCoeffs(b, x);
        // only one-to-one powers: an even power (x^2, (ax+b)^4, x^(2/3)) has no single inverse on the reals
        if (Lb && e.v.n % 2n !== 0n) {
          const inv = canon(X.div(X.sub(X.pow(t, X.num(N.inv(e.v))), Lb[1]), Lb[0]));
          return { x: inv, positive: e.v.d % 2n === 0n || e.v.n % 2n === 0n };
        }
      }
      if (X.freeOf(b, x) && (b === E || X.isNum(b))) {
        const Le = e === x ? [ONE, ZERO] : linearCoeffs(e, x);
        if (Le) return { x: canon(X.div(X.sub(X.div(X.fn("ln", t), X.fn("ln", b)), Le[1]), Le[0])), positive: true };
      }
    }
    if (g.k === "fn" && g.name === "ln") {
      const L2 = g.args[0] === x ? [ONE, ZERO] : linearCoeffs(g.args[0], x);
      if (L2) return { x: canon(X.div(X.sub(X.exp(t), L2[1]), L2[0])), positive: false };
    }
    return null;
  }
  trySub(f, x, g, allowInverse = true) {
    const dg = D(g, x);
    if (dg === ZERO || X.contains(dg, X.UNDEF) || dg.k === "deriv") return null;
    const t = freshSym(f, "u");
    let h;
    try { h = canon(X.div(f, dg)); } catch (e) { if (e.code === "BUDGET") return null; throw e; }
    let hr = replaceAll(h, g, t);
    let inv = null;
    if (!X.freeOf(hr, x)) {
      const pr = polyInG(h, g, x, t);
      if (pr) hr = pr;
    }
    if (!X.freeOf(hr, x)) {
      inv = allowInverse ? this.inverse(g, x, t) : null;
      if (!allowInverse) {
        const alt0 = replaceAll(canon(expandC(h)), g, t);
        if (!X.freeOf(alt0, x)) return null;
      }
      if (!inv) {
        // try the expanded / combined form of h once
        const alt = replaceAll(canon(expandC(h)), g, t);
        if (!X.freeOf(alt, x)) return null;
        hr = alt;
      } else {
        const ctx = makeCtx({ budget: { ops: 300000 }, assume: inv.positive ? new Map([[t.name, new Set(["positive"])]]) : new Map() });
        hr = simplify(X.subs(hr, { [x.name]: inv.x }), ctx);
        if (!X.freeOf(hr, x)) return null;
      }
    } else hr = canon(hr);
    if (hr === X.UNDEF || X.contains(hr, X.UNDEF)) return null;
    // no progress: the substituted integrand is the original one renamed
    if (X.subs(hr, { [t.name]: x }) === f) return null;
    const m = this.mark();
    const G = this.I(hr, t);
    if (!G) return null;
    const F = canon(X.subs(G, { [t.name]: g }));
    this.stepAdopt(m, { rule: "int.usub", title: `Substitute ${t.name} = ${T(g)}`, why: `d${t.name} = ${T(dg)} d${x.name}${inv ? `, and ${x.name} = ${T(inv.x)}` : ""}, so the integral becomes an integral in ${t.name}.`, before: X.integral(f, x), after: X.integral(hr, t) });
    this.step({ rule: "int.usub", title: "Substitute back", why: `Replace ${t.name} by ${T(g)}.`, before: G, after: F });
    return F;
  }

  // ------------------------------------------------ expand products of sums / powers of sums
  expandFirst(f, x) {
    if (f.k !== "mul" && f.k !== "pow") return null;
    const hasSum = f.k === "pow" ? f.args[0].k === "add" && X.isInt(f.args[1]) && f.args[1].v.n > 1n : f.args.some((a) => a.k === "add" || (a.k === "pow" && a.args[0].k === "add" && X.isInt(a.args[1]) && a.args[1].v.n > 1n));
    if (!hasSum) return null;
    if (X.size(f) > 60) return null;
    let e;
    try { e = expandC(f); } catch (err) { if (err.code === "BUDGET") return null; throw err; }
    if (e === f || e.k !== "add" || e.args.length > 40) return null;
    const G = this.I(e, x);
    if (!G) return null;
    this.step({ rule: "int.linear", title: "Expand", why: "Multiply out, then integrate term by term.", before: X.integral(f, x), after: X.integral(e, x) });
    return G;
  }

  // ------------------------------------------------ layer 6: integration by parts
  partsClass(w, x) {
    if (X.freeOf(w, x)) return 9;
    const base = w.k === "pow" && X.isInt(w.args[1]) && w.args[1].v.n > 0n ? w.args[0] : w;
    if (base.k === "fn" && (base.name === "ln" || base.name === "log")) return 0;
    if (base.k === "fn" && INV.has(base.name)) return 1;
    if (base.k === "fn" && (TRIG.has(base.name) || HYP.has(base.name))) return 3;
    if (base.k === "pow" && !X.freeOf(base.args[1], x)) return 4;
    if (polyCoeffs(w, x)) return 2;
    return 5;
  }
  parts(f, x) {
    const factors = f.k === "mul" ? f.args.slice() : [f];
    const cls = factors.map((w) => this.partsClass(w, x));
    const best = Math.min(...cls);
    if (best > 3) return null;
    const i = cls.indexOf(best);
    const u = factors[i];
    const rest = factors.filter((_, j) => j !== i);
    const dv = rest.length ? canon(X.mul(...rest)) : ONE;
    // polynomials are integrated only when u is a transcendental log / inverse function
    if (best === 2 && rest.length === 0) return null;
    const m = this.mark();
    if (best === 3 && dv === ONE) return null;
    if (best === 2 && rest.every((w) => this.partsClass(w, x) === 2)) return null;
    if (u.k === "fn" && (u.name === "abs" || u.name === "sign")) return null;
    const v = this.attempt(() => this.I(dv, x));
    if (!v || usesSpecial(v) || X.contains(v, X.fn("erf", x))) return null;
    const du = D(u, x);
    const r = canon(X.mul(v, du));
    const uv = canon(X.mul(u, v));
    const before = X.integral(f, x);
    // cyclic case: r = c f  ->  I = uv - c I
    const c1 = ratioConst(r, f, x);
    if (c1 !== null && c1 !== NEG_ONE) {
      const res = canon(X.div(uv, X.add(ONE, c1)));
      this.stepAdopt(m, { rule: "int.parts", title: "Integration by parts (the integral returns)", why: `With u = ${T(u)} and dv = ${T(dv)} dx, the new integral is ${T(c1)} times the original one, so I = uv - (${T(c1)}) I; solve for I.`, before, after: res });
      return res;
    }
    // second round for the cyclic case: integrate r by parts once more with the same kind of choice
    const cyc = this.attempt(() => {
      const fr = r.k === "mul" ? r.args : [r];
      const [cr, restr] = splitConst(r, x);
      const fac = restr.k === "mul" ? restr.args : [restr];
      const cl = fac.map((w) => this.partsClass(w, x));
      const j = cl.indexOf(best);
      if (j < 0 || fr.length < 1) return null;
      const u2 = fac[j];
      const dv2 = canon(X.mul(...fac.filter((_, k) => k !== j)));
      const v2 = this.attempt(() => this.I(dv2, x));
      if (!v2) return null;
      const r2 = canon(X.mul(cr, v2, D(u2, x)));
      const c2 = ratioConst(r2, f, x);
      if (c2 === null) return null;
      // I = uv - (cr u2 v2 - c2 I)  ->  I (1 - c2) = uv - cr u2 v2
      const den = canon(X.sub(ONE, c2));
      if (den === ZERO) return null;
      const res = canon(X.div(X.sub(uv, X.mul(cr, u2, v2)), den));
      this.stepAdopt(m, { rule: "int.parts", title: "Integration by parts twice (the integral returns)", why: `Integrating by parts twice (u = ${T(u)}, then u = ${T(u2)}) gives the original integral back with factor ${T(c2)}; solving the equation I = ... + (${T(c2)}) I gives the result.`, before, after: res });
      return res;
    });
    if (cyc) return cyc;
    const G = this.I(r, x);
    if (!G) return null;
    const res = canon(X.sub(uv, G));
    this.stepAdopt(m, { rule: "int.parts", title: "Integration by parts", why: `u dv = uv - v du with u = ${T(u)} and dv = ${T(dv)} dx, so du = ${du === ONE ? "" : T(du) + " "}dx and v = ${T(v)}. Then subtract the integral of v du.`, before, after: res });
    return res;
  }

  // ------------------------------------------------ layer 7: trigonometric integrals
  trig(f, x) {
    const trigNodes = collect(f, (w) => w.k === "fn" && TRIG.has(w.name) && !X.freeOf(w, x));
    if (!trigNodes.length) return null;
    const argsSet = [...new Set(trigNodes.map((w) => w.args[0]))];
    if (argsSet.length > 1) return this.productToSum(f, x, argsSet);
    const u = argsSet[0];
    const L = u === x ? [ONE, ZERO] : linearCoeffs(u, x);
    if (!L) return null;
    const a = L[0];
    const S = X.sym("S__"), Cs = X.sym("C__");
    const toSC = (w) => X.mapTree(w, (n) => {
      if (n.k !== "fn" || n.args[0] !== u) return n;
      switch (n.name) {
        case "sin": return S; case "cos": return Cs; case "tan": return X.div(S, Cs); case "cot": return X.div(Cs, S);
        case "sec": return X.recip(Cs); case "csc": return X.recip(S); default: return n;
      }
    });
    const g = canon(toSC(f));
    if (!X.freeOf(g, x)) return null; // x also outside the trig functions
    // monomial c S^m C^n ?
    const mono = monomialSC(g, S, Cs);
    const back = (h) => canon(X.subs(h, { S__: X.fn("sin", u), C__: X.fn("cos", u) }));
    const w = freshSym(f, "w");
    const before = X.integral(f, x);
    if (mono) {
      const { c, m, n } = mono;
      // pure sec^n / csc^n, n >= 3: reduction formula
      if (m === 0 && n <= -3) return this.secReduction(f, x, u, a, c, -n, "sec");
      if (n === 0 && m <= -3) return this.secReduction(f, x, u, a, c, -m, "csc");
      // tan^m sec^n type (m even > 0, n < 0 odd): sin^2 = 1 - cos^2 gives pure sec powers (reduction formula)
      if (m > 0 && m % 2 === 0 && n < 0 && n % 2 !== 0) {
        const h = canon(expandC(X.mul(c, X.pow(X.sub(ONE, X.pow(Cs, TWO)), X.num(m / 2)), X.pow(Cs, X.num(n)))));
        const r = this.attempt(() => {
          const hx = back(h);
          const G = this.I(hx, x);
          if (G) this.step({ rule: "int.trig", title: "Pythagorean identity", why: "Write sin^2 = 1 - cos^2 and split into powers of sec.", before, after: X.integral(hx, x) });
          return G;
        });
        if (r) return r;
      }
      if (n > 0 && n % 2 === 0 && m < 0 && m % 2 !== 0) {
        const h = canon(expandC(X.mul(c, X.pow(X.sub(ONE, X.pow(S, TWO)), X.num(n / 2)), X.pow(S, X.num(m)))));
        const r = this.attempt(() => {
          const hx = back(h);
          const G = this.I(hx, x);
          if (G) this.step({ rule: "int.trig", title: "Pythagorean identity", why: "Write cos^2 = 1 - sin^2 and split into powers of csc.", before, after: X.integral(hx, x) });
          return G;
        });
        if (r) return r;
      }
      if (m % 2 !== 0 && (n % 2 === 0 || m > 0 || n < 0)) {
        // w = cos u: S^m C^n du = -(1 - w^2)^((m-1)/2) w^n dw / a
        const h = canon(X.mul(X.neg(c), X.pow(X.sub(ONE, X.pow(w, TWO)), X.num((m - 1) / 2)), X.pow(w, X.num(n)), X.recip(a)));
        const G = this.I(h, w);
        if (G) {
          const res = canon(X.subs(G, { [w.name]: X.fn("cos", u) }));
          this.step({ rule: "int.trig", title: `Odd power of sine: substitute ${w.name} = cos(${T(u)})`, why: `Keep one factor sin(${T(u)}), write the remaining even power with sin^2 = 1 - cos^2; then d${w.name} = -${a === ONE ? "" : T(a) + " "}sin(${T(u)}) dx.`, before, after: X.integral(h, w) });
          this.step({ rule: "int.trig", title: "Substitute back", why: `${w.name} = cos(${T(u)}).`, before: G, after: res });
          return res;
        }
      }
      if (n % 2 !== 0) {
        const h = canon(X.mul(c, X.pow(X.sub(ONE, X.pow(w, TWO)), X.num((n - 1) / 2)), X.pow(w, X.num(m)), X.recip(a)));
        const G = this.I(h, w);
        if (G) {
          const res = canon(X.subs(G, { [w.name]: X.fn("sin", u) }));
          this.step({ rule: "int.trig", title: `Odd power of cosine: substitute ${w.name} = sin(${T(u)})`, why: `Keep one factor cos(${T(u)}), write the remaining even power with cos^2 = 1 - sin^2; then d${w.name} = ${a === ONE ? "" : T(a) + " "}cos(${T(u)}) dx.`, before, after: X.integral(h, w) });
          this.step({ rule: "int.trig", title: "Substitute back", why: `${w.name} = sin(${T(u)}).`, before: G, after: res });
          return res;
        }
      }
      if (m % 2 === 0 && n % 2 === 0) {
        if (m >= 0 && n >= 0) {
          // half-angle formulas
          const u2 = canon(X.mul(TWO, u));
          const h = canon(expandC(X.mul(c, X.pow(X.mul(HALF, X.sub(ONE, X.fn("cos", u2))), X.num(m / 2)), X.pow(X.mul(HALF, X.add(ONE, X.fn("cos", u2))), X.num(n / 2)))));
          this.step({ rule: "int.trig", title: "Half-angle formulas", why: `Even powers: sin^2 u = (1 - cos 2u)/2 and cos^2 u = (1 + cos 2u)/2 with u = ${T(u)}.`, before, after: X.integral(h, x) });
          const G = this.I(h, x);
          if (G) return G;
          return null;
        }
        if (m >= 0 && n < 0) {
          // S^m = (1 - C^2)^(m/2) -> sum of even powers of cos
          const h = canon(expandC(X.mul(c, X.pow(X.sub(ONE, X.pow(Cs, TWO)), X.num(m / 2)), X.pow(Cs, X.num(n)))));
          if (h.k === "add") {
            const hx = back(h);
            this.step({ rule: "int.trig", title: "Pythagorean identity", why: "Write sin^2 = 1 - cos^2 and split into powers of cos (sec).", before, after: X.integral(hx, x) });
            const G = this.I(hx, x);
            if (G) return G;
          }
        }
        if (n >= 0 && m < 0) {
          const h = canon(expandC(X.mul(c, X.pow(X.sub(ONE, X.pow(S, TWO)), X.num(n / 2)), X.pow(S, X.num(m)))));
          if (h.k === "add") {
            const hx = back(h);
            this.step({ rule: "int.trig", title: "Pythagorean identity", why: "Write cos^2 = 1 - sin^2 and split into powers of sin (csc).", before, after: X.integral(hx, x) });
            const G = this.I(hx, x);
            if (G) return G;
          }
        }
      }
      // tan / cot substitution for m + n even with a negative power
      if ((m + n) % 2 === 0 && (m < 0 || n < 0)) {
        const useCot = n > m;
        // tan: S^m C^n du = w^m (1 + w^2)^(-(m+n)/2 - 1) dw
        const h = useCot
          ? canon(X.mul(X.neg(c), X.pow(w, X.num(n)), X.pow(X.add(ONE, X.pow(w, TWO)), X.num(-(m + n) / 2 - 1)), X.recip(a)))
          : canon(X.mul(c, X.pow(w, X.num(m)), X.pow(X.add(ONE, X.pow(w, TWO)), X.num(-(m + n) / 2 - 1)), X.recip(a)));
        const G = this.I(h, w);
        if (G) {
          const res = backSimp(canon(X.subs(G, { [w.name]: X.fn(useCot ? "cot" : "tan", u) })));
          this.step({ rule: "int.trig", title: `Substitute ${w.name} = ${useCot ? "cot" : "tan"}(${T(u)})`, why: `The powers of sin and cos have an even total, so the integrand is a rational function of ${useCot ? "cot" : "tan"}(${T(u)}).`, before, after: X.integral(h, w) });
          return res;
        }
      }
    }
    // tan^n alone (n >= 2): reduction tan^n = tan^(n-2) sec^2 - tan^(n-2)
    return this.bioche(f, x, g, S, Cs, u, a);
  }
  secReduction(f, x, u, a, c, n, kind) {
    // sec^n: sec^(n-2) tan/(n-1) + (n-2)/(n-1) int sec^(n-2); csc^n: -csc^(n-2) cot/(n-1) + (n-2)/(n-1) int csc^(n-2)
    const s = X.fn(kind, u), t = X.fn(kind === "sec" ? "tan" : "cot", u);
    const lower = canon(X.pow(s, X.num(n - 2)));
    const G = this.I(lower, x);
    if (!G) return null;
    const first = X.mul(kind === "sec" ? ONE : NEG_ONE, X.pow(s, X.num(n - 2)), t, X.num(1, n - 1), X.recip(a));
    const res = canon(X.mul(c, X.add(first, X.mul(X.num(n - 2, n - 1), G))));
    this.step({ rule: "int.trig", title: `Reduction formula for ${kind}^${n}`, why: kind === "sec" ? "sec^n u du = sec^(n-2) u tan u/(n-1) + (n-2)/(n-1) sec^(n-2) u du (integration by parts with dv = sec^2 u du)." : "csc^n u du = -csc^(n-2) u cot u/(n-1) + (n-2)/(n-1) csc^(n-2) u du.", before: X.integral(f, x), after: res });
    return res;
  }
  // Bioche's rules: choose w = cos, sin or tan by the symmetry of R(S, C); else Weierstrass
  bioche(f, x, g, S, Cs, u, a) {
    const [nt, dt] = P.numDen(canon(expandTogether(g)));
    if (!P.isPolynomial(nt, ["S__", "C__"]) || !P.isPolynomial(dt, ["S__", "C__"])) return null;
    const before = X.integral(f, x);
    const w = freshSym(f, "w");
    const same = (h1, h2) => canon(X.sub(h1, h2)) === ZERO || canon(expandTogether(X.sub(h1, h2))) === ZERO;
    const gS = canon(X.subs(g, { S__: X.neg(S) })), gC = canon(X.subs(g, { C__: X.neg(Cs) })), gSC = canon(X.subs(g, { S__: X.neg(S), C__: X.neg(Cs) }));
    const tries = [];
    if (same(gS, X.neg(g))) tries.push("cos");
    if (same(gC, X.neg(g))) tries.push("sin");
    if (same(gSC, g)) tries.push("tan");
    for (const kind of tries) {
      let h;
      if (kind === "cos") h = canon(X.subs(canon(X.div(g, X.mul(NEG_ONE, S))), { S__: X.sqrt(X.sub(ONE, X.pow(w, TWO))), C__: w }));
      else if (kind === "sin") h = canon(X.subs(canon(X.div(g, Cs)), { C__: X.sqrt(X.sub(ONE, X.pow(w, TWO))), S__: w }));
      else h = canon(X.div(X.subs(g, { S__: X.div(w, X.sqrt(X.add(ONE, X.pow(w, TWO)))), C__: X.recip(X.sqrt(X.add(ONE, X.pow(w, TWO)))) }), X.add(ONE, X.pow(w, TWO))));
      h = canon(X.div(h, a));
      if (!X.freeOf(h, S) || !X.freeOf(h, Cs) || collect(h, (n) => n.k === "pow" && !X.isInt(n.args[1]) && !X.freeOf(n, w)).length) continue;
      const G = this.I(h, w);
      if (!G) continue;
      const res = backSimp(canon(X.subs(G, { [w.name]: X.fn(kind, u) })));
      this.step({ rule: "int.trig", title: `Substitute ${w.name} = ${kind}(${T(u)})`, why: `The integrand is a rational function of sin and cos with the symmetry of Bioche's rule for ${kind}, so ${w.name} = ${kind}(${T(u)}) turns it into a rational function of ${w.name}.`, before, after: X.integral(h, w) });
      return res;
    }
    // Weierstrass t = tan(u/2)
    const t = freshSym(f, "t");
    const den = X.add(ONE, X.pow(t, TWO));
    const h = canon(expandTogether(X.mul(X.subs(g, { S__: X.div(X.mul(TWO, t), den), C__: X.div(X.sub(ONE, X.pow(t, TWO)), den) }), X.div(TWO, den), X.recip(a))));
    this.step({ rule: "int.weierstrass", title: `Weierstrass substitution ${t.name} = tan(${T(u)}/2)`, why: `sin u = 2t/(1 + t^2), cos u = (1 - t^2)/(1 + t^2), du = 2 dt/(1 + t^2) turn a rational function of sin and cos into a rational function of t. (The result is valid between the points where tan(u/2) is undefined.)`, before, after: X.integral(h, t) });
    const G = this.I(h, t);
    if (!G) return null;
    this.conditions.push(`valid on each interval where tan(${T(canon(X.mul(HALF, u)))}) is defined; the constant may differ between those intervals`);
    return backSimp(canon(X.subs(G, { [t.name]: X.fn("tan", canon(X.mul(HALF, u))) })));
  }
  productToSum(f, x, argsSet) {
    // only products of sin/cos of linear arguments (each at power 1), times constants
    const [c, rest] = splitConst(f, x);
    const fac = rest.k === "mul" ? rest.args : [rest];
    if (fac.length !== 2) {
      // powers like sin(x)^2 cos(2x): expand one power into a sum first
      return null;
    }
    const [p, q] = fac;
    if (p.k !== "fn" || q.k !== "fn" || !["sin", "cos"].includes(p.name) || !["sin", "cos"].includes(q.name)) return null;
    if (!linearCoeffs(p.args[0], x) && p.args[0] !== x) return null;
    if (!linearCoeffs(q.args[0], x) && q.args[0] !== x) return null;
    const A = p.args[0], Bv = q.args[0];
    const sum = X.add(A, Bv), dif = X.sub(A, Bv);
    let h;
    if (p.name === "sin" && q.name === "sin") h = X.mul(HALF, X.sub(X.fn("cos", dif), X.fn("cos", sum)));
    else if (p.name === "cos" && q.name === "cos") h = X.mul(HALF, X.add(X.fn("cos", dif), X.fn("cos", sum)));
    else if (p.name === "sin") h = X.mul(HALF, X.add(X.fn("sin", sum), X.fn("sin", dif)));
    else h = X.mul(HALF, X.add(X.fn("sin", sum), X.fn("sin", X.neg(dif))));
    h = canon(X.mul(c, h));
    this.step({ rule: "int.trig", title: "Product to sum", why: "sin A cos B = [sin(A + B) + sin(A - B)]/2 (and the analogous identities) turn the product into a sum of single sines and cosines.", before: X.integral(f, x), after: X.integral(h, x) });
    void argsSet;
    return this.I(h, x);
  }

  // ------------------------------------------------ layer 8/9: sqrt of a quadratic (trig substitution / Euler)
  radicalQuadratic(f, x) {
    const rads = collect(f, (w) => w.k === "pow" && X.isNum(w.args[1]) && w.args[1].v.d === 2n && !X.freeOf(w.args[0], x));
    if (!rads.length) return null;
    const Qd = rads[0].args[0];
    if (!rads.every((r) => r.args[0] === Qd)) return null;
    const cq = polyCoeffs(Qd, x);
    if (!cq || cq.length !== 3 || !cq.every(X.isNum)) return null;
    const [c0, b0, a0] = cq.map((t) => t.v);
    // complete the square: a (x + h)^2 + k
    const h = N.div(b0, N.mul(N.Q(2), a0));
    const k = N.sub(c0, N.div(N.mul(b0, b0), N.mul(N.Q(4), a0)));
    const th = freshSym(f, "t");
    const before = X.integral(f, x);
    if (N.isNeg(a0) && N.isPos(k)) {
      // Q = k - |a| (x + h)^2 ; x + h = sqrt(k/|a|) sin t ; sqrt(Q) = sqrt(k) cos t
      const A = canon(X.sqrt(X.num(N.div(k, N.neg(a0)))));
      const xs = canon(X.sub(X.mul(A, X.fn("sin", th)), X.num(h)));
      const sq = canon(X.mul(X.sqrt(X.num(k)), X.fn("cos", th)));
      const g = this.subRadical(f, x, Qd, sq, xs, th);
      if (!g) return null;
      const G = this.I(g, th);
      if (!G) return null;
      const z = canon(X.div(X.add(x, X.num(h)), A));
      let res = backSimp(canon(X.subs(expandMultiAngle(G), { [th.name]: X.fn("asin", z) })));
      res = rebaseRadical(res, X.sub(ONE, X.pow(z, TWO)), Qd, k);
      this.step({ rule: "int.trigsub", title: `Trigonometric substitution ${T(canon(X.add(x, X.num(h))))} = ${T(A)} sin(${th.name})`, why: `Completing the square gives ${T(canon(X.sub(X.num(k), X.mul(X.num(N.neg(a0)), X.pow(X.add(x, X.num(h)), TWO)))))}; with this substitution the square root becomes ${T(sq)} (cos t >= 0 for t in [-pi/2, pi/2]).`, before, after: X.integral(g, th) });
      this.step({ rule: "int.trigsub", title: "Back-substitute", why: `t = asin(${T(z)}); cos(asin z) = sqrt(1 - z^2).`, before: G, after: res });
      return res;
    }
    if (N.isPos(a0) && !N.isZero(k)) {
      // standard forms (hyperbolic substitution): with u = x + h and R = sqrt(Q),
      //   R dx = u R/2 + k/(2 sqrt a) ln|sqrt(a) u + R|,   dx/R = ln|sqrt(a) u + R|/sqrt(a)
      const [cst, rest] = splitConst(f, x);
      const R = X.sqrt(Qd), sa = canon(X.sqrt(X.num(a0)));
      const u = canon(X.add(x, X.num(h)));
      const L = X.fn("ln", X.fn("abs", X.add(X.mul(sa, u), R)));
      let res = null;
      if (rest === R) res = canon(X.mul(cst, X.add(X.mul(HALF, u, R), X.mul(X.num(k), X.recip(X.mul(TWO, sa)), L))));
      else if (rest === X.pow(Qd, X.num(-1, 2))) res = canon(X.mul(cst, X.recip(sa), L));
      if (res) {
        this.step({ rule: "int.trigsub", title: "Standard form for a square root of a quadratic", why: `Completing the square gives ${T(canon(X.add(X.mul(X.num(a0), X.pow(u, TWO)), X.num(k))))}; the hyperbolic substitution ${T(u)} = ${T(canon(X.sqrt(X.num(N.abs(N.div(k, a0))))))} ${N.isPos(k) ? "sinh" : "cosh"}(t) gives the standard antiderivative, written with logarithms.`, before, after: res });
        return res;
      }
    }
    if (N.isPos(a0) && N.isPos(k)) {
      // x + h = sqrt(k/a) tan t, sqrt(Q) = sqrt(k) sec t (sec t > 0 for t in (-pi/2, pi/2))
      const r = this.attempt(() => {
        const A = canon(X.sqrt(X.num(N.div(k, a0))));
        const xs = canon(X.sub(X.mul(A, X.fn("tan", th)), X.num(h)));
        const sq = canon(X.mul(X.sqrt(X.num(k)), X.fn("sec", th)));
        const g = this.subRadical(f, x, Qd, sq, xs, th);
        if (!g) return null;
        const G = this.I(g, th);
        if (!G) return null;
        const z = canon(X.div(X.add(x, X.num(h)), A));
        let res = backSimp(canon(X.subs(expandMultiAngle(G), { [th.name]: X.fn("atan", z) })));
        res = rebaseRadical(res, X.add(ONE, X.pow(z, TWO)), Qd, k);
        if (!X.freeOf(res, th)) return null;
        this.step({ rule: "int.trigsub", title: `Trigonometric substitution ${T(canon(X.add(x, X.num(h))))} = ${T(A)} tan(${th.name})`, why: `Completing the square gives ${T(canon(X.add(X.mul(X.num(a0), X.pow(X.add(x, X.num(h)), TWO)), X.num(k))))}; with this substitution the square root becomes ${T(sq)} (sec t > 0 for t in (-pi/2, pi/2)).`, before, after: X.integral(g, th) });
        this.step({ rule: "int.trigsub", title: "Back-substitute", why: `t = atan(${T(z)}); sec(atan z) = sqrt(1 + z^2), sin(atan z) = z/sqrt(1 + z^2).`, before: G, after: res });
        return res;
      });
      if (r) return r;
    }
    if (N.isPos(a0)) return this.euler(f, x, Qd, a0, b0, c0);
    return null;
  }
  // replace sqrt(Q)^k by sq^k and x by xs; dx = xs' dt
  subRadical(f, x, Qd, sq, xs, th) {
    const r = X.mapTree(f, (w) => (w.k === "pow" && w.args[0] === Qd && X.isNum(w.args[1]) ? X.pow(sq, X.num(N.mul(w.args[1].v, N.Q(2)))) : w));
    // only the radical replacements may carry the old base
    const inner = X.subs(r, { [x.name]: xs });
    const g = canon(X.mul(inner, D(xs, th)));
    if (!X.freeOf(g, x)) return null;
    return g;
  }
  euler(f, x, Qd, a0, b0, c0) {
    // sqrt(a x^2 + b x + c) = sqrt(a) sqrt(x^2 + p x + q); sqrt(x^2 + p x + q) = t - x
    const p = N.div(b0, a0), q = N.div(c0, a0);
    const t = freshSym(f, "t");
    const den = X.add(X.num(p), X.mul(TWO, t));
    const xs = canon(X.div(X.sub(X.pow(t, TWO), X.num(q)), den));
    const sq1 = canon(X.div(X.add(X.pow(t, TWO), X.mul(X.num(p), t), X.num(q)), den)); // t - x
    const sq = canon(X.mul(X.sqrt(X.num(a0)), sq1));
    const g0 = this.subRadical(f, x, Qd, sq, xs, t);
    if (!g0) return null;
    const g = canon(expandTogether(g0));
    const G = this.I(g, t);
    if (!G) return null;
    const back = canon(X.add(x, X.sqrt(X.add(X.pow(x, TWO), X.mul(X.num(p), x), X.num(q)))));
    const res = canon(X.subs(G, { [t.name]: back }));
    this.step({ rule: "int.euler", title: `Euler substitution ${t.name} = x + sqrt(${T(canon(X.add(X.pow(x, TWO), X.mul(X.num(p), x), X.num(q))))})`, why: "Squaring sqrt(x^2 + p x + q) = t - x gives x as a rational function of t, so the integrand becomes a rational function of t.", before: X.integral(f, x), after: X.integral(g, t) });
    this.step({ rule: "int.euler", title: "Substitute back", why: `t = ${T(back)}.`, before: G, after: res });
    return res;
  }

  // ------------------------------------------------ hyperbolic functions -> exponentials
  hyperbolic(f, x) {
    const hs = collect(f, (w) => w.k === "fn" && HYP.has(w.name) && !X.freeOf(w, x));
    if (!hs.length) return null;
    const g = canon(X.mapTree(f, (w) => {
      if (w.k !== "fn" || !HYP.has(w.name)) return w;
      const u = w.args[0], ep = X.exp(u), em = X.exp(X.neg(u));
      switch (w.name) {
        case "sinh": return X.mul(HALF, X.sub(ep, em));
        case "cosh": return X.mul(HALF, X.add(ep, em));
        case "tanh": return X.div(X.sub(ep, em), X.add(ep, em));
        case "coth": return X.div(X.add(ep, em), X.sub(ep, em));
        case "sech": return X.div(TWO, X.add(ep, em));
        case "csch": return X.div(TWO, X.sub(ep, em));
        default: return w;
      }
    }));
    const e = canon(expandC(g));
    this.step({ rule: "int.table", title: "Write hyperbolic functions with exponentials", why: "sinh u = (e^u - e^-u)/2, cosh u = (e^u + e^-u)/2.", before: X.integral(f, x), after: X.integral(e, x) });
    return this.I(e, x);
  }

  // ------------------------------------------------ heuristic Risch-Norman (only at the top levels)
  norman(f, x) {
    if (this.depth > 2) return null;
    const F = normanIntegrate(f, x, { tick: () => this.tick() });
    if (!F) return null;
    this.step({ rule: "int.risch", title: "Undetermined coefficients (Risch-Norman ansatz)", why: "Try F as a combination of products of the functions that occur in the integrand (and their derivatives' partners), with unknown constant coefficients; matching F' with the integrand fixes the coefficients, and F' = f is then checked.", before: X.integral(f, x), after: F });
    return F;
  }

  // ------------------------------------------------ layer 10: special functions
  specialFn(f, x) {
    const r = specialIntegral(f, x, this);
    if (!r) return null;
    if (r.nonelementary && !r.F) { this.noteNonelementary(f, r.proof); return null; }
    this.special = true;
    if (r.proof) this.noteNonelementary(f, r.proof);
    this.step({ rule: "int.special", title: r.title, why: r.why, before: X.integral(f, x), after: r.F });
    return r.F;
  }
}

// sign of a constant expression under assumptions (1, -1, 0 or null)
function constSign(u, assume) {
  if (!X.freeSymbols(u).size) {
    const v = evalD(u, {});
    if (!Number.isFinite(v)) return null;
    return v > 1e-12 ? 1 : v < -1e-12 ? -1 : canon(u) === ZERO ? 0 : null;
  }
  if (assume) {
    const ctx = makeCtx({ assume });
    try {
      const s = simplify(X.fn("sign", u), ctx);
      if (X.isNum(s)) return Number(s.v.n);
    } catch (_) { /* ignore */ }
  }
  return null;
}

function expandTogether(u) {
  try {
    const [n, d] = togetherND(u);
    // cancel a univariate gcd when possible
    const vs = [...X.freeSymbols(d)];
    if (vs.length === 1 && d !== ONE) {
      try {
        const pn = P.fromTree(n, vs[0]), pd = P.fromTree(d, vs[0]);
        if (pn && pd) {
          const g = P.gcd(pn, pd);
          if (g.length > 1) return canon(X.div(P.toTree(P.exactDiv(pn, g), vs[0]), P.toTree(P.exactDiv(pd, g), vs[0])));
        }
      } catch (e) { if (e && e.code === "BUDGET") throw e; }
    }
    return canon(X.div(n, d));
  } catch (e) { if (e && e.code === "BUDGET") return u; throw e; }
}
function combine(u) {
  // common denominator of a sum (products of denominators; fine for small inputs)
  const parts = u.args.map((t) => P.numDen(t));
  let den = ONE;
  for (const [, d] of parts) if (d !== ONE) den = X.mul(den, d);
  den = canon(den);
  const num = canon(X.add(...parts.map(([n, d]) => X.mul(n, X.div(den, d)))));
  return canon(X.div(num, den));
}

// r / f when it is free of x (a constant), else null
function ratioConst(r, f, x) {
  try {
    const q = canon(X.div(r, f));
    if (X.freeOf(q, x) && q !== X.UNDEF) return q;
    const q2 = canon(expandTogether(q));
    if (X.freeOf(q2, x) && q2 !== X.UNDEF) return q2;
  } catch (e) { if (e.code !== "BUDGET") throw e; }
  return null;
}

// h rational in x and g a polynomial: write numerator and denominator as polynomials in g (g-adic
// expansion with constant digits); returns the rational function of t or null
function polyInG(h, g, x, t) {
  let gp;
  try { gp = P.fromTree(g, x.name); } catch (e) { if (e && e.code === "BUDGET") return null; throw e; }
  if (!gp || gp.length < 3) return null;
  let parts;
  try { parts = togetherND(h); } catch (e) { if (e && e.code === "BUDGET") return null; throw e; }
  let pn, pd;
  try { pn = P.fromTree(parts[0], x.name); pd = P.fromTree(parts[1], x.name); } catch (e) { if (e && e.code === "BUDGET") return null; throw e; }
  if (!pn || !pd || !pd.length) return null;
  const gg = P.gcd(pn, pd);
  if (gg.length > 1) { pn = P.exactDiv(pn, gg); pd = P.exactDiv(pd, gg); }
  const conv = (p) => {
    const digits = [];
    for (let guard = 0; p.length && guard < 60; guard++) {
      const { q, r } = P.divmod(p, gp);
      if (r.length > 1) return null;
      digits.push(r.length ? r[0] : N.ZERO);
      p = q;
    }
    if (p.length) return null;
    return canon(X.add(...digits.map((c, i) => X.mul(X.num(c), X.pow(t, X.num(i))))));
  };
  const nt = conv(pn), dt = conv(pd);
  if (!nt || !dt) return null;
  return canon(X.div(nt, dt));
}

// c S^m C^n with integer m, n ?
function monomialSC(g, S, C) {
  let m = 0, n = 0;
  const fac = g.k === "mul" ? g.args : [g];
  const consts = [];
  for (const w of fac) {
    if (w === ONE) continue;
    if (X.freeOf(w, S) && X.freeOf(w, C)) { consts.push(w); continue; }
    const [b, e] = w.k === "pow" ? w.args : [w, ONE];
    if (!X.isInt(e)) return null;
    if (b === S) m += Number(e.v.n); else if (b === C) n += Number(e.v.n); else return null;
  }
  if (Math.abs(m) > 40 || Math.abs(n) > 40) return null;
  return { c: canon(X.mul(ONE, ...consts)), m, n };
}

// ---------------------------------------------------------------- public entry
export function integrate(f, x, opts = {}) {
  const xs = typeof x === "string" ? X.sym(x) : x;
  const log = new StepLog();
  const f0 = canon(f);
  if (f0 === X.UNDEF) throw intError("UNSUPPORTED", "The integrand is undefined.");
  const eng = new Engine({ ...opts, steps: log });
  let F = null, err = null;
  try { F = eng.I(f0, xs); } catch (e) {
    if (e && (e.code === "BUDGET" || e.code === "TIMEOUT" || e.code === "UNSUPPORTED")) err = e;
    else if (e instanceof RangeError && /call stack/i.test(e.message)) err = intError("UNSUPPORTED", "Quelvra: the simplifier could not handle an intermediate expression");
    else throw e;
  }
  if (!F && !eng.neProofs.get(f0)) {
    // last resort after a failure or an exhausted budget: the Risch-Norman ansatz on its own budget
    try {
      const G = normanIntegrate(f0, xs, {});
      if (G) { F = G; err = null; log.add({ rule: "int.risch", title: "Undetermined coefficients (Risch-Norman ansatz)", why: "Try F as a combination of products of the functions that occur in the integrand, with unknown constant coefficients; matching F' with the integrand fixes them.", before: X.integral(f0, xs), after: G }); }
    } catch (e) { if (!e || !e.code) { if (!(e instanceof RangeError)) throw e; } }
  }
  if (!F) {
    const proof = eng.neProofs.get(f0);
    if (proof) throw intError("NONELEMENTARY", `This integral has no elementary antiderivative. ${proof}`, { proof });
    if (err) throw err;
    throw intError("UNSUPPORTED", "Quelvra could not find an antiderivative with its methods. This does not prove that none exists.");
  }
  F = backSimp(F);
  // presentation: prefer the expanded form when it is shorter (it must pass the same checks)
  const cands = [];
  try {
    const Fe = backSimp(canon(expandC(F)));
    if (Fe !== F && Fe !== X.UNDEF && T(Fe).length < T(F).length) cands.push(Fe);
  } catch (e) { if (!e || (e.code !== "BUDGET" && e.code !== "TIMEOUT")) throw e; }
  cands.push(F);
  let chk = null, vres = null, lastErr = null;
  for (const G of cands) {
    const c = checkAntiderivative(G, f0, xs, { positive: opts.positive });
    if (c.ok !== true) { lastErr = intError("UNSUPPORTED", `The candidate antiderivative ${T(G)} failed the independent check (${c.detail}); Quelvra does not return unverified answers.`, { rejected: G, check: c }); continue; }
    // second, fully independent check with the verifier (differentiation + its own evaluator) when it can evaluate G
    let v = null;
    if (!usesSpecial(G)) {
      v = verifyAntiderivative(G, f0, xs.name, { diffFn: (u, w) => diff(u, w) });
      if (v.status === "failed") { lastErr = intError("UNSUPPORTED", `The candidate antiderivative ${T(G)} failed verification.`, { rejected: G, check: v }); continue; }
    }
    F = G; chk = c; vres = v; lastErr = null; break;
  }
  if (lastErr) throw lastErr;
  if (opts.steps && opts.steps !== NO_STEPS) for (const st of log.steps) opts.steps.add(st);
  const conditions = [];
  for (const c of eng.conditions) if (!conditions.includes(c)) conditions.push(c);
  const method = mainMethod(log.steps || []);
  return { F, method, steps: log.steps || [], conditions, special: eng.special || usesSpecial(F), nonelementary: eng.neProofs.get(f0) || null, check: chk, verifier: vres };
}
function mainMethod(steps) {
  const order = ["int.risch", "int.special", "int.weierstrass", "int.euler", "int.trigsub", "int.parts", "int.trig", "int.partial", "int.usub", "int.poly", "int.linear", "int.table"];
  const seen = new Set();
  const walk = (ss) => { for (const s of ss) { seen.add(s.rule); if (s.sub) walk(s.sub); } };
  walk(steps);
  for (const r of order) if (seen.has(r)) return r;
  return "int.table";
}

export { Engine };
