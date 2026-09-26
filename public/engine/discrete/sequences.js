// Recurrences, generating functions, series coefficients and sequence identification.
//
//   rsolve(a(n) = ..., a(0) = .., ...)      closed form of a linear recurrence (solver: calc/recur.js)
//   genfunc(recurrence equations...)        ordinary generating function of a C-finite sequence
//   genfunc(term, n)                        ... of an explicit quasi-polynomial term (sum P(n) mu^n)
//   seriescoeff(f, x, k)                    coefficient of x^k in the power series of a rational f
//   findsequence(t0, t1, ...)               polynomial or linear-recurrence pattern (a conjecture)
//
// Independent checks:
//   rsolve       the recurrence is iterated directly from the initial conditions (exact rationals)
//                and the closed form is evaluated exactly (in Q or a quadratic field Q(sqrt d)) at
//                the same 20 indices; when no exact evaluation is possible the comparison is made
//                to 40+ significant digits and said so.
//   genfunc      the sequence is C-finite of order <= d (d from the recurrence order plus the
//                annihilator of the right-hand side, or from the quasi-polynomial term); the
//                rational function has a denominator of degree L; two C-finite sequences of orders
//                <= d and <= L that agree on d + L consecutive terms are equal, so the series of
//                P/Q is expanded by long division and compared with the directly computed terms.
//   seriescoeff  the truncated series is multiplied back by the denominator and compared with the
//                numerator mod x^(k+1) (which determines the series uniquely when Q(0) != 0).
//   findsequence the formula (or recurrence) is re-evaluated on every given term; the next term is
//                computed by a second route (difference table / recurrence vs formula). The result
//                is labelled as a pattern that fits, not a proof.

import { refuse, ansText, ansTree, check, step, N, X } from "./util.js";
import { ratOf, intOf } from "./decode.js";
import { simplify } from "../simplify.js";
import { detectRecurrence, solveRecurrence, verifyRecurrence } from "../calc/recur.js";
import { hp, log10Abs } from "../calc/cutil.js";
import { toText } from "../print.js";

const Z = N.ZERO, ONE = N.ONE;
const qs = (r) => N.toString(r);
const simpNum = (u) => { let s; try { s = simplify(u); } catch (_) { return null; } return s && s.k === "num" ? s.v : null; };

// ---------------------------------------------------------------- rational polynomials (index = power)
const ptrim = (a) => { const r = a.slice(); while (r.length && N.isZero(r[r.length - 1])) r.pop(); return r; };
const padd = (a, b) => ptrim(Array.from({ length: Math.max(a.length, b.length) }, (_, i) => N.add(a[i] || Z, b[i] || Z)));
const pscale = (a, c) => ptrim(a.map((x) => N.mul(x, c)));
const pneg = (a) => pscale(a, N.NEG_ONE);
function pmul(a, b) {
  if (!a.length || !b.length) return [];
  const r = Array(a.length + b.length - 1).fill(Z);
  for (let i = 0; i < a.length; i++) if (!N.isZero(a[i])) for (let j = 0; j < b.length; j++) r[i + j] = N.add(r[i + j], N.mul(a[i], b[j]));
  return ptrim(r);
}
function ptree(cs, x) {
  const xs = X.sym(x);
  const terms = [];
  for (let i = 0; i < cs.length; i++) if (!N.isZero(cs[i])) terms.push(i === 0 ? X.num(cs[i]) : X.mul(X.num(cs[i]), i === 1 ? xs : X.pow(xs, X.num(i))));
  return terms.length ? X.add(...terms) : X.ZERO;
}
// power series of P/Q to `count` terms (Q(0) != 0)
function seriesDiv(P, Qp, count) {
  if (!Qp.length || N.isZero(Qp[0])) throw refuse("the denominator vanishes at x = 0");
  const out = [];
  const q0 = Qp[0];
  for (let k = 0; k < count; k++) {
    let s = P[k] || Z;
    for (let j = 1; j < Qp.length && j <= k; j++) s = N.sub(s, N.mul(Qp[j], out[k - j]));
    out.push(N.div(s, q0));
  }
  return out;
}

// ---------------------------------------------------------------- rational functions of x
function ratFun(u, x) {
  switch (u.k) {
    case "num": return { P: ptrim([u.v]), Q: [ONE] };
    case "sym": if (u.name === x) return { P: [Z, ONE], Q: [ONE] }; throw refuse(`unexpected symbol ${u.name}; expected a rational function of ${x}`);
    case "add": return u.args.map((a) => ratFun(a, x)).reduce((s, t) => ({ P: padd(pmul(s.P, t.Q), pmul(t.P, s.Q)), Q: pmul(s.Q, t.Q) }));
    case "mul": return u.args.map((a) => ratFun(a, x)).reduce((s, t) => ({ P: pmul(s.P, t.P), Q: pmul(s.Q, t.Q) }));
    case "pow": {
      const e = ratOf(u.args[1]);
      if (!e || e.d !== 1n) throw refuse("only integer powers are supported in a rational function");
      if (N.isZero(e) ) return { P: [ONE], Q: [ONE] };
      if (e.n > 2000n || e.n < -2000n) throw refuse("the power is too large");
      const b = ratFun(u.args[0], x);
      let P = [ONE], Qp = [ONE];
      const k = e.n < 0n ? -e.n : e.n;
      for (let i = 0n; i < k; i++) { P = pmul(P, b.P); Qp = pmul(Qp, b.Q); }
      if (!P.length && e.n < 0n) throw refuse("division by zero");
      return e.n < 0n ? { P: Qp, Q: P } : { P, Q: Qp };
    }
    default: {
      const r = ratOf(u);
      if (r) return { P: ptrim([r]), Q: [ONE] };
      throw refuse(`expected a rational function of ${x}`);
    }
  }
}

// ---------------------------------------------------------------- Berlekamp-Massey over Q
// returns connection coefficients c[1..L] with s(n) = sum c_j s(n - j) for n >= L
function berlekampMassey(s) {
  let C = [ONE], B = [ONE];
  let L = 0, m = 1, b = ONE;
  for (let n = 0; n < s.length; n++) {
    let d = s[n];
    for (let i = 1; i <= L; i++) d = N.add(d, N.mul(C[i] || Z, s[n - i]));
    if (N.isZero(d)) { m++; continue; }
    const coef = N.div(d, b);
    const T = C.slice();
    const shifted = Array(m).fill(Z).concat(B.map((v) => N.mul(v, coef)));
    const nc = [];
    for (let i = 0; i < Math.max(C.length, shifted.length); i++) nc.push(N.sub(C[i] || Z, shifted[i] || Z));
    C = nc;
    if (2 * L <= n) { L = n + 1 - L; B = T; b = d; m = 1; } else m++;
  }
  const c = [];
  for (let j = 1; j <= L; j++) c.push(N.neg(C[j] || Z));
  return { L, c };
}

// ---------------------------------------------------------------- exact evaluation in Q(sqrt d)
function squarefreeSplit(n) { // n > 0 bigint -> [s, f] with n = s^2 f, f squarefree
  let s = 1n, f = 1n, m = n;
  for (let p = 2n; p * p <= m; p++) {
    if (p > 1000000n) throw refuse("radicand too large");
    let e = 0;
    while (m % p === 0n) { m /= p; e++; }
    for (let i = 0; i < Math.floor(e / 2); i++) s *= p;
    if (e % 2) f *= p;
  }
  f *= m;
  return [s, f];
}
function evalQuad(u, env) {
  let D = null; // the radicand (squarefree, != 1), fixed for the whole evaluation
  const E = (a, b = Z) => ({ a, b });
  const need = (d) => { if (D === null) D = d; else if (D !== d) throw refuse("two different radicals"); };
  const add = (p, q) => E(N.add(p.a, q.a), N.add(p.b, q.b));
  const mul = (p, q) => E(N.add(N.mul(p.a, q.a), D === null ? Z : N.mul(N.mul(p.b, q.b), N.Q(D))), N.add(N.mul(p.a, q.b), N.mul(p.b, q.a)));
  const inv = (p) => {
    const nrm = N.sub(N.mul(p.a, p.a), D === null ? Z : N.mul(N.mul(p.b, p.b), N.Q(D)));
    if (N.isZero(nrm)) throw refuse("division by zero");
    return E(N.div(p.a, nrm), N.neg(N.div(p.b, nrm)));
  };
  const sqrtR = (r) => {
    if (N.isZero(r)) return E(Z);
    const sg = r.n < 0n ? -1n : 1n;
    const [s, f] = squarefreeSplit((r.n < 0n ? -r.n : r.n) * r.d);
    const coef = N.Q(s, r.d);
    if (f === 1n && sg > 0n) return E(coef);
    need(sg * f);
    return E(Z, coef);
  };
  const go = (w) => {
    switch (w.k) {
      case "num": return E(w.v);
      case "sym": if (w.name in env) return E(env[w.name]); throw refuse(`unbound ${w.name}`);
      case "const": if (w.name === "I") { need(-1n); return E(Z, ONE); } throw refuse("constant");
      case "add": return w.args.map(go).reduce(add);
      case "mul": return w.args.map(go).reduce(mul);
      case "fn": if (w.name === "sqrt" && w.args.length === 1) { const v = go(w.args[0]); if (!N.isZero(v.b)) throw refuse("nested radical"); return sqrtR(v.a); } throw refuse("function");
      case "pow": {
        const ev = go(w.args[1]);
        if (!N.isZero(ev.b)) throw refuse("irrational exponent");
        const e = ev.a;
        const base = go(w.args[0]);
        if (e.d === 2n && e.n === 1n) { if (!N.isZero(base.b)) throw refuse("nested radical"); return sqrtR(base.a); }
        if (e.d !== 1n) throw refuse("fractional power");
        if (e.n > 10000n || e.n < -10000n) throw refuse("power too large");
        let k = e.n < 0n ? -e.n : e.n, r = E(ONE), b = base;
        while (k > 0n) { if (k & 1n) r = mul(r, b); b = mul(b, b); k >>= 1n; }
        return e.n < 0n ? inv(r) : r;
      }
      default: throw refuse("unsupported node");
    }
  };
  return go(u);
}
// does tree(n = m) equal the rational v?  -> "exact" | "numeric" | false | null (undecided)
function agrees(tree, n, m, v) {
  try {
    const q = evalQuad(tree, { [n]: N.Q(BigInt(m)) });
    return N.isZero(q.b) && N.eq(q.a, v) ? "exact" : false;
  } catch (e) { if (e && e.code !== "UNSUPPORTED") throw e; }
  const s = simpNum(X.subs(tree, { [n]: X.num(m) }));
  if (s) return N.eq(s, v) ? "exact" : false;
  const d = hp(X.sub(X.subs(tree, { [n]: X.num(m) }), X.num(v)), {}, { digits: 60, maxDigits: 200 });
  if (!d.ok || !d.big) return null;
  const mag = Math.max(0, Math.log10(Math.max(1, Math.abs(N.toFloat(v)))));
  return log10Abs(d.big) - mag < -40 ? "numeric" : false;
}

// ---------------------------------------------------------------- recurrence iteration
// info from detectRecurrence: main is sum c_j __r{j} - g(n) (in some arrangement) = 0.
function iterate(info, count) {
  const { n, main, shifts, ics } = info;
  const j0 = shifts[0], j1 = shifts[shifts.length - 1];
  const order = j1 - j0;
  const vals = new Map();
  for (const ic of ics) {
    const v = ic.value.k === "num" ? ic.value.v : simpNum(ic.value);
    if (!v) throw refuse("the initial conditions must be rational numbers");
    vals.set(ic.at, v);
  }
  if (vals.size !== order) throw refuse(`a recurrence of order ${order} needs ${order} initial values`);
  const i0 = [...vals.keys()].reduce((a, b) => (a < b ? a : b));
  for (let i = 0; i < order; i++) if (!vals.has(i0 + BigInt(i))) throw refuse("the initial values must be at consecutive indices");
  const out = [];
  for (let i = 0; i < order && out.length < count; i++) out.push(vals.get(i0 + BigInt(i)));
  for (let t = i0 + BigInt(order); out.length < count; t++) {
    const n0 = t - BigInt(j1);
    const sub = { [n]: X.num(N.Q(n0)) };
    for (const j of shifts) if (j !== j1) sub[`__r${j}`] = X.num(out[Number(n0 + BigInt(j) - i0)]);
    const at = (s) => simpNum(X.subs(main, { ...sub, [`__r${j1}`]: X.num(s) }));
    const d0 = at(Z), d1 = at(ONE);
    if (!d0 || !d1) throw refuse("the recurrence does not evaluate to rational numbers");
    const c = N.sub(d1, d0);
    if (N.isZero(c)) throw refuse(`the leading coefficient vanishes at ${info.F}(${t})`);
    out.push(N.neg(N.div(d0, c)));
  }
  return { start: i0, terms: out };
}

// ---------------------------------------------------------------- quasi-polynomials sum P(n) mu^n
// tree -> Map(key -> {mu: Rational, deg}) giving the C-finite order bound, or null
function quasiPoly(u, n) {
  const one = () => new Map([["1", { mu: ONE, deg: 0 }]]);
  const merge = (A, B) => { const r = new Map(A); for (const [k, v] of B) { const w = r.get(k); r.set(k, w ? { mu: v.mu, deg: Math.max(w.deg, v.deg) } : v); } return r; };
  const prod = (A, B) => {
    const r = new Map();
    for (const a of A.values()) for (const b of B.values()) {
      const mu = N.mul(a.mu, b.mu), k = qs(mu), deg = a.deg + b.deg, w = r.get(k);
      r.set(k, w ? { mu, deg: Math.max(w.deg, deg) } : { mu, deg });
    }
    return r;
  };
  const go = (w) => {
    if (!X.hasSym(w, n)) {
      if (X.freeSymbols(w).size) return null;
      return ratOf(w) ? one() : null;
    }
    switch (w.k) {
      case "sym": return new Map([["1", { mu: ONE, deg: 1 }]]);
      case "add": { let r = new Map(); for (const a of w.args) { const q = go(a); if (!q) return null; r = merge(r, q); } return r; }
      case "mul": { let r = one(); for (const a of w.args) { const q = go(a); if (!q) return null; r = prod(r, q); if (r.size > 40) return null; } return r; }
      case "pow": {
        const [b, e] = w.args;
        if (!X.hasSym(b, n)) {
          const base = ratOf(b);
          if (!base || N.isZero(base)) return null;
          // exponent must be a n + c with a non-negative integer a
          const a = simpNum(X.sub(X.subs(e, { [n]: X.ONE }), X.subs(e, { [n]: X.ZERO })));
          const c = simpNum(X.subs(e, { [n]: X.ZERO }));
          if (!a || !c || a.d !== 1n || a.n < 0n || a.n > 64n) return null;
          const chk = simpNum(X.sub(X.sub(e, X.mul(X.num(a), X.sym(n))), X.num(c)));
          if (!chk || !N.isZero(chk)) return null;
          if (c.d !== 1n) return null;
          const mu = N.pow(base, Number(a.n));
          return new Map([[qs(mu), { mu, deg: 0 }]]);
        }
        const k = ratOf(e);
        if (!k || k.d !== 1n || k.n < 0n || k.n > 60n) return null;
        let r = one(); const q = go(b); if (!q) return null;
        for (let i = 0n; i < k.n; i++) { r = prod(r, q); if (r.size > 40) return null; }
        return r;
      }
      default: return null;
    }
  };
  const r = go(u);
  if (!r) return null;
  let d = 0;
  for (const v of r.values()) d += v.deg + 1;
  return { d, parts: r };
}

// ---------------------------------------------------------------- rsolve
function eqsOf(args) {
  if (!args.length || !args.every((a) => a.k === "eq")) return null;
  return detectRecurrence(args.length === 1 ? args[0] : X.system(...args));
}
function cmdRsolve(args, env) {
  const info = eqsOf(args);
  if (!info) throw refuse("rsolve expects a recurrence such as a(n) = 2a(n-1) + 1 and initial values a(0) = 1");
  const res = solveRecurrence(info, { timeLimit: env && env.timeLimit ? Math.min(10000, env.timeLimit) : 10000 });
  const label = `${info.F}(${info.n})`;
  const steps = [step("rsolve", `Solve the recurrence (${res.method || "linear recurrence"})`, "Characteristic roots, a particular solution, then the constants from the initial values."), ...(res.steps || [])];
  const freeConsts = (res.constants || []).filter((C) => !(res.constantsSolved && res.constantsSolved[C.name]));
  return {
    answers: [ansTree(label, res.value)], steps,
    note: freeConsts.length ? "Arbitrary constants remain because not enough initial values were given." : "",
    checks: () => {
      if (freeConsts.length) {
        const v = verifyRecurrence(info, res);
        return [check("recurrence residual", v.status === "verified-exact", `general solution substituted into the recurrence (${v.status})`)];
      }
      const { start, terms } = iterate(info, 20);
      let exact = 0, numeric = 0;
      for (let i = 0; i < terms.length; i++) {
        const m = Number(start) + i;
        const a = agrees(res.value, info.n, m, terms[i]);
        if (!a) return [check("direct iteration", false, `the closed form gives a different value at ${info.F}(${m}) than iterating the recurrence (${qs(terms[i])})`)];
        if (a === "exact") exact++; else numeric++;
      }
      return [{ ...(numeric ? { method: "numeric" } : {}), ...check("direct iteration", true, `the recurrence was iterated exactly from the initial values; the closed form matches all ${terms.length} terms ${info.F}(${start}) .. ${info.F}(${Number(start) + terms.length - 1}) (${numeric ? `${exact} exactly, ${numeric} to 40+ digits` : "exactly"})`) }];
    },
  };
}

// ---------------------------------------------------------------- genfunc
function gfVar(used) { return ["x", "z", "t", "s"].find((v) => !used.has(v)); }
function cmdGenfunc(args) {
  let terms, dBound, source, gx;
  if (args.length && args.every((a) => a.k === "eq")) {
    const info = eqsOf(args);
    if (!info) throw refuse("genfunc expects a recurrence with initial values, or an explicit term and its index, e.g. genfunc(n^2, n)");
    const { n, main, shifts } = info;
    const j0 = shifts[0], j1 = shifts[shifts.length - 1];
    // constant coefficients and a quasi-polynomial right-hand side
    const zero = Object.fromEntries(shifts.map((j) => [`__r${j}`, X.ZERO]));
    const rest = simplify(X.subs(main, zero));
    for (const j of shifts) {
      const cj = simplify(X.sub(X.subs(main, { ...zero, [`__r${j}`]: X.ONE }), rest));
      if (X.hasSym(cj, n) || !ratOf(cj)) throw refuse("generating functions are computed for constant-coefficient recurrences");
    }
    const rv = simpNum(rest);
    const qp = rv && N.isZero(rv) ? { d: 0 } : quasiPoly(rest, n);
    if (!qp) throw refuse("the right-hand side must be a sum of polynomial times exponential terms");
    const it = iterate(info, 1);
    if (it.start !== 0n) throw refuse("give the initial values starting at index 0");
    dBound = (j1 - j0) + qp.d;
    const count = 2 * dBound + 8;
    terms = iterate(info, count).terms;
    source = `the recurrence of order ${j1 - j0}${qp.d ? ` with a right-hand side annihilated by an operator of order ${qp.d}` : ""}`;
    gx = gfVar(new Set([n]));
  } else {
    let term = args[0], n;
    if (args.length === 2 && args[1].k === "sym") n = args[1].name;
    else if (args.length === 1) { const fs = [...X.freeSymbols(term)]; if (fs.length !== 1) throw refuse("name the index variable, e.g. genfunc(n^2, n)"); n = fs[0]; }
    else throw refuse("genfunc expects a recurrence, or an explicit term and its index");
    if (term.k === "eq") term = term.args[1];
    const qp = quasiPoly(term, n);
    if (!qp) throw refuse("only terms of the form sum P(n) c^n (polynomial times exponential) have a rational generating function that can be certified");
    dBound = qp.d;
    const count = 2 * dBound + 8;
    terms = [];
    for (let m = 0; m < count; m++) {
      const v = simpNum(X.subs(term, { [n]: X.num(m) }));
      if (!v) throw refuse(`the term does not evaluate to a rational number at ${n} = ${m}`);
      terms.push(v);
    }
    source = `the term is a quasi-polynomial whose C-finite order is at most ${dBound}`;
    gx = gfVar(new Set([n]));
  }
  if (dBound > 60) throw refuse("the recurrence is too large");
  const { L, c } = berlekampMassey(terms);
  if (2 * L + 4 > terms.length) throw refuse("no short recurrence was found");
  const Qp = ptrim([ONE, ...c.map(N.neg)]);
  const P = ptrim(pmul(Qp, terms).slice(0, Math.max(L, 1)));
  const tree = X.mul(ptree(P, gx), X.pow(ptree(Qp, gx), X.NEG_ONE));
  return {
    answers: [ansTree("generating function", tree)],
    steps: [step("genfunc.terms", "Compute the first terms", `${terms.slice(0, 8).map(qs).join(", ")}, ...`),
      step("genfunc.bm", "Find the shortest linear recurrence (Berlekamp-Massey)", `Denominator ${toText(ptree(Qp, gx))}; numerator = (denominator x series) truncated below degree ${Math.max(L, 1)}.`)],
    checks: () => {
      const need = dBound + Qp.length + 2;
      if (need > terms.length) return [check("series comparison", false, "not enough terms to certify")];
      const ser = seriesDiv(P, Qp, need);
      const bad = ser.findIndex((v, i) => !N.eq(v, terms[i]));
      const ok = bad < 0;
      return [check("series comparison", ok, ok
        ? `long division of the rational function reproduces the first ${need} terms; ${source}, the rational function's coefficients satisfy a recurrence of order ${Qp.length - 1}, and two such sequences agreeing on ${need} >= ${dBound} + ${Qp.length - 1} consecutive terms are identical`
        : `the series differs at index ${bad}`)];
    },
  };
}

// ---------------------------------------------------------------- seriescoeff
function cmdSeriesCoeff(args) {
  if (args.length !== 3 || args[1].k !== "sym") throw refuse("use seriescoeff(f, x, k)");
  const x = args[1].name;
  const k = intOf(args[2], "a non-negative integer power");
  if (k < 0n || k > 20000n) throw refuse("the power must be between 0 and 20000");
  let { P, Q: Qp } = ratFun(args[0], x);
  if (!Qp.length) throw refuse("division by zero");
  // strip common powers of x
  let v = 0;
  while (Qp.length && N.isZero(Qp[0])) {
    if (P.length && N.isZero(P[0])) { P = P.slice(1); Qp = Qp.slice(1); continue; }
    Qp = Qp.slice(1); v++;
  }
  const K = Number(k) + v; // coefficient of x^k in x^-v P/Q is coefficient of x^(k+v) in P/Q
  const ser = seriesDiv(P, Qp, K + 1);
  const val = ser[K];
  return {
    answers: [ansTree("coefficient", X.num(val))],
    steps: [step("series.divide", "Expand as a power series", `Write f = ${v ? `x^-${v} ` : ""}P(x)/Q(x) and divide term by term: c_m = (p_m - sum q_j c_(m-j)) / q_0.`)],
    checks: () => {
      // multiply back: (series truncated) * Q == P mod x^(K+1)
      const prod = pmul(ser, Qp);
      for (let i = 0; i <= K; i++) if (!N.eq(prod[i] || Z, P[i] || Z)) return [check("multiply back", false, `series x denominator differs from the numerator at degree ${i}`)];
      return [check("multiply back", true, `the truncated series times the denominator equals the numerator through degree ${K}, which determines every coefficient up to x^${K} uniquely (the denominator's constant term is non-zero)`)];
    },
  };
}

// ---------------------------------------------------------------- findsequence
function cmdFindSequence(args) {
  const terms = args.map((a) => { const r = ratOf(a); if (!r) throw refuse("findsequence expects numbers"); return r; });
  if (terms.length < 3) throw refuse("at least 3 terms (and spare terms to test the pattern) are needed");
  if (terms.length > 200) throw refuse("too many terms");
  const len = terms.length;
  // polynomial: difference table
  let row = terms.slice(), deg = -1;
  const lead = [];
  for (let d = 0; d < len; d++) {
    lead.push(row[0]);
    if (row.every((v) => N.eq(v, row[0]))) { deg = d; break; }
    row = row.slice(1).map((v, i) => N.sub(v, row[i]));
  }
  const nsym = X.sym("n");
  if (deg >= 0 && len >= deg + 3) {
    // Newton forward form sum lead[j] * C(n, j) -> monomial coefficients
    let poly = [];
    let basis = [ONE]; // C(n, j) as polynomial
    for (let j = 0; j <= deg; j++) {
      poly = padd(poly, pscale(basis, lead[j]));
      basis = pscale(pmul(basis, [N.Q(-BigInt(j)), ONE]), N.Q(1n, BigInt(j + 1)));
    }
    const tree = ptree(poly, "n");
    const at = (m) => poly.reduceRight((s, c) => N.add(N.mul(s, N.Q(BigInt(m))), c), Z);
    // next term by extending the difference table (a second route)
    const table = [terms.slice()];
    for (let d = 0; d < deg; d++) { const r = table[table.length - 1]; table.push(r.slice(1).map((v, i) => N.sub(v, r[i]))); }
    let nxt = Z;
    for (const r of table) nxt = N.add(nxt, r[r.length - 1]);
    return {
      answers: [ansTree("formula", tree), ansTree("next term", X.num(nxt))], solutionStatus: "evidence",
      note: `A pattern that fits the ${len} given terms (with n starting at 0): the differences become constant at order ${deg}. Any finite list has other continuations, so this is a conjecture, not a proof.`,
      steps: [step("seq.differences", "Difference table", `Order-${deg} differences are constant (${qs(lead[deg])}), using ${len - deg - 1} spare term(s) beyond the ${deg + 1} that determine the polynomial.`)],
      checks: () => {
        const cs = [];
        for (let m = 0; m < len; m++) {
          const v = simpNum(X.subs(tree, { n: X.num(m) }));
          if (!v || !N.eq(v, terms[m])) return [check("fits the terms", false, `the formula gives ${v && qs(v)} at n = ${m}`)];
        }
        cs.push(check("fits the terms", true, `the formula reproduces all ${len} given terms`));
        cs.push(check("next term", N.eq(at(len), nxt), `the formula at n = ${len} agrees with the extended difference table (${qs(nxt)})`));
        return cs;
      },
    };
  }
  const { L, c } = berlekampMassey(terms);
  if (L >= 1 && len >= 2 * L + 2) {
    const rec = (k) => c.reduce((s, cj, j) => N.add(s, N.mul(cj, terms[k - 1 - j])), Z);
    const nxt = c.reduce((s, cj, j) => N.add(s, N.mul(cj, terms[len - 1 - j])), Z);
    const answers = [];
    let formula = null;
    if (L === 1 && !N.isZero(terms[0])) {
      formula = X.mul(X.num(terms[0]), X.pow(X.num(c[0]), nsym));
      answers.push(ansTree("formula", formula));
    }
    const rtext = `a(n) = ${c.map((cj, j) => ({ cj, j: j + 1 })).filter((t) => !N.isZero(t.cj)).map((t, i) => {
      const neg = N.isNeg(t.cj), mag = qs(N.abs(t.cj));
      const body = `${mag === "1" ? "" : mag}a(n-${t.j})`;
      return i === 0 ? `${neg ? "-" : ""}${body}` : `${neg ? " - " : " + "}${body}`;
    }).join("")}`;
    answers.push(ansText("recurrence", rtext), ansTree("next term", X.num(nxt)));
    return {
      answers, solutionStatus: "evidence",
      note: `A pattern that fits the ${len} given terms: a linear recurrence of order ${L} (for n >= ${L}, n starting at 0), found with ${len - 2 * L} spare term(s). Any finite list has other continuations, so this is a conjecture, not a proof.`,
      steps: [step("seq.bm", "Shortest linear recurrence (Berlekamp-Massey)", rtext)],
      checks: () => {
        const cs = [];
        for (let k = L; k < len; k++) if (!N.eq(rec(k), terms[k])) return [check("fits the terms", false, `the recurrence fails at n = ${k}`)];
        cs.push(check("fits the terms", true, `the recurrence holds at every n = ${L} .. ${len - 1}`));
        if (formula) {
          for (let m = 0; m <= len; m++) {
            const v = simpNum(X.subs(formula, { n: X.num(m) }));
            const want = m < len ? terms[m] : nxt;
            if (!v || !N.eq(v, want)) return [check("closed form", false, `the closed form fails at n = ${m}`)];
          }
          cs.push(check("closed form", true, "the closed form reproduces every given term and the next term"));
        }
        return cs;
      },
    };
  }
  throw refuse("no polynomial or linear-recurrence pattern is supported by enough spare terms; give more terms");
}

export const SEQ_HANDLERS = { rsolve: cmdRsolve, genfunc: cmdGenfunc, seriescoeff: cmdSeriesCoeff, findsequence: cmdFindSequence };
export { berlekampMassey, seriesDiv, ratFun, evalQuad, quasiPoly };
