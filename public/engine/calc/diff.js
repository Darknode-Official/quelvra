// Quelvra symbolic differentiation (fully algorithmic: always succeeds on elementary input).
//
//   diff(u, x, {order, steps, ctx})       -> derivative tree (simplified), steps optional
//   diffSteps(u, x)                       -> { result, steps }
//   implicitDiff(eqNode, x, y)            -> dy/dx
//   gradient(u, vars) / jacobian(fs, vars) / hessian(u, vars) / directional(u, vars, dir)
//
// Conditions that the derivative needs (|u|' = u/|u| u' requires u != 0) are returned in
// ctx.conditions when a condition sink is supplied.

import * as X from "../expr.js";
import * as N from "../num.js";
import { simplify, S, makeCtx } from "../simplify.js";
import { toText } from "../print.js";
import { StepLog, NO_STEPS } from "../steps.js";

const { ZERO, ONE, TWO, NEG_ONE, HALF, E, PI } = X;

// Derivatives of named functions of one argument u: returns f'(u) as a tree in u.
const TABLE = {
  sin: (u) => S.fn("cos", u),
  cos: (u) => S.neg(S.fn("sin", u)),
  tan: (u) => S.pow(S.fn("sec", u), TWO),
  cot: (u) => S.neg(S.pow(S.fn("csc", u), TWO)),
  sec: (u) => S.mul(S.fn("sec", u), S.fn("tan", u)),
  csc: (u) => S.neg(S.mul(S.fn("csc", u), S.fn("cot", u))),
  asin: (u) => S.pow(S.sub(ONE, S.pow(u, TWO)), X.num(-1, 2)),
  acos: (u) => S.neg(S.pow(S.sub(ONE, S.pow(u, TWO)), X.num(-1, 2))),
  atan: (u) => S.pow(S.add(ONE, S.pow(u, TWO)), NEG_ONE),
  acot: (u) => S.neg(S.pow(S.add(ONE, S.pow(u, TWO)), NEG_ONE)),
  asec: (u) => S.pow(S.mul(S.fn("abs", u), S.sqrt(S.sub(S.pow(u, TWO), ONE))), NEG_ONE),
  acsc: (u) => S.neg(S.pow(S.mul(S.fn("abs", u), S.sqrt(S.sub(S.pow(u, TWO), ONE))), NEG_ONE)),
  sinh: (u) => S.fn("cosh", u),
  cosh: (u) => S.fn("sinh", u),
  tanh: (u) => S.pow(S.fn("sech", u), TWO),
  coth: (u) => S.neg(S.pow(S.fn("csch", u), TWO)),
  sech: (u) => S.neg(S.mul(S.fn("sech", u), S.fn("tanh", u))),
  csch: (u) => S.neg(S.mul(S.fn("csch", u), S.fn("coth", u))),
  asinh: (u) => S.pow(S.add(S.pow(u, TWO), ONE), X.num(-1, 2)),
  acosh: (u) => S.pow(S.sub(S.pow(u, TWO), ONE), X.num(-1, 2)),
  atanh: (u) => S.pow(S.sub(ONE, S.pow(u, TWO)), NEG_ONE),
  ln: (u) => S.pow(u, NEG_ONE),
  erf: (u) => S.mul(S.div(TWO, S.sqrt(PI)), S.pow(E, S.neg(S.pow(u, TWO)))),
  abs: (u) => S.div(u, S.fn("abs", u)),
};
const RULE_NAME = {
  sin: "d/du sin u = cos u", cos: "d/du cos u = -sin u", tan: "d/du tan u = sec^2 u",
  cot: "d/du cot u = -csc^2 u", sec: "d/du sec u = sec u tan u", csc: "d/du csc u = -csc u cot u",
  asin: "d/du asin u = 1/sqrt(1 - u^2)", acos: "d/du acos u = -1/sqrt(1 - u^2)", atan: "d/du atan u = 1/(1 + u^2)",
  sinh: "d/du sinh u = cosh u", cosh: "d/du cosh u = sinh u", tanh: "d/du tanh u = sech^2 u",
  ln: "d/du ln u = 1/u", abs: "d/du |u| = u/|u| (u != 0)", erf: "d/du erf u = (2/sqrt(pi)) e^(-u^2)",
};

// (fg)' = f'g + fg' with f and g named in the order they are written
function productWhy(u, vary) {
  const t = toText(u);
  const [f, g] = [...vary].sort((a, b) => t.indexOf(toText(a)) - t.indexOf(toText(b)));
  return `(fg)' = f'g + fg' with f = ${toText(f)} and g = ${toText(g)}: differentiate one factor at a time and add.`;
}

// ---------------- core ----------------
// Steps read top-down: a rule's step comes first and the derivatives it needed (logged while it was
// being computed, after `mark`) become its sub-steps, in the order the parts are written.
function adopt(log, mark, st) {
  const s = log.add(st);
  const cur = log.cur;
  if (!s || !cur || mark >= cur.length - 1) return s;
  const kids = cur.splice(mark, cur.length - 1 - mark);
  const whole = st.before && st.before.k === "deriv" ? toText(st.before.args[0]) : "";
  const key = (k) => {
    const t = k.before && k.before.k === "deriv" ? toText(k.before.args[0]).replace(/^-/, "") : null;
    const i = t ? whole.indexOf(t) : -1;
    return i < 0 ? Infinity : i;
  };
  s.sub = [...kids.map((k, i) => [k, i]).sort((a, b) => key(a[0]) - key(b[0]) || a[1] - b[1]).map((p) => p[0]), ...(s.sub || [])];
  return s;
}
function d(u, x, log, ctx) {
  if (X.freeOf(u, x)) return ZERO;
  const mark = log.cur ? log.cur.length : 0;
  switch (u.k) {
    case "sym": return u === x ? ONE : ZERO;
    case "add": {
      const parts = u.args.map((t) => d(t, x, log, ctx));
      const r = S.add(...parts);
      adopt(log, mark, { rule: "diff.sum", title: "Sum rule", why: "The derivative of a sum is the sum of the derivatives." + (u.args.some((t) => X.freeOf(t, x)) ? " A constant term has derivative 0." : ""), before: X.deriv(u, x), after: r });
      return r;
    }
    case "mul": {
      // constant factor
      const cst = u.args.filter((f) => X.freeOf(f, x));
      const vary = u.args.filter((f) => !X.freeOf(f, x));
      if (cst.length) {
        const inner = vary.length === 1 ? vary[0] : X.mul(...vary);
        const dv = d(inner, x, log, ctx);
        const r = S.mul(...cst, dv);
        adopt(log, mark, { rule: "diff.constant-multiple", title: "Constant multiple rule", why: `${toText(S.mul(...cst))} does not depend on ${x.name}, so it stays as a factor.`, before: X.deriv(u, x), after: r });
        return r;
      }
      // quotient presentation: numerator / denominator
      const num = vary.filter((f) => !(f.k === "pow" && X.isNum(f.args[1]) && f.args[1].v.n < 0n));
      const den = vary.filter((f) => f.k === "pow" && X.isNum(f.args[1]) && f.args[1].v.n < 0n);
      if (num.length && den.length) {
        const f = num.length === 1 ? num[0] : X.mul(...num);
        const gg = S.mul(...den.map((p) => S.pow(p.args[0], X.num(N.neg(p.args[1].v)))));
        const df = d(f, x, log, ctx), dg = d(gg, x, log, ctx);
        const r = S.div(S.sub(S.mul(df, gg), S.mul(f, dg)), S.pow(gg, TWO));
        adopt(log, mark, { rule: "diff.quotient", title: "Quotient rule", why: "(f/g)' = (f'g - fg')/g^2", before: X.deriv(u, x), after: r, conditions: [X.rel("!=", gg, ZERO)] });
        return r;
      }
      // product rule (n-ary): sum over i of f1 ... fi' ... fn
      const terms = vary.map((fi, i) => S.mul(...vary.map((fj, j) => (i === j ? d(fj, x, log, ctx) : fj))));
      const r = S.add(...terms);
      adopt(log, mark, { rule: "diff.product", title: "Product rule", why: vary.length === 2 ? productWhy(u, vary) : "Differentiate one factor at a time and add the results.", before: X.deriv(u, x), after: r });
      return r;
    }
    case "pow": {
      const [b, e] = u.args;
      if (X.freeOf(e, x)) {
        // power rule with chain rule
        const db = d(b, x, log, ctx);
        const r = S.mul(e, S.pow(b, S.sub(e, ONE)), db);
        const chain = b !== x;
        if (X.isNum(e) && e.v.d !== 1n && e.v.d % 2n === 0n && ctx.conditions) ctx.conditions.push({ node: b, rel: ">0", reason: "the derivative of an even root needs a positive radicand" });
        if (X.isNum(e) && e.v.n < 0n && ctx.conditions) ctx.conditions.push({ node: b, rel: "!=0", reason: "negative power" });
        adopt(log, mark, { rule: chain ? "diff.power-chain" : "diff.power", title: chain ? "Power rule with chain rule" : "Power rule", why: chain ? `d/dx u^n = n u^(n-1) u', with u = ${toText(b)}, n = ${toText(e)}.` : `d/dx x^n = n x^(n-1) with n = ${toText(e)}.`, before: X.deriv(u, x), after: r });
        return r;
      }
      if (X.freeOf(b, x)) {
        // a^v -> a^v ln(a) v'
        const de = d(e, x, log, ctx);
        const r = b === E ? S.mul(u, de) : S.mul(u, S.fn("ln", b), de);
        adopt(log, mark, { rule: b === E ? "diff.exp" : "diff.exponential", title: b === E ? "Exponential rule" : "Exponential rule (base a)", why: (b === E ? "d/dx e^u = e^u u'" : "d/dx a^u = a^u ln(a) u'") + (e === x ? "." : `, with u = ${toText(e)}.`), before: X.deriv(u, x), after: r });
        return r;
      }
      // u^v with both variable: logarithmic differentiation
      const r = log.group({ rule: "diff.logarithmic", title: "Logarithmic differentiation", why: "Both base and exponent depend on the variable: write y = u^v, so ln y = v ln u, then differentiate.", before: X.deriv(u, x) }, (step) => {
        const res = S.mul(u, d(S.mul(e, S.fn("ln", b)), x, log, ctx));
        if (step) step.after = res;
        return res;
      });
      if (ctx.conditions) ctx.conditions.push({ node: b, rel: ">0", reason: "u^v with variable exponent needs u > 0" });
      return r;
    }
    case "fn": {
      if (u.name === "log") {
        const [base, arg] = u.args;
        if (X.freeOf(base, x)) {
          const r = S.div(d(arg, x, log, ctx), S.mul(arg, S.fn("ln", base)));
          adopt(log, mark, { rule: "diff.log-base", title: "Logarithm rule", why: `d/dx log_b(u) = u' / (u ln b) with b = ${toText(base)}.`, before: X.deriv(u, x), after: r });
          return r;
        }
        return d(S.div(S.fn("ln", arg), S.fn("ln", base)), x, log, ctx);
      }
      const rule = TABLE[u.name];
      if (!rule || u.args.length !== 1) {
        // unknown function f(x): leave an unevaluated derivative (chain rule applied symbolically)
        if (u.args.length === 1) {
          const inner = u.args[0];
          const outer = X.deriv(X.fn(u.name, X.sym("_u")), X.sym("_u"));
          const r = inner === x ? X.deriv(u, x) : S.mul(X.subs(outer, { _u: inner }), d(inner, x, log, ctx));
          return r;
        }
        return X.deriv(u, x);
      }
      const inner = u.args[0];
      const outer = rule(inner);
      const di = d(inner, x, log, ctx);
      const r = S.mul(outer, di);
      if (u.name === "abs" && ctx.conditions) ctx.conditions.push({ node: inner, rel: "!=0", reason: "|u| is not differentiable where u = 0" });
      if (u.name === "ln" && ctx.conditions) ctx.conditions.push({ node: inner, rel: ">0", reason: "ln u is defined for u > 0" });
      const chain = inner !== x;
      adopt(log, mark, { rule: `diff.${u.name}${chain ? "-chain" : ""}`, title: chain ? `Chain rule with ${u.name}` : `Derivative of ${u.name}`, why: (RULE_NAME[u.name] || `derivative of ${u.name}`) + (chain ? `, with u = ${toText(inner)}, times u'.` : "."), before: X.deriv(u, x), after: r });
      return r;
    }
    case "piecewise": {
      const out = [];
      for (let i = 0; i < u.args.length; i += 2) out.push(d(u.args[i], x, log, ctx), u.args[i + 1]);
      adopt(log, mark, { rule: "diff.piecewise", title: "Differentiate each piece", why: "Inside each piece the derivative is the derivative of that piece; at the boundaries the derivative must be checked separately.", before: X.deriv(u, x), after: X.piecewise(...out) });
      return X.mk("piecewise", out);
    }
    case "deriv": {
      // d/dx (d/dy f) : differentiate the inner result first
      const inner = diff(u.args[0], u.args[1], { order: u.args[2] });
      return d(inner, x, log, ctx);
    }
    case "eq": return X.eq(d(u.args[0], x, log, ctx), d(u.args[1], x, log, ctx));
    case "tuple": case "vector": return X.withArgs(u, u.args.map((a) => d(a, x, log, ctx)));
    case "matrix": return X.withArgs(u, u.args.map((r) => X.withArgs(r, r.args.map((a) => d(a, x, log, ctx)))));
    case "integral": {
      // Leibniz rule for integral with variable upper/lower limits (fundamental theorem)
      if (u.args.length === 4) {
        const [f, t, lo, hi] = u.args;
        if (X.freeOf(f, x)) {
          const r = S.sub(S.mul(X.subs(f, { [t.name]: hi }), d(hi, x, log, ctx)), S.mul(X.subs(f, { [t.name]: lo }), d(lo, x, log, ctx)));
          adopt(log, mark, { rule: "diff.ftc", title: "Fundamental theorem of calculus", why: "d/dx of the integral from a(x) to b(x) of f(t) dt is f(b(x)) b'(x) - f(a(x)) a'(x).", before: X.deriv(u, x), after: r });
          return r;
        }
      }
      return X.deriv(u, x);
    }
    default:
      return X.deriv(u, x);
  }
}

export function diff(u, x, opts = {}) {
  const xs = typeof x === "string" ? X.sym(x) : x;
  const orderNode = opts.order === undefined ? ONE : typeof opts.order === "number" ? X.num(opts.order) : opts.order;
  if (!X.isInt(orderNode) || orderNode.v.n < 0n) return X.deriv(u, xs, orderNode);
  const n = Number(orderNode.v.n);
  if (n > 50) throw Object.assign(new Error("Quelvra: derivative order too large (limit 50)"), { code: "BUDGET" });
  const log = opts.steps || NO_STEPS;
  const ctx = opts.ctx || makeCtx();
  let cur = simplify(u, ctx);
  for (let i = 0; i < n; i++) {
    const mark = log.cur ? log.cur.length : 0;
    const res = simplify(d(cur, xs, log, ctx), ctx);
    if (n > 1) adopt(log, mark, { rule: "diff.higher-order", title: `Derivative number ${i + 1}`, why: `Differentiate again to reach order ${n}.`, before: X.deriv(cur, xs), after: res, kind: "note" });
    cur = res;
  }
  return cur;
}

export function diffSteps(u, x, opts = {}) {
  const log = new StepLog();
  const ctx = makeCtx({ conditions: [], ...(opts.ctxOpts || {}) });
  const result = diff(u, x, { ...opts, steps: log, ctx });
  return { result, steps: log.steps, conditions: ctx.conditions };
}

// Implicit differentiation of F(x, y) = G(x, y): dy/dx = -F_x / F_y where F := lhs - rhs.
export function implicitDiff(eqNode, x, y, opts = {}) {
  const xs = typeof x === "string" ? X.sym(x) : x;
  const ys = typeof y === "string" ? X.sym(y) : y;
  const F = eqNode.k === "eq" ? S.sub(eqNode.args[0], eqNode.args[1]) : simplify(eqNode);
  const log = opts.steps || NO_STEPS;
  const Fx = diff(F, xs), Fy = diff(F, ys);
  const r = simplify(S.neg(S.div(Fx, Fy)));
  log.add({ rule: "diff.implicit", title: "Implicit differentiation", why: `Differentiate both sides with respect to ${xs.name}, treating ${ys.name} as a function of ${xs.name}, then solve for dy/dx. Equivalently dy/dx = -F_x/F_y.`, before: eqNode, after: X.eq(X.deriv(ys, xs), r), conditions: [X.rel("!=", Fy, ZERO)] });
  return r;
}

export const gradient = (u, vars) => X.vector(...vars.map((v) => diff(u, v)));
export const jacobian = (fs, vars) => X.matrix(fs.map((f) => X.tuple(...vars.map((v) => diff(f, v)))));
export const hessian = (u, vars) => X.matrix(vars.map((a) => X.tuple(...vars.map((b) => diff(diff(u, a), b)))));
// Directional derivative along `dir` (a list of trees), normalised to a unit vector.
export function directional(u, vars, dir) {
  const g = vars.map((v) => diff(u, v));
  const norm = S.sqrt(S.add(...dir.map((c) => S.pow(c, TWO))));
  return simplify(S.div(S.add(...g.map((gi, i) => S.mul(gi, dir[i]))), norm));
}
