// Quelvra identifier: deterministic structural classification of a math tree.
//
// classify(node, {variable, goal}) -> problem card
//   { kind, family, goal, unknowns, params, degree, features, method: "structural", label, notes }
//
// kind   : arithmetic | expression | equation | inequality | system | derivative | integral | limit |
//          sum | product | matrix | vector | function-definition | command | set | interval | unknown
// family : for equations/inequalities: linear, quadratic, cubic, quartic, polynomial, rational,
//          radical, absolute-value, exponential, logarithmic, trigonometric, hyperbolic,
//          transcendental, literal, identity, constant ; for systems: linear-system, nonlinear-system,
//          inequality-system ; otherwise a finer label.
// The identifier never computes an answer. It only recommends solver families.

import * as X from "./expr.js";
import * as N from "./num.js";
import { simplify, expand } from "./simplify.js";

const TRIG = new Set(["sin", "cos", "tan", "cot", "sec", "csc"]);
const ATRIG = new Set(["asin", "acos", "atan", "acot", "asec", "acsc"]);
const HYP = new Set(["sinh", "cosh", "tanh", "coth", "sech", "csch", "asinh", "acosh", "atanh"]);
const COMMANDS = new Set(["solve", "simplify", "expand", "factor", "series", "taylor", "plot", "det", "inv", "transpose", "rank", "trace", "rref",
  "eigenvalues", "eigenvectors", "isprime", "factorint", "phi", "divisors", "mean", "median", "mode", "variance", "stdev", "gcd", "lcm", "convert",
  "kaprekar", "collatz", "collatzverify", "goldbach", "goldbachverify", "twinprimes", "primegaps", "zetazeros", "eulerbricks", "movingsofa",
  // function analysis, geometry and optimisation (call forms from the language engine; see parse.js FUNCTIONS)
  "domain", "range", "zeros", "intercepts", "asymptotes", "extrema", "inflection", "monotonic", "critical", "tangent", "normal", "inverse",
  "completesquare", "apart", "identity", "line", "slope", "distance", "midpoint", "arclength", "areabetween", "volume", "avgvalue",
  "maximize", "minimize", "dot", "cross"]);

// Choose the unknown(s) to solve for.
const PREFERRED = ["x", "y", "z", "t", "n", "u", "v", "w", "a", "b", "c", "theta"];
export function pickUnknowns(node, requested) {
  if (requested) return (Array.isArray(requested) ? requested : [requested]).map((v) => (typeof v === "string" ? v : v.name));
  const fs = [...X.freeSymbols(node)];
  if (!fs.length) return [];
  const sorted = fs.sort((a, b) => {
    const ia = PREFERRED.indexOf(a), ib = PREFERRED.indexOf(b);
    return (ia < 0 ? 99 : ia) - (ib < 0 ? 99 : ib) || a.localeCompare(b);
  });
  return sorted;
}

// Structural features of expression u with respect to variable x.
export function features(u, x) {
  const f = { polynomial: true, degree: 0, rational: false, radical: false, abs: false, exponential: false, log: false,
    trig: false, inverseTrig: false, hyperbolic: false, otherFn: [], factorial: false, piecewise: false, floor: false, xInExponentAndBase: false };
  const walk = (w, inDenom) => {
    if (X.freeOf(w, x)) return;
    switch (w.k) {
      case "sym": return;
      case "add": case "mul": w.args.forEach((a) => walk(a, inDenom)); return;
      case "pow": {
        const [b, e] = w.args;
        const bx = !X.freeOf(b, x), ex = !X.freeOf(e, x);
        if (ex) {
          f.exponential = true; f.polynomial = false;
          if (bx) f.xInExponentAndBase = true;
          walk(e, inDenom);
        }
        if (bx) {
          if (X.isNum(e)) {
            if (e.v.d !== 1n) { f.radical = true; f.polynomial = false; }
            if (e.v.n < 0n) { f.rational = true; f.polynomial = false; }
          } else if (!ex) f.polynomial = false;
          walk(b, inDenom || (X.isNum(e) && e.v.n < 0n));
        }
        return;
      }
      case "fn": {
        const n = w.name;
        if (n === "abs") f.abs = true;
        else if (n === "ln" || n === "log") f.log = true;
        else if (TRIG.has(n)) f.trig = true;
        else if (ATRIG.has(n)) f.inverseTrig = true;
        else if (HYP.has(n)) f.hyperbolic = true;
        else if (n === "factorial" || n === "gamma") f.factorial = true;
        else if (n === "floor" || n === "ceil") f.floor = true;
        else f.otherFn.push(n);
        f.polynomial = false;
        w.args.forEach((a) => walk(a, inDenom));
        return;
      }
      case "piecewise": f.piecewise = true; f.polynomial = false; return;
      default: f.polynomial = false; return;
    }
  };
  walk(u, false);
  if (f.polynomial) f.degree = polyDegree(u, x);
  return f;
}

// Degree of a polynomial expression in x (after expansion); -1 if not polynomial.
export function polyDegree(u, x) {
  let e;
  try { e = expand(u); } catch (_) { return -1; }
  const termDeg = (t) => {
    if (X.freeOf(t, x)) return 0;
    if (t.k === "sym") return 1;
    if (t.k === "pow" && t.args[0] === x && X.isInt(t.args[1]) && t.args[1].v.n > 0n) return Number(t.args[1].v.n);
    if (t.k === "mul") {
      let d = 0;
      for (const f of t.args) { const k = termDeg(f); if (k < 0) return -1; d += k; }
      return d;
    }
    return -1;
  };
  if (e.k === "add") {
    let m = 0;
    for (const t of e.args) { const k = termDeg(t); if (k < 0) return -1; m = Math.max(m, k); }
    return m;
  }
  return termDeg(e);
}

function familyOf(f, degree) {
  const transcendentalKinds = [f.exponential, f.log, f.trig || f.inverseTrig, f.hyperbolic].filter(Boolean).length;
  if (f.factorial || f.floor || f.otherFn.length || f.piecewise) return "special";
  if (transcendentalKinds > 1 || f.xInExponentAndBase) return "transcendental";
  if ((f.exponential || f.log || f.trig || f.inverseTrig || f.hyperbolic) && (f.radical || f.rational || f.abs || degree > 1)) {
    // e.g. x e^x = 2, x = cos x
    if (f.trig && !f.exponential && !f.log && !f.hyperbolic) return "trigonometric";
    if (f.exponential && !f.log && !f.trig) return "exponential";
    if (f.log && !f.exponential && !f.trig) return "logarithmic";
    return "transcendental";
  }
  if (f.exponential) return "exponential";
  if (f.log) return "logarithmic";
  if (f.trig || f.inverseTrig) return "trigonometric";
  if (f.hyperbolic) return "hyperbolic";
  if (f.abs) return "absolute-value";
  if (f.radical) return "radical";
  if (f.rational) return "rational";
  return ["constant", "linear", "quadratic", "cubic", "quartic"][degree] || "polynomial";
}

const LABELS = {
  linear: "Linear equation", quadratic: "Quadratic equation", cubic: "Cubic equation", quartic: "Quartic equation",
  polynomial: "Polynomial equation", rational: "Rational equation", radical: "Radical equation", "absolute-value": "Absolute-value equation",
  exponential: "Exponential equation", logarithmic: "Logarithmic equation", trigonometric: "Trigonometric equation", hyperbolic: "Hyperbolic equation",
  transcendental: "Transcendental equation", special: "Equation with special functions", constant: "Equation without the unknown",
};

// Transcendental "mixed" equations where x appears both inside and outside a transcendental function.
function mixedTranscendental(u, x, f) {
  if (!(f.exponential || f.log || f.trig || f.hyperbolic)) return false;
  // x appears outside any function / exponent?
  const outside = (w) => {
    if (w === x) return true;
    if (w.k === "fn") return false;
    if (w.k === "pow") return !X.freeOf(w.args[0], x) && X.freeOf(w.args[1], x) ? outside(w.args[0]) : false;
    return w.args.some(outside);
  };
  return outside(u);
}

export function classify(node, opts = {}) {
  const card = { kind: "unknown", family: "", goal: opts.goal || "", unknowns: [], params: [], degree: null, features: null, method: "structural", label: "", notes: [] };
  let u = node;

  // command wrappers: solve(eq, x), factor(p), ...
  if (u.k === "fn" && COMMANDS.has(u.name)) {
    const inner = u.args[0];
    if (u.name === "solve" && inner) {
      const sub = classify(inner, { variable: u.args[1] && u.args[1].k === "sym" ? u.args[1].name : opts.variable, goal: "solve" });
      return { ...sub, goal: "solve", command: "solve" };
    }
    if (["simplify", "expand", "factor"].includes(u.name) && inner) {
      const sub = classify(inner, { ...opts, goal: u.name });
      return { ...sub, goal: u.name, command: u.name, label: { simplify: "Simplify", expand: "Expand", factor: "Factor" }[u.name] + " " + (sub.label || "expression").toLowerCase() };
    }
    return { ...card, kind: "command", family: u.name, goal: u.name, command: u.name, unknowns: pickUnknowns(u), label: `Compute ${u.name}` };
  }

  switch (u.k) {
    case "deriv": {
      const v = u.args[1];
      const partial = X.freeSymbols(u.args[0]).size > 1;
      return { ...card, kind: "derivative", family: partial ? "partial-derivative" : u.args[0].k === "eq" ? "implicit-derivative" : "derivative", goal: "differentiate",
        unknowns: [v.name], label: partial ? `Partial derivative with respect to ${v.name}` : `Derivative with respect to ${v.name}` };
    }
    case "integral": {
      const definite = u.args.length === 4;
      const improper = definite && (u.args[2] === X.OO || u.args[3] === X.OO || X.contains(u.args[2], X.OO) || X.contains(u.args[3], X.OO));
      return { ...card, kind: "integral", family: improper ? "improper-integral" : definite ? "definite-integral" : "indefinite-integral", goal: "integrate",
        unknowns: [u.args[1].name], label: improper ? "Improper integral" : definite ? "Definite integral" : "Indefinite integral" };
    }
    case "limit": {
      const to = u.args[2];
      const atInf = to === X.OO || X.contains(to, X.OO);
      return { ...card, kind: "limit", family: atInf ? "limit-at-infinity" : u.dir ? "one-sided-limit" : "limit", goal: "limit",
        unknowns: [u.args[1].name], label: atInf ? "Limit at infinity" : u.dir ? `One-sided limit (${u.dir === "+" ? "from the right" : "from the left"})` : "Limit" };
    }
    case "sum": case "product": {
      const inf = u.args[3] === X.OO;
      return { ...card, kind: u.k, family: inf ? "infinite-series" : "finite-" + u.k, goal: u.k === "sum" ? "sum" : "product",
        unknowns: [u.args[1].name], label: inf ? "Infinite series" : u.k === "sum" ? "Finite sum" : "Finite product" };
    }
    case "matrix": case "vector":
      return { ...card, kind: u.k, family: u.k, goal: opts.goal || "evaluate", label: u.k === "matrix" ? "Matrix" : "Vector" };
    case "fndef":
      return { ...card, kind: "function-definition", family: "function", goal: "define", label: `Define ${u.name}` };
    case "interval":
      return { ...card, kind: "interval", family: "interval", goal: opts.goal || "evaluate", label: "Interval" };
    case "set": case "tuple":
      return { ...card, kind: u.k, family: u.k, goal: "evaluate", label: u.k === "set" ? "Set" : "List" };
    case "system": return classifySystem(u, card, opts);
    case "and": case "or":
      if (u.args.every((a) => a.k === "rel" || a.k === "eq" || a.k === "and" || a.k === "or")) {
        const unknowns = pickUnknowns(u, opts.variable);
        const x = X.sym(unknowns[0] || "x");
        const f = features(X.add(...u.args.map((r) => X.sub(r.args[0], r.args[1] || X.ZERO))), x);
        return { ...card, kind: "inequality", family: "compound-" + familyOf(f, f.degree), goal: "solve", unknowns: unknowns.slice(0, 1), params: unknowns.slice(1),
          features: f, label: "Compound inequality" };
      }
      break;
    case "eq": case "rel": return classifyRelation(u, card, opts);
    default: break;
  }

  // plain expression
  const fs = X.freeSymbols(u);
  if (!fs.size) return { ...card, kind: "arithmetic", family: "arithmetic", goal: opts.goal || "evaluate", label: "Arithmetic" };
  const unknowns = pickUnknowns(u, opts.variable);
  const x = X.sym(unknowns[0]);
  const f = features(simplify(u), x);
  return { ...card, kind: "expression", family: f.polynomial ? (unknowns.length > 1 ? "multivariate-polynomial" : "polynomial") : f.rational && !f.radical && !f.trig && !f.exponential && !f.log ? "rational-expression" : "expression",
    goal: opts.goal || "simplify", unknowns, features: f, degree: f.polynomial ? f.degree : null, label: "Expression" };
}

function classifyRelation(u, card, opts) {
  const [l, r] = u.args;
  // f(x) = expr  -> function definition when lhs is a user function call of symbols
  if (u.k === "eq" && l.k === "fn" && ["f", "g", "h"].includes(l.name) && l.args.every((a) => a.k === "sym") && !opts.goal) {
    return { ...card, kind: "function-definition", family: "function", goal: "define", unknowns: l.args.map((a) => a.name), label: `Define ${l.name}(${l.args.map((a) => a.name).join(", ")})`, fndef: true };
  }
  const diff = simplify(X.sub(l, r));
  const unknowns = pickUnknowns(u, opts.variable);
  if (!unknowns.length) {
    return { ...card, kind: u.k === "eq" ? "equation" : "inequality", family: "constant", goal: "check", unknowns: [], label: u.k === "eq" ? "Check an equality" : "Check an inequality" };
  }
  const x = X.sym(unknowns[0]);
  const f = features(diff, x);
  let family = familyOf(f, f.degree);
  if (mixedTranscendental(diff, x, f) && ["exponential", "logarithmic", "trigonometric", "hyperbolic"].includes(family)) family = "transcendental";
  const params = unknowns.slice(1);
  const card2 = {
    ...card, kind: u.k === "eq" ? "equation" : "inequality", family, goal: opts.goal || "solve", unknowns: [x.name], params,
    degree: f.polynomial ? f.degree : null, features: f,
    label: (u.k === "eq" ? LABELS[family] || "Equation" : (LABELS[family] || "Inequality").replace("equation", "inequality").replace("Equation", "Inequality")) + (params.length ? ` in ${x.name}` : ""),
  };
  if (params.length && u.k === "eq") card2.notes.push(`Other symbols (${params.join(", ")}) are treated as constants; solving for ${x.name}.`);
  if (u.k === "eq" && params.length && f.polynomial && f.degree === 1) card2.family = "linear", card2.literal = true;
  return card2;
}

function classifySystem(u, card, opts) {
  const eqs = u.args;
  const unknowns = pickUnknowns(u, opts.variable);
  const allEq = eqs.every((e) => e.k === "eq");
  const hasIneq = eqs.some((e) => e.k === "rel" || e.k === "and");
  let linear = allEq;
  if (allEq) {
    for (const e of eqs) {
      const d = simplify(X.sub(e.args[0], e.args[1]));
      for (const v of unknowns) {
        const f = features(d, X.sym(v));
        if (!f.polynomial || f.degree > 1) { linear = false; break; }
      }
      // products of unknowns (xy) make it nonlinear
      const ex = expand(d);
      const terms = ex.k === "add" ? ex.args : [ex];
      for (const t of terms) {
        const cnt = unknowns.filter((v) => !X.freeOf(t, X.sym(v))).length;
        if (cnt > 1) linear = false;
      }
      if (!linear) break;
    }
  }
  const family = hasIneq ? "inequality-system" : linear ? "linear-system" : "nonlinear-system";
  return { ...card, kind: "system", family, goal: "solve", unknowns, equations: eqs.length,
    label: hasIneq ? "System of inequalities" : `${linear ? "Linear" : "Nonlinear"} system (${eqs.length} equations, ${unknowns.length} unknowns)` };
}
