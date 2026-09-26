// Quelvra printer: math tree -> plain text (re-parseable) and LaTeX.
// Display order differs from canonical order: sums print highest degree first (x^2 + 2x + 3).

import * as N from "./num.js";
import * as X from "./expr.js";

const PREC = { rel: 0, add: 1, mul: 2, neg: 2, pow: 4, atom: 5 };

function degreeKey(t) {
  // rough total degree for display ordering
  if (X.isNum(t)) return -1;
  if (t.k === "sym" || t.k === "const") return 1;
  if (t.k === "pow") {
    const e = t.args[1];
    return X.isNum(e) ? N.toFloat(e.v) * Math.max(0, degreeKey(t.args[0])) : 1;
  }
  if (t.k === "mul") return t.args.reduce((s, f) => s + Math.max(0, degreeKey(f)), 0);
  return 0.5;
}
const leadNeg = (t) => (X.isNum(t) ? N.isNeg(t.v) : t.k === "mul" && X.isNum(t.args[0]) && N.isNeg(t.args[0].v)) ? 1 : 0;
// display order of factors: numbers, symbols and their powers, then functions, then sums
function factorRank(f) {
  const b = f.k === "pow" ? f.args[0] : f;
  if (b.k === "sym" || b.k === "const") return f.k === "pow" && X.isNum(f.args[1]) && f.args[1].v.d !== 1n ? 2 : 1;
  if (b.k === "fn") return 3;
  return 4;
}
// linear factors x + c read in the conventional order: smaller |c| first, then negative c first
// ((x - 1)(x + 1), (x - 2)(x - 3), (x + 2)(x - 3)); other factors keep canonical order
function linearKey(f) {
  if (f.k !== "add" || f.args.length !== 2) return null;
  const [c, t] = X.isNum(f.args[0]) ? f.args : X.isNum(f.args[1]) ? [f.args[1], f.args[0]] : [null, null];
  if (!c || t.k !== "sym") return null;
  const v = N.toFloat(c.v);
  return Math.abs(v) + (v < 0 ? 0 : 1e-9);
}
const displayFactors = (fs) => fs.map((f, i) => [f, i]).sort((a, b) => {
  const r = factorRank(a[0]) - factorRank(b[0]);
  if (r) return r;
  const ka = linearKey(a[0]), kb = linearKey(b[0]);
  if (ka !== null && kb !== null && ka !== kb) return ka - kb;
  return a[1] - b[1];
}).map(([f]) => f);
// a + bi: in a constant complex number the real part comes first (11 - 2i, not -2i + 11)
const hasI = (t) => t === X.I || (t.args || []).some(hasI);
const realFirst = (u, ts) => (ts.some(hasI) && !ts.every(hasI) && X.freeSymbols(u).size === 0 ? [...ts.filter((t) => !hasI(t)), ...ts.filter(hasI)] : ts);
function displayTerms(u) {
  return realFirst(u, displayTermsRaw(u));
}
function displayTermsRaw(u) {
  const terms = u.args.slice();
  // stable sort: higher degree first, keep canonical order among equals (reversed)
  return terms
    .map((t, i) => [t, i])
    .sort((a, b) => degreeKey(b[0]) - degreeKey(a[0]) || leadNeg(a[0]) - leadNeg(b[0]) || a[1] - b[1])
    .map(([t]) => t);
}

// Split a product into sign, numerator factors, denominator factors.
function fracParts(u) {
  let c = N.ONE;
  const num = [], den = [];
  const fs = u.k === "mul" ? u.args : [u];
  for (const f of fs) {
    if (X.isNum(f)) c = N.mul(c, f.v);
    else if (f.k === "pow" && X.isNum(f.args[1]) && N.isNeg(f.args[1].v)) {
      const e = N.neg(f.args[1].v);
      den.push(N.isOne(e) ? f.args[0] : X.pow(f.args[0], X.num(e)));
    } else num.push(f);
  }
  return { neg: N.isNeg(c), cn: N.abs(c).n, cd: c.d, num: displayFactors(num), den: displayFactors(den) };
}

const fnName = { asin: "asin", acos: "acos", atan: "atan" };

// ---------------- text ----------------
export function toText(u, opts = {}) {
  return txt(u, 0, opts);
}
function wrap(s, need, have) {
  return have < need ? `(${s})` : s;
}
function precOf(u) {
  switch (u.k) {
    case "add": return PREC.add;
    case "mul": {
      const p = fracParts(u);
      if (p.neg) return PREC.neg;
      return PREC.mul;
    }
    case "num": return u.v.d !== 1n ? PREC.mul : N.isNeg(u.v) ? PREC.neg : PREC.atom;
    case "pow": {
      const e = u.args[1];
      if (X.isNum(e) && (N.isNeg(e.v) || (e.v.d === 2n && e.v.n === 1n))) return X.isNum(e) && N.isNeg(e.v) ? PREC.mul : PREC.atom;
      return PREC.pow;
    }
    case "eq": case "rel": case "and": case "or": return PREC.rel;
    default: return PREC.atom;
  }
}
function txt(u, need, o) {
  const s = txtRaw(u, o);
  return wrap(s, need, precOf(u));
}
function txtRaw(u, o) {
  switch (u.k) {
    case "num": return N.toString(u.v);
    case "sym": { const k = u.name.indexOf("_"); return k > 0 && /[^A-Za-z0-9]/.test(u.name.slice(k + 1)) ? `${u.name.slice(0, k)}_(${u.name.slice(k + 1)})` : u.name; }
    case "const": return { pi: "pi", e: "e", I: "i", oo: "oo", undef: "undefined" }[u.name] || u.name;
    case "bool": return u.v ? "true" : "false";
    case "unit": return u.name;
    case "add": {
      const ts = displayTerms(u);
      let s = "";
      ts.forEach((t, i) => {
        let neg = false, body;
        if (X.isNum(t) && N.isNeg(t.v)) { neg = true; body = N.toString(N.neg(t.v)); }
        else if (t.k === "mul" && fracParts(t).neg) { neg = true; body = txt(X.mul(...negateCoeff(t)), PREC.add + 1, o); }
        else body = txt(t, PREC.add, o);
        if (i === 0) s = (neg ? "-" : "") + body;
        else s += (neg ? " - " : " + ") + body;
      });
      return s;
    }
    case "mul": {
      const p = fracParts(u);
      const numF = p.num.map((f) => txt(f, PREC.mul, o));
      let top = "";
      if (p.cn !== 1n || !numF.length) top = p.cn.toString();
      for (const f of numF) {
        if (!top) top = f;
        else top += (/^[0-9]/.test(f) || /[0-9]$/.test(top) && /^[0-9(]/.test(f) === false && false ? "*" : needsStar(top, f) ? "*" : "") + f;
      }
      let s = top;
      const denF = p.den.map((f) => txt(f, PREC.pow, o));
      if (p.cd !== 1n) denF.unshift(p.cd.toString());
      if (denF.length) {
        const joined = denF.reduce((acc, f) => (acc ? acc + (needsStar(acc, f) ? "*" : "") + f : f), "");
        const d = denF.length === 1 ? denF[0] : "(" + joined + ")";
        const t = numF.length > 1 || (numF.length === 1 && p.cn !== 1n) ? `${s}` : s;
        s = `${needsParenTop(t, p) ? `(${t})` : t}/${d}`;
      }
      return (p.neg ? "-" : "") + s;
    }
    case "pow": {
      const [b, e] = u.args;
      if (X.isNum(e)) {
        if (N.isNeg(e.v)) {
          const pos = N.neg(e.v);
          return "1/" + txt(N.isOne(pos) ? b : X.pow(b, X.num(pos)), PREC.pow, o);
        }
        if (e.v.n === 1n && e.v.d === 2n) return `sqrt(${txt(b, 0, o)})`;
        if (e.v.n === 1n && e.v.d === 3n) return `cbrt(${txt(b, 0, o)})`;
      }
      if (b === X.E) return `e^${txt(e, PREC.atom, o)}`;
      return `${txt(b, PREC.pow + 1, o)}^${txt(e, PREC.atom, o)}`;
    }
    case "fn": {
      const a = u.args;
      if (u.name === "abs") return `|${txt(a[0], 0, o)}|`;
      if (u.name === "factorial") return `${txt(a[0], PREC.atom, o)}!`;
      if (u.name === "log") {
        if (X.isNum(a[0]) && a[0].v.n === 10n && a[0].v.d === 1n) return `log(${txt(a[1], 0, o)})`;
        return `log_${txt(a[0], PREC.atom, o)}(${txt(a[1], 0, o)})`;
      }
      if (u.name === "pm") return `${txt(a[0], PREC.add, o)} +- ${txt(a[1], PREC.add + 1, o)}`;
      return `${fnName[u.name] || u.name}(${a.map((x) => txt(x, 0, o)).join(", ")})`;
    }
    case "eq": return `${txt(u.args[0], 1, o)} = ${txt(u.args[1], 1, o)}`;
    case "rel": return `${txt(u.args[0], 1, o)} ${u.op} ${txt(u.args[1], 1, o)}`;
    case "and": {
      const [a, b] = u.args;
      if (u.args.length === 2 && a.k === "rel" && b.k === "rel" && a.args[1] === b.args[0] && a.op[0] === b.op[0] && "<>".includes(a.op[0]))
        return `${txt(a.args[0], 1, o)} ${a.op} ${txt(a.args[1], 1, o)} ${b.op} ${txt(b.args[1], 1, o)}`;
      return u.args.map((x) => txt(x, 0, o)).join(" and ");
    }
    case "or": return u.args.map((x) => txt(x, 0, o)).join(" or ");
    case "not": return `not ${txt(u.args[0], PREC.atom, o)}`;
    case "system": return u.args.map((a) => txt(a, 0, o)).join(", ");
    case "tuple": return `(${u.args.map((a) => txt(a, 0, o)).join(", ")})`;
    case "vector": return `[${u.args.map((a) => txt(a, 0, o)).join(", ")}]`;
    case "matrix": return `[${u.args.map((r) => `[${r.args.map((a) => txt(a, 0, o)).join(", ")}]`).join(", ")}]`;
    case "set": return `{${u.args.map((a) => txt(a, 0, o)).join(", ")}}`;
    case "interval": return `${u.lo_open ? "(" : "["}${txt(u.args[0], 0, o)}, ${txt(u.args[1], 0, o)}${u.hi_open ? ")" : "]"}`;
    case "piecewise": {
      const parts = [];
      for (let i = 0; i < u.args.length; i += 2) parts.push(`${txt(u.args[i], 0, o)} if ${txt(u.args[i + 1], 0, o)}`);
      return `piecewise(${parts.join("; ")})`;
    }
    case "deriv": {
      const [e, v, n] = u.args;
      const ord = X.isOne(n) ? "" : `^${txt(n, PREC.atom, o)}`;
      return `d${ord}/d${v.name}${ord} (${txt(e, 0, o)})`;
    }
    case "integral": {
      const [e, v, lo, hi] = u.args;
      return lo ? `integrate(${txt(e, 0, o)}, ${v.name}, ${txt(lo, 0, o)}, ${txt(hi, 0, o)})` : `integrate(${txt(e, 0, o)}, ${v.name})`;
    }
    case "limit": {
      const [e, v, to] = u.args;
      return `lim ${v.name}->${txt(to, PREC.add + 1, o)}${u.dir} (${txt(e, 0, o)})`;
    }
    case "sum": case "product": {
      const [e, v, lo, hi] = u.args;
      return `${u.k === "sum" ? "sum" : "prod"}(${txt(e, 0, o)}, ${v.name}, ${txt(lo, 0, o)}, ${txt(hi, 0, o)})`;
    }
    case "fndef": return `${u.name}(${u.args[0].args.map((a) => txt(a, 0, o)).join(", ")}) = ${txt(u.args[1], 0, o)}`;
    case "quant": return `${u.q} ${txt(u.args[0], 0, o)}: ${txt(u.args[1], 0, o)}`;
    default: return `${u.k}(${u.args.map((a) => txt(a, 0, o)).join(", ")})`;
  }
}
function negateCoeff(t) {
  const fs = t.args.slice();
  fs[0] = X.num(N.neg(fs[0].v));
  return N.isOne(fs[0].v) ? fs.slice(1) : fs;
}
function needsStar(left, right) {
  // keep output re-parseable and readable: 2x, 2sqrt(3), x*y
  if (/[0-9]$/.test(left) && /^[0-9]/.test(right)) return true;
  if (/[A-Za-z0-9_)]$/.test(left) && /^[A-Za-z]/.test(right) && !/[0-9]$/.test(left)) return true;
  if (/(^|[^A-Za-z])[fgh]$|[A-Za-z]{2,}$/.test(left) && /^\(/.test(right)) return true; // f(…) would read as a call
  if (/\)$/.test(left) && /^[0-9]/.test(right)) return true;
  if (/!$/.test(left)) return true;
  return false;
}
function needsParenTop(t, p) {
  return p.num.length > 1 || (p.num.length === 1 && p.cn !== 1n) ? /[+\-]/.test(t.replace(/^-/, "")) && false : false;
}

// ---------------- LaTeX ----------------
export function toLatex(u) {
  return tex(u, 0);
}
function texWrap(s, need, have) {
  return have < need ? `\\left(${s}\\right)` : s;
}
function tex(u, need) {
  return texWrap(texRaw(u), need, precOf(u));
}
const TEX_FN = {
  sin: "\\sin", cos: "\\cos", tan: "\\tan", cot: "\\cot", sec: "\\sec", csc: "\\csc",
  asin: "\\arcsin", acos: "\\arccos", atan: "\\arctan", sinh: "\\sinh", cosh: "\\cosh", tanh: "\\tanh",
  ln: "\\ln", exp: "\\exp", gcd: "\\gcd", det: "\\det", max: "\\max", min: "\\min",
};
const GREEK = new Set(["alpha", "beta", "gamma", "delta", "epsilon", "zeta", "eta", "theta", "iota", "kappa", "lambda", "mu", "nu", "xi", "rho", "sigma", "tau", "upsilon", "phi", "chi", "psi", "omega", "Gamma", "Delta", "Theta", "Lambda", "Xi", "Pi", "Sigma", "Phi", "Psi", "Omega"]);
function texSym(name) {
  const [base, sub] = name.split("_");
  const b = GREEK.has(base) ? "\\" + base : base.length > 1 ? `\\mathrm{${base}}` : base;
  return sub ? `${b}_{${sub}}` : b;
}
function texRaw(u) {
  switch (u.k) {
    case "num": return u.v.d === 1n ? u.v.n.toString() : `${N.isNeg(u.v) ? "-" : ""}\\frac{${N.babs(u.v.n)}}{${u.v.d}}`;
    case "sym": return texSym(u.name);
    case "const": return { pi: "\\pi", e: "e", I: "i", oo: "\\infty", undef: "\\text{undefined}" }[u.name];
    case "bool": return u.v ? "\\text{true}" : "\\text{false}";
    case "unit": return `\\,\\mathrm{${u.name}}`;
    case "add": {
      const ts = displayTerms(u);
      let s = "";
      ts.forEach((t, i) => {
        let neg = false, body;
        if (X.isNum(t) && N.isNeg(t.v)) { neg = true; body = tex(X.num(N.neg(t.v)), PREC.add); }
        else if (t.k === "mul" && fracParts(t).neg) { neg = true; body = tex(X.mul(...negateCoeff(t)), PREC.add + 1); }
        else body = tex(t, PREC.add);
        s += i === 0 ? (neg ? "-" : "") + body : (neg ? " - " : " + ") + body;
      });
      return s;
    }
    case "mul": {
      const p = fracParts(u);
      const numF = p.num.map((f) => tex(f, PREC.mul));
      let top = p.cn !== 1n || !numF.length ? p.cn.toString() : "";
      for (const f of numF) top = top ? top + (/[0-9]$/.test(top) && /^[0-9]/.test(f) ? " \\cdot " : " ") + f : f;
      const den = p.den.map((f) => tex(f, PREC.mul));
      if (p.cd !== 1n) den.unshift(p.cd.toString());
      const s = den.length ? `\\frac{${top || "1"}}{${den.join(" ")}}` : top;
      return (p.neg ? "-" : "") + s;
    }
    case "pow": {
      const [b, e] = u.args;
      if (X.isNum(e)) {
        if (N.isNeg(e.v)) {
          const pos = N.neg(e.v);
          return `\\frac{1}{${tex(N.isOne(pos) ? b : X.pow(b, X.num(pos)), 0)}}`;
        }
        if (e.v.n === 1n && e.v.d === 2n) return `\\sqrt{${tex(b, 0)}}`;
        if (e.v.n === 1n) return `\\sqrt[${e.v.d}]{${tex(b, 0)}}`;
      }
      return `${tex(b, PREC.pow + 1)}^{${tex(e, 0)}}`;
    }
    case "fn": {
      const a = u.args;
      if (u.name === "abs") return `\\left|${tex(a[0], 0)}\\right|`;
      if (u.name === "factorial") return `${tex(a[0], PREC.atom)}!`;
      if (u.name === "floor") return `\\left\\lfloor ${tex(a[0], 0)}\\right\\rfloor`;
      if (u.name === "ceil") return `\\left\\lceil ${tex(a[0], 0)}\\right\\rceil`;
      if (u.name === "binomial" && a.length === 2) return `\\binom{${tex(a[0], 0)}}{${tex(a[1], 0)}}`;
      if (u.name === "log") {
        if (X.isNum(a[0]) && a[0].v.n === 10n && a[0].v.d === 1n) return `\\log\\left(${tex(a[1], 0)}\\right)`;
        return `\\log_{${tex(a[0], 0)}}\\left(${tex(a[1], 0)}\\right)`;
      }
      if (u.name === "pm") return `${tex(a[0], PREC.add)} \\pm ${tex(a[1], PREC.add + 1)}`;
      const name = TEX_FN[u.name] || (u.name.length > 1 ? `\\operatorname{${u.name}}` : u.name);
      return `${name}\\left(${a.map((x) => tex(x, 0)).join(", ")}\\right)`;
    }
    case "eq": return `${tex(u.args[0], 1)} = ${tex(u.args[1], 1)}`;
    case "rel": return `${tex(u.args[0], 1)} ${{ "<": "<", "<=": "\\le", ">": ">", ">=": "\\ge", "!=": "\\ne" }[u.op]} ${tex(u.args[1], 1)}`;
    case "and": return u.args.map((a) => tex(a, 0)).join(" \\text{ and } ");
    case "or": return u.args.map((a) => tex(a, 0)).join(" \\text{ or } ");
    case "system": return `\\begin{cases} ${u.args.map((a) => tex(a, 0)).join(" \\\\ ")} \\end{cases}`;
    case "tuple": return `\\left(${u.args.map((a) => tex(a, 0)).join(", ")}\\right)`;
    case "vector": return `\\begin{bmatrix} ${u.args.map((a) => tex(a, 0)).join(" \\\\ ")} \\end{bmatrix}`;
    case "matrix": return `\\begin{bmatrix} ${u.args.map((r) => r.args.map((a) => tex(a, 0)).join(" & ")).join(" \\\\ ")} \\end{bmatrix}`;
    case "set": return `\\left\\{${u.args.map((a) => tex(a, 0)).join(", ")}\\right\\}`;
    case "interval": return `${u.lo_open ? "\\left(" : "\\left["}${tex(u.args[0], 0)}, ${tex(u.args[1], 0)}${u.hi_open ? "\\right)" : "\\right]"}`;
    case "piecewise": {
      const rows = [];
      for (let i = 0; i < u.args.length; i += 2) rows.push(`${tex(u.args[i], 0)} & ${u.args[i + 1] === X.TRUE ? "\\text{otherwise}" : tex(u.args[i + 1], 0)}`);
      return `\\begin{cases} ${rows.join(" \\\\ ")} \\end{cases}`;
    }
    case "deriv": {
      const [e, v, n] = u.args;
      const ord = X.isOne(n) ? "" : `^{${tex(n, 0)}}`;
      return `\\frac{d${ord}}{d${texSym(v.name)}${ord}}\\left(${tex(e, 0)}\\right)`;
    }
    case "integral": {
      const [e, v, lo, hi] = u.args;
      return `\\int${lo ? `_{${tex(lo, 0)}}^{${tex(hi, 0)}}` : ""} ${tex(e, PREC.mul)} \\, d${texSym(v.name)}`;
    }
    case "limit": {
      const [e, v, to] = u.args;
      return `\\lim_{${texSym(v.name)} \\to ${tex(to, 0)}${u.dir ? `^{${u.dir}}` : ""}} ${tex(e, PREC.mul)}`;
    }
    case "sum": case "product": {
      const [e, v, lo, hi] = u.args;
      return `\\${u.k === "sum" ? "sum" : "prod"}_{${texSym(v.name)}=${tex(lo, 0)}}^{${tex(hi, 0)}} ${tex(e, PREC.mul)}`;
    }
    case "fndef": return `${u.name}\\left(${u.args[0].args.map((a) => tex(a, 0)).join(", ")}\\right) = ${tex(u.args[1], 0)}`;
    default: return `\\operatorname{${u.k}}\\left(${u.args.map((a) => tex(a, 0)).join(", ")}\\right)`;
  }
}
