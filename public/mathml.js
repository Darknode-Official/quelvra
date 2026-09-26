// Quelvra MathML renderer: math tree -> MathML Core markup (rendered natively by the browser).
//
//   toMathML(u, { display, highlight, alttext })  -> "<math ...>...</math>"
//   mathmlBody(u, { highlight })                  -> inner markup (no <math> wrapper)
//   mathmlFromText(src, opts)                     -> { ok, mathml, tree, error }
//   changedIds(before, after)                     -> Set of node ids in `after` that are new
//
// Display order follows print.js: sums print highest degree first, negative terms as
// subtraction, negative powers and rational coefficients as fractions. Pure module: no DOM.

import * as N from "./engine/num.js";
import * as X from "./engine/expr.js";
import { parseDetailed } from "./engine/parse.js";

const PREC = { rel: 0, add: 1, mul: 2, neg: 2, pow: 4, atom: 5 };
const NS = 'xmlns="http://www.w3.org/1998/Math/MathML"';

const GREEK = {
  alpha: "α", beta: "β", gamma: "γ", delta: "δ", epsilon: "ϵ", varepsilon: "ε",
  zeta: "ζ", eta: "η", theta: "θ", vartheta: "ϑ", iota: "ι", kappa: "κ",
  lambda: "λ", mu: "μ", nu: "ν", xi: "ξ", omicron: "ο", rho: "ρ", sigma: "σ",
  tau: "τ", upsilon: "υ", phi: "ϕ", varphi: "φ", chi: "χ", psi: "ψ", omega: "ω",
  Gamma: "Γ", Delta: "Δ", Theta: "Θ", Lambda: "Λ", Xi: "Ξ", Pi: "Π",
  Sigma: "Σ", Phi: "Φ", Psi: "Ψ", Omega: "Ω",
};
const FN_NAME = { asin: "arcsin", acos: "arccos", atan: "arctan", acot: "arccot", asec: "arcsec", acsc: "arccsc" };
const REL_OP = { "<": "&lt;", "<=": "≤", ">": "&gt;", ">=": "≥", "!=": "≠" };
const MINUS = "−", TIMES_INVIS = "⁢", APPLY = "⁡", CDOT = "⋅";

export function esc(s) {
  return String(s).replace(/&/g, "&amp;").replace(/</g, "&lt;").replace(/>/g, "&gt;").replace(/"/g, "&quot;");
}

// ---------- display ordering (mirrors print.js) ----------
function degreeKey(t) {
  if (X.isNum(t)) return -1;
  if (t.k === "sym" || t.k === "const") return 1;
  if (t.k === "pow") {
    const e = t.args[1];
    return X.isNum(e) ? N.toFloat(e.v) * Math.max(0, degreeKey(t.args[0])) : 1;
  }
  if (t.k === "mul") return t.args.reduce((s, f) => s + Math.max(0, degreeKey(f)), 0);
  return 0.5;
}
const leadNeg = (t) => ((X.isNum(t) ? N.isNeg(t.v) : t.k === "mul" && X.isNum(t.args[0]) && N.isNeg(t.args[0].v)) ? 1 : 0);
function factorRank(f) {
  const b = f.k === "pow" ? f.args[0] : f;
  if (b.k === "sym" || b.k === "const") return f.k === "pow" && X.isNum(f.args[1]) && f.args[1].v.d !== 1n ? 2 : 1;
  if (b.k === "fn") return 3;
  if (b.k === "unit") return 5;
  return 4;
}
const displayFactors = (fs) => fs.map((f, i) => [f, i]).sort((a, b) => factorRank(a[0]) - factorRank(b[0]) || a[1] - b[1]).map(([f]) => f);
// a + bi: in a constant complex number the real part comes first (11 - 2i, not -2i + 11)
const hasI = (t) => t === X.I || (t.args || []).some(hasI);
export function displayTerms(u) {
  const ts = displayTermsRaw(u);
  return ts.some(hasI) && !ts.every(hasI) && X.freeSymbols(u).size === 0 ? [...ts.filter((t) => !hasI(t)), ...ts.filter(hasI)] : ts;
}
function displayTermsRaw(u) {
  return u.args
    .map((t, i) => [t, i])
    .sort((a, b) => degreeKey(b[0]) - degreeKey(a[0]) || leadNeg(a[0]) - leadNeg(b[0]) || a[1] - b[1])
    .map(([t]) => t);
}
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
function negateCoeff(t) {
  const fs = t.args.slice();
  fs[0] = X.num(N.neg(fs[0].v));
  return N.isOne(fs[0].v) ? fs.slice(1) : fs;
}
function precOf(u) {
  switch (u.k) {
    case "add": return PREC.add;
    case "mul": return fracParts(u).neg ? PREC.neg : PREC.mul;
    case "num": return u.v.d !== 1n ? PREC.mul : N.isNeg(u.v) ? PREC.neg : PREC.atom;
    case "pow": {
      const e = u.args[1];
      if (X.isNum(e) && N.isNeg(e.v)) return PREC.mul;
      if (X.isNum(e) && e.v.n === 1n) return PREC.atom; // radicals
      return PREC.pow;
    }
    case "eq": case "rel": case "and": case "or": return PREC.rel;
    case "fn": return u.name === "pm" ? PREC.add : PREC.atom;
    case "integral": case "sum": case "product": case "limit": case "deriv": return PREC.mul;
    default: return PREC.atom;
  }
}

// ---------- element helpers ----------
const mrow = (...xs) => `<mrow>${xs.join("")}</mrow>`;
const mo = (s, attrs = "") => `<mo${attrs}>${s}</mo>`;
const mi = (s, attrs = "") => `<mi${attrs}>${s}</mi>`;
const mn = (s) => `<mn>${s}</mn>`;
const mtext = (s) => `<mtext>${esc(s)}</mtext>`;
const paren = (inner, l = "(", r = ")") => mrow(mo(l), inner, mo(r));
const frac = (a, b) => `<mfrac>${mrow(a)}${mrow(b)}</mfrac>`;
const sup = (a, b) => `<msup>${mrow(a)}${mrow(b)}</msup>`;
const sub = (a, b) => `<msub>${mrow(a)}${mrow(b)}</msub>`;
const space = (w = "0.1667em") => `<mspace width="${w}"></mspace>`;
const table = (rows, align = "left") =>
  `<mtable columnalign="${align}">${rows.map((r) => `<mtr>${r.map((c) => `<mtd>${c}</mtd>`).join("")}</mtr>`).join("")}</mtable>`;

function symML(name) {
  const m = String(name).match(/^([A-Za-z]+)(?:_\{?([A-Za-z0-9]+)\}?)?$/);
  if (!m) return mi(esc(name));
  const [, base, subs] = m;
  let b;
  if (GREEK[base]) b = mi(GREEK[base]);
  else if (base.length > 1) b = mi(esc(base), ' mathvariant="normal"');
  else b = mi(esc(base));
  if (!subs) return b;
  const s = /^\d+$/.test(subs) ? mn(subs) : symML(subs);
  return `<msub>${b}${s}</msub>`;
}
function numML(r) {
  if (r.d === 1n) return N.isNeg(r) ? mrow(mo(MINUS), mn(N.babs(r.n).toString())) : mn(r.n.toString());
  const f = frac(mn(N.babs(r.n).toString()), mn(r.d.toString()));
  return N.isNeg(r) ? mrow(mo(MINUS), f) : f;
}
const CONST_ML = { pi: mi("π"), e: mi("e"), I: mi("i"), oo: mi("∞"), undef: mtext("undefined") };

// Does this factor's rendering start with a digit (so juxtaposition would be ambiguous)?
function startsWithDigit(f) {
  if (X.isNum(f)) return true;
  if (f.k === "pow") {
    const e = f.args[1];
    if (X.isNum(e) && (N.isNeg(e.v) || e.v.n === 1n)) return false;
    return startsWithDigit(f.args[0]) && precOf(f.args[0]) > PREC.pow;
  }
  if (f.k === "mul") return startsWithDigit(f.args[0]);
  return false;
}

// ---------- renderer ----------
class R {
  constructor(opts = {}) {
    this.hl = opts.highlight instanceof Set ? opts.highlight : opts.highlight ? new Set(opts.highlight) : null;
  }
  w(u, need) {
    const s = this.raw(u);
    const out = precOf(u) < need ? paren(s) : s;
    return this.hl && this.hl.has(u.id) ? `<mrow class="changed">${out}</mrow>` : out;
  }
  // numerator/denominator product (no leading sign, used inside fractions)
  prod(cn, factors) {
    const parts = [];
    if (cn !== 1n || !factors.length) parts.push(mn(cn.toString()));
    for (const f of factors) {
      if (parts.length) parts.push(f.k === "unit" ? space() : mo(startsWithDigit(f) ? CDOT : TIMES_INVIS));
      parts.push(this.w(f, PREC.mul));
    }
    return parts.length === 1 ? parts[0] : mrow(...parts);
  }
  args(list) {
    const out = [];
    list.forEach((a, i) => { if (i) out.push(mo(",")); out.push(this.w(a, 0)); });
    return mrow(...out);
  }
  callFn(nameML, args) {
    return mrow(nameML, mo(APPLY), paren(this.args(args)));
  }
  raw(u) {
    switch (u.k) {
      case "num": return numML(u.v);
      case "sym": return symML(u.name);
      case "const": return CONST_ML[u.name] || mi(esc(u.name));
      case "bool": return mtext(u.v ? "true" : "false");
      case "unit": return mi(esc(u.name), ' mathvariant="normal" class="unit"');
      case "add": {
        const out = [];
        displayTerms(u).forEach((t, i) => {
          let neg = false, body;
          if (X.isNum(t) && N.isNeg(t.v)) { neg = true; body = this.w(X.num(N.neg(t.v)), PREC.add); }
          else if (t.k === "mul" && fracParts(t).neg) {
            neg = true;
            const pos = X.mul(...negateCoeff(t));
            body = this.hl && this.hl.has(t.id) ? `<mrow class="changed">${this.w(pos, PREC.add + 1)}</mrow>` : this.w(pos, PREC.add + 1);
          } else body = this.w(t, PREC.add);
          if (i === 0) out.push(neg ? mo(MINUS) : "", body);
          else out.push(mo(neg ? MINUS : "+"), body);
        });
        return mrow(...out);
      }
      case "mul": {
        const p = fracParts(u);
        let s;
        if (p.den.length || p.cd !== 1n) {
          const top = this.prod(p.cn, p.num);
          const bottom = this.prod(p.cd, p.den);
          s = frac(top, bottom);
          // keep units outside the fraction bar when they are the only numerator factor besides a number
        } else s = this.prod(p.cn, p.num);
        return p.neg ? mrow(mo(MINUS), s) : s;
      }
      case "pow": {
        const [b, e] = u.args;
        if (X.isNum(e)) {
          if (N.isNeg(e.v)) {
            const pos = N.neg(e.v);
            return frac(mn("1"), this.w(N.isOne(pos) ? b : X.pow(b, X.num(pos)), 0));
          }
          if (e.v.n === 1n && e.v.d === 2n) return `<msqrt>${this.w(b, 0)}</msqrt>`;
          if (e.v.n === 1n) return `<mroot>${mrow(this.w(b, 0))}${mn(e.v.d.toString())}</mroot>`;
        }
        // unsimplified root(x, n) = x^(n^-1)
        if (e.k === "pow" && e.args[1] === X.NEG_ONE && X.isInt(e.args[0]) && e.args[0].v.n > 1n)
          return `<mroot>${mrow(this.w(b, 0))}${mn(e.args[0].v.n.toString())}</mroot>`;
        // f(x)^n for named functions keeps the call intact: sin(x)^2
        return sup(this.w(b, PREC.pow + 1), this.w(e, 0));
      }
      case "fn": return this.fn(u);
      case "eq": return mrow(this.w(u.args[0], 1), mo("="), this.w(u.args[1], 1));
      case "rel": return mrow(this.w(u.args[0], 1), mo(REL_OP[u.op] || esc(u.op)), this.w(u.args[1], 1));
      case "and": {
        const [a, b] = u.args;
        if (u.args.length === 2 && a.k === "rel" && b.k === "rel" && a.args[1] === b.args[0] && a.op[0] === b.op[0] && "<>".includes(a.op[0]))
          return mrow(this.w(a.args[0], 1), mo(REL_OP[a.op]), this.w(a.args[1], 1), mo(REL_OP[b.op]), this.w(b.args[1], 1));
        return this.joined(u.args, mtext(" and "));
      }
      case "or": return this.joined(u.args, mtext(" or "));
      case "not": return mrow(mo("¬"), this.w(u.args[0], PREC.atom));
      case "system":
        return mrow(mo("{", ' stretchy="true"'), table(u.args.map((a) => [this.w(a, 0)])));
      case "tuple": return paren(this.args(u.args));
      case "vector": return paren(table(u.args.map((a) => [this.w(a, 0)]), "center"), "[", "]");
      case "matrix": return paren(table(u.args.map((r) => r.args.map((a) => this.w(a, 0))), "center"), "[", "]");
      case "set": return u.args.length ? paren(this.args(u.args), "{", "}") : mi("∅");
      case "interval":
        return mrow(mo(u.lo_open ? "(" : "["), this.w(u.args[0], 0), mo(","), this.w(u.args[1], 0), mo(u.hi_open ? ")" : "]"));
      case "piecewise": {
        const rows = [];
        for (let i = 0; i < u.args.length; i += 2) {
          const c = u.args[i + 1];
          rows.push([this.w(u.args[i], 0), c === X.TRUE || c === undefined ? mtext("otherwise") : mrow(mtext("if "), this.w(c, 0))]);
        }
        return mrow(mo("{", ' stretchy="true"'), table(rows));
      }
      case "deriv": {
        const [e, v, n] = u.args;
        const one = X.isOne(n);
        const d = mi("d", ' mathvariant="normal"');
        const top = one ? d : sup(d, this.w(n, 0));
        const bottom = one ? mrow(d, symML(v.name)) : mrow(d, sup(symML(v.name), this.w(n, 0)));
        const body = e.k === "fn" && !["abs", "factorial"].includes(e.name) ? this.w(e, 0) : precOf(e) >= PREC.atom ? this.w(e, 0) : paren(this.w(e, 0));
        return mrow(frac(top, bottom), body);
      }
      case "integral": {
        const [e, v, lo, hi] = u.args;
        const sign = lo ? `<msubsup>${mo("∫")}${mrow(this.w(lo, 0))}${mrow(this.w(hi, 0))}</msubsup>` : mo("∫");
        return mrow(sign, this.w(e, PREC.mul), space(), mi("d", ' mathvariant="normal"'), symML(v.name));
      }
      case "limit": {
        const [e, v, to] = u.args;
        let target = this.w(to, 0);
        if (u.dir) target = sup(target, mo(u.dir === "-" ? MINUS : "+"));
        const under = mrow(symML(v.name), mo("→"), target);
        return mrow(`<munder>${mi("lim", ' mathvariant="normal"')}${under}</munder>`, space(), this.w(e, PREC.mul));
      }
      case "sum": case "product": {
        const [e, v, lo, hi] = u.args;
        const op = mo(u.k === "sum" ? "∑" : "∏", ' largeop="true" movablelimits="false"');
        return mrow(`<munderover>${op}${mrow(symML(v.name), mo("="), this.w(lo, 0))}${mrow(this.w(hi, 0))}</munderover>`, this.w(e, PREC.mul));
      }
      case "fndef":
        return mrow(this.callFn(symML(u.name), u.args[0].args), mo("="), this.w(u.args[1], 0));
      case "quant":
        return mrow(mo(u.q === "exists" ? "∃" : "∀"), this.w(u.args[0], 0), mo(":"), this.w(u.args[1], 0));
      default:
        return this.callFn(mi(esc(u.k), ' mathvariant="normal"'), u.args);
    }
  }
  joined(list, sep) {
    const out = [];
    list.forEach((a, i) => { if (i) out.push(sep); out.push(this.w(a, 0)); });
    return mrow(...out);
  }
  fn(u) {
    const a = u.args;
    switch (u.name) {
      case "abs": return mrow(mo("|"), this.w(a[0], 0), mo("|"));
      case "floor": return mrow(mo("⌊"), this.w(a[0], 0), mo("⌋"));
      case "ceil": return mrow(mo("⌈"), this.w(a[0], 0), mo("⌉"));
      case "factorial": return mrow(this.w(a[0], PREC.atom), mo("!"));
      case "factorial2": return mrow(this.w(a[0], PREC.atom), mo("!!"));
      case "binomial": case "nCr": return paren(`<mfrac linethickness="0">${mrow(this.w(a[0], 0))}${mrow(this.w(a[1], 0))}</mfrac>`);
      case "pm": return mrow(this.w(a[0], PREC.add), mo("±"), this.w(a[1], PREC.add + 1));
      case "approx": return mrow(this.w(a[0], 1), mo("≈"), this.w(a[1], 1));
      case "prime": return mrow(this.w(a[0], PREC.atom), mo("′"));
      case "conj": return `<mover>${mrow(this.w(a[0], 0))}${mo("¯", ' stretchy="true"')}</mover>`;
      case "log": {
        if (a.length === 2) {
          if (X.isNum(a[0]) && a[0].v.n === 10n && a[0].v.d === 1n) return this.callFn(mi("log"), [a[1]]);
          return mrow(sub(mi("log"), this.w(a[0], 0)), mo(APPLY), paren(this.w(a[1], 0)));
        }
        return this.callFn(mi("log"), a);
      }
      case "mod": return mrow(this.w(a[0], PREC.mul), space("0.4em"), mi("mod", ' mathvariant="normal"'), space("0.4em"), this.w(a[1], PREC.mul + 1));
      default: {
        const name = FN_NAME[u.name] || u.name;
        const nm = name.length > 1 ? mi(esc(name), ' mathvariant="normal"') : symML(name);
        return this.callFn(nm, a);
      }
    }
  }
}

export function mathmlBody(u, opts = {}) {
  return new R(opts).w(u, 0);
}

export function toMathML(u, opts = {}) {
  const display = opts.display === false ? "inline" : "block";
  const alt = opts.alttext ? ` alttext="${esc(opts.alttext)}"` : "";
  return `<math ${NS} display="${display}"${alt}>${mathmlBody(u, opts)}</math>`;
}

// Parse text and render; never throws.
export function mathmlFromText(src, opts = {}) {
  try {
    const { node, warnings } = parseDetailed(src);
    return { ok: true, tree: node, warnings, mathml: toMathML(node, opts) };
  } catch (e) {
    return {
      ok: false,
      error: { message: e && e.message ? e.message : String(e), pos: e && typeof e.pos === "number" ? e.pos : null, hint: (e && e.hint) || "" },
    };
  }
}

// Ids of the maximal subtrees of `after` that do not occur anywhere in `before`.
// Hash-consing makes "occurs" an identity test, so unchanged parts are never highlighted.
export function changedIds(before, after) {
  const out = new Set();
  if (!before || !after || before === after) return out;
  const seen = new Set();
  const collect = (u) => { if (seen.has(u.id)) return; seen.add(u.id); for (const a of u.args) collect(a); };
  collect(before);
  const walk = (u) => {
    if (seen.has(u.id)) return;
    // if some child is unchanged the node itself is new but only mark the changed children
    const kids = u.args.filter((a) => !seen.has(a.id));
    // leaves, wholly new nodes, and new nodes built only from reused parts are marked as a unit
    if (!u.args.length || kids.length === u.args.length || kids.length === 0) { out.add(u.id); return; }
    for (const a of kids) walk(a);
  };
  walk(after);
  // a root whose children were all reused (e.g. reordering) still counts as changed
  if (!out.size) out.add(after.id);
  return out;
}
