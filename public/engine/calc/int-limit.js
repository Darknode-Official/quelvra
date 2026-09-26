// Limits for the definite-integral module.
//
//   lim(u, x, to, dir) -> { k: "fin", v: tree } | { k: "inf", s: +1 | -1 } | { k: "dne", reason } | { k: "unknown", reason }
//
// Elementary expressions go to calc/limit.js (series / Gruntz / L'Hopital, each proven). Expressions that
// contain the special functions of the integrator (erf, erfi, Si, Ci, Shi, Chi, Ei, li, FresnelS, FresnelC),
// which limit.js does not know, are split with the sum and product rules of limits; each special function
// is replaced by its known limit (or its value where it is continuous). Indeterminate combinations are
// reported as unknown, never guessed.

import * as X from "../expr.js";
import { limit as extLimit } from "./limit.js";
import { canon, evalD, SPECIAL } from "./int-util.js";
import { toText } from "../print.js";
import { setPrinter as setLimitPrinter } from "./limit.js";

setLimitPrinter(toText);
const usesSpecial = (u) => (u.k === "fn" && SPECIAL.has(u.name)) || u.args.some(usesSpecial);

const { ZERO, ONE, HALF, PI, OO } = X;
export const NEG_OO = X.mul(X.NEG_ONE, OO);
export const isNegInf = (u) => u === NEG_OO || (u.k === "mul" && u.args.length === 2 && X.isNum(u.args[0]) && u.args[0].v.n < 0n && u.args[1] === OO);
export const isInf = (u) => u === OO || isNegInf(u);

const FIN = (v) => ({ k: "fin", v: canon(v) });
const INF = (s) => ({ k: "inf", s });
const UNK = (reason) => ({ k: "unknown", reason });

// behaviour of the special functions: value at +oo, -oo (null = not real / unknown), and points where
// they tend to -oo (logarithmic singularities)
const SPEC = {
  erf: { pos: FIN(ONE), neg: FIN(X.NEG_ONE), odd: true },
  erfi: { pos: INF(1), neg: INF(-1), odd: true },
  Si: { pos: FIN(X.mul(HALF, PI)), neg: FIN(X.mul(X.num(-1, 2), PI)), odd: true },
  Ci: { pos: FIN(ZERO), neg: null, sing: [ZERO] },
  Shi: { pos: INF(1), neg: INF(-1), odd: true },
  Chi: { pos: INF(1), neg: null, sing: [ZERO] },
  Ei: { pos: INF(1), neg: FIN(ZERO), sing: [ZERO] },
  li: { pos: INF(1), neg: null, sing: [ONE], zeroAt0: true },
  FresnelS: { pos: FIN(HALF), neg: FIN(X.num(-1, 2)), odd: true },
  FresnelC: { pos: FIN(HALF), neg: FIN(X.num(-1, 2)), odd: true },
};

function fromExt(r) {
  if (r.status === "exact") {
    const v = r.value;
    if (v === OO) return INF(1);
    if (isNegInf(v)) return INF(-1);
    if (X.contains(v, OO) || v === X.UNDEF) return UNK("limit value not a real number");
    return FIN(v);
  }
  if (r.status === "dne") return { k: "dne", reason: r.reason };
  return UNK(r.reason || "limit unknown");
}

// sign of a finite constant tree (numerically, with a safety margin); 0 only for an exact zero
function signOf(v) {
  if (v === ZERO) return 0;
  const d = evalD(v);
  if (!Number.isFinite(d) || Math.abs(d) < 1e-12) return null;
  return d > 0 ? 1 : -1;
}

export function lim(u, x, to, dir = "", opts = {}) {
  const depth = opts.depth || 0;
  u = canon(u);
  if (X.freeOf(u, x)) return FIN(u);
  if (depth > 12) return UNK("expression too deep");
  if (!usesSpecial(u)) {
    try { return fromExt(extLimit(u, x, to, dir, { timeLimit: opts.timeLimit || 3000 })); } catch (e) {
      if (e && e.code) return UNK(e.message);
      if (e instanceof RangeError) {
        // retry mirrored (x = -y) when the point is negative: the simplifier's recursion is triggered by
        // trig / atan of all-negative sums, which the mirror image avoids
        const tv = evalD(to);
        if (!opts.mirrored && Number.isFinite(tv) && tv < 0) {
          try {
            const um = canon(X.subs(u, { [x.name]: X.neg(x) }));
            return lim(um, x, canon(X.neg(to)), dir === "+" ? "-" : dir === "-" ? "+" : "", { ...opts, mirrored: true });
          } catch (e2) { if (!(e2 instanceof RangeError) && !(e2 && e2.code)) throw e2; }
        }
        return UNK("the simplifier recursed without end on this limit");
      }
      throw e;
    }
  }
  const sub = (w) => lim(w, x, to, dir, { ...opts, depth: depth + 1 });
  if (u.k === "add") {
    // elementary part as one piece (so that cancellations inside it are handled by limit.js)
    const el = u.args.filter((t) => !usesSpecial(t)), sp = u.args.filter((t) => usesSpecial(t));
    const parts = [...(el.length ? [sub(X.add(...el))] : []), ...sp.map(sub)];
    let fin = ZERO, infS = 0;
    for (const p of parts) {
      if (p.k === "unknown") return p;
      if (p.k === "dne") return parts.every((q) => q === p || q.k === "fin") ? p : UNK("oscillating term combined with others");
      if (p.k === "inf") { if (infS && infS !== p.s) return UNK("oo - oo"); infS = p.s; } else fin = X.add(fin, p.v);
    }
    return infS ? INF(infS) : FIN(fin);
  }
  if (u.k === "mul") {
    const el = u.args.filter((t) => !usesSpecial(t)), sp = u.args.filter((t) => usesSpecial(t));
    const parts = [...(el.length ? [sub(X.mul(...el))] : []), ...sp.map(sub)];
    let fin = ONE, sgn = 1, anyInf = false, anyZero = false, dne = null;
    for (const p of parts) {
      if (p.k === "unknown") return p;
      if (p.k === "dne") { dne = p; continue; }
      if (p.k === "inf") { anyInf = true; sgn *= p.s; continue; }
      const s = signOf(p.v);
      if (s === 0) anyZero = true;
      else if (s === null) { if (anyInf) return UNK("sign unknown"); }
      else sgn *= s;
      fin = X.mul(fin, p.v);
    }
    if (dne) return !anyInf && !anyZero && parts.filter((p) => p.k === "dne").length === 1 ? dne : UNK("oscillating factor");
    if (anyInf && anyZero) return UNK("0 * oo");
    if (anyInf) return INF(sgn);
    return FIN(fin);
  }
  if (u.k === "pow" && X.isNum(u.args[1])) {
    const e = u.args[1].v, p = sub(u.args[0]);
    const ePos = e.n > 0n, eInt = e.d === 1n;
    if (p.k !== "fin" && p.k !== "inf") return p;
    if (p.k === "inf") {
      if (!ePos) return FIN(ZERO);
      if (p.s > 0) return INF(1);
      return eInt ? INF(e.n % 2n === 0n ? 1 : -1) : UNK("fractional power of a negative quantity");
    }
    const s = signOf(p.v);
    if (s === 0) return ePos ? FIN(ZERO) : UNK("power of a quantity tending to 0");
    if (s === null) return UNK("sign unknown");
    if (s < 0 && !eInt) return UNK("fractional power of a negative number");
    return FIN(X.pow(p.v, u.args[1]));
  }
  if (u.k === "fn" && u.args.length === 1) {
    const p = sub(u.args[0]);
    if (p.k === "unknown") return p;
    const spec = SPEC[u.name];
    if (spec) {
      if (p.k === "dne") return UNK("oscillating argument");
      if (p.k === "inf") { const r = p.s > 0 ? spec.pos : spec.neg; return r || UNK(`${u.name} is not real there`); }
      const v = p.v;
      if (spec.sing && spec.sing.includes(v)) return INF(-1);
      if (v === ZERO && (spec.odd || spec.zeroAt0)) return FIN(ZERO);
      const d = evalD(X.fn(u.name, v));
      if (!Number.isFinite(d)) return UNK(`${u.name} is not defined at the limit point`);
      return FIN(X.fn(u.name, v));
    }
    // elementary function of a special-function argument: continuous functions only
    if (p.k === "fin") {
      const CONT = new Set(["sin", "cos", "exp", "atan", "sinh", "cosh", "tanh", "asinh", "erf"]);
      if (CONT.has(u.name)) return FIN(X.fn(u.name, p.v));
      if (u.name === "abs") return FIN(X.fn("abs", p.v));
      if (u.name === "ln") { const s = signOf(p.v); if (s === 1) return FIN(X.fn("ln", p.v)); return UNK("ln near a non-positive value"); }
      return UNK("function of a special function");
    }
    if (p.k === "inf") {
      if (u.name === "atan") return FIN(X.mul(p.s > 0 ? HALF : X.num(-1, 2), PI));
      if (u.name === "exp") return p.s > 0 ? INF(1) : FIN(ZERO);
      if (u.name === "ln") return p.s > 0 ? INF(1) : UNK("ln of -oo");
      if (u.name === "abs") return INF(1);
      if (u.name === "tanh") return FIN(p.s > 0 ? ONE : X.NEG_ONE);
    }
    return UNK("unsupported function limit");
  }
  return UNK("unsupported expression for a limit");
}

export function limText(r, T) {
  if (r.k === "fin") return T(r.v);
  if (r.k === "inf") return r.s > 0 ? "+oo" : "-oo";
  if (r.k === "dne") return "does not exist";
  return "unknown";
}

void SPECIAL;
