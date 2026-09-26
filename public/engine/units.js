// Quelvra units as mathematical types.
//
// A unit has a dimension vector over the 7 SI base dimensions (L, M, T, I, Theta, N, J) with
// rational exponents, and an exact factor (a tree, usually a rational; `deg` carries pi) that
// converts it to the coherent SI unit of that dimension. A quantity is { value: tree, unit }.
//
// Affine temperature units (degC, degF) carry an offset that is applied ONLY in a pure
// conversion of a single temperature unit (20 degC -> 293.15 K). Inside compound units they
// act as temperature intervals (J/(kg*degC) = J/(kg*K)).
//
// Adding or subtracting quantities of different dimensions is rejected with a clear message.

import * as N from "./num.js";
import * as X from "./expr.js";
import { simplify, makeCtx } from "./simplify.js";
import { parse } from "./parse.js";
import { toText } from "./print.js";
import { evalFloat } from "./linalg.js";

const Z = (u) => simplify(u, makeCtx());
const fail = (msg, code) => Object.assign(new Error(msg), { code });
const step = (rule, title, why, before = null, after = null) => ({ rule, title, why, before, after, conditions: [], sub: [], kind: "equivalent" });

export const BASE = ["L", "M", "T", "I", "Theta", "N", "J"];
const D = (L = 0, M = 0, T = 0, I = 0, Th = 0, Nn = 0, J = 0) => [L, M, T, I, Th, Nn, J].map((v) => N.Q(v));
const dimEq = (a, b) => a.every((v, i) => N.eq(v, b[i]));
const dimAdd = (a, b) => a.map((v, i) => N.add(v, b[i]));
const dimScale = (a, e) => a.map((v) => N.mul(v, e));
const isDimless = (d) => d.every(N.isZero);
const dec = (s) => X.num(N.fromDecimal(s));
const frac = (a, b) => X.num(N.Q(a, b));

// ------------------------------------------------------------------ tables
const PREFIXES = [
  ["da", 1], ["Y", 24], ["Z", 21], ["E", 18], ["P", 15], ["T", 12], ["G", 9], ["M", 6], ["k", 3], ["h", 2],
  ["d", -1], ["c", -2], ["m", -3], ["u", -6], ["µ", -6], ["μ", -6], ["n", -9], ["p", -12], ["f", -15], ["a", -18], ["z", -21], ["y", -24],
];
const pow10 = (e) => X.num(e >= 0 ? N.Q(10n ** BigInt(e)) : N.Q(1n, 10n ** BigInt(-e)));

const UNITS = new Map();
function def(names, factor, dim, { prefix = false, offset = null, label } = {}) {
  const f = typeof factor === "string" ? dec(factor) : factor.k ? factor : X.num(factor);
  for (const n of [].concat(names)) UNITS.set(n, { symbol: [].concat(names)[0], factor: Z(f), dim, prefix, offset, label: label || [].concat(names)[0] });
}
const LEN = D(1), MASS = D(0, 1), TIME = D(0, 0, 1), CUR = D(0, 0, 0, 1), TEMP = D(0, 0, 0, 0, 1), AMT = D(0, 0, 0, 0, 0, 1), LUM = D(0, 0, 0, 0, 0, 0, 1), ONE = D();
const FORCE = D(1, 1, -2), ENERGY = D(2, 1, -2), POWER = D(2, 1, -3), PRESS = D(-1, 1, -2), CHARGE = D(0, 0, 1, 1), VOLT = D(2, 1, -3, -1);
// SI base and derived
def("m", 1, LEN, { prefix: true });
def("g", frac(1, 1000), MASS, { prefix: true });
def("s", 1, TIME, { prefix: true });
def("A", 1, CUR, { prefix: true });
def("K", 1, TEMP, { prefix: true });
def("mol", 1, AMT, { prefix: true });
def("cd", 1, LUM, { prefix: true });
def("N", 1, FORCE, { prefix: true });
def("J", 1, ENERGY, { prefix: true });
def("W", 1, POWER, { prefix: true });
def("Pa", 1, PRESS, { prefix: true });
def("Hz", 1, D(0, 0, -1), { prefix: true });
def("C", 1, CHARGE, { prefix: true });
def("V", 1, VOLT, { prefix: true });
def(["ohm", "Ω", "Ohm"], 1, D(2, 1, -3, -2), { prefix: true });
def("F", 1, D(-2, -1, 4, 2), { prefix: true });
def("S", 1, D(-2, -1, 3, 2), { prefix: true });
def("Wb", 1, D(2, 1, -2, -1), { prefix: true });
def("T", 1, D(0, 1, -2, -1), { prefix: true });
def("H", 1, D(2, 1, -2, -2), { prefix: true });
// accepted non-SI
def(["L", "l"], frac(1, 1000), D(3), { prefix: true });
def("min", 60, TIME);
def(["h", "hr"], 3600, TIME);
def("day", 86400, TIME);
def("week", 604800, TIME);
def("yr", 31557600, TIME, { label: "Julian year" });
def("ha", 10000, D(2));
def("t", 1000, MASS, { label: "tonne" });
def(["angstrom", "Å"], dec("1e-10"), LEN);
// imperial / US customary (exact international definitions)
def("in", "0.0254", LEN);
def("ft", "0.3048", LEN);
def("yd", "0.9144", LEN);
def("mi", "1609.344", LEN);
def("nmi", 1852, LEN);
def("lb", "0.45359237", MASS);
def("oz", Z(X.div(dec("0.45359237"), X.num(16))), MASS);
def("ton", Z(X.mul(X.num(2000), dec("0.45359237"))), MASS, { label: "short ton" });
def("gal", Z(X.mul(X.num(231), X.pow(dec("0.0254"), X.num(3)))), D(3), { label: "US gallon" });
def("mph", Z(X.div(dec("1609.344"), X.num(3600))), D(1, 0, -1));
def(["kph"], frac(1000, 3600), D(1, 0, -1));
def("knot", frac(1852, 3600), D(1, 0, -1));
def("lbf", Z(X.mul(dec("0.45359237"), dec("9.80665"))), FORCE);
def("psi", Z(X.div(X.mul(dec("0.45359237"), dec("9.80665")), X.pow(dec("0.0254"), X.TWO))), PRESS);
// energy / pressure
def("eV", dec("1.602176634e-19"), ENERGY, { prefix: true });
def("cal", dec("4.184"), ENERGY, { prefix: true, label: "thermochemical calorie" });
def("Wh", 3600, ENERGY, { prefix: true });
def("atm", 101325, PRESS);
def("bar", 100000, PRESS, { prefix: true });
def("mmHg", dec("133.322387415"), PRESS);
def("torr", frac(101325, 760), PRESS);
// angles (dimensionless)
def("rad", 1, ONE, { prefix: true });
def(["deg", "°"], Z(X.div(X.PI, X.num(180))), ONE);
def("rev", Z(X.mul(X.TWO, X.PI)), ONE);
// temperature (affine): SI kelvin = value * factor + offset
def(["degC", "°C", "celsius"], 1, TEMP, { offset: N.fromDecimal("273.15") });
def(["degF", "°F", "fahrenheit"], frac(5, 9), TEMP, { offset: N.Q(45967, 180) });

// long names ("miles", "kilometres", "pounds") map onto the symbols above
const WORDS = {
  meter: "m", gram: "g", second: "s", sec: "s", ampere: "A", amp: "A", kelvin: "K", mole: "mol", candela: "cd",
  newton: "N", joule: "J", watt: "W", pascal: "Pa", hertz: "Hz", coulomb: "C", volt: "V", farad: "F", siemens: "S",
  weber: "Wb", tesla: "T", henry: "H", liter: "L", minute: "min", hour: "h", day: "day", week: "week", year: "yr",
  hectare: "ha", tonne: "t", inch: "in", foot: "ft", yard: "yd", mile: "mi", "nautical mile": "nmi", pound: "lb",
  ounce: "oz", gallon: "gal", knot: "knot", calorie: "cal", electronvolt: "eV", atmosphere: "atm", radian: "rad",
  degree: "deg", revolution: "rev", celsius: "degC", fahrenheit: "degF",
};
const WORD_PREFIX = { kilo: "k", centi: "c", milli: "m", micro: "µ", nano: "n", mega: "M", giga: "G", deci: "d" };
function wordUnit(w) {
  let s = w.toLowerCase().replace(/metre/g, "meter").replace(/litre/g, "liter");
  if (s === "feet") s = "foot";
  else if (/(inch|siemens)es$/.test(s) || s === "inches") s = s.replace(/es$/, "");
  else if (/s$/.test(s) && !/(siemens|hertz|celsius)$/.test(s)) s = s.slice(0, -1);
  if (WORDS[s]) return WORDS[s];
  for (const [p, sym] of Object.entries(WORD_PREFIX)) {
    if (s.startsWith(p) && WORDS[s.slice(p.length)]) {
      const base = WORDS[s.slice(p.length)];
      const b = UNITS.get(base);
      if (b && b.prefix) return sym + base;
    }
  }
  return null;
}
// multi-word phrases -> unit syntax the parser reads ("miles per hour" -> "mi/h", "square feet" -> "ft^2")
export function normalizeUnitWords(src) {
  return String(src)
    .replace(/\bdeg(?:ree)?s?\s+(celsius|centigrade|fahrenheit|kelvin|c|f)\b/gi, (_, u) => ({ c: "degC", f: "degF", centigrade: "degC", kelvin: "K" })[u.toLowerCase()] || (/^c/i.test(u) ? "degC" : "degF"))
    .replace(/\bnautical\s+miles?\b/gi, "nmi")
    .replace(/\b(square|sq\.?|cubic)\s+([a-z]+)/gi, (_, k, u) => `${u}^${/^cub/i.test(k) ? 3 : 2}`)
    .replace(/\s+per\s+/gi, "/");
}

function lookup(sym) {
  const u = UNITS.get(sym);
  if (u) return { ...u, symbol: sym };
  if (/^[A-Za-z]{3,}$/.test(sym)) { const w = wordUnit(sym); if (w && w !== sym) { const r = lookup(w); if (r) return { ...r, symbol: w }; } }
  for (const [p, e] of PREFIXES) {
    if (sym.length > p.length && sym.startsWith(p)) {
      const b = UNITS.get(sym.slice(p.length));
      if (b && b.prefix) return { ...b, symbol: sym, factor: Z(X.mul(b.factor, pow10(e))), prefix: false, label: sym };
    }
  }
  return null;
}
export const knownUnits = () => [...UNITS.keys()];

// ------------------------------------------------------------------ unit values
// unit = { parts: [[symbol, Rational exponent]], factor: tree, dim: Rational[7], offset: Rational|null, text }
function makeUnit(parts, factor, dim, offset = null) {
  const u = { parts, factor, dim, offset };
  u.text = unitText(parts);
  return Object.freeze(u);
}
function atomUnit(sym) {
  const e = lookup(sym);
  if (!e) throw fail(`Quelvra: unknown unit "${sym}"`, "UNIT");
  return makeUnit([[e.symbol, N.ONE]], e.factor, e.dim, e.offset);
}
export const DIMENSIONLESS = makeUnit([], X.ONE, ONE);
function combine(a, b, sign = N.ONE) {
  const parts = a.parts.map(([s, e]) => [s, e]);
  for (const [s, e] of b.parts) {
    const i = parts.findIndex(([t]) => t === s);
    const ee = N.mul(e, sign);
    if (i >= 0) parts[i][1] = N.add(parts[i][1], ee); else parts.push([s, ee]);
  }
  const kept = parts.filter(([, e]) => !N.isZero(e));
  const factor = Z(X.mul(a.factor, X.pow(b.factor, X.num(sign))));
  return makeUnit(kept, factor, dimAdd(a.dim, dimScale(b.dim, sign)));
}
export const mulUnits = (a, b) => combine(asUnit(a), asUnit(b));
export const divUnits = (a, b) => combine(asUnit(a), asUnit(b), N.NEG_ONE);
function ratExp(e) {
  if (e && typeof e === "object") { if (e.k === "num") return e.v; if (typeof e.n === "bigint") return e; }
  if (typeof e === "bigint") return N.Q(e);
  const m = String(e).trim().match(/^\(?\s*([+-]?[\d.]+)\s*(?:\/\s*([\d.]+))?\s*\)?$/);
  if (!m) throw fail(`Quelvra: exponent ${e} must be a rational number`, "DOMAIN");
  return m[2] ? N.div(N.fromDecimal(m[1]), N.fromDecimal(m[2])) : N.fromDecimal(m[1]);
}
export function powUnit(a, e) {
  a = asUnit(a);
  e = ratExp(e);
  return makeUnit(a.parts.map(([s, x]) => [s, N.mul(x, e)]).filter(([, x]) => !N.isZero(x)), Z(X.pow(a.factor, X.num(e))), dimScale(a.dim, e));
}
function unitText(parts) {
  const f = ([s, e]) => (N.isOne(N.abs(e)) ? s : `${s}^${e.d === 1n ? N.abs(e).n : `(${N.toString(N.abs(e))})`}`);
  const pos = parts.filter(([, e]) => N.isPos(e)), neg = parts.filter(([, e]) => N.isNeg(e));
  if (!pos.length && !neg.length) return "1";
  if (!pos.length) return parts.map(([s, e]) => `${s}^${e.d === 1n ? e.n : `(${N.toString(e)})`}`).join("*");
  const top = pos.map(f).join("*");
  if (!neg.length) return top;
  const bot = neg.map(f).join("*");
  return `${top}/${neg.length > 1 ? `(${bot})` : bot}`;
}

// ------------------------------------------------------------------ unit parser
// Grammar: expr := term (('*' | '/' | '.' | juxtaposition) term)* ; term := atom ('^' exp)? ;
// atom := name | '(' expr ')' | '1' ; exp := ['-'] int ['/' int] | '(' same ')'. '/' is left-associative.
const SUPER = { "²": "^2", "³": "^3", "¹": "^1", "⁻": "^-" };
export function parseUnit(src) {
  if (src && typeof src === "object" && src.parts) return src;
  let s = String(src).trim().replace(/[²³¹]/g, (c) => SUPER[c]).replace(/·|⋅|×/g, "*").replace(/\*\*/g, "^");
  if (s === "" || s === "1") return DIMENSIONLESS;
  let i = 0;
  const peek = () => { while (s[i] === " ") i++; return s[i]; };
  const err = (m) => fail(`Quelvra: cannot read unit "${src}": ${m}`, "UNIT");
  const readExp = () => {
    let paren = false;
    if (peek() === "(") { paren = true; i++; }
    peek();
    const m = s.slice(i).match(/^([+-]?\d+)(?:\s*\/\s*(\d+))?/);
    if (!m) throw err("bad exponent");
    i += m[0].length;
    if (paren) { if (peek() !== ")") throw err("missing )"); i++; }
    return N.Q(BigInt(m[1]), m[2] ? BigInt(m[2]) : 1n);
  };
  const atom = () => {
    const c = peek();
    if (c === "(") { i++; const u = expr(); if (peek() !== ")") throw err("missing )"); i++; return u; }
    if (c === "1") { i++; return DIMENSIONLESS; }
    const m = s.slice(i).match(/^(°[CF]?|[A-Za-zµμΩÅ]+)/);
    if (!m) throw err(`unexpected "${c}"`);
    i += m[0].length;
    return atomUnit(m[0]);
  };
  const term = () => {
    let u = atom();
    if (peek() === "^") { i++; u = powUnit(u, readExp()); }
    return u;
  };
  const expr = () => {
    let u = term();
    for (let guard = 0; guard < 1000; guard++) {
      const c = peek();
      if (c === "*" || c === ".") { i++; u = mulUnits(u, term()); }
      else if (c === "/") { i++; u = divUnits(u, term()); }
      else if (c !== undefined && c !== ")" && /[A-Za-z(µμΩ°Å]/.test(c)) u = mulUnits(u, term());
      else break;
    }
    return u;
  };
  const u = expr();
  if (peek() !== undefined) throw err(`unexpected "${s[i]}"`);
  // a single affine unit keeps its offset
  if (u.parts.length === 1 && N.isOne(u.parts[0][1])) {
    const e = lookup(u.parts[0][0]);
    if (e && e.offset) return makeUnit(u.parts, u.factor, u.dim, e.offset);
  }
  return u;
}
const asUnit = (u) => (u && u.parts ? u : parseUnit(u));

// ------------------------------------------------------------------ dimensions
const NAMED_DIMS = [
  [ONE, "dimensionless"], [LEN, "length"], [MASS, "mass"], [TIME, "time"], [CUR, "electric current"], [TEMP, "temperature"],
  [AMT, "amount of substance"], [LUM, "luminous intensity"], [D(2), "area"], [D(3), "volume"], [D(1, 0, -1), "velocity"],
  [D(1, 0, -2), "acceleration"], [FORCE, "force"], [ENERGY, "energy"], [POWER, "power"], [PRESS, "pressure"],
  [D(0, 0, -1), "frequency"], [CHARGE, "electric charge"], [VOLT, "voltage"], [D(2, 1, -3, -2), "resistance"],
  [D(-3, 1), "density"], [D(1, 1, -1), "momentum"],
];
export function dimensionText(dim) {
  const parts = BASE.map((b, i) => [b, dim[i]]).filter(([, e]) => !N.isZero(e));
  if (!parts.length) return "1";
  return parts.map(([b, e]) => (N.isOne(e) ? b : `${b}^${N.toString(e)}`)).join(" ");
}
export function dimensionName(dim) {
  dim = Array.isArray(dim) ? dim : asUnit(dim).dim;
  const hit = NAMED_DIMS.find(([d]) => dimEq(d, dim));
  return hit ? hit[1] : dimensionText(dim);
}
export const sameDimension = (a, b) => dimEq(asUnit(a).dim, asUnit(b).dim);

// ------------------------------------------------------------------ quantities
const valueTree = (v) => {
  if (v && v.k) return Z(v);
  if (typeof v === "bigint") return X.num(v);
  if (typeof v === "number") return X.num(Number.isInteger(v) ? N.Q(BigInt(v)) : N.fromDecimal(String(v)));
  if (v && typeof v.n === "bigint") return X.num(v);
  return Z(parse(String(v)));
};
export const quantity = (value, unit) => Object.freeze({ value: valueTree(value), unit: asUnit(unit) });
const NUM_RE = /^\s*([+-]?(?:\d+(?:\.\d*)?|\.\d+)(?:[eE][+-]?\d+)?)(?:\s*\/\s*(\d+(?:\.\d*)?))?(?:\s*(?:\*|x|×)\s*10\^([+-]?\d+))?\s*/;
export function parseQuantity(src) {
  const s = String(src).trim();
  const m = s.match(NUM_RE);
  if (!m) throw fail(`Quelvra: "${src}" does not start with a number`, "INPUT");
  let v = N.fromDecimal(m[1]);
  if (m[2]) v = N.div(v, N.fromDecimal(m[2]));
  if (m[3]) v = N.mul(v, N.pow(N.Q(10), BigInt(m[3])));
  return quantity(X.num(v), parseUnit(s.slice(m[0].length)));
}
function describe(u) { return `${dimensionName(u.dim)} (${u.text})`; }

export function convert(q, target) {
  q = q.unit ? q : parseQuantity(q);
  const t = asUnit(target);
  if (!dimEq(q.unit.dim, t.dim)) throw fail(`Quelvra: cannot convert ${describe(q.unit)} to ${describe(t)}`, "DIMENSION");
  const steps = [];
  let value;
  if (q.unit.offset || t.offset) {
    if (q.unit.parts.length !== 1 || t.parts.length !== 1) throw fail("Quelvra: affine temperature units can only be converted on their own", "UNIT");
    const oS = q.unit.offset || N.ZERO, oT = t.offset || N.ZERO;
    const si = Z(X.add(X.mul(q.value, q.unit.factor), X.num(oS)));
    value = Z(X.div(X.sub(si, X.num(oT)), t.factor));
    steps.push(step("units.affine", "Affine temperature conversion", `Convert to kelvin (K = value * ${toText(q.unit.factor)} + ${N.toString(oS)}), then to ${t.text}.`, q.value, value));
  } else {
    const ratio = Z(X.div(q.unit.factor, t.factor));
    value = Z(X.mul(q.value, ratio));
    steps.push(step("units.convert", `Multiply by the conversion factor ${toText(ratio)}`, `1 ${q.unit.text} = ${toText(ratio)} ${t.text} exactly.`, q.value, value));
  }
  return { value, unit: t, steps };
}
export function add(a, b, verb = "add") {
  a = a.unit ? a : parseQuantity(a);
  b = b.unit ? b : parseQuantity(b);
  if (!dimEq(a.unit.dim, b.unit.dim)) throw fail(`Quelvra: cannot ${verb} ${describe(a.unit)} and ${describe(b.unit)}`, "DIMENSION");
  if ((a.unit.offset || b.unit.offset) && a.unit.text !== b.unit.text)
    throw fail(`Quelvra: cannot ${verb} absolute temperatures in different scales (${a.unit.text}, ${b.unit.text}); convert to K first`, "UNIT");
  const bv = a.unit.text === b.unit.text ? b.value : Z(X.mul(b.value, X.div(b.unit.factor, a.unit.factor)));
  return quantity(verb === "add" ? Z(X.add(a.value, bv)) : Z(X.sub(a.value, bv)), a.unit);
}
export const sub = (a, b) => add(a, b, "subtract");
const noAffine = (q) => { if (q.unit.offset) throw fail(`Quelvra: ${q.unit.text} is an affine unit; convert to K before multiplying`, "UNIT"); return q; };
const asQ = (q) => (q.unit ? q : q.k || typeof q === "number" || typeof q === "bigint" ? quantity(q, DIMENSIONLESS) : parseQuantity(q));
export function mul(a, b) { a = noAffine(asQ(a)); b = noAffine(asQ(b)); return quantity(Z(X.mul(a.value, b.value)), mulUnits(a.unit, b.unit)); }
export function div(a, b) {
  a = noAffine(asQ(a)); b = noAffine(asQ(b));
  if (b.value === X.ZERO) throw fail("Quelvra: division by zero", "DOMAIN");
  return quantity(Z(X.div(a.value, b.value)), divUnits(a.unit, b.unit));
}
export function pow(a, e) {
  a = noAffine(asQ(a));
  const r = ratExp(e);
  return quantity(Z(X.pow(a.value, X.num(r))), powUnit(a.unit, r));
}

// ------------------------------------------------------------------ simplification to named units
const DERIVED = ["N", "J", "W", "Pa", "C", "V", "ohm", "F", "S", "Wb", "T", "H", "m", "kg", "s", "A", "K", "mol", "cd"];
// Named unit with the same dimension whose factor matches exactly (possibly with an SI prefix).
export function simplifyUnit(u) {
  u = asUnit(u);
  if (u.parts.length <= 1 && (!u.parts.length || N.isOne(u.parts[0][1]))) return u;
  for (const name of DERIVED) {
    const d = parseUnit(name);
    if (!dimEq(d.dim, u.dim)) continue;
    const ratio = Z(X.div(u.factor, d.factor));
    if (ratio === X.ONE) return d;
    if (ratio.k === "num" && name !== "kg") {
      for (const [p, e] of PREFIXES) {
        if (p === "µ" || p === "μ") continue;
        if (pow10(e) === ratio) { const c = lookup(p + name); if (c) return atomUnit(p + name); }
      }
    }
  }
  return u;
}
// Express a quantity in its named SI unit (value rescaled exactly): 3 g*cm/s^2 -> 3/100000 N.
export function simplifyQuantity(q) {
  q = q.unit ? q : parseQuantity(q);
  const s = simplifyUnit(q.unit);
  if (s !== q.unit) return quantity(convert(q, s).value, s);
  for (const name of DERIVED) {
    const d = parseUnit(name);
    if (dimEq(d.dim, q.unit.dim) && q.unit.parts.length > 1) return quantity(convert(q, d).value, d);
  }
  return q;
}

// ------------------------------------------------------------------ dimensional analysis
// checkDimensions("F = m*a", {F: "N", m: "kg", a: "m/s^2"})
export function checkDimensions(expr, symbolUnits = {}) {
  const u = typeof expr === "string" ? parse(expr) : expr;
  const problems = [], unknown = new Set();
  const unitOf = (name) => {
    const get = (k) => (symbolUnits instanceof Map ? symbolUnits.get(k) : Object.prototype.hasOwnProperty.call(symbolUnits, k) ? symbolUnits[k] : undefined);
    // the parser writes x0 as x_0; accept either spelling in the map
    let v = get(name);
    if (v === undefined && name.includes("_")) v = get(name.replace(/_/g, "")) ?? get(name.replace(/_\{?([^}]*)\}?/g, "$1"));
    if (v === undefined) { unknown.add(name); return null; }
    return asUnit(v).dim;
  };
  const dimOf = (w) => {
    switch (w.k) {
      case "num": case "const": return ONE;
      case "sym": return unitOf(w.name) || ONE;
      case "unit": return asUnit(w.name).dim;
      case "add": {
        const ds = w.args.map(dimOf);
        for (let i = 1; i < ds.length; i++) if (!dimEq(ds[0], ds[i]))
          problems.push(`cannot add ${dimensionName(ds[0])} (${toText(w.args[0])}) and ${dimensionName(ds[i])} (${toText(w.args[i])})`);
        return ds[0];
      }
      case "mul": return w.args.map(dimOf).reduce(dimAdd, ONE);
      case "pow": {
        const b = dimOf(w.args[0]), ed = dimOf(w.args[1]);
        if (!isDimless(ed)) problems.push(`exponent ${toText(w.args[1])} must be dimensionless`);
        if (isDimless(b)) return ONE;
        const e = Z(w.args[1]);
        if (e.k !== "num") { problems.push(`a dimensioned base ${toText(w.args[0])} needs a numeric exponent`); return b; }
        return dimScale(b, e.v);
      }
      case "fn": {
        const ds = w.args.map(dimOf);
        if (w.name === "abs" || w.name === "floor" || w.name === "ceil") return ds[0];
        if (w.name === "sqrt") return dimScale(ds[0], N.HALF);
        ds.forEach((d, i) => { if (!isDimless(d)) problems.push(`the argument of ${w.name} (${toText(w.args[i])}) must be dimensionless, it is ${dimensionName(d)}`); });
        return ONE;
      }
      case "eq": case "rel": {
        const [l, r] = w.args.map(dimOf);
        if (!dimEq(l, r)) problems.push(`the two sides differ: ${dimensionName(l)} vs ${dimensionName(r)}`);
        return l;
      }
      default: return ONE;
    }
  };
  let lhs = null, rhs = null;
  if (u.k === "eq" || u.k === "rel") {
    lhs = dimOf(u.args[0]); rhs = dimOf(u.args[1]);
    if (!dimEq(lhs, rhs)) problems.push(`the two sides differ: ${dimensionName(lhs)} vs ${dimensionName(rhs)}`);
  } else dimOf(u);
  return {
    consistent: problems.length === 0, problems, unknownSymbols: [...unknown],
    lhs: lhs && dimensionName(lhs), rhs: rhs && dimensionName(rhs),
    steps: [step("units.dimension-check", problems.length ? "Dimensions are inconsistent" : "Dimensions are consistent", problems.length ? problems.join("; ") : "Every sum adds like dimensions and both sides agree.", u, null)],
  };
}

// ------------------------------------------------------------------ text front end
export function decimalOf(v, digits = 12) {
  if (v.k === "num") {
    const r = v.v, a = N.abs(r);
    if (N.isZero(a) || (N.cmp(a, N.Q(1n, 10000n)) >= 0 && N.cmp(a, N.Q(10n ** 15n)) < 0)) return N.toDecimalString(r, digits);
    // scientific notation, exact mantissa rounding
    let e = BigInt(a.n.toString().length - a.d.toString().length);
    const at = (k) => (k >= 0n ? N.Q(10n ** k) : N.Q(1n, 10n ** -k));
    while (N.cmp(N.div(a, at(e)), N.ONE) < 0) e--;
    while (N.cmp(N.div(a, at(e)), N.Q(10)) >= 0) e++;
    let mant = N.toDecimalString(N.div(r, at(e)), digits);
    if (/^-?10(\.|$)/.test(mant)) { e++; mant = N.toDecimalString(N.div(r, at(e)), digits); }
    return `${mant}e${e}`;
  }
  const f = evalFloat(v);
  return Number(f.toPrecision(digits)).toString();
}
// convertText("5 km/h to m/s") -> { value, unit, text, decimal, exact, steps }
export function convertText(src) {
  src = normalizeUnitWords(src);
  const m = String(src).match(/^(.*\S)\s+(?:to|in|into|as)\s+(.+)$/) || String(src).match(/^(.*\S)\s*(?:->|=>|→)\s*(.+)$/);
  if (!m) {
    const q = simplifyQuantity(parseQuantity(src));
    return { value: q.value, unit: q.unit, text: `${toText(q.value)} ${q.unit.text}`, decimal: `${decimalOf(q.value)} ${q.unit.text}`, exact: true, steps: [] };
  }
  const q = parseQuantity(m[1]);
  const r = convert(q, m[2]);
  const isNumV = r.value.k === "num";
  const decimal = decimalOf(r.value);
  return {
    input: q, value: r.value, unit: r.unit, exact: true,
    text: `${toText(r.value)} ${r.unit.text}`,
    decimal: `${decimal} ${r.unit.text}`,
    repeating: isNumV && !isTerminating(r.value.v),
    steps: r.steps,
  };
}
function isTerminating(r) {
  let d = r.d;
  while (d % 2n === 0n) d /= 2n;
  while (d % 5n === 0n) d /= 5n;
  return d === 1n;
}
