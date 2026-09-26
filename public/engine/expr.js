// Quelvra math tree: the one contract every engine shares.
//
// Nodes are immutable, hash-consed objects: building the same structure twice returns
// the same object, so `a === b` is structural equality and node ids are stable keys for
// memoisation. Every compound node keeps its children in `args`.
//
// kinds
//   num      { v: Rational }                     exact integer or rational
//   sym      { name }                            variable
//   const    { name: pi | e | I | oo | undef }   symbolic constants (oo = +infinity)
//   add      args: terms                         n-ary sum (subtraction is add of a negated term)
//   mul      args: factors                       n-ary product (division is a negative power)
//   pow      args: [base, exponent]
//   fn       { name } args                       sin, cos, ln, log(b, x), abs, factorial, user f(x) ...
//   eq       args: [lhs, rhs]
//   rel      { op: < <= > >= != } args: [lhs, rhs]
//   and/or/not                                  logical connectives over relations
//   system   args: equations / relations
//   tuple    args                                ordered list, also a matrix row
//   vector   args
//   matrix   args: tuple rows
//   set      args
//   interval { lo_open, hi_open } args: [lo, hi]
//   piecewise args: [value1, cond1, value2, cond2, ...]  (cond may be const "true")
//   deriv    args: [expr, var, order]
//   integral args: [expr, var] or [expr, var, lo, hi]
//   limit    { dir: "" | "+" | "-" } args: [expr, var, to]
//   sum/product args: [expr, var, lo, hi]
//   fndef    { name } args: [params(tuple), body]
//   unit     { name }                            physical unit (m, s, kg, ...)
//   quant    { q: forall | exists } args: [var, body]
//   bool     { v: true | false }

import * as N from "./num.js";

let NEXT_ID = 1;
const TABLE = new Map();
export const srcLoc = new WeakMap(); // node -> { start, end } set by the parser (first sighting)

const EXTRA_KEYS = ["v", "name", "op", "dir", "q", "lo_open", "hi_open"];

function keyOf(k, args, extra) {
  let key = k;
  if (extra) {
    for (const f of EXTRA_KEYS) {
      if (extra[f] === undefined) continue;
      const val = extra[f];
      key += "|" + f + "=" + (f === "v" && typeof val === "object" ? val.n + "/" + val.d : String(val));
    }
  }
  if (args) for (const a of args) key += "," + a.id;
  return key;
}

export function mk(k, args, extra) {
  const key = keyOf(k, args, extra);
  const hit = TABLE.get(key);
  if (hit) return hit;
  const node = { k, id: NEXT_ID++, args: args ? Object.freeze(args.slice()) : EMPTY, ...(extra || {}) };
  Object.freeze(node);
  TABLE.set(key, node);
  return node;
}
const EMPTY = Object.freeze([]);
export const tableSize = () => TABLE.size;

// ---------- constructors (raw: no simplification) ----------
export const num = (v, d) => {
  if (typeof v === "object" && v !== null && "n" in v) return mk("num", null, { v });
  return mk("num", null, { v: N.Q(v, d === undefined ? 1n : d) });
};
export const sym = (name) => mk("sym", null, { name });
export const konst = (name) => mk("const", null, { name });
export const bool = (v) => mk("bool", null, { v: !!v });
export const unit = (name) => mk("unit", null, { name });

export const ZERO = num(0), ONE = num(1), TWO = num(2), NEG_ONE = num(-1), HALF = num(1, 2);
export const PI = konst("pi"), E = konst("e"), I = konst("I"), OO = konst("oo"), UNDEF = konst("undef");
export const TRUE = bool(true), FALSE = bool(false);

export const add = (...a) => (a.length === 1 ? a[0] : a.length === 0 ? ZERO : mk("add", a));
export const mul = (...a) => (a.length === 1 ? a[0] : a.length === 0 ? ONE : mk("mul", a));
export const pow = (b, e) => mk("pow", [b, e]);
export const neg = (u) => mul(NEG_ONE, u);
export const sub = (a, b) => add(a, neg(b));
export const div = (a, b) => mul(a, pow(b, NEG_ONE));
export const recip = (b) => pow(b, NEG_ONE);
export const sqrt = (u) => pow(u, HALF);
export const exp = (u) => pow(E, u);
export const fn = (name, ...args) => mk("fn", args, { name });
export const eq = (l, r) => mk("eq", [l, r]);
export const rel = (op, l, r) => mk("rel", [l, r], { op });
export const and = (...a) => mk("and", a);
export const or = (...a) => mk("or", a);
export const not = (a) => mk("not", [a]);
export const system = (...a) => mk("system", a);
export const tuple = (...a) => mk("tuple", a);
export const vector = (...a) => mk("vector", a);
export const matrix = (rows) => mk("matrix", rows.map((r) => (r.k === "tuple" ? r : tuple(...r))));
export const set = (...a) => mk("set", a);
export const interval = (lo, hi, lo_open = false, hi_open = false) => mk("interval", [lo, hi], { lo_open: !!lo_open, hi_open: !!hi_open });
export const piecewise = (...pairs) => mk("piecewise", pairs.flat());
export const deriv = (e, v, order = ONE) => mk("deriv", [e, v, typeof order === "number" ? num(order) : order]);
export const integral = (e, v, lo, hi) => mk("integral", lo === undefined ? [e, v] : [e, v, lo, hi]);
export const limit = (e, v, to, dir = "") => mk("limit", [e, v, to], { dir });
export const sum = (e, v, lo, hi) => mk("sum", [e, v, lo, hi]);
export const product = (e, v, lo, hi) => mk("product", [e, v, lo, hi]);
export const fndef = (name, params, body) => mk("fndef", [tuple(...params), body], { name });
export const quant = (q, v, body) => mk("quant", [v, body], { q });

// ---------- predicates ----------
export const isNum = (u) => u.k === "num";
export const isInt = (u) => u.k === "num" && u.v.d === 1n;
export const isZero = (u) => u.k === "num" && u.v.n === 0n;
export const isOne = (u) => u.k === "num" && u.v.n === 1n && u.v.d === 1n;
export const isNegNum = (u) => u.k === "num" && u.v.n < 0n;
export const isSym = (u, name) => u.k === "sym" && (name === undefined || u.name === name);
export const isConst = (u, name) => u.k === "const" && (name === undefined || u.name === name);
export const isFn = (u, name) => u.k === "fn" && (name === undefined || u.name === name);
export const isRelation = (u) => u.k === "eq" || u.k === "rel";
// "Constant" in the algebraic sense: contains no free symbols.
export const isConstantExpr = (u) => freeSymbols(u).size === 0;

// Replace the children of a node, keeping kind and extra fields.
export function withArgs(u, args) {
  if (args.length === u.args.length && args.every((a, i) => a === u.args[i])) return u;
  const extra = {};
  for (const f of EXTRA_KEYS) if (u[f] !== undefined) extra[f] = u[f];
  return mk(u.k, args, extra);
}

// Bottom-up map. f receives a node whose children are already mapped.
export function mapTree(u, f, memo = new Map()) {
  const hit = memo.get(u);
  if (hit) return hit;
  const r = f(u.args.length ? withArgs(u, u.args.map((a) => mapTree(a, f, memo))) : u);
  memo.set(u, r);
  return r;
}

// Variables that bind inside a node (so they are not free).
function boundVar(u) {
  if (u.k === "sum" || u.k === "product" || u.k === "quant") return u.k === "quant" ? u.args[0] : u.args[1];
  if (u.k === "integral" && u.args.length === 4) return u.args[1];
  if (u.k === "limit") return u.args[1];
  return null;
}

const FS_MEMO = new WeakMap();
export function freeSymbols(u) {
  let s = FS_MEMO.get(u);
  if (s) return s;
  s = new Set();
  if (u.k === "sym") s.add(u.name);
  else if (u.k === "fndef") {
    const params = new Set(u.args[0].args.map((p) => p.name));
    for (const n of freeSymbols(u.args[1])) if (!params.has(n)) s.add(n);
  } else {
    const b = boundVar(u);
    u.args.forEach((a, i) => {
      if (b && a === b && i === (u.k === "quant" ? 0 : 1)) return;
      for (const n of freeSymbols(a)) if (!b || n !== b.name) s.add(n);
    });
  }
  FS_MEMO.set(u, s);
  return s;
}
export const hasSym = (u, name) => freeSymbols(u).has(typeof name === "string" ? name : name.name);
export const freeOf = (u, x) => !hasSym(u, x);

// True if `sub` occurs anywhere inside u (structural, thanks to hash-consing).
export function contains(u, target) {
  if (u === target) return true;
  for (const a of u.args) if (contains(a, target)) return true;
  return false;
}

// Substitute symbols: map is Map<name, node> or plain object. Respects bound variables.
export function subs(u, map) {
  const m = map instanceof Map ? map : new Map(Object.entries(map));
  if (!m.size) return u;
  const go = (w) => {
    if (w.k === "sym") return m.has(w.name) ? m.get(w.name) : w;
    if (!w.args.length) return w;
    const b = boundVar(w);
    if (b && m.has(b.name)) {
      const inner = new Map(m);
      inner.delete(b.name);
      return withArgs(w, w.args.map((a) => subs(a, inner)));
    }
    return withArgs(w, w.args.map(go));
  };
  return go(u);
}
// Replace every occurrence of a subtree.
export function replace(u, from, to) {
  if (u === from) return to;
  if (!u.args.length) return u;
  return withArgs(u, u.args.map((a) => replace(a, from, to)));
}

export function size(u) {
  let n = 1;
  for (const a of u.args) n += size(a);
  return n;
}
export function depth(u) {
  let d = 0;
  for (const a of u.args) d = Math.max(d, depth(a));
  return d + 1;
}

// ---------- canonical ordering (Cohen, "Computer Algebra and Symbolic Computation", O-1..O-7) ----------
const KIND_RANK = { num: 0, const: 1, sym: 1, pow: 2, mul: 2, add: 2, fn: 3 };
const CONST_ORDER = { I: "~0I", pi: "~1pi", e: "~2e", oo: "~9oo", undef: "~9undef" };
const nameOf = (u) => (u.k === "const" ? CONST_ORDER[u.name] || u.name : u.name);

export function before(u, v) {
  if (u === v) return false;
  // O-1 numbers first, by value
  if (u.k === "num" && v.k === "num") return N.lt(u.v, v.v);
  if (u.k === "num") return true;
  if (v.k === "num") return false;
  const us = u.k === "sym" || u.k === "const", vs = v.k === "sym" || v.k === "const";
  // O-2 symbols lexicographic (constants sort before plain letters, I first)
  if (us && vs) {
    const a = nameOf(u), b = nameOf(v);
    return a < b;
  }
  // O-3 sums/products: compare last operands, then walk backwards, then length
  if ((u.k === "add" && v.k === "add") || (u.k === "mul" && v.k === "mul")) {
    const m = u.args.length, n = v.args.length;
    for (let j = 0; j < Math.min(m, n); j++) {
      const a = u.args[m - 1 - j], b = v.args[n - 1 - j];
      if (a !== b) return before(a, b);
    }
    return m < n;
  }
  // O-4 powers: base, then exponent
  if (u.k === "pow" && v.k === "pow") {
    if (u.args[0] !== v.args[0]) return before(u.args[0], v.args[0]);
    return before(u.args[1], v.args[1]);
  }
  // O-6 functions: name, then arguments
  if (u.k === "fn" && v.k === "fn") {
    if (u.name !== v.name) return u.name < v.name;
    const m = u.args.length, n = v.args.length;
    for (let j = 0; j < Math.min(m, n); j++) if (u.args[j] !== v.args[j]) return before(u.args[j], v.args[j]);
    return m < n;
  }
  // Mixed cases
  if (u.k === "mul" && (v.k === "pow" || v.k === "add" || vs || v.k === "fn")) return before(u, mk("mul", [v]));
  if (v.k === "mul" && (u.k === "pow" || u.k === "add" || us || u.k === "fn")) return !before(v, u) && u !== v;
  if (u.k === "pow" && (v.k === "add" || vs || v.k === "fn")) return before(u, mk("pow", [v, ONE]));
  if (v.k === "pow" && (u.k === "add" || us || u.k === "fn")) return !before(v, u);
  if (u.k === "add" && (vs || v.k === "fn")) return before(u, mk("add", [v]));
  if (v.k === "add" && (us || u.k === "fn")) return !before(v, u);
  if (u.k === "fn" && vs) return u.name === nameOf(v) ? false : u.name < nameOf(v);
  if (v.k === "fn" && us) return !before(v, u);
  // Everything else (relations, matrices, ...) sorts after algebraic kinds, then by kind name / id
  const ru = KIND_RANK[u.k] ?? 9, rv = KIND_RANK[v.k] ?? 9;
  if (ru !== rv) return ru < rv;
  if (u.k !== v.k) return u.k < v.k;
  return u.id < v.id;
}
export const sortArgs = (args) => args.slice().sort((a, b) => (a === b ? 0 : before(a, b) ? -1 : 1));

// Split a term into [numeric coefficient, rest] ; 3*x*y -> [3, x*y]
export function coeffAndTerm(u) {
  if (u.k === "num") return [u.v, ONE];
  if (u.k === "mul" && u.args[0].k === "num") {
    const rest = u.args.slice(1);
    return [u.args[0].v, rest.length === 1 ? rest[0] : mk("mul", rest)];
  }
  return [N.ONE, u];
}
// Split a factor into [base, exponent]
export function baseExp(u) {
  if (u.k === "pow") return [u.args[0], u.args[1]];
  return [u, ONE];
}
