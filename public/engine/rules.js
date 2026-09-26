// Quelvra rewrite-rule engine.
//
// Pattern language
//   Patterns are ordinary math trees in which some symbols are PATTERN VARIABLES:
//     _a    matches any subtree (the same variable must match the same subtree everywhere)
//     __c   OPTIONAL variable: may also match the identity of its context
//           (1 inside a product or as an exponent, 0 inside a sum)
//   Write patterns as source strings, e.g. rule("log.product", "ln(_a*_b)", ...). pat(src) parses them.
//   Typed constraints go in `where`: { n: "integer", c: ["numeric", "nonzero"], a: { freeOf: "x" } }
//   (integer, numeric, rational, nonzero, positive, negative, nonnegative, even, odd, posint, int2
//    (integer >= 2), const (symbol-free), nonnum, sum, notone, or a predicate (node, ctx) -> bool).
//
//   add and mul patterns are matched associatively-commutatively: the pattern terms match target
//   terms in any order. At the rule's root, a sum/product pattern matches a SUBSET of the target's
//   terms and the rest is kept (3sin^2x + 3cos^2x + y -> 3 + y). Inside, a bare variable absorbs the
//   remaining terms (sqrt(_a + _b) against sqrt(x + y + 1)). Numeric literals match numerically:
//   pattern 2*sin(_x)*cos(_x) matches 6 sin x cos x at the root (3 is kept as the rest).
//
// Rule record
//   { id, title, match, guard(b, ctx) -> true | false | { conditions: [rel], assumption?: bool },
//     transform(b, ctx) -> tree | null, explain(b) -> string, kind: "equivalent" | "conditional",
//     domainConditions(b) -> [rel] (implied by the input's domain), cost?, tags, raw? }
//   A guard's conditions with assumption: true are EXTRA assumptions (the rewrite is only valid under
//   them); without it they are consequences of the input's own domain that the result no longer shows
//   (e.g. ln a + ln b -> ln(ab) needs a > 0, b > 0). Both are attached to the step; assumption rewrites
//   run only when the caller passes allowConditional: true.
//
// Complexity score (lower is simpler), used by the scheduler to accept only improving rewrites:
//   cost(u) = nodes + digits + 2*radicals + 2*reciprocals + depth + functions
//     nodes       number of tree nodes
//     digits      for each number, floor((decimal digits of numerator and denominator - 2) / 6)
//     radicals    pow nodes whose exponent is a non-integer rational or symbolic
//     reciprocals pow nodes with a negative exponent (fractions)
//     depth       nesting depth of the tree
//     functions   fn nodes (sin, ln, abs, ...)

import * as N from "./num.js";
import * as X from "./expr.js";
import { simplify, makeCtx, expand, together } from "./simplify.js";
import { parse } from "./parse.js";
import { toText } from "./print.js";
import { signUnder, normalizeConditions, inferDomain, checkPoint, decideRel, safeSimplify } from "./domain.js";

const { ZERO, ONE, TWO, NEG_ONE, HALF, PI, E, I, UNDEF, TRUE, FALSE } = X;
const REST = "\u0000rest";

function budgetErr(msg) {
  const e = new Error("Quelvra: " + msg);
  e.code = "BUDGET";
  return e;
}
const now = () => (typeof performance !== "undefined" ? performance.now() : Date.now());

// ---------------- context helpers ----------------
export function ensureCtx(ctx) {
  return ctx || makeCtx({ budget: { ops: 3_000_000 } });
}
const plain = (ctx) => ({ ...ctx, conditions: null });
// Canonicalise; a foundation bug can make simplify recurse forever on some inputs, so a RangeError
// is converted to "no result" (the caller then rejects the candidate).
function canon(u, ctx) {
  try { return simplify(u, plain(ctx)); } catch (e) { if (e instanceof RangeError) return null; throw e; }
}
function canonNotes(u, ctx) {
  const c = { ...ctx, conditions: [] };
  try {
    const r = simplify(u, c);
    const rels = c.conditions.map(noteToRel);
    return [r, normalizeConditions(rels, ctx) || rels];
  } catch (e) {
    if (e instanceof RangeError) return [null, []];
    throw e;
  }
}
function noteToRel(n) {
  const op = n.rel === "!=0" ? "!=" : n.rel === ">=0" ? ">=" : ">";
  return X.rel(op, n.node, ZERO);
}
const C = (u, ctx) => canon(u, ctx || ensureCtx());

// ---------------- patterns ----------------
const HAS_PV = new WeakMap();
const isPV = (u) => u.k === "sym" && u.name.charCodeAt(0) === 95;
const isOptPV = (u) => isPV(u) && u.name.startsWith("__");
const pvKey = (u) => u.name.replace(/^_+/, "");
export function hasPV(u) {
  let r = HAS_PV.get(u);
  if (r !== undefined) return r;
  r = isPV(u) || u.args.some(hasPV);
  HAS_PV.set(u, r);
  return r;
}
export const pv = (name, optional = false) => X.sym((optional ? "__" : "_") + name);

const PAT_CTX = makeCtx({ budget: { ops: 1e9 } });
const PAT_CACHE = new Map();
// Parse a pattern source string (or normalise a tree) into matchable form.
export function pat(src) {
  if (typeof src !== "string") return normalizePattern(src);
  const hit = PAT_CACHE.get(src);
  if (hit) return hit;
  const s = src.replace(/(^|[^A-Za-z_])(__|_)([A-Za-z][A-Za-z0-9]*)/g, (m, pre, us, name) => `${pre} ${us === "__" ? "W" : "Z"}_${name} `);
  let u = parse(s);
  u = X.mapTree(u, (w) => (w.k === "sym" && /^[ZW]_/.test(w.name) ? X.sym((w.name[0] === "W" ? "__" : "_") + w.name.slice(2)) : w));
  u = normalizePattern(u);
  PAT_CACHE.set(src, u);
  return u;
}
// Light normalisation: ground subtrees canonical; sums/products flattened with one numeric literal.
function normalizePattern(u) {
  return X.mapTree(u, (w) => {
    if (!hasPV(w)) return simplify(w, PAT_CTX);
    if (w.k === "add" || w.k === "mul") {
      const isMul = w.k === "mul";
      let c = isMul ? N.ONE : N.ZERO;
      const rest = [];
      for (const a of w.args) {
        for (const b of a.k === w.k ? a.args : [a]) {
          if (b.k === "num") c = isMul ? N.mul(c, b.v) : N.add(c, b.v);
          else rest.push(b);
        }
      }
      if (isMul && N.isZero(c)) return ZERO;
      const lit = isMul ? (N.isOne(c) ? [] : [X.num(c)]) : N.isZero(c) ? [] : [X.num(c)];
      const args = isMul ? [...lit, ...rest] : [...rest, ...lit];
      return args.length === 1 ? args[0] : isMul ? X.mul(...args) : X.add(...args);
    }
    if (w.k === "pow" && w.args[1] === ONE) return w.args[0];
    return w;
  });
}

// ---------------- constraints ----------------
function isIntegerNode(u, ctx) {
  if (u.k === "num") return u.v.d === 1n;
  if (u.k === "sym") { const t = ctx && ctx.assume && ctx.assume.get(u.name); return !!(t && t.has("integer")); }
  return false;
}
const CHECKS = {
  integer: (u, ctx) => isIntegerNode(u, ctx),
  numeric: (u) => u.k === "num",
  number: (u) => u.k === "num",
  rational: (u) => u.k === "num",
  nonzero: (u, ctx) => { const s = signUnder(u, ctx); return s === 1 || s === -1 || s === "nz"; },
  positive: (u, ctx) => signUnder(u, ctx) === 1,
  negative: (u, ctx) => signUnder(u, ctx) === -1,
  nonnegative: (u, ctx) => { const s = signUnder(u, ctx); return s === 1 || s === 0 || s === "nn"; },
  even: (u) => u.k === "num" && u.v.d === 1n && u.v.n % 2n === 0n,
  odd: (u) => u.k === "num" && u.v.d === 1n && u.v.n % 2n !== 0n,
  posint: (u) => u.k === "num" && u.v.d === 1n && u.v.n > 0n,
  negint: (u) => u.k === "num" && u.v.d === 1n && u.v.n < 0n,
  int2: (u) => u.k === "num" && u.v.d === 1n && u.v.n >= 2n,
  const: (u) => X.freeSymbols(u).size === 0,
  nonnum: (u) => u.k !== "num",
  sum: (u) => u.k === "add",
  notone: (u) => u !== ONE,
  fraction: (u) => u.k === "num" && u.v.d !== 1n,
};
function checkWhere(spec, u, ctx) {
  if (!spec) return true;
  if (Array.isArray(spec)) return spec.every((s) => checkWhere(s, u, ctx));
  if (typeof spec === "function") return !!spec(u, ctx);
  if (typeof spec === "string") {
    const f = CHECKS[spec];
    if (!f) throw new Error("Quelvra: unknown pattern constraint " + spec);
    return f(u, ctx);
  }
  if (spec.freeOf) return X.freeOf(u, spec.freeOf);
  return true;
}

// ---------------- matching ----------------
class Matcher {
  constructor(where, ctx, limit) {
    this.where = where || {};
    this.ctx = ctx;
    this.ops = 0;
    this.limit = limit || 20000;
  }
  tick() { if (++this.ops > this.limit) throw budgetErr("pattern matching budget exhausted"); }
  bind(B, v, t) {
    const cur = B.get(v.name);
    if (cur !== undefined) return cur === t ? B : null;
    if (!checkWhere(this.where[pvKey(v)], t, this.ctx)) return null;
    const B2 = new Map(B);
    B2.set(v.name, t);
    return B2;
  }
}
function splitTerms(t, op) {
  const isMul = op === "mul";
  if (t.k === "num") return { coef: t.v, items: [] };
  if (t.k === op) {
    let coef = isMul ? N.ONE : N.ZERO;
    const items = [];
    for (const a of t.args) {
      if (a.k === "num") coef = isMul ? N.mul(coef, a.v) : N.add(coef, a.v);
      else items.push(a);
    }
    return { coef, items };
  }
  return { coef: isMul ? N.ONE : N.ZERO, items: [t] };
}
function combine(M, op, elems) {
  if (!elems.length) return op === "mul" ? ONE : ZERO;
  if (elems.length === 1) return elems[0];
  const r = canon(op === "mul" ? X.mul(...elems) : X.add(...elems), M.ctx);
  if (!r) throw budgetErr("combine failed");
  return r;
}
function* match(M, p, t, B) {
  M.tick();
  if (isPV(p)) { const B2 = M.bind(B, p, t); if (B2) yield B2; return; }
  if (!hasPV(p)) { if (p === t) yield B; return; }
  if (p.k === "add" || p.k === "mul") { yield* matchAC(M, p, t, B, false); return; }
  if (p.k === "pow") {
    const [pb, pe] = p.args;
    if (t.k === "pow") for (const B1 of match(M, pb, t.args[0], B)) yield* match(M, pe, t.args[1], B1);
    else if (isOptPV(pe)) { const B1 = M.bind(B, pe, ONE); if (B1) yield* match(M, pb, t, B1); }
    return;
  }
  if (t.k !== p.k || t.args.length !== p.args.length) return;
  for (const f of ["name", "op", "dir", "q", "lo_open", "hi_open"]) if (p[f] !== t[f]) return;
  yield* matchSeq(M, p.args, t.args, 0, B);
}
function* matchSeq(M, ps, ts, i, B) {
  if (i === ps.length) { yield B; return; }
  for (const B1 of match(M, ps[i], ts[i], B)) yield* matchSeq(M, ps, ts, i + 1, B1);
}
function specificity(p) {
  if (isPV(p)) return 0;
  let s = p.k === "fn" ? 3 : p.k === "num" ? 0 : 1;
  for (const a of p.args) s += specificity(a);
  return s;
}
function* matchAC(M, p, t, B, top) {
  const op = p.k, isMul = op === "mul";
  const idQ = isMul ? N.ONE : N.ZERO;
  let kp = idQ;
  const parts = [];
  for (const a of p.args) {
    if (a.k === "num") kp = isMul ? N.mul(kp, a.v) : N.add(kp, a.v);
    else parts.push(a);
  }
  const T = splitTerms(t, op);
  let coef = T.coef;
  if (!N.eq(kp, idQ)) {
    if (isMul) {
      if (N.isZero(kp) || N.isZero(coef)) return;
      coef = N.div(coef, kp);
      // inside a function argument only integer multiples: sin(2*_x) must not match sin(x) as 2*(x/2)
      if (!top && !N.eq(kp, N.NEG_ONE) && coef.d !== 1n) return;
    } else {
      if (N.isZero(T.coef)) return;
      coef = N.sub(coef, kp);
    }
  }
  const structural = parts.filter((a) => !isPV(a)).map((a, i) => [a, i]).sort((x, y) => specificity(y[0]) - specificity(x[0]) || x[1] - y[1]).map((x) => x[0]);
  const bare = parts.filter(isPV);
  if (structural.length + bare.length > T.items.length + 1 + bare.filter(isOptPV).length) return;
  yield* acStructural(M, op, structural, 0, bare, T.items, new Array(T.items.length).fill(false), coef, B, top);
}
function* acStructural(M, op, parts, i, bare, items, used, coef, B, top) {
  M.tick();
  if (i === parts.length) {
    yield* acBare(M, op, bare, items.filter((_, j) => !used[j]), coef, B, top);
    return;
  }
  const part = parts[i];
  for (let j = 0; j < items.length; j++) {
    if (used[j]) continue;
    for (const B1 of match(M, part, items[j], B)) {
      used[j] = true;
      yield* acStructural(M, op, parts, i + 1, bare, items, used, coef, B1, top);
      used[j] = false;
    }
  }
  const idQ = op === "mul" ? N.ONE : N.ZERO;
  if (!N.eq(coef, idQ)) for (const B1 of match(M, part, X.num(coef), B)) yield* acStructural(M, op, parts, i + 1, bare, items, used, idQ, B1, top);
}
function removeValue(op, val, items, coef) {
  const isMul = op === "mul";
  const V = splitTerms(val, op);
  const out = items.slice();
  for (const vi of V.items) {
    const k = out.indexOf(vi);
    if (k < 0) return null;
    out.splice(k, 1);
  }
  let c = coef;
  if (isMul) { if (N.isZero(V.coef)) return null; c = N.div(c, V.coef); }
  else if (!N.isZero(V.coef)) { if (N.isZero(c)) return null; c = N.sub(c, V.coef); }
  return { items: out, coef: c };
}
function* acBare(M, op, bare, pool, coef, B, top) {
  const isMul = op === "mul";
  const idQ = isMul ? N.ONE : N.ZERO;
  const idNode = isMul ? ONE : ZERO;
  // an unbound variable that occurs more than once (_x + _x): bind its first occurrence to each
  // candidate element, then the other occurrences are removed as bound values
  const dup = bare.find((v, i) => !B.has(v.name) && bare.indexOf(v) !== i);
  if (dup) {
    const restBare = bare.slice();
    restBare.splice(restBare.indexOf(dup), 1);
    for (let j = 0; j < pool.length; j++) {
      const B2 = M.bind(B, dup, pool[j]);
      if (B2) yield* acBare(M, op, restBare, pool.filter((_, k) => k !== j), coef, B2, top);
    }
    if (!N.eq(coef, idQ)) { const B2 = M.bind(B, dup, X.num(coef)); if (B2) yield* acBare(M, op, restBare, pool, idQ, B2, top); }
    return;
  }
  let items = pool, c = coef;
  const unbound = [];
  for (const v of bare) {
    if (B.has(v.name)) {
      const r = removeValue(op, B.get(v.name), items, c);
      if (!r) return;
      items = r.items; c = r.coef;
    } else unbound.push(v);
  }
  const elems = items.slice();
  if (!N.eq(c, idQ)) elems.unshift(X.num(c));
  if (top) {
    const used = new Array(elems.length).fill(false);
    function* go(i, B1) {
      M.tick();
      if (i === unbound.length) {
        const rest = elems.filter((_, j) => !used[j]);
        const B2 = new Map(B1);
        B2.set(REST, rest.length ? combine(M, op, rest) : null);
        yield B2;
        return;
      }
      const v = unbound[i];
      for (let j = 0; j < elems.length; j++) {
        if (used[j]) continue;
        const B2 = M.bind(B1, v, elems[j]);
        if (!B2) continue;
        used[j] = true;
        yield* go(i + 1, B2);
        used[j] = false;
      }
      if (isOptPV(v)) { const B2 = M.bind(B1, v, idNode); if (B2) yield* go(i + 1, B2); }
    }
    yield* go(0, B);
    return;
  }
  const n = unbound.length, m = elems.length;
  if (n === 0) { if (m === 0) yield B; return; }
  if (n === 1) {
    const v = unbound[0];
    if (m === 0) { if (isOptPV(v)) { const B2 = M.bind(B, v, idNode); if (B2) yield B2; } return; }
    const B2 = M.bind(B, v, combine(M, op, elems));
    if (B2) yield B2;
    return;
  }
  // several bare variables: one collector takes the remainder, the others one element each
  for (let ci = n - 1; ci >= 0; ci--) {
    const others = unbound.filter((_, k) => k !== ci);
    const used = new Array(m).fill(false);
    function* go(i, B1) {
      M.tick();
      if (i === others.length) {
        const rest = elems.filter((_, j) => !used[j]);
        const col = unbound[ci];
        if (!rest.length && !isOptPV(col)) return;
        const B2 = M.bind(B1, col, rest.length ? combine(M, op, rest) : idNode);
        if (B2) yield B2;
        return;
      }
      const v = others[i];
      for (let j = 0; j < m; j++) {
        if (used[j]) continue;
        const B2 = M.bind(B1, v, elems[j]);
        if (!B2) continue;
        used[j] = true;
        yield* go(i + 1, B2);
        used[j] = false;
      }
      if (isOptPV(v)) { const B2 = M.bind(B1, v, idNode); if (B2) yield* go(i + 1, B2); }
    }
    yield* go(0, B);
  }
}
function* matchTop(M, p, t) {
  if ((p.k === "add" || p.k === "mul") && hasPV(p)) yield* matchAC(M, p, t, new Map(), true);
  else yield* match(M, p, t, new Map());
}
// Public: all matches of a pattern at the root of a tree, as plain binding objects
// ({ a: node, ... , rest: node | null }). Bounded by `limit` results.
export function matchPattern(pattern, tree, opts = {}) {
  const p = typeof pattern === "string" ? pat(pattern) : pattern;
  const M = new Matcher(opts.where, ensureCtx(opts.ctx), opts.matchLimit);
  const out = [];
  for (const B of matchTop(M, p, tree)) {
    out.push(toObj(B));
    if (out.length >= (opts.limit || 20)) break;
  }
  return out;
}
function toObj(B) {
  const o = {};
  for (const [k, v] of B) if (k === REST) o.rest = v; else o[k.replace(/^_+/, "")] = v;
  return o;
}
function instantiate(rhs, b) {
  const m = new Map();
  const walk = (u) => {
    if (isPV(u)) { const key = pvKey(u); m.set(u.name, b[key] !== undefined ? b[key] : isOptPV(u) ? ONE : u); return; }
    for (const a of u.args) walk(a);
  };
  walk(rhs);
  return X.subs(rhs, m);
}

// ---------------- rules ----------------
const RULES = new Map();
export function rule(id, lhs, rhs, opts = {}) {
  const r = {
    id,
    title: opts.title || id,
    match: typeof lhs === "string" ? pat(lhs) : lhs && lhs.k ? pat(lhs) : null,
    matcher: typeof lhs === "function" ? lhs : null,
    lhsSrc: typeof lhs === "string" ? lhs : null,
    rhsSrc: typeof rhs === "string" ? rhs : null,
    rhs: typeof rhs === "string" ? pat(rhs) : rhs && rhs.k ? rhs : null,
    transformFn: typeof rhs === "function" ? rhs : null,
    where: opts.where || {},
    guard: opts.guard || null,
    domainConditions: opts.domainConditions || null,
    why: opts.why || null,
    kind: opts.kind || "equivalent",
    cost: opts.cost,
    tags: opts.tags || [],
    raw: !!opts.raw,
  };
  r.transform = (b, ctx) => (r.transformFn ? r.transformFn(b, ctx) : instantiate(r.rhs, b));
  r.explain = (b, extra) => {
    if (r.why) return typeof r.why === "function" ? r.why(b) : r.why;
    return r.title + (extra ? ": " + extra : "");
  };
  RULES.set(id, r);
  return r;
}
export const getRule = (id) => RULES.get(id);
export const allRules = () => [...RULES.values()];

function runGuard(rule, b, ctx, opts) {
  let g = rule.guard ? rule.guard(b, ctx) : true;
  if (!g) return null;
  if (g === true) g = { conditions: [] };
  let conds = g.conditions || [];
  const dom = rule.domainConditions ? rule.domainConditions(b, ctx) || [] : [];
  const normA = normalizeConditions(conds, ctx);
  const normD = normalizeConditions(dom, ctx);
  if (!normA || !normD) return null;
  const assumption = !!g.assumption && normA.length > 0;
  if (assumption && !opts.allowConditional) return null;
  const all = [...normA];
  for (const d of normD) if (!all.includes(d)) all.push(d);
  return { conditions: all, assumption };
}
// Try a rule at ONE node. Returns { rhs, b, g } or null.
function tryRule(rule, node, ctx, opts = {}) {
  const M = new Matcher(rule.where, ctx, opts.matchLimit);
  const cands = rule.matcher ? [rule.matcher(node, ctx)].filter(Boolean).map((b) => new Map(Object.entries(b).map(([k, v]) => ["_" + k, v]))) : matchTop(M, rule.match, node);
  let n = 0;
  for (const B of cands) {
    if (++n > (opts.maxBindings || 12)) break;
    const b = rule.matcher ? Object.fromEntries([...B].map(([k, v]) => [k.slice(1), v])) : toObj(B);
    const g = runGuard(rule, b, ctx, opts);
    if (!g) continue;
    let rhs = rule.transform(b, ctx);
    if (!rhs) continue;
    if (b.rest) rhs = rule.match.k === "add" ? X.add(rhs, b.rest) : X.mul(rhs, b.rest);
    return { rhs, b, g };
  }
  return null;
}
function* positions(u, path = []) {
  if (u.k === "num" || u.k === "sym" || u.k === "const" || u.k === "bool") return;
  yield [u, path];
  for (let i = 0; i < u.args.length; i++) yield* positions(u.args[i], [...path, i]);
}
function replaceAt(u, path, sub, i = 0) {
  if (i === path.length) return sub;
  const args = u.args.slice();
  args[path[i]] = replaceAt(u.args[path[i]], path, sub, i + 1);
  return X.withArgs(u, args);
}
// Conditions of the input's domain that the output no longer shows (x^2/x -> x loses x != 0).
function lostDomain(before, after, ctx) {
  try {
    const now = new Set(inferDomain(after, { ctx }).rels);
    return inferDomain(before, { ctx }).rels.filter((c) => c !== FALSE && !now.has(c));
  } catch (e) {
    if (e.code === "BUDGET") return [];
    throw e;
  }
}
function makeStep(rule, r, before, after, at, notes, ctx) {
  const conditions = [...r.g.conditions];
  for (const n of notes || []) if (!conditions.includes(n)) conditions.push(n);
  if (ctx && after) for (const n of lostDomain(before, after, ctx)) if (!conditions.includes(n)) conditions.push(n);
  const condText = conditions.length ? ` (valid when ${conditions.map((c) => toText(c)).join(", ")})` : "";
  return {
    rule: rule.id,
    title: rule.title,
    why: rule.explain(r.b, `${toText(at)} = ${safeText(r.rhs)}`) + condText,
    before, after, at, replacement: r.rhs,
    conditions,
    kind: conditions.length ? "conditional" : "equivalent",
    conditionKind: r.g.assumption ? "assumption" : conditions.length ? "domain" : null,
    tags: rule.tags,
  };
}
function safeText(u) { try { return toText(u); } catch (_) { return "?"; } }

// Apply a rule at the first matching position (preorder) or, with { all: true }, at every
// non-overlapping position bottom-up. Returns { tree, step } or null.
export function applyRule(tree, ruleOrId, ctx, opts = {}) {
  const rule = typeof ruleOrId === "string" ? RULES.get(ruleOrId) : ruleOrId;
  if (!rule) throw new Error("Quelvra: unknown rule " + ruleOrId);
  ctx = ensureCtx(ctx);
  const o = { allowConditional: true, ...opts };
  if (!o.all) {
    for (const [node, path] of positions(tree)) {
      const r = tryRule(rule, node, ctx, o);
      if (!r) continue;
      const replaced = replaceAt(tree, path, r.rhs);
      const [after, notes] = rule.raw ? [replaced, []] : canonNotes(replaced, ctx);
      if (!after || after === tree) continue;
      return { tree: after, step: makeStep(rule, r, tree, after, node, notes, ctx) };
    }
    return null;
  }
  const conds = [];
  let count = 0, assumption = false;
  const out = X.mapTree(tree, (u) => {
    const r = tryRule(rule, u, ctx, o);
    if (!r) return u;
    count++;
    if (r.g.assumption) assumption = true;
    for (const c of r.g.conditions) if (!conds.includes(c)) conds.push(c);
    return r.rhs;
  });
  if (!count) return null;
  const [after, notes] = rule.raw ? [out, []] : canonNotes(out, ctx);
  if (!after || after === tree) return null;
  const step = makeStep(rule, { g: { conditions: conds, assumption }, b: {}, rhs: after }, tree, after, tree, notes, ctx);
  step.count = count;
  return { tree: after, step };
}

// ---------------- complexity ----------------
const COST = new WeakMap();
export function complexity(u) {
  const hit = COST.get(u);
  if (hit !== undefined) return hit;
  let c = 1;
  let d = 0;
  if (u.k === "num") {
    const len = u.v.n.toString().replace("-", "").length + u.v.d.toString().length;
    c += Math.max(0, Math.floor((len - 2) / 6));
  } else if (u.k === "pow") {
    const e = u.args[1];
    if (e.k !== "num" || e.v.d !== 1n) c += 2;
    if ((e.k === "num" && N.isNeg(e.v)) || (e.k === "mul" && e.args[0].k === "num" && N.isNeg(e.args[0].v))) c += 2;
  } else if (u.k === "fn") c += 1;
  for (const a of u.args) {
    c += complexity(a) - depthOf(a); // children's cost without their depth term
    d = Math.max(d, depthOf(a));
  }
  c += d + 1;
  COST.set(u, c);
  return c;
}
const DEPTH = new WeakMap();
function depthOf(u) {
  let d = DEPTH.get(u);
  if (d === undefined) { d = X.depth(u); DEPTH.set(u, d); }
  return d;
}

// ---------------- external hooks ----------------
const EXTERNAL = new Map();
// registerExternal("factor", (tree, ctx) => tree | null), "apart", "gcd" (polynomial engine), ...
// registerExternal(name, null) removes the hook.
export function registerExternal(name, fn) {
  if (fn === null) { EXTERNAL.delete(name); return; }
  if (typeof fn !== "function") throw new TypeError("registerExternal needs a function");
  EXTERNAL.set(name, fn);
}
export const getExternal = (name) => EXTERNAL.get(name) || null;

// ---------------- helpers used by rules ----------------
const pos = (u, ctx) => signUnder(u, ctx) === 1;
const nonneg = (u, ctx) => { const s = signUnder(u, ctx); return s === 1 || s === 0 || s === "nn"; };
const isReal = (ctx) => !ctx || ctx.domain !== "complex";
const R = (op, a, b) => X.rel(op, a, b);
const gt0 = (u) => R(">", u, ZERO);
const ge0 = (u) => R(">=", u, ZERO);
const ne0 = (u) => R("!=", u, ZERO);
const ln = (u) => X.fn("ln", u);
const abs = (u) => X.fn("abs", u);
const qOf = (u) => (u.k === "num" ? u.v : null);
const hasRadical = (u) => u.k === "pow" && u.args[1].k === "num" && u.args[1].v.d === 2n ? true : u.args.some(hasRadical);
const TRIG = new Set(["sin", "cos", "tan", "cot", "sec", "csc"]);
const hasTrig = (u) => (u.k === "fn" && TRIG.has(u.name)) || u.args.some(hasTrig);

// Exact rational square root (or null)
function ratSqrt(q) {
  if (N.isNeg(q)) return null;
  const [a, ea] = N.iroot(q.n, 2);
  const [b, eb] = N.iroot(q.d, 2);
  return ea && eb ? N.Q(a, b) : null;
}

// ---------------- univariate polynomials over Q (for cancellation) ----------------
function toPoly(u, x) {
  const terms = u.k === "add" ? u.args : [u];
  const coeffs = [];
  for (const t of terms) {
    const [k, rest] = X.coeffAndTerm(t);
    let deg;
    if (rest === ONE) deg = 0;
    else if (rest === x) deg = 1;
    else if (rest.k === "pow" && rest.args[0] === x && rest.args[1].k === "num" && rest.args[1].v.d === 1n && rest.args[1].v.n > 0n) {
      if (rest.args[1].v.n > 200n) return null;
      deg = Number(rest.args[1].v.n);
    } else return null;
    while (coeffs.length <= deg) coeffs.push(N.ZERO);
    coeffs[deg] = N.add(coeffs[deg], k);
  }
  return trimP(coeffs);
}
function trimP(p) { while (p.length && N.isZero(p[p.length - 1])) p.pop(); return p; }
function divmodP(a, b) {
  a = a.slice();
  const q = new Array(Math.max(0, a.length - b.length + 1)).fill(N.ZERO);
  const lb = b[b.length - 1];
  let guard = 0;
  while (a.length >= b.length && a.length) {
    if (++guard > 1000) throw budgetErr("polynomial division");
    const k = N.div(a[a.length - 1], lb);
    const sh = a.length - b.length;
    q[sh] = k;
    for (let i = 0; i < b.length; i++) a[sh + i] = N.sub(a[sh + i], N.mul(k, b[i]));
    trimP(a);
  }
  return [trimP(q), a];
}
function gcdP(a, b) {
  let guard = 0;
  while (b.length) {
    if (++guard > 500) throw budgetErr("polynomial gcd");
    const [, r] = divmodP(a, b);
    a = b; b = r;
  }
  if (!a.length) return a;
  const lc = a[a.length - 1];
  return a.map((c) => N.div(c, lc));
}
function fromPoly(p, x, ctx) {
  const terms = p.map((c, i) => (N.isZero(c) ? null : X.mul(X.num(c), i === 0 ? ONE : X.pow(x, X.num(i))))).filter(Boolean);
  return C(terms.length ? X.add(...terms) : ZERO, ctx);
}
// numerator / denominator split without touching the canonicaliser's default context
function splitFraction(u, ctx) {
  const fs = u.k === "mul" ? u.args : [u];
  const num = [], den = [];
  for (const f of fs) {
    if (f.k === "pow" && f.args[1].k === "num" && N.isNeg(f.args[1].v)) den.push(X.pow(f.args[0], X.num(N.neg(f.args[1].v))));
    else if (f.k === "num" && f.v.d !== 1n) { num.push(X.num(f.v.n)); den.push(X.num(f.v.d)); }
    else num.push(f);
  }
  return [C(X.mul(...num), ctx), C(X.mul(...den), ctx)];
}

// ================= RULE LIBRARY =================
const SETS = new Map();
export function defineRuleSet(name, mode, rules, description = "") {
  const set = { name, mode, rules: rules.map((r) => (typeof r === "string" ? RULES.get(r) : r)), description };
  if (set.rules.some((r) => !r)) throw new Error("Quelvra: rule set " + name + " references an unknown rule");
  SETS.set(name, set);
  return set;
}
export const ruleSet = (name) => SETS.get(name);
export const ruleSetNames = () => [...SETS.keys()];

// ---------- exponents ----------
rule("exp.power_of_power", "(_x^_a)^_b", "_x^(_a*_b)", {
  title: "Power of a power",
  why: "(x^a)^b = x^(ab) holds for integer b, or for x > 0.",
  guard: (b, ctx) => (isIntegerNode(b.b, ctx) || pos(b.x, ctx) ? true : { conditions: [gt0(b.x)], assumption: true }),
  tags: ["exponent"],
});
rule("exp.sum_exponent", "_a^(_b + _c)", (b, ctx) => X.mul(C(X.pow(b.a, b.b), ctx), C(X.pow(b.a, b.c), ctx)), {
  title: "Split a sum in the exponent",
  why: "a^(b+c) = a^b a^c for a > 0 (or a != 0 with integer exponents).",
  guard: (b, ctx) => {
    if (pos(b.a, ctx)) return true;
    if (isIntegerNode(b.b, ctx) && isIntegerNode(b.c, ctx)) return { conditions: [ne0(b.a)] };
    return { conditions: [gt0(b.a)], assumption: true };
  },
  raw: true,
  tags: ["exponent"],
});
rule("exp.product_base", "(_a*_b)^_n", "_a^_n*_b^_n", {
  title: "Power of a product",
  why: "(ab)^n = a^n b^n for integer n, for an odd root over the reals, or when one factor is >= 0.",
  where: { n: "nonnum" },
  guard: (b, ctx) => {
    if (isIntegerNode(b.n, ctx) || nonneg(b.a, ctx) || nonneg(b.b, ctx)) return true;
    return { conditions: [ge0(b.a), ge0(b.b)], assumption: true };
  },
  tags: ["exponent"],
});
rule("exp.product_base_root", "(_a*_b)^_n", "_a^_n*_b^_n", {
  title: "Root of a product",
  why: "(ab)^q = a^q b^q when one factor is >= 0 (principal roots); in general it fails: sqrt((-1)(-1)) != sqrt(-1)sqrt(-1).",
  where: { n: "fraction" },
  guard: (b, ctx) => {
    if (nonneg(b.a, ctx) || nonneg(b.b, ctx)) return true;
    if (isReal(ctx) && b.n.v.d % 2n === 1n) return true;
    return { conditions: [ge0(b.a), ge0(b.b)], assumption: true };
  },
  tags: ["exponent", "radical"],
});
rule("exp.combine_bases", "_a^_n*_b^_n", "(_a*_b)^_n", {
  title: "Combine powers with the same exponent",
  why: "a^n b^n = (ab)^n where both sides are defined (both bases >= 0 for even roots).",
  where: { n: (u) => !(u.k === "num" && u.v.d === 1n) },
  guard: (b, ctx) => {
    if (nonneg(b.a, ctx) && nonneg(b.b, ctx)) return true;
    if (b.n.k === "num") {
      if (!isReal(ctx)) return { conditions: [ge0(b.a), ge0(b.b)], assumption: true };
      // even root: the left side already needs a >= 0 and b >= 0
      if (b.n.v.d % 2n === 0n) return N.isNeg(b.n.v) ? { conditions: [gt0(b.a), gt0(b.b)] } : { conditions: [ge0(b.a), ge0(b.b)] };
      return true;
    }
    return { conditions: [gt0(b.a), gt0(b.b)], assumption: true };
  },
  tags: ["exponent", "radical"],
});
rule("exp.log_inverse", "_b^log(_b, _x)", "_x", {
  title: "Exponential undoes the logarithm",
  why: "b^(log_b x) = x for x > 0.",
  domainConditions: (b) => [gt0(b.x)],
  tags: ["exponent", "log"],
});
rule("exp.to_radical", "_x^_q", (b) => {
  const q = b.q.v;
  const n = q.d;
  const p = q.n < 0n ? -q.n : q.n;
  const whole = p / n, r = p % n;
  const rad = X.pow(b.x, X.num(N.Q(1n, n)));
  const parts = [];
  if (whole > 0n) parts.push(whole === 1n ? b.x : X.pow(b.x, X.num(whole)));
  if (r > 0n) parts.push(r === 1n ? rad : X.pow(rad, X.num(r)));
  const body = parts.length === 1 ? parts[0] : X.mul(...parts);
  return q.n < 0n ? X.pow(body, NEG_ONE) : body;
}, {
  title: "Fractional exponent as a radical",
  why: "x^(p/n) is the n-th root of x raised to p: x^(3/2) = x sqrt(x).",
  where: { q: (u) => u.k === "num" && u.v.d !== 1n && !(u.v.n === 1n || u.v.n === -1n) },
  raw: true,
  tags: ["exponent", "radical"],
});

// ---------- radicals ----------
function matchDenest(node, ctx) {
  if (node.k !== "pow" || node.args[1] !== HALF) return null;
  const A = node.args[0];
  if (A.k !== "add" || A.args.length !== 2) return null;
  let a = null, rad = null;
  for (const t of A.args) if (t.k === "num") a = t.v; else rad = t;
  if (!a || !rad) return null;
  let bq = N.ONE, cnode = rad;
  if (rad.k === "mul" && rad.args.length === 2 && rad.args[0].k === "num") { bq = rad.args[0].v; cnode = rad.args[1]; }
  if (cnode.k !== "pow" || cnode.args[1] !== HALF || cnode.args[0].k !== "num") return null;
  const c = cnode.args[0].v;
  const d = N.sub(N.mul(a, a), N.mul(N.mul(bq, bq), c));
  const r = ratSqrt(d);
  if (!r) return null;
  const p = N.div(N.add(a, r), N.Q(2)), q = N.div(N.sub(a, r), N.Q(2));
  if (N.isNeg(q) || N.isNeg(p)) return null;
  const s = N.isNeg(bq) ? NEG_ONE : ONE;
  const result = C(X.add(X.sqrt(X.num(p)), X.mul(s, X.sqrt(X.num(q)))), ctx);
  // exact verification: result >= 0 and result^2 == radicand
  if (!result || result === node) return null;
  const sq = C(expand(X.pow(result, TWO), plain(ctx)), ctx);
  if (sq !== A) return null;
  return { a: A, result };
}
rule("rad.denest", matchDenest, (b) => b.result, {
  title: "Denest a square root",
  why: "sqrt(a + b sqrt(c)) = sqrt(p) + sqrt(q) with p + q = a and 4pq = b^2 c (checked exactly by squaring).",
  tags: ["radical"],
});
function matchRationalize(node, ctx) {
  if (node.k !== "pow" || node.args[1] !== NEG_ONE) return null;
  const D = node.args[0];
  if (D.k !== "add") return null;
  const rad = D.args.filter(hasRadical), others = D.args.filter((t) => !hasRadical(t));
  if (!rad.length) return null;
  let A, B;
  if (others.length) { A = C(X.add(...others), ctx); B = C(X.add(...rad), ctx); }
  else if (rad.length >= 2) { A = rad[0]; B = C(X.add(...rad.slice(1)), ctx); }
  else return null;
  const conj = C(X.sub(A, B), ctx);
  const prod = C(expand(X.sub(X.pow(A, TWO), X.pow(B, TWO)), plain(ctx)), ctx);
  if (!conj || !prod) return null;
  return { d: D, conj, prod };
}
rule("rad.rationalize", matchRationalize, (b, ctx) => {
  const r = X.mul(b.conj, X.pow(b.prod, NEG_ONE));
  return b.prod.k === "num" ? expand(r, plain(ctx)) : r; // numeric denominator: distribute it
}, {
  title: "Rationalize the denominator",
  why: "Multiply numerator and denominator by the conjugate so the square roots in the denominator cancel.",
  guard: (b, ctx) => {
    if (X.freeSymbols(b.d).size === 0) return b.prod !== ZERO;
    // the new denominator can vanish where the old one did not: an extra condition
    return { conditions: [ne0(b.prod)], assumption: true };
  },
  tags: ["radical", "fraction"],
});

// ---------- logarithms ----------
const logGuardProduct = (b, ctx) => {
  if (pos(b.a, ctx) || pos(b.b, ctx)) return true;
  if (!isReal(ctx)) return false;
  return { conditions: [gt0(X.mul(b.a, b.b))] };
};
rule("log.quotient", "ln(_a*_b^(-1))", (b, ctx) => {
  if (pos(b.a, ctx) || pos(b.b, ctx)) return X.sub(ln(b.a), ln(b.b));
  return X.sub(ln(abs(b.a)), ln(abs(b.b)));
}, {
  title: "Logarithm of a quotient",
  why: "ln(a/b) = ln a - ln b needs a > 0 and b > 0; in general ln(a/b) = ln|a| - ln|b| where a/b > 0.",
  where: { a: "notone" },
  guard: (b, ctx) => (pos(b.a, ctx) || pos(b.b, ctx) ? true : isReal(ctx) ? { conditions: [gt0(X.mul(b.a, X.pow(b.b, NEG_ONE)))] } : false),
  tags: ["log"],
});
rule("log.product", "ln(_a*_b)", (b, ctx) => {
  if (pos(b.a, ctx) || pos(b.b, ctx)) return X.add(ln(b.a), ln(b.b));
  return X.add(ln(abs(b.a)), ln(abs(b.b)));
}, {
  title: "Logarithm of a product",
  why: "ln(ab) = ln a + ln b needs a > 0 and b > 0 (one known positive factor suffices, since ab > 0); otherwise ln(ab) = ln|a| + ln|b| where ab > 0.",
  guard: logGuardProduct,
  tags: ["log"],
});
function lnPower(x, n, ctx, L = ln) {
  // returns [result, conditions, assumption] or null
  if (pos(x, ctx)) return [X.mul(n, L(x)), [], false];
  if (n.k === "num") {
    const q = n.v;
    const pEven = q.n % 2n === 0n, qEven = q.d % 2n === 0n;
    if (!isReal(ctx)) return null;
    if (qEven) return [X.mul(n, L(x)), [gt0(x)], false];
    if (pEven) return [X.mul(n, L(abs(x))), [ne0(x)], false];
    return [X.mul(n, L(x)), [gt0(x)], false];
  }
  return [X.mul(n, L(x)), [gt0(x)], true];
}
rule("log.power", "ln(_x^_n)", (b, ctx) => lnPower(b.x, b.n, ctx)[0], {
  title: "Logarithm of a power",
  why: "ln(x^n) = n ln x needs x > 0; for even n over the reals ln(x^2) = 2 ln|x| (x != 0), NOT 2 ln x.",
  guard: (b, ctx) => {
    if (b.x === E) return false;
    const r = lnPower(b.x, b.n, ctx);
    if (!r) return false;
    return { conditions: r[1], assumption: r[2] };
  },
  tags: ["log"],
});
rule("log.int_power", (node) => {
  if (node.k !== "fn" || node.name !== "ln" || node.args[0].k !== "num") return null;
  const q = node.args[0].v;
  if (!N.isPos(q) || N.isOne(q)) return null;
  if (q.d !== 1n) return { p: X.num(q.n), q: X.num(q.d), frac: TRUE };
  const { factors, rest } = N.trialFactor(q.n);
  if (rest !== 1n || !factors.size) return null;
  let g = 0n;
  for (const e of factors.values()) g = N.bgcd(g, e);
  if (g < 2n) return null;
  let base = 1n;
  for (const [p, e] of factors) base *= p ** (e / g);
  return { base: X.num(base), k: X.num(g) };
}, (b) => (b.frac ? X.sub(ln(b.p), ln(b.q)) : X.mul(b.k, ln(b.base))), {
  title: "Logarithm of a number",
  why: "ln(m^k) = k ln m and ln(p/q) = ln p - ln q for positive numbers.",
  tags: ["log"],
});
rule("log.b_product", "log(_c, _a*_b)", (b, ctx) => (pos(b.a, ctx) || pos(b.b, ctx) ? X.add(X.fn("log", b.c, b.a), X.fn("log", b.c, b.b)) : X.add(X.fn("log", b.c, abs(b.a)), X.fn("log", b.c, abs(b.b)))), {
  title: "Logarithm of a product (base b)",
  why: "log_c(ab) = log_c a + log_c b for a, b > 0; otherwise with absolute values where ab > 0.",
  guard: logGuardProduct,
  tags: ["log"],
});
rule("log.b_power", "log(_c, _x^_n)", (b, ctx) => lnPower(b.x, b.n, ctx, (u) => X.fn("log", b.c, u))[0], {
  title: "Logarithm of a power (base b)",
  why: "log_c(x^n) = n log_c x for x > 0; with |x| for even n.",
  guard: (b, ctx) => {
    if (b.x === b.c) return false;
    const r = lnPower(b.x, b.n, ctx);
    if (!r) return false;
    return { conditions: r[1], assumption: r[2] };
  },
  tags: ["log"],
});
rule("log.change_base", "log(_b, _x)", "ln(_x)/ln(_b)", {
  title: "Change of base",
  why: "log_b x = ln x / ln b.",
  tags: ["log"],
});
rule("log.to_base", "ln(_x)*ln(_b)^(-1)", "log(_b, _x)", {
  title: "Quotient of logarithms as one logarithm",
  why: "ln x / ln b = log_b x.",
  where: { b: (u) => u !== E },
  tags: ["log"],
});
rule("log.inverse_exp", "ln(e^_x)", "_x", {
  title: "Logarithm undoes the exponential",
  why: "ln(e^x) = x for real x.",
  guard: (b, ctx) => (isReal(ctx) ? true : { conditions: [R(">", b.x.k === "num" ? b.x : X.fn("im", b.x), X.mul(NEG_ONE, PI))], assumption: true }),
  tags: ["log"],
});
rule("log.inverse_pow", "log(_b, _b^_x)", "_x", {
  title: "Logarithm undoes the power",
  why: "log_b(b^x) = x for b > 0, b != 1.",
  domainConditions: (b) => [gt0(b.b), R("!=", b.b, ONE)],
  tags: ["log"],
});
const lnContractGuard = (b, ctx) => {
  if (!isReal(ctx) && !(pos(b.a, ctx) && pos(b.b, ctx))) return false;
  return { conditions: [gt0(b.a), gt0(b.b)] };
};
rule("log.contract_sum", "ln(_a) + ln(_b)", "ln(_a*_b)", {
  title: "Combine a sum of logarithms",
  why: "ln a + ln b = ln(ab) where both logarithms are defined (a > 0, b > 0).",
  guard: lnContractGuard,
  tags: ["log"],
});
rule("log.contract_diff", "ln(_a) - ln(_b)", "ln(_a/_b)", {
  title: "Combine a difference of logarithms",
  why: "ln a - ln b = ln(a/b) where both logarithms are defined (a > 0, b > 0).",
  guard: lnContractGuard,
  tags: ["log"],
});
rule("log.contract_coeff", "_n*ln(_a)", "ln(_a^_n)", {
  title: "Move a coefficient into the logarithm",
  why: "n ln a = ln(a^n) where ln a is defined (a > 0).",
  where: { n: ["numeric", (u) => !N.isOne(u.v)] },
  guard: (b, ctx) => (isReal(ctx) || pos(b.a, ctx) ? { conditions: [gt0(b.a)] } : false),
  tags: ["log"],
});
rule("log.b_contract_sum", "log(_c, _a) + log(_c, _b)", "log(_c, _a*_b)", {
  title: "Combine a sum of logarithms (base b)",
  why: "log_c a + log_c b = log_c(ab) where both are defined.",
  guard: lnContractGuard,
  tags: ["log"],
});
rule("log.b_contract_diff", "log(_c, _a) - log(_c, _b)", "log(_c, _a/_b)", {
  title: "Combine a difference of logarithms (base b)",
  why: "log_c a - log_c b = log_c(a/b) where both are defined.",
  guard: lnContractGuard,
  tags: ["log"],
});

// ---------- trigonometry ----------
rule("trig.pythag", "__c*sin(_x)^2 + __c*cos(_x)^2", "__c", {
  title: "Pythagorean identity", why: "sin^2 x + cos^2 x = 1.", tags: ["trig"],
});
rule("trig.pythag_cos", "__c - __c*sin(_x)^2", "__c*cos(_x)^2", {
  title: "Pythagorean identity", why: "1 - sin^2 x = cos^2 x.", tags: ["trig"],
});
rule("trig.pythag_sin", "__c - __c*cos(_x)^2", "__c*sin(_x)^2", {
  title: "Pythagorean identity", why: "1 - cos^2 x = sin^2 x.", tags: ["trig"],
});
rule("trig.pythag_tan", "__c + __c*tan(_x)^2", "__c*sec(_x)^2", {
  title: "Pythagorean identity (tangent)", why: "1 + tan^2 x = sec^2 x (both undefined where cos x = 0).", tags: ["trig"],
});
rule("trig.pythag_cot", "__c + __c*cot(_x)^2", "__c*csc(_x)^2", {
  title: "Pythagorean identity (cotangent)", why: "1 + cot^2 x = csc^2 x (both undefined where sin x = 0).", tags: ["trig"],
});
rule("trig.pythag_sec", "__c*sec(_x)^2 - __c", "__c*tan(_x)^2", {
  title: "Pythagorean identity (secant)", why: "sec^2 x - 1 = tan^2 x.", tags: ["trig"],
});
rule("trig.pythag_csc", "__c*csc(_x)^2 - __c", "__c*cot(_x)^2", {
  title: "Pythagorean identity (cosecant)", why: "csc^2 x - 1 = cot^2 x.", tags: ["trig"],
});
rule("trig.pythag_mixed", "__a*sin(_x)^2 + __b*cos(_x)^2", (b) => {
  const a = b.a.v, c = b.b.v;
  return N.lt(a, c) ? X.add(b.a, X.mul(X.num(N.sub(c, a)), X.pow(X.fn("cos", b.x), TWO))) : X.add(b.b, X.mul(X.num(N.sub(a, c)), X.pow(X.fn("sin", b.x), TWO)));
}, {
  title: "Pythagorean identity with different coefficients",
  why: "a sin^2 x + b cos^2 x = min(a,b) + |a - b| (sin^2 x or cos^2 x).",
  where: { a: "numeric", b: "numeric" },
  guard: (b) => !N.eq(b.a.v, b.b.v),
  tags: ["trig"],
});
rule("trig.double_sin_contract", "__c*sin(_x)*cos(_x)", "__c/2*sin(2*_x)", {
  title: "Double-angle formula", why: "2 sin x cos x = sin 2x.", tags: ["trig"],
});
rule("trig.double_cos_contract", "__c*cos(_x)^2 - __c*sin(_x)^2", "__c*cos(2*_x)", {
  title: "Double-angle formula", why: "cos^2 x - sin^2 x = cos 2x.", tags: ["trig"],
});
rule("trig.double_cos_contract2", "2*__c*cos(_x)^2 - __c", "__c*cos(2*_x)", {
  title: "Double-angle formula", why: "2cos^2 x - 1 = cos 2x.", tags: ["trig"],
});
rule("trig.double_cos_contract3", "__c - 2*__c*sin(_x)^2", "__c*cos(2*_x)", {
  title: "Double-angle formula", why: "1 - 2sin^2 x = cos 2x.", tags: ["trig"],
});
rule("trig.tan_contract", "sin(_x)^__n*cos(_x)^(-__n)", "tan(_x)^__n", {
  title: "Quotient identity", why: "sin x / cos x = tan x.", tags: ["trig"],
});
rule("trig.cot_contract", "cos(_x)^__n*sin(_x)^(-__n)", "cot(_x)^__n", {
  title: "Quotient identity", why: "cos x / sin x = cot x.", tags: ["trig"],
});
rule("trig.tan_to_sincos", "tan(_x)", "sin(_x)/cos(_x)", { title: "Tangent as sine over cosine", why: "tan x = sin x / cos x.", tags: ["trig"] });
rule("trig.cot_to_sincos", "cot(_x)", "cos(_x)/sin(_x)", { title: "Cotangent as cosine over sine", why: "cot x = cos x / sin x.", tags: ["trig"] });
rule("trig.sec_to_cos", "sec(_x)", "1/cos(_x)", { title: "Reciprocal identity", why: "sec x = 1 / cos x.", tags: ["trig"] });
rule("trig.csc_to_sin", "csc(_x)", "1/sin(_x)", { title: "Reciprocal identity", why: "csc x = 1 / sin x.", tags: ["trig"] });
rule("trig.recip_cos", "cos(_x)^_n", "sec(_x)^(-_n)", { title: "Reciprocal identity", why: "1 / cos x = sec x.", where: { n: "negint" }, tags: ["trig"] });
rule("trig.recip_sin", "sin(_x)^_n", "csc(_x)^(-_n)", { title: "Reciprocal identity", why: "1 / sin x = csc x.", where: { n: "negint" }, tags: ["trig"] });
rule("trig.recip_tan", "tan(_x)^_n", "cot(_x)^(-_n)", {
  title: "Reciprocal identity", why: "1 / tan x = cot x where tan x is defined.", where: { n: "negint" },
  domainConditions: (b) => [ne0(X.fn("cos", b.x))], tags: ["trig"],
});
rule("trig.sin_sum", "sin(_a + _b)", "sin(_a)*cos(_b) + cos(_a)*sin(_b)", { title: "Angle addition", why: "sin(a + b) = sin a cos b + cos a sin b.", tags: ["trig"] });
rule("trig.cos_sum", "cos(_a + _b)", "cos(_a)*cos(_b) - sin(_a)*sin(_b)", { title: "Angle addition", why: "cos(a + b) = cos a cos b - sin a sin b.", tags: ["trig"] });
rule("trig.tan_sum", "tan(_a + _b)", "(tan(_a) + tan(_b))/(1 - tan(_a)*tan(_b))", {
  title: "Angle addition (tangent)", why: "tan(a + b) = (tan a + tan b)/(1 - tan a tan b) where tan a and tan b are defined.",
  guard: (b) => ({ conditions: [ne0(X.fn("cos", b.a)), ne0(X.fn("cos", b.b))], assumption: true }),
  tags: ["trig"],
});
rule("trig.sin_double", "sin(2*_x)", "2*sin(_x)*cos(_x)", { title: "Double-angle formula", why: "sin 2x = 2 sin x cos x.", tags: ["trig"] });
rule("trig.cos_double", "cos(2*_x)", "cos(_x)^2 - sin(_x)^2", { title: "Double-angle formula", why: "cos 2x = cos^2 x - sin^2 x.", tags: ["trig"] });
rule("trig.cos_double_cos", "cos(2*_x)", "2*cos(_x)^2 - 1", { title: "Double-angle formula", why: "cos 2x = 2cos^2 x - 1.", tags: ["trig"] });
rule("trig.cos_double_sin", "cos(2*_x)", "1 - 2*sin(_x)^2", { title: "Double-angle formula", why: "cos 2x = 1 - 2sin^2 x.", tags: ["trig"] });
rule("trig.tan_double", "tan(2*_x)", "2*tan(_x)/(1 - tan(_x)^2)", {
  title: "Double-angle formula (tangent)", why: "tan 2x = 2tan x/(1 - tan^2 x) where tan x is defined.",
  guard: (b) => ({ conditions: [ne0(X.fn("cos", b.x))], assumption: true }), tags: ["trig"],
});
rule("trig.sin_multiple", "sin(_n*_x)", (b) => {
  const m = X.mul(X.num(N.sub(b.n.v, N.ONE)), b.x);
  return X.add(X.mul(X.fn("sin", m), X.fn("cos", b.x)), X.mul(X.fn("cos", m), X.fn("sin", b.x)));
}, { title: "Multiple-angle expansion", why: "sin(nx) = sin((n-1)x + x) by angle addition.", where: { n: "int2", x: "nonnum" }, tags: ["trig"] });
rule("trig.cos_multiple", "cos(_n*_x)", (b) => {
  const m = X.mul(X.num(N.sub(b.n.v, N.ONE)), b.x);
  return X.sub(X.mul(X.fn("cos", m), X.fn("cos", b.x)), X.mul(X.fn("sin", m), X.fn("sin", b.x)));
}, { title: "Multiple-angle expansion", why: "cos(nx) = cos((n-1)x + x) by angle addition.", where: { n: "int2", x: "nonnum" }, tags: ["trig"] });
rule("trig.power_reduce_sin", "sin(_x)^2", "(1 - cos(2*_x))/2", { title: "Power reduction (half-angle)", why: "sin^2 x = (1 - cos 2x)/2.", tags: ["trig"] });
rule("trig.power_reduce_cos", "cos(_x)^2", "(1 + cos(2*_x))/2", { title: "Power reduction (half-angle)", why: "cos^2 x = (1 + cos 2x)/2.", tags: ["trig"] });
rule("trig.half_tan", "tan(1/2*_x)", "sin(_x)/(1 + cos(_x))", {
  title: "Half-angle formula (tangent)", why: "tan(x/2) = sin x/(1 + cos x); both sides are undefined exactly where cos x = -1.", tags: ["trig"],
});
rule("trig.half_abs_sin", "|sin(1/2*_x)|", "sqrt((1 - cos(_x))/2)", { title: "Half-angle formula", why: "|sin(x/2)| = sqrt((1 - cos x)/2).", tags: ["trig"] });
rule("trig.half_abs_cos", "|cos(1/2*_x)|", "sqrt((1 + cos(_x))/2)", { title: "Half-angle formula", why: "|cos(x/2)| = sqrt((1 + cos x)/2).", tags: ["trig"] });
rule("trig.sum_to_product_sin", "sin(_a) + sin(_b)", "2*sin((_a + _b)/2)*cos((_a - _b)/2)", { title: "Sum to product", why: "sin a + sin b = 2 sin((a+b)/2) cos((a-b)/2).", tags: ["trig"] });
rule("trig.diff_to_product_sin", "sin(_a) - sin(_b)", "2*cos((_a + _b)/2)*sin((_a - _b)/2)", { title: "Sum to product", why: "sin a - sin b = 2 cos((a+b)/2) sin((a-b)/2).", tags: ["trig"] });
rule("trig.sum_to_product_cos", "cos(_a) + cos(_b)", "2*cos((_a + _b)/2)*cos((_a - _b)/2)", { title: "Sum to product", why: "cos a + cos b = 2 cos((a+b)/2) cos((a-b)/2).", tags: ["trig"] });
rule("trig.diff_to_product_cos", "cos(_a) - cos(_b)", "-2*sin((_a + _b)/2)*sin((_a - _b)/2)", { title: "Sum to product", why: "cos a - cos b = -2 sin((a+b)/2) sin((a-b)/2).", tags: ["trig"] });
rule("trig.product_to_sum_ss", "sin(_a)*sin(_b)", "(cos(_a - _b) - cos(_a + _b))/2", { title: "Product to sum", why: "sin a sin b = (cos(a-b) - cos(a+b))/2.", tags: ["trig"] });
rule("trig.product_to_sum_cc", "cos(_a)*cos(_b)", "(cos(_a - _b) + cos(_a + _b))/2", { title: "Product to sum", why: "cos a cos b = (cos(a-b) + cos(a+b))/2.", tags: ["trig"] });
rule("trig.product_to_sum_sc", "sin(_a)*cos(_b)", "(sin(_a + _b) + sin(_a - _b))/2", { title: "Product to sum", why: "sin a cos b = (sin(a+b) + sin(a-b))/2.", tags: ["trig"] });
// inverse functions: only where valid
rule("trig.asin_sin", "asin(sin(_x))", "_x", {
  title: "Inverse sine of sine", why: "asin(sin x) = x only for -pi/2 <= x <= pi/2.",
  guard: (b) => ({ conditions: [R(">=", b.x, X.mul(num(-1, 2), PI)), R("<=", b.x, X.mul(HALF, PI))], assumption: true }), tags: ["trig", "inverse"],
});
rule("trig.acos_cos", "acos(cos(_x))", "_x", {
  title: "Inverse cosine of cosine", why: "acos(cos x) = x only for 0 <= x <= pi.",
  guard: (b) => ({ conditions: [R(">=", b.x, ZERO), R("<=", b.x, PI)], assumption: true }), tags: ["trig", "inverse"],
});
rule("trig.atan_tan", "atan(tan(_x))", "_x", {
  title: "Inverse tangent of tangent", why: "atan(tan x) = x only for -pi/2 < x < pi/2.",
  guard: (b) => ({ conditions: [R(">", b.x, X.mul(num(-1, 2), PI)), R("<", b.x, X.mul(HALF, PI))], assumption: true }), tags: ["trig", "inverse"],
});
const inUnit = (b) => [R(">=", b.x, NEG_ONE), R("<=", b.x, ONE)];
rule("trig.sin_asin", "sin(asin(_x))", "_x", { title: "Sine of inverse sine", why: "sin(asin x) = x for -1 <= x <= 1.", domainConditions: inUnit, tags: ["trig", "inverse"] });
rule("trig.cos_acos", "cos(acos(_x))", "_x", { title: "Cosine of inverse cosine", why: "cos(acos x) = x for -1 <= x <= 1.", domainConditions: inUnit, tags: ["trig", "inverse"] });
rule("trig.cos_asin", "cos(asin(_x))", "sqrt(1 - _x^2)", { title: "Cosine of inverse sine", why: "cos(asin x) = sqrt(1 - x^2) (cos is >= 0 on [-pi/2, pi/2]).", domainConditions: inUnit, tags: ["trig", "inverse"] });
rule("trig.sin_acos", "sin(acos(_x))", "sqrt(1 - _x^2)", { title: "Sine of inverse cosine", why: "sin(acos x) = sqrt(1 - x^2) (sin is >= 0 on [0, pi]).", domainConditions: inUnit, tags: ["trig", "inverse"] });
rule("trig.cos_atan", "cos(atan(_x))", "1/sqrt(1 + _x^2)", { title: "Cosine of inverse tangent", why: "cos(atan x) = 1/sqrt(1 + x^2).", tags: ["trig", "inverse"] });
rule("trig.sin_atan", "sin(atan(_x))", "_x/sqrt(1 + _x^2)", { title: "Sine of inverse tangent", why: "sin(atan x) = x/sqrt(1 + x^2).", tags: ["trig", "inverse"] });
rule("trig.tan_asin", "tan(asin(_x))", "_x/sqrt(1 - _x^2)", { title: "Tangent of inverse sine", why: "tan(asin x) = x/sqrt(1 - x^2) for -1 < x < 1.", domainConditions: (b) => [R(">", b.x, NEG_ONE), R("<", b.x, ONE)], tags: ["trig", "inverse"] });
function num(n, d) { return X.num(n, d); }

// ---------- fractions / rational ----------
rule("rational.together", (node, ctx) => {
  if (node.k !== "add" || !node.args.some((t) => splitFraction(t, ctx)[1] !== ONE)) return null;
  const r = together(node, plain(ctx));
  return r && r !== node ? { result: r } : null;
}, (b) => b.result, { title: "Combine over a common denominator", why: "a/b + c/d = (ad + bc)/(bd).", tags: ["fraction"] });
function matchCancel(node, ctx) {
  if (node.k !== "mul" && node.k !== "pow") return null;
  const [n0, d0] = splitFraction(node, ctx);
  if (d0 === ONE || d0.k === "num") return null;
  const n = C(expand(n0, plain(ctx)), ctx), d = C(expand(d0, plain(ctx)), ctx);
  if (!n || !d) return null;
  const fs = new Set([...X.freeSymbols(n), ...X.freeSymbols(d)]);
  const ext = getExternal("cancel");
  if (fs.size !== 1) {
    if (ext) { const r = ext(node, ctx); if (r && r.result && r.result !== node) return { result: r.result, g: r.factor || ONE }; }
    return null;
  }
  const x = X.sym([...fs][0]);
  const pn = toPoly(n, x), pd = toPoly(d, x);
  if (!pn || !pd || pd.length < 2) return null;
  const g = gcdP(pn, pd);
  if (g.length < 2) return null;
  const [qn, rn] = divmodP(pn, g), [qd, rd] = divmodP(pd, g);
  if (rn.length || rd.length) return null;
  const result = C(X.mul(fromPoly(qn, x, ctx), X.pow(fromPoly(qd, x, ctx), NEG_ONE)), ctx);
  // state the condition through the denominator's own factors when possible: (x-1)^2 -> x != 1
  const facs = [];
  let left = g;
  for (const f of d0.k === "mul" ? d0.args : [d0]) {
    const base = f.k === "pow" && f.args[1].k === "num" && f.args[1].v.d === 1n ? f.args[0] : f;
    const pf = toPoly(C(expand(base, plain(ctx)), ctx) || base, x);
    if (!pf || pf.length < 2) continue;
    let guard = 0;
    for (;;) {
      if (++guard > 50) break;
      const [qq, rr] = divmodP(left, pf);
      if (rr.length || !qq.length) break;
      if (!facs.includes(base)) facs.push(base);
      left = qq;
      if (left.length < 2) break;
    }
  }
  const gNode = left.length < 2 && facs.length ? C(X.mul(...facs), ctx) : fromPoly(g, x, ctx);
  return { result, g: gNode };
}
rule("rational.cancel", matchCancel, (b) => b.result, {
  title: "Cancel a common factor",
  why: "Numerator and denominator share a polynomial factor; cancelling it is valid where that factor is nonzero.",
  domainConditions: (b) => (b.g === ONE ? [] : [ne0(b.g)]),
  tags: ["fraction"],
});
rule("rational.apart", (node, ctx) => {
  const ext = getExternal("apart");
  if (!ext) return null;
  const r = ext(node, ctx);
  return r && r !== node ? { result: r } : null;
}, (b) => b.result, { title: "Partial fractions", why: "Split a rational function into partial fractions (polynomial engine).", tags: ["fraction"] });

// ---------- abs / piecewise ----------
rule("abs.to_piecewise", "|_x|", (b) => X.piecewise(b.x, R(">=", b.x, ZERO), X.neg(b.x), TRUE), {
  title: "Absolute value as a piecewise function", why: "|x| = x for x >= 0 and -x otherwise.", tags: ["abs", "piecewise"],
});
rule("abs.product", "|_a*_b|", "|_a|*|_b|", { title: "Absolute value of a product", why: "|ab| = |a||b|.", tags: ["abs"] });
rule("abs.square", "|_x|^_n", "_x^_n", {
  title: "Even power of an absolute value", why: "|x|^2 = x^2 for real x (any even power).", where: { n: "even" },
  guard: (b, ctx) => isReal(ctx), tags: ["abs"],
});
rule("abs.sqrt_square", "(_x^2)^(1/2)", "|_x|", {
  title: "Square root of a square", why: "sqrt(x^2) = |x| for real x, NOT x.", guard: (b, ctx) => isReal(ctx), tags: ["abs", "radical"],
});
rule("abs.decide", "|_x|", (b, ctx) => (signUnder(b.x, ctx) === 1 || signUnder(b.x, ctx) === "nn" || signUnder(b.x, ctx) === 0 ? b.x : X.neg(b.x)), {
  title: "Absolute value with known sign", why: "|x| = x when x >= 0 and -x when x <= 0.",
  guard: (b, ctx) => { const s = signUnder(b.x, ctx); return s === 1 || s === -1 || s === 0 || s === "nn" || s === "np"; },
  tags: ["abs"],
});
function matchPiecewise(node, ctx) {
  if (node.k !== "piecewise") return null;
  const a = node.args;
  const out = [];
  let changed = false;
  for (let i = 0; i + 1 < a.length; i += 2) {
    const d = a[i + 1] === TRUE ? true : a[i + 1] === FALSE ? false : decideRel(a[i + 1], ctx);
    if (d === false) { changed = true; continue; }
    if (d === true) {
      if (!out.length) return { result: a[i] };
      out.push(a[i], TRUE);
      if (i + 2 < a.length) changed = true;
      break;
    }
    out.push(a[i], a[i + 1]);
  }
  if (!out.length) return { result: UNDEF };
  const vals = out.filter((_, i) => i % 2 === 0);
  if (vals.every((v) => v === vals[0]) && out[out.length - 1] === TRUE) return { result: vals[0] };
  return changed ? { result: X.mk("piecewise", out) } : null;
}
rule("piecewise.decide", matchPiecewise, (b) => b.result, {
  title: "Resolve a piecewise branch", why: "A branch condition is decided by the assumptions (or is always true/false).", tags: ["piecewise"],
});

// ---------- expansion / factoring hooks ----------
rule("expand.distribute", (node, ctx) => {
  if (node.k !== "mul" || !node.args.some((f) => f.k === "add")) return null;
  const r = expand(node, plain(ctx));
  return r !== node ? { result: r } : null;
}, (b) => b.result, { title: "Distribute", why: "a(b + c) = ab + ac.", tags: ["expand"] });
rule("expand.power", (node, ctx) => {
  if (node.k !== "pow" || node.args[0].k !== "add" || node.args[1].k !== "num" || node.args[1].v.d !== 1n || node.args[1].v.n < 2n || node.args[1].v.n > 12n) return null;
  return { result: expand(node, plain(ctx)) };
}, (b) => b.result, { title: "Expand a power of a sum", why: "(a + b)^n by the binomial theorem.", tags: ["expand"] });
rule("expand.numeric_distribute", (node) => {
  if (node.k !== "mul" || node.args.length !== 2 || node.args[0].k !== "num" || node.args[1].k !== "add") return null;
  return { result: X.add(...node.args[1].args.map((t) => X.mul(node.args[0], t))) };
}, (b) => b.result, { title: "Distribute a numeric factor", why: "c(a + b) = ca + cb.", tags: ["expand"] });
rule("factor.external", (node, ctx) => {
  const f = getExternal("factor");
  if (!f || (node.k !== "add")) return null;
  const r = f(node, ctx);
  return r && r !== node ? { result: r } : null;
}, (b) => b.result, { title: "Factor", why: "Factor with the polynomial engine.", tags: ["factor"] });

// ---------- rule sets ----------
defineRuleSet("exponents", "improve", ["exp.log_inverse", "exp.combine_bases", "exp.power_of_power", "exp.product_base_root"], "power rules that make expressions simpler");
defineRuleSet("exponents.expand", "directional", ["exp.power_of_power", "exp.product_base", "exp.product_base_root", "exp.sum_exponent"], "distribute exponents");
defineRuleSet("exponents.radical", "directional", ["exp.to_radical"], "fractional exponents to radicals (display form)");
defineRuleSet("radicals", "improve", ["rad.denest", "rad.rationalize", "abs.sqrt_square", "exp.combine_bases"], "denest, rationalize numeric denominators, combine radicals");
defineRuleSet("radicals.rationalize", "directional", ["rad.rationalize"], "rationalize denominators (symbolic ones with conditions)");
defineRuleSet("logs", "improve", ["log.to_base", "log.contract_sum", "log.contract_diff", "log.b_contract_sum", "log.b_contract_diff", "log.inverse_exp", "log.inverse_pow"], "logarithm simplification");
defineRuleSet("logs.expand", "directional", ["log.quotient", "log.product", "log.power", "log.b_product", "log.b_power", "log.int_power"], "expand logarithms (with |.| and conditions where needed)");
defineRuleSet("logs.contract", "directional", ["log.contract_coeff", "log.contract_sum", "log.contract_diff", "log.b_contract_sum", "log.b_contract_diff"], "contract logarithms");
defineRuleSet("logs.change_base", "directional", ["log.change_base"], "rewrite log_b x as ln x / ln b");
defineRuleSet("trig", "improve", [
  "trig.pythag", "trig.pythag_cos", "trig.pythag_sin", "trig.pythag_tan", "trig.pythag_cot", "trig.pythag_sec", "trig.pythag_csc",
  "trig.pythag_mixed", "trig.double_sin_contract", "trig.double_cos_contract", "trig.double_cos_contract2", "trig.double_cos_contract3",
  "trig.tan_contract", "trig.cot_contract",
], "trigonometric identities that shorten expressions");
defineRuleSet("trig.inverse", "improve", ["trig.sin_asin", "trig.cos_acos", "trig.cos_asin", "trig.sin_acos", "trig.cos_atan", "trig.sin_atan", "trig.tan_asin", "trig.asin_sin", "trig.acos_cos", "trig.atan_tan"], "inverse-function identities (with their conditions)");
defineRuleSet("trig.tosincos", "directional", ["trig.tan_to_sincos", "trig.cot_to_sincos", "trig.sec_to_cos", "trig.csc_to_sin"], "rewrite in sin and cos");
defineRuleSet("trig.reciprocal", "improve", ["trig.recip_cos", "trig.recip_sin", "trig.recip_tan"], "1/cos -> sec etc.");
defineRuleSet("trig.expand", "directional", ["trig.sin_sum", "trig.cos_sum", "trig.tan_sum", "trig.sin_double", "trig.cos_double", "trig.tan_double", "trig.sin_multiple", "trig.cos_multiple"], "angle addition and multiple angles");
defineRuleSet("trig.double.cos", "directional", ["trig.cos_double_cos"], "cos 2x = 2cos^2 x - 1");
defineRuleSet("trig.double.sin", "directional", ["trig.cos_double_sin"], "cos 2x = 1 - 2 sin^2 x");
defineRuleSet("trig.power_reduce", "directional", ["trig.power_reduce_sin", "trig.power_reduce_cos"], "power reduction / half-angle");
defineRuleSet("trig.half_angle", "directional", ["trig.half_tan", "trig.half_abs_sin", "trig.half_abs_cos"], "half-angle formulas");
defineRuleSet("trig.sum_to_product", "directional", ["trig.sum_to_product_sin", "trig.diff_to_product_sin", "trig.sum_to_product_cos", "trig.diff_to_product_cos"], "sums of sines/cosines to products");
defineRuleSet("trig.product_to_sum", "directional", ["trig.product_to_sum_ss", "trig.product_to_sum_cc", "trig.product_to_sum_sc"], "products of sines/cosines to sums");
defineRuleSet("rational", "improve", ["rational.cancel", "rational.together"], "cancel common factors, combine fractions");
defineRuleSet("rational.apart", "directional", ["rational.apart"], "partial fractions (needs registerExternal('apart', fn))");
defineRuleSet("abs", "improve", ["abs.decide", "abs.sqrt_square", "abs.square", "abs.product", "piecewise.decide"], "absolute values and piecewise functions");
defineRuleSet("abs.piecewise", "directional", ["abs.to_piecewise"], "absolute value as a piecewise function");
defineRuleSet("expand", "directional", ["expand.power", "expand.distribute"], "distribute products and powers of sums");
defineRuleSet("expand.numeric", "improve", ["expand.numeric_distribute"], "distribute a numeric factor when shorter");
defineRuleSet("factor", "improve", ["factor.external"], "factor with the polynomial engine (registerExternal('factor', fn))");

const SIMPLIFY_SETS = ["abs", "rational", "radicals", "exponents", "logs", "trig", "trig.inverse", "expand.numeric", "factor"];

// ---------------- scheduler ----------------
function resolveRules(ruleSets, strategy) {
  const out = [];
  const add = (r, directional) => { if (!out.some((e) => e.rule === r)) out.push({ rule: r, directional }); };
  for (const s of [].concat(ruleSets)) {
    if (typeof s === "string") {
      const set = SETS.get(s);
      if (set) { for (const r of set.rules) add(r, set.mode === "directional"); continue; }
      const r = RULES.get(s);
      if (!r) throw new Error("Quelvra: unknown rule set " + s);
      add(r, strategy === "directional");
    } else if (s && s.rules) for (const r of s.rules) add(r, s.mode === "directional");
    else if (s && s.id) add(s, strategy === "directional");
  }
  return out;
}
// Repeatedly apply rules, re-canonicalising after each rewrite.
// strategy: "auto" (default: directional sets accept any change, other sets only improving ones),
//           "improve" (only strictly cheaper results), "directional" (any change), "best" (cheapest candidate per step)
export function simplifyWith(tree, ruleSets, opts = {}) {
  const ctx = ensureCtx(opts.ctx);
  const maxSteps = opts.maxSteps ?? 40, maxMs = opts.maxMs ?? 1500, strategy = opts.strategy || "auto";
  const rules = resolveRules(ruleSets, strategy);
  const t0 = now();
  const steps = [];
  let [cur, notes0] = canonNotes(tree, ctx);
  if (!cur) return { result: tree, steps, conditions: [], cost: complexity(tree), stopped: "error" };
  if (cur !== tree) for (const n of lostDomain(tree, cur, ctx)) if (!notes0.includes(n)) notes0.push(n);
  if (cur !== tree && notes0.length) {
    steps.push({ rule: "simplify.canonical", title: "Simplify", why: "Automatic simplification (cancellations need the stated conditions).", before: tree, after: cur, at: tree, conditions: notes0, kind: "conditional", conditionKind: "domain", tags: [] });
  }
  const size0 = X.size(cur);
  const cap = opts.sizeCap ?? 4 * size0 + 40;
  const seen = new Set([cur.id]);
  const failed = new Set();
  let curCost = complexity(cur);
  let stopped = null;
  const o = { allowConditional: !!opts.allowConditional, maxBindings: opts.maxBindings, matchLimit: opts.matchLimit };
  let it = 0;
  try {
    for (; it < maxSteps; it++) {
      let best = null;
      search: for (const { rule, directional } of rules) {
        for (const [node, path] of positions(cur)) {
          if (now() - t0 > maxMs) { stopped = "time"; break search; }
          const key = rule.id + "|" + node.id;
          if (failed.has(key)) continue;
          let r;
          try { r = tryRule(rule, node, ctx, o); } catch (e) { if (e.code === "BUDGET") { failed.add(key); continue; } throw e; }
          if (!r) { failed.add(key); continue; }
          const replaced = replaceAt(cur, path, r.rhs);
          const cand = rule.raw ? replaced : canon(replaced, ctx);
          if (!cand || cand === cur || cand === UNDEF || seen.has(cand.id)) continue;
          if (X.size(cand) > cap) continue;
          const c = complexity(cand);
          const dirOK = strategy === "directional" || (strategy === "auto" && directional);
          if (!dirOK && !(c < curCost)) continue;
          const entry = { rule, r, node, path, cand, c, replaced };
          if (strategy === "best") { if (!best || c < best.c) best = entry; continue; }
          best = entry;
          break search;
        }
      }
      if (!best) break;
      const [after, notes] = best.rule.raw ? [best.cand, []] : canonNotes(best.replaced, ctx);
      steps.push(makeStep(best.rule, best.r, cur, after || best.cand, best.node, notes, ctx));
      cur = after || best.cand;
      seen.add(cur.id);
      curCost = complexity(cur);
      if (stopped) break;
    }
    if (it >= maxSteps) stopped = "steps";
  } catch (e) {
    if (e.code !== "BUDGET") throw e;
    stopped = "budget";
  }
  return { result: cur, steps, conditions: collectConditions(steps), cost: curCost, stopped };
}
function collectConditions(steps) {
  const out = [];
  for (const s of steps) for (const c of s.conditions || []) if (!out.includes(c)) out.push(c);
  return out;
}

// ---------------- high-level commands ----------------
function pick(cands) {
  let best = cands[0];
  for (const c of cands.slice(1)) if (c && c.cost < best.cost) best = c;
  return best;
}
function chain(first, second) {
  if (!second) return first;
  const steps = [...first.steps, ...second.steps];
  return { result: second.result, steps, conditions: collectConditions(steps), cost: complexity(second.result), stopped: second.stopped || first.stopped };
}
// The "Simplify" command: canonicalise, try the rule sets, keep the cheapest equivalent form.
// Rewrites that need extra assumptions are skipped unless allowConditional; every condition used
// (including those the result no longer shows, like x != 1 after cancelling) is attached.
export function simplifyFull(tree, opts = {}) {
  const ctx = ensureCtx(opts.ctx);
  const o = { ...opts, ctx };
  const [c0, notes] = canonNotes(tree, ctx);
  if (!c0) return { result: tree, steps: [], conditions: [], cost: complexity(tree), initialCost: complexity(tree) };
  const base = { result: c0, steps: [], conditions: [], cost: complexity(c0) };
  if (c0 !== tree) for (const n of lostDomain(tree, c0, ctx)) if (!notes.includes(n)) notes.push(n);
  if (c0 !== tree) {
    base.steps.push({ rule: "simplify.canonical", title: "Simplify", why: "Automatic simplification: numbers folded, like terms collected.", before: tree, after: c0, at: tree, conditions: notes, kind: notes.length ? "conditional" : "equivalent", conditionKind: notes.length ? "domain" : null, tags: [] });
    base.conditions = notes.slice();
  }
  const cands = [base];
  const A = chain(base, simplifyWith(c0, SIMPLIFY_SETS, { ...o, strategy: "improve" }));
  cands.push(A);
  if (hasTrig(c0)) {
    const B = trigsimp(A.result, o);
    cands.push(chain(A, B));
  }
  if (c0.k === "add" || c0.k === "mul" || c0.k === "pow") {
    const ex = canon(expand(c0, plain(ctx)), ctx);
    if (ex && ex !== c0 && X.size(ex) < 4 * X.size(c0) + 40) {
      const eStep = { rule: "expand", title: "Expand", why: "Distribute products and powers.", before: c0, after: ex, at: c0, conditions: [], kind: "equivalent", conditionKind: null, tags: ["expand"] };
      const D = simplifyWith(ex, SIMPLIFY_SETS, { ...o, strategy: "improve" });
      cands.push(chain({ ...base, steps: [...base.steps, eStep] }, D));
    }
  }
  const best = pick(cands);
  return { result: best.result, steps: best.steps, conditions: collectConditions(best.steps), cost: best.cost, initialCost: complexity(c0) };
}
// trigsimp: try (1) the trig identities directly, (2) rewriting to sin/cos, combining, simplifying
// and contracting again, (3) expanding angles first; choose the cheapest.
export function trigsimp(tree, opts = {}) {
  const ctx = ensureCtx(opts.ctx);
  const o = { ...opts, ctx };
  const sets = ["trig", "trig.inverse", "rational", "abs", "trig.reciprocal"];
  const c1 = simplifyWith(tree, sets, { ...o, strategy: "improve" });
  const cands = [c1];
  const sc = simplifyWith(c1.result, ["trig.tosincos"], { ...o, strategy: "directional" });
  if (sc.result !== c1.result) {
    let path = chain(c1, sc);
    const tg = together(sc.result, plain(ctx));
    if (tg && tg !== sc.result) {
      path = chain(path, { result: tg, steps: [{ rule: "rational.together", title: "Combine over a common denominator", why: "a/b + c/d = (ad + bc)/(bd).", before: sc.result, after: tg, at: sc.result, conditions: [], kind: "equivalent", conditionKind: null, tags: ["fraction"] }], stopped: null });
    }
    const s2 = simplifyWith(path.result, sets, { ...o, strategy: "improve" });
    cands.push(chain(path, s2));
  }
  const ex = simplifyWith(c1.result, ["trig.expand"], { ...o, strategy: "directional", maxSteps: 8 });
  if (ex.result !== c1.result) cands.push(chain(chain(c1, ex), simplifyWith(ex.result, sets, { ...o, strategy: "improve" })));
  const best = pick(cands);
  return { ...best, conditions: collectConditions(best.steps) };
}
const directional = (sets, extra = {}) => (tree, opts = {}) => simplifyWith(tree, sets, { ...extra, ...opts, strategy: "directional" });
export const expandLog = directional(["logs.expand"]);
export const contractLog = directional(["logs.contract"]);
export const expandTrig = directional(["trig.expand", "expand"], { maxSteps: 30 });
export const rationalize = (tree, opts = {}) => simplifyWith(tree, ["radicals.rationalize"], { allowConditional: true, ...opts, strategy: "directional" });
export const radsimp = (tree, opts = {}) => simplifyWith(tree, ["radicals", "rational", "expand.numeric"], { ...opts, strategy: "improve" });
export function exponentsimp(tree, opts = {}) {
  const r = simplifyWith(tree, ["exponents"], { ...opts, strategy: "improve" });
  if (!opts.toRadicals) return r;
  return chain(r, simplifyWith(r.result, ["exponents.radical"], { ...opts, strategy: "directional" }));
}
export const expandExponents = directional(["exponents.expand"]);
export const expandAll = directional(["expand"]);

// ---------------- numeric evaluation (double precision, complex-capable) ----------------
// evalNumeric(tree, env, { mode: "real" | "complex" }) -> { re, im } or null when undefined.
// mode "real" is strict: any non-real intermediate value makes the expression undefined.
export function evalNumeric(u, env = {}, opts = {}) {
  const real = (opts.mode || "real") !== "complex";
  const E0 = env instanceof Map ? env : new Map(Object.entries(env));
  let ops = 0;
  const bad = () => { throw UNDEF_SIGNAL; };
  const chk = (z) => {
    if (!Number.isFinite(z[0]) || !Number.isFinite(z[1])) bad();
    if (real) { if (Math.abs(z[1]) > 1e-9 * Math.max(1, Math.abs(z[0]))) bad(); return [z[0], 0]; }
    return z;
  };
  const cmul = (a, b) => [a[0] * b[0] - a[1] * b[1], a[0] * b[1] + a[1] * b[0]];
  const cdiv = (a, b) => { const d = b[0] * b[0] + b[1] * b[1]; if (d === 0) bad(); return [(a[0] * b[0] + a[1] * b[1]) / d, (a[1] * b[0] - a[0] * b[1]) / d]; };
  const clog = (a) => { if (a[0] === 0 && a[1] === 0) bad(); return [Math.log(Math.hypot(a[0], a[1])), Math.atan2(a[1], a[0])]; };
  const cexp = (a) => { const m = Math.exp(a[0]); return [m * Math.cos(a[1]), m * Math.sin(a[1])]; };
  const realOnly = (a) => { if (Math.abs(a[1]) > 1e-12) bad(); return a[0]; };
  const cpowInt = (b, n) => {
    if (n === 0) { if (b[0] === 0 && b[1] === 0) bad(); return [1, 0]; }
    if (b[1] === 0) { if (b[0] === 0 && n < 0) bad(); return [Math.pow(b[0], n), 0]; }
    let r = [1, 0];
    for (let i = 0; i < Math.abs(n); i++) r = cmul(r, b);
    return n < 0 ? cdiv([1, 0], r) : r;
  };
  const gamma = (x) => {
    if (x <= 0 && Number.isInteger(x)) bad();
    if (x < 0.5) return Math.PI / (Math.sin(Math.PI * x) * gamma(1 - x));
    const g = 7, c = [0.99999999999980993, 676.5203681218851, -1259.1392167224028, 771.32342877765313, -176.61502916214059, 12.507343278686905, -0.13857109526572012, 9.9843695780195716e-6, 1.5056327351493116e-7];
    x -= 1;
    let a = c[0];
    const t = x + g + 0.5;
    for (let i = 1; i < g + 2; i++) a += c[i] / (x + i);
    return Math.sqrt(2 * Math.PI) * Math.pow(t, x + 0.5) * Math.exp(-t) * a;
  };
  const cond = (c) => {
    if (c.k === "bool") return c.v;
    if (c.k === "and") return c.args.every(cond);
    if (c.k === "or") return c.args.some(cond);
    if (c.k === "not") return !cond(c.args[0]);
    if (c.k === "rel" || c.k === "eq") {
      const a = realOnly(ev(c.args[0])), b = realOnly(ev(c.args[1]));
      const op = c.k === "eq" ? "=" : c.op;
      return { "<": a < b, "<=": a <= b, ">": a > b, ">=": a >= b, "!=": a !== b, "=": a === b }[op];
    }
    if (c.k === "fn" && c.name === "isInteger") return Number.isInteger(realOnly(ev(c.args[0])));
    bad();
  };
  const ev = (w) => {
    if (++ops > 200000) throw budgetErr("numeric evaluation");
    switch (w.k) {
      case "num": return [N.toFloat(w.v), 0];
      case "const":
        if (w.name === "pi") return [Math.PI, 0];
        if (w.name === "e") return [Math.E, 0];
        if (w.name === "I") return chk([0, 1]);
        return bad();
      case "sym": {
        if (!E0.has(w.name)) throw new Error("evalNumeric: no value for " + w.name);
        const v = E0.get(w.name);
        if (typeof v === "number") return [v, 0];
        if (Array.isArray(v)) return v;
        if (v && typeof v === "object" && "re" in v) return [v.re, v.im || 0];
        return ev(v);
      }
      case "add": return chk(w.args.map(ev).reduce((s, z) => [s[0] + z[0], s[1] + z[1]], [0, 0]));
      case "mul": return chk(w.args.map(ev).reduce((s, z) => cmul(s, z), [1, 0]));
      case "pow": {
        const [bn, en] = w.args;
        const b = ev(bn);
        if (en.k === "num") {
          const q = en.v;
          if (q.d === 1n) return chk(cpowInt(b, Number(q.n)));
          const p = Number(q.n), d = Number(q.d);
          if (b[1] === 0 && b[0] >= 0) { if (b[0] === 0 && p < 0) bad(); return chk([Math.pow(b[0], p / d), 0]); }
          if (b[1] === 0 && real) {
            if (d % 2 === 1) { const m = Math.pow(-b[0], p / d); return chk([p % 2 === 0 ? m : -m, 0]); }
            return bad();
          }
          if (b[1] === 0 && d % 2 === 1 && !real && opts.oddRootReal !== false) {
            // complex mode keeps the principal branch
          }
          return chk(cexp(cmul([p / d, 0], clog(b))));
        }
        const e = ev(en);
        if (b[1] === 0 && e[1] === 0) {
          if (b[0] > 0) return chk([Math.pow(b[0], e[0]), 0]);
          if (b[0] === 0) { if (e[0] > 0) return [0, 0]; bad(); }
          if (Number.isInteger(e[0])) return chk([Math.pow(b[0], e[0]), 0]);
          if (real) bad();
        }
        if (b[0] === 0 && b[1] === 0) { if (e[0] > 0) return [0, 0]; bad(); }
        return chk(cexp(cmul(e, clog(b))));
      }
      case "fn": {
        const a = w.args.map(ev);
        const x = a[0];
        const R1 = () => realOnly(x);
        switch (w.name) {
          case "sin": return chk([Math.sin(x[0]) * Math.cosh(x[1]), Math.cos(x[0]) * Math.sinh(x[1])]);
          case "cos": return chk([Math.cos(x[0]) * Math.cosh(x[1]), -Math.sin(x[0]) * Math.sinh(x[1])]);
          case "tan": { const c = Math.cos(R1()); if (c === 0) bad(); return chk([Math.tan(x[0]), 0]); }
          case "cot": { const s = Math.sin(R1()); if (s === 0) bad(); return chk([Math.cos(x[0]) / s, 0]); }
          case "sec": { const c = Math.cos(R1()); if (c === 0) bad(); return chk([1 / c, 0]); }
          case "csc": { const s = Math.sin(R1()); if (s === 0) bad(); return chk([1 / s, 0]); }
          case "asin": { const v = R1(); if (v < -1 || v > 1) bad(); return [Math.asin(v), 0]; }
          case "acos": { const v = R1(); if (v < -1 || v > 1) bad(); return [Math.acos(v), 0]; }
          case "atan": return chk([Math.atan(R1()), 0]);
          case "acot": return chk([Math.PI / 2 - Math.atan(R1()), 0]);
          case "asec": { const v = R1(); if (Math.abs(v) < 1) bad(); return [Math.acos(1 / v), 0]; }
          case "acsc": { const v = R1(); if (Math.abs(v) < 1) bad(); return [Math.asin(1 / v), 0]; }
          case "sinh": return chk([Math.sinh(R1()), 0]);
          case "cosh": return chk([Math.cosh(R1()), 0]);
          case "tanh": return chk([Math.tanh(R1()), 0]);
          case "asinh": return chk([Math.asinh(R1()), 0]);
          case "acosh": { const v = R1(); if (v < 1) bad(); return [Math.acosh(v), 0]; }
          case "atanh": { const v = R1(); if (v <= -1 || v >= 1) bad(); return [Math.atanh(v), 0]; }
          case "ln": if (real && (x[1] !== 0 || x[0] <= 0)) bad(); return chk(clog(x));
          case "log": {
            const [bb, yy] = a.length === 1 ? [[10, 0], a[0]] : a;
            if (real && (bb[0] <= 0 || yy[0] <= 0)) bad();
            const lb = clog(bb);
            if (lb[0] === 0 && lb[1] === 0) bad();
            return chk(cdiv(clog(yy), lb));
          }
          case "exp": return chk(cexp(x));
          case "sqrt": return ev(X.pow(w.args[0], HALF));
          case "cbrt": return ev(X.pow(w.args[0], X.num(1, 3)));
          case "abs": return [Math.hypot(x[0], x[1]), 0];
          case "sign": return [Math.sign(R1()), 0];
          case "floor": return [Math.floor(R1()), 0];
          case "ceil": return [Math.ceil(R1()), 0];
          case "round": return [Math.round(R1()), 0];
          case "factorial": return chk([gamma(R1() + 1), 0]);
          case "gamma": return chk([gamma(R1()), 0]);
          case "re": return [x[0], 0];
          case "im": return [x[1], 0];
          default: return bad();
        }
      }
      case "piecewise": {
        for (let i = 0; i + 1 < w.args.length; i += 2) if (cond(w.args[i + 1])) return ev(w.args[i]);
        return bad();
      }
      default: return bad();
    }
  };
  try {
    const z = ev(u);
    return { re: z[0], im: real ? 0 : z[1] };
  } catch (e) {
    if (e === UNDEF_SIGNAL) return null;
    throw e;
  }
}
const UNDEF_SIGNAL = { undefinedValue: true };

// ---------------- equivalence checking ----------------
function isDefinedExact(tree, pt, dom, ctx) {
  const chk = checkPoint(dom, pt, { ctx });
  if (chk.ok === false) return { defined: false };
  const v = canon(X.subs(tree, pt), ctx);
  if (!v || v === UNDEF || X.contains(v, UNDEF) || X.contains(v, X.OO)) return { defined: false };
  if (isReal(ctx) && X.contains(v, I)) return { defined: false };
  return { defined: chk.ok !== null ? true : null, value: v };
}
const ptText = (pt) => Object.fromEntries([...pt].map(([k, v]) => [k, toText(v)]));
// isEquivalent(a, b, { vars, ctx, samples, seed }) ->
//   { verdict: "equivalent" | "not-equivalent" | "equivalent-under-conditions" | "unknown",
//     method: "symbolic" | "exact-sampling" | "numeric", probable, conditions, domainDiffs: [{ point, aDefined, bDefined }],
//     counterexample: { point, a, b } | null }
export function isEquivalent(a, b, opts = {}) {
  const ctx = ensureCtx(opts.ctx || (opts.domain ? makeCtx({ domain: opts.domain, budget: { ops: 3_000_000 } }) : null));
  const vars = opts.vars || [...new Set([...X.freeSymbols(a), ...X.freeSymbols(b)])].sort();
  const out = { verdict: "unknown", method: null, probable: false, conditions: [], domainDiffs: [], counterexample: null, samples: 0 };
  // (1) symbolic difference
  const [d0, notes] = canonNotes(X.sub(a, b), ctx);
  let symZero = d0 === ZERO;
  if (!symZero && d0) {
    const e = canon(expand(d0, plain(ctx)), ctx);
    if (e === ZERO) symZero = true;
    else if (e) {
      const tg = together(e, plain(ctx));
      const [nn] = splitFraction(tg, ctx);
      if (canon(expand(nn, plain(ctx)), ctx) === ZERO) symZero = true;
    }
  }
  if (!symZero && d0 && hasTrig(d0)) {
    try { if (trigsimp(d0, { ctx, maxMs: 300 }).result === ZERO) symZero = true; } catch (e) { if (e.code !== "BUDGET") throw e; }
  }
  const domA = inferDomain(a, { ctx }), domB = inferDomain(b, { ctx });
  // (2) exact rational sampling
  const rnd = mulberry(opts.seed ?? 20240917);
  const special = [0, 1, -1, 2, -2, 1 / 2, -1 / 2, 3];
  const nPts = opts.samples ?? 16;
  let agree = 0, floatNeeded = [];
  for (let i = 0; i < nPts; i++) {
    const pt = new Map();
    vars.forEach((v, j) => {
      let q;
      if (i < special.length) {
        const s = special[(i + j * 3) % special.length];
        q = N.fromDecimal(String(s));
      } else q = N.Q(BigInt(Math.floor(rnd() * 19) - 9), BigInt(1 + Math.floor(rnd() * 4)));
      pt.set(v, X.num(q));
    });
    out.samples++;
    const A = isDefinedExact(a, pt, domA, ctx), B = isDefinedExact(b, pt, domB, ctx);
    if (A.defined === false || B.defined === false) {
      if (A.defined !== B.defined && A.defined !== null && B.defined !== null) out.domainDiffs.push({ point: ptText(pt), aDefined: A.defined, bDefined: B.defined });
      continue;
    }
    const diff = canon(X.sub(A.value, B.value), ctx);
    if (diff === ZERO) { agree++; continue; }
    if (diff && diff.k === "num") {
      out.verdict = "not-equivalent"; out.method = "exact-sampling";
      out.counterexample = { point: ptText(pt), a: toText(A.value), b: toText(B.value) };
      return out;
    }
    floatNeeded.push([pt, A.value, B.value]);
  }
  for (const [pt, va, vb] of floatNeeded) {
    const fa = evalNumeric(va, {}, { mode: isReal(ctx) ? "real" : "complex" });
    const fb = evalNumeric(vb, {}, { mode: isReal(ctx) ? "real" : "complex" });
    if (!fa || !fb) continue;
    const scale = Math.max(1, Math.hypot(fa.re, fa.im), Math.hypot(fb.re, fb.im));
    const err = Math.hypot(fa.re - fb.re, fa.im - fb.im) / scale;
    if (err > 1e-8 && !symZero) {
      out.verdict = "not-equivalent"; out.method = "numeric";
      out.counterexample = { point: ptText(pt), a: toText(va), b: toText(vb) };
      return out;
    }
    if (err <= 1e-10) { agree++; out.probable = true; }
  }
  // (3) floating evaluation at random real points (last resort)
  if (!symZero && agree < 3) {
    for (let i = 0; i < 24; i++) {
      const env = {};
      for (const v of vars) env[v] = (rnd() * 8 - 4) || 0.37;
      const fa = evalNumeric(a, env, { mode: isReal(ctx) ? "real" : "complex" });
      const fb = evalNumeric(b, env, { mode: isReal(ctx) ? "real" : "complex" });
      if (!fa || !fb) {
        if (!!fa !== !!fb) out.domainDiffs.push({ point: Object.fromEntries(Object.entries(env).map(([k, v]) => [k, String(v)])), aDefined: !!fa, bDefined: !!fb, numeric: true });
        continue;
      }
      const scale = Math.max(1, Math.hypot(fa.re, fa.im), Math.hypot(fb.re, fb.im));
      const err = Math.hypot(fa.re - fb.re, fa.im - fb.im) / scale;
      if (err > 1e-8) {
        out.verdict = "not-equivalent"; out.method = "numeric"; out.probable = true;
        out.counterexample = { point: env, a: String(fa.re), b: String(fb.re) };
        return out;
      }
      agree++;
      out.probable = true;
    }
  }
  const domCond = [];
  for (const c of [...domA.rels, ...domB.rels]) if (!domCond.includes(c)) domCond.push(c);
  out.conditions = [...notes];
  if (symZero) {
    out.method = "symbolic";
    out.probable = false;
    out.verdict = out.domainDiffs.length || notes.length ? "equivalent-under-conditions" : "equivalent";
  } else if (agree === 0) {
    out.verdict = "unknown";
    out.method = "sampling";
  } else {
    out.method = out.probable ? "numeric" : "exact-sampling";
    out.verdict = out.domainDiffs.length ? "equivalent-under-conditions" : "equivalent";
  }
  if (out.verdict === "equivalent-under-conditions") for (const c of domCond) if (!out.conditions.includes(c)) out.conditions.push(c);
  return out;
}
function mulberry(seed) {
  let s = seed >>> 0;
  return () => {
    s = (s + 0x6d2b79f5) >>> 0;
    let t = s;
    t = Math.imul(t ^ (t >>> 15), t | 1);
    t ^= t + Math.imul(t ^ (t >>> 7), t | 61);
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
  };
}
