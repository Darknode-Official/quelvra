// Decoders: parsed call-form arguments (math trees) -> plain JavaScript values.
// Every decoder throws a refusal (code UNSUPPORTED) with a readable message when the argument
// does not have the expected shape; nothing is guessed.

import * as X from "../expr.js";
import * as N from "../num.js";
import { simplify } from "../simplify.js";
import { refuse } from "./util.js";

// constant arithmetic -> Rational, or null
export function ratOf(u) {
  if (!u) return null;
  if (u.k === "num") return u.v;
  if (X.freeSymbols(u).size) return null;
  let s;
  try { s = simplify(u); } catch (_) { return null; }
  return s && s.k === "num" ? s.v : null;
}
export function intOf(u, what = "an integer") {
  const r = ratOf(u);
  if (!r || r.d !== 1n) throw refuse(`expected ${what}`);
  return r.n;
}
export const isList = (u) => u && (u.k === "vector" || u.k === "tuple" || u.k === "matrix" || u.k === "set");
export function listOf(u, what = "a list") {
  if (!isList(u)) throw refuse(`expected ${what}`);
  return u.args;
}
// vertex / element label: integers, identifiers (x_1 -> x1), e / i / pi, vlabel(char codes)
export function labelOf(u) {
  if (!u) throw refuse("missing label");
  if (u.k === "num") { if (u.v.d !== 1n) throw refuse("labels must be integers or names"); return String(u.v.n); }
  if (u.k === "sym") return u.name.replace(/_(\d+)$/, "$1").replace(/_\{?([A-Za-z0-9]+)\}?$/, "$1");
  if (u.k === "const") return { e: "e", I: "i", pi: "pi" }[u.name] || (() => { throw refuse(`"${u.name}" cannot be a label`); })();
  if (u.k === "fn" && u.name === "vlabel") return String.fromCharCode(...u.args.map((a) => Number(intOf(a))));
  if (u.k === "mul" && u.args.length === 2 && u.args[0].k === "num" && u.args[0].v.n === -1n && u.args[1].k === "num") return String(-u.args[1].v.n);
  const r = ratOf(u);
  if (r && r.d === 1n) return String(r.n);
  throw refuse("labels must be integers or names");
}
// element value for sets / relations: bigint, string, tuple (array) or set ({set: [...]})
export function valueOf(u) {
  if (u.k === "tuple") return u.args.map(valueOf);
  if (u.k === "vector" || u.k === "set") return { set: u.args.map(valueOf) };
  if (u.k === "matrix") return { set: u.args.map((row) => ({ set: row.args.map(valueOf) })) };
  const r = ratOf(u);
  if (r) { if (r.d !== 1n) throw refuse("set elements must be integers, names, tuples or sets"); return r.n; }
  return labelOf(u);
}

// polynomial in x with rational coefficients: tree -> array of Rationals (index = power)
export function polyOf(u, x = "x") {
  const add = (a, b) => { const r = []; for (let i = 0; i < Math.max(a.length, b.length); i++) r.push(N.add(a[i] || N.ZERO, b[i] || N.ZERO)); return trim(r); };
  const mul = (a, b) => { if (!a.length || !b.length) return []; const r = Array(a.length + b.length - 1).fill(N.ZERO); a.forEach((c, i) => b.forEach((d, j) => { r[i + j] = N.add(r[i + j], N.mul(c, d)); })); return trim(r); };
  const trim = (r) => { while (r.length && N.isZero(r[r.length - 1])) r.pop(); return r; };
  const go = (w) => {
    switch (w.k) {
      case "num": return trim([w.v]);
      case "sym": if (w.name === x) return [N.ZERO, N.ONE]; throw refuse(`unexpected symbol ${w.name} in a polynomial in ${x}`);
      case "add": return w.args.map(go).reduce(add, []);
      case "mul": return w.args.map(go).reduce(mul, [N.ONE]);
      case "pow": {
        const e = ratOf(w.args[1]);
        const b = go(w.args[0]);
        if (!e || e.d !== 1n || e.n < 0n) {
          if (e && e.d === 1n && b.length === 1) return trim([N.pow(b[0], Number(e.n))]);
          throw refuse("polynomials need non-negative integer powers");
        }
        if (e.n > 4096n) throw refuse("the power is too large");
        let r = [N.ONE];
        for (let i = 0n; i < e.n; i++) r = mul(r, b);
        return r;
      }
      default: {
        const r = ratOf(w);
        if (r) return trim([r]);
        throw refuse("expected a polynomial");
      }
    }
  };
  return go(u);
}
export function intPolyOf(u, x = "x") {
  const cs = polyOf(u, x);
  if (cs.some((c) => c.d !== 1n)) throw refuse("expected a polynomial with integer coefficients");
  return cs.map((c) => c.n);
}
