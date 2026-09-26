// Quelvra worker <-> page serialisation.
//
// Math trees are hash-consed objects that cannot cross postMessage as-is (their identity and
// frozen shape would be lost). The worker converts every tree in a result into a record
//
//   { $tree: 1, text: toText(t), latex: toLatex(t), json: <plain nested JSON of the tree> }
//
// JSON node format:  { k, a?: [child...], v?: "n/d", name?, op?, dir?, q?, lo_open?, hi_open? }
// The page rebuilds a real tree from `json` with expr.js `mk` (so it is hash-consed into the
// page's own table and `a === b` still means structural equality) and stores it as `node`.
// BigInt values anywhere else are converted to decimal strings.

import * as N from "./engine/num.js";
import * as X from "./engine/expr.js";
import { toText, toLatex } from "./engine/print.js";

const EXTRA = ["name", "op", "dir", "q", "lo_open", "hi_open"];

export const isTree = (v) =>
  !!v && typeof v === "object" && typeof v.k === "string" && typeof v.id === "number" && Array.isArray(v.args);
export const isTreeRecord = (v) => !!v && typeof v === "object" && v.$tree === 1;

export function treeToJSON(u) {
  const o = { k: u.k };
  if (u.k === "num") o.v = u.v.n.toString() + "/" + u.v.d.toString();
  else if (u.k === "bool") o.v = !!u.v;
  for (const f of EXTRA) if (u[f] !== undefined) o[f] = u[f];
  if (u.args.length) o.a = u.args.map(treeToJSON);
  return o;
}

export function treeFromJSON(j) {
  if (!j || typeof j !== "object" || typeof j.k !== "string") throw new Error("Quelvra: bad tree JSON");
  if (j.k === "num") {
    const [n, d] = String(j.v).split("/");
    return X.num(N.Q(BigInt(n), BigInt(d || "1")));
  }
  if (j.k === "bool") return X.bool(!!j.v);
  const extra = {};
  let any = false;
  for (const f of EXTRA) if (j[f] !== undefined) { extra[f] = j[f]; any = true; }
  const args = (j.a || []).map(treeFromJSON);
  return X.mk(j.k, args.length ? args : null, any ? extra : undefined);
}

function safe(fn, u) {
  try { return fn(u); } catch (_) { return ""; }
}

export function serializeTree(u) {
  return { $tree: 1, text: safe(toText, u), latex: safe(toLatex, u), json: treeToJSON(u) };
}

// Deep-copy a value, turning trees into records, BigInt into strings, dropping functions.
export function serializeResult(value, depth = 0) {
  if (depth > 200) return null;
  if (value === null || value === undefined) return value;
  const t = typeof value;
  if (t === "bigint") return value.toString();
  if (t === "function" || t === "symbol") return undefined;
  if (t !== "object") return value;
  if (isTree(value)) return serializeTree(value);
  if (value instanceof Error) return { message: value.message, code: value.code || null };
  if (Array.isArray(value)) return value.map((v) => serializeResult(v, depth + 1));
  if (value instanceof Map) return Object.fromEntries([...value].map(([k, v]) => [String(k), serializeResult(v, depth + 1)]));
  if (value instanceof Set) return [...value].map((v) => serializeResult(v, depth + 1));
  if (value.n !== undefined && value.d !== undefined && typeof value.n === "bigint") return N.toString(value); // Rational
  const out = {};
  for (const key of Object.keys(value)) {
    const v = serializeResult(value[key], depth + 1);
    if (v !== undefined) out[key] = v;
  }
  return out;
}

// Page side: rebuild trees inside records (record.node). Records whose JSON is invalid keep
// only their text/latex so the UI can still show them.
export function deserializeResult(value, depth = 0) {
  if (depth > 200 || value === null || typeof value !== "object") return value;
  if (isTreeRecord(value)) {
    let node = null;
    try { node = treeFromJSON(value.json); } catch (_) { node = null; }
    return { $tree: 1, text: value.text, latex: value.latex, node };
  }
  if (Array.isArray(value)) return value.map((v) => deserializeResult(v, depth + 1));
  const out = {};
  for (const key of Object.keys(value)) out[key] = deserializeResult(value[key], depth + 1);
  return out;
}

// Error payload used by the worker protocol.
export function errorPayload(e) {
  return {
    code: (e && (e.code || (e.name === "QuelvraSyntaxError" ? "SYNTAX" : null))) || "ENGINE",
    message: (e && e.message) || String(e),
    pos: e && typeof e.pos === "number" ? e.pos : null,
    hint: (e && e.hint) || "",
  };
}
