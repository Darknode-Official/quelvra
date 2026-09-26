// Shared text helpers for the advanced discrete recognisers (lang.js, lang-*.js).

// ---------------------------------------------------------------- shared helpers
export function normalise(s) {
  return String(s || "")
    .replace(/[−–]/g, "-").replace(/—/g, "-")
    .replace(/→|⟶/g, "->").replace(/↔|⟷/g, "<->")
    .replace(/\s+/g, " ").trim().replace(/[.?!]+$/, "").trim();
}
// split on top-level separators (default comma), respecting (), [], {}
export function splitTop(s, seps = [","]) {
  const out = []; let depth = 0, cur = "";
  for (let i = 0; i < s.length; i++) {
    const ch = s[i];
    if ("([{".includes(ch)) depth++;
    else if (")]}".includes(ch)) depth--;
    if (depth === 0) {
      const sep = seps.find((x) => s.startsWith(x, i));
      if (sep) { out.push(cur.trim()); cur = ""; i += sep.length - 1; continue; }
    }
    cur += ch;
  }
  if (cur.trim() || out.length) out.push(cur.trim());
  return out;
}
// matching close bracket index for the open bracket at i, or -1
export function matchClose(s, i) {
  let depth = 0;
  for (let j = i; j < s.length; j++) { if ("([{".includes(s[j])) depth++; else if (")]}".includes(s[j])) { depth--; if (depth === 0) return j; } }
  return -1;
}
// "name(args)" covering the whole text -> { name, args: [raw strings] } or null
export function callForm(text) {
  const m = text.match(/^([A-Za-z][A-Za-z_]*)\s*\(/);
  if (!m) return null;
  const open = m[0].length - 1;
  const close = matchClose(text, open);
  if (close !== text.length - 1) return null;
  const inner = text.slice(open + 1, close).trim();
  return { name: m[1].toLowerCase(), args: inner ? splitTop(inner) : [] };
}
// a vertex / element label as parse-safe text: integers and single letters stay, others are char codes
export function lab(l) {
  l = String(l).trim();
  if (/^-?\d+$/.test(l)) return l.replace(/^-/, "-");
  if (/^[A-Za-z]$/.test(l)) return l;
  if (/^[A-Za-z]\d+$/.test(l)) return l;
  if (!l) throw new Error("empty label");
  return `vlabel(${[...l].map((c) => c.charCodeAt(0)).join(", ")})`;
}
// "key = value" arguments -> map (lowercase keys); positional args kept in order
export function keyArgs(args) {
  const named = {}, pos = [];
  for (const a of args) { const m = a.match(/^([A-Za-z][A-Za-z_0-9()]*)\s*=\s*(.+)$/); if (m) named[m[1].toLowerCase()] = m[2].trim(); else pos.push(a); }
  return { named, pos };
}
// integer-looking text (allowing 10^6 and 1,000 is NOT handled; plain digits and ^)
export const INT = String.raw`-?\d+(?:\s*\^\s*\d+)?`;
export function numText(s) { s = String(s).trim(); return /^-?\d+(?:\s*\^\s*\d+)?(?:\s*\/\s*\d+)?$/.test(s) ? s.replace(/\s+/g, "") : null; }

// set text "{1, 2, a}" / "{(1,2), (2,3)}" -> canonical list "[1, 2, a]" (tuples kept) or null
export function setText(s) {
  s = s.trim();
  if (!s.startsWith("{") || matchClose(s, 0) !== s.length - 1) return null;
  const inner = s.slice(1, -1).trim();
  if (!inner) return "[]";
  const items = splitTop(inner).map(elemText);
  if (items.some((x) => x === null)) return null;
  return `[${items.join(", ")}]`;
}
export function elemText(s) {
  s = s.trim();
  if (!s) return null;
  if (s.startsWith("{")) return setText(s);
  if (s.startsWith("(") && matchClose(s, 0) === s.length - 1) {
    const parts = splitTop(s.slice(1, -1)).map(elemText);
    if (parts.some((x) => x === null)) return null;
    return parts.length === 1 ? parts[0] : `(${parts.join(", ")})`;
  }
  if (/^-?\d+$/.test(s)) return s;
  if (/^[A-Za-z][A-Za-z0-9_]*$/.test(s)) return lab(s);
  if (s === "∅") return "[]";
  return null;
}
