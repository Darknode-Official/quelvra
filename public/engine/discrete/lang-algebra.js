// Abstract-algebra phrasings -> canonical commands (see algebra.js).

import { callForm, matchClose } from "./lang-util.js";

// ---------------------------------------------------------------- permutations
// "(1 2 3)(4 5)" / "(1,2,3)(4,5)" -> ["pcycle(1, 2, 3)", "pcycle(4, 5)"]; "[2, 3, 1]" -> one-line
export function permText(s) {
  s = s.trim();
  if (/^\[\s*\d+(?:\s*,\s*\d+)*\s*\]$/.test(s)) return [s];
  if (/^(?:\(\s*\d+(?:\s*[,\s]\s*\d+)*\s*\)\s*)+$/.test(s)) {
    const cs = [...s.matchAll(/\(([^)]*)\)/g)].map((m) => m[1].trim().split(/[\s,]+/).filter(Boolean));
    if (cs.some((c) => c.length < 1)) return null;
    return cs.map((c) => `pcycle(${c.join(", ")})`);
  }
  return null;
}
const permAt = (t, re) => { const m = t.match(re); if (!m) return null; const p = permText(m[1]); return p ? p : null; };

// ---------------------------------------------------------------- fields
// "GF(7)", "Z_5", "Z/5Z", "F_5", "GF(2^3) with modulus m", "GF(2)[x]/(m)", "GF(9) = GF(3)[x]/(m)", "Z_2[x]/(m)"
function fieldSpec(s) {
  s = s.trim();
  let m;
  const P = String.raw`(?:GF\s*\(\s*(\d+)\s*\)|Z\s*_\s*\{?(\d+)\}?|Z\s*/\s*(\d+)\s*Z|F\s*_\s*\{?(\d+)\}?|Z(\d+))`;
  const pOf = (mm, i) => mm[i] || mm[i + 1] || mm[i + 2] || mm[i + 3] || mm[i + 4];
  if ((m = s.match(new RegExp(`^(?:GF\\s*\\(\\s*\\d+(?:\\s*\\^\\s*\\d+)?\\s*\\)\\s*=\\s*)?${P}\\s*\\[\\s*([a-z])\\s*\\]\\s*/\\s*\\((.+)\\)$`, "i")))) return { p: pOf(m, 1), mod: m[7], x: m[6] };
  if ((m = s.match(/^GF\s*\(\s*(\d+)\s*\^\s*(\d+)\s*\)\s*(?:with|using|mod(?:ulo)?|defined by)?\s*(?:the\s+)?(?:modulus|irreducible polynomial|polynomial)?\s*(.+)$/i))) return { p: m[1], mod: m[3].trim(), k: m[2] };
  if ((m = s.match(new RegExp(`^${P}$`, "i")))) return { p: pOf(m, 1) };
  return null;
}
function gfCall(expr, f) { return `gfcalc(${expr}, ${f.p}${f.mod ? `, ${f.mod}` : ""})`; }
// "X over GF(p)" / "mod p" / "modulo p"
function overPrime(s) {
  const m = s.match(/^(.+?)\s+(?:over|in)\s+(?:the\s+field\s+)?(GF\s*\(\s*\d+\s*\)|Z\s*_\s*\{?\d+\}?|Z\s*\/\s*\d+\s*Z|F\s*_\s*\{?\d+\}?|Z\d+)$/i) || s.match(/^(.+?)\s+(?:mod|modulo)\s+(\d+)$/i);
  if (!m) return null;
  const f = /^\d+$/.test(m[2]) ? { p: m[2] } : fieldSpec(m[2]);
  return f && !f.mod ? { poly: m[1].trim(), p: f.p } : null;
}
const polyish = (s) => /^[\sx\d+\-*^()]+$/.test(s) && /x/.test(s);
const gaussish = (s) => /^[\s\di+\-*^()]+$/.test(s) && /\d/.test(s);

const FRIENDLY = { perm: "perminfo", perminfo: "perminfo", permutation: "perminfo", permcompose: "permcompose", unitgroup: "unitgroup", cyclicgroup: "cyclicgroup", abeliangroups: "abeliangroups", gfcalc: "gfcalc", factormod: "factormod", irreducible: "isirreducible", isirreducible: "isirreducible", gaussgcd: "gaussgcd", gaussfactor: "gaussfactor", quotientring: "quotientring", elementorder: "elementorder" };

export function recogniseAlgebra(text) {
  const t = text;
  const cf = callForm(t);
  if (cf && FRIENDLY[cf.name]) {
    const cmd = FRIENDLY[cf.name];
    if (cmd === "perminfo" || cmd === "permcompose") {
      const inner = t.slice(t.indexOf("(") + 1, -1).trim();
      if (cmd === "perminfo") { const p = permText(inner); return p ? { math: `perminfo(${p.join(", ")})`, interpretation: "Permutation" } : null; }
      const parts = splitPerms(inner);
      if (!parts) return null;
      return { math: `permcompose(${parts.join(", ")})`, interpretation: "Product of permutations (right to left)" };
    }
    return { math: `${cmd}(${cf.args.join(", ")})`, interpretation: cmd };
  }
  return recognisePerms(t) || recogniseGroups(t) || recogniseFields(t) || recogniseGauss(t);
}
// "(1 2), (1 3)" -> each argument one permutation
function splitPerms(s) {
  const args = []; let i = 0;
  while (i < s.length) {
    while (s[i] === " " || s[i] === ",") i++;
    if (i >= s.length) break;
    let j = i;
    if (s[i] === "[") j = matchClose(s, i) + 1;
    else while (j < s.length && s[j] === "(") { j = matchClose(s, j) + 1; while (s[j] === " " && s[j + 1] === "(") j++; }
    if (j <= i) return null;
    const p = permText(s.slice(i, j));
    if (!p) return null;
    args.push(p.length === 1 ? p[0] : `[${p.map((c) => `[${c.slice(7, -1)}]`).join(", ")}]`);
    i = j;
  }
  return args.length >= 2 ? args : null;
}

function recognisePerms(t) {
  let p;
  const PERM = String.raw`((?:\(\s*\d+(?:[\s,]+\d+)*\s*\)\s*)+|\[\s*\d+(?:\s*,\s*\d+)*\s*\])`;
  if ((p = permAt(t, new RegExp(`^(?:find\\s+|what is\\s+)?(?:the\\s+)?(?:order|sign|parity|inverse|cycle (?:decomposition|notation|type)|cycles)\\s+of\\s+(?:the\\s+)?(?:permutation\\s+)?${PERM}$`, "i")))) return { math: `perminfo(${p.join(", ")})`, interpretation: "Permutation" };
  if ((p = permAt(t, new RegExp(`^is\\s+(?:the\\s+)?(?:permutation\\s+)?${PERM}\\s+(?:even|odd)(?:\\s+or\\s+(?:even|odd))?$`, "i")))) return { math: `perminfo(${p.join(", ")})`, interpretation: "Permutation parity" };
  if ((p = permAt(t, new RegExp(`^(?:write|express|convert)\\s+(?:the\\s+)?(?:permutation\\s+)?${PERM}\\s+(?:in|as|to|into)\\s+(?:disjoint\\s+)?(?:cycle notation|cycles|a product of disjoint cycles)$`, "i")))) return { math: `perminfo(${p.join(", ")})`, interpretation: "Cycle notation" };
  const m = t.match(new RegExp(`^(?:compute|find|calculate|evaluate|simplify)?\\s*(?:the\\s+)?(?:product|composition)\\s+(?:of\\s+)?(?:the\\s+permutations\\s+)?${PERM}$`, "i"));
  if (m) { const cs = permText(m[1]); if (cs && cs.length >= 2) return { math: `permcompose(${cs.join(", ")})`, interpretation: "Product of permutations (right to left)" }; }
  return null;
}

function recogniseGroups(t) {
  let m;
  // order of a in Z_n (additive) or mod n / in U(n) / (Z/nZ)* (multiplicative)
  if ((m = t.match(/^(?:find\s+|what is\s+)?(?:the\s+)?(?:multiplicative\s+|additive\s+)?order of (-?\d+)\s+(?:in|modulo|mod)\s+(.+)$/i))) {
    const a = m[1], g = m[2].trim();
    let mm;
    if ((mm = g.match(/^(?:\(\s*Z\s*\/\s*(\d+)\s*Z\s*\)\s*(?:\*|\^\s*\*|\^\s*×|×)|U\s*\(\s*(\d+)\s*\)|Z\s*_\s*\{?(\d+)\}?\s*(?:\^\s*)?(?:\*|×))$/i))) return { math: `elementorder(${a}, ${mm[1] || mm[2] || mm[3]}, 1)`, interpretation: "Multiplicative order" };
    if ((mm = g.match(/^(?:Z\s*_\s*\{?(\d+)\}?|Z\s*\/\s*(\d+)\s*Z)$/i))) return { math: `elementorder(${a}, ${mm[1] || mm[2]}, ${/multiplicative/i.test(t) ? 1 : 0})`, interpretation: "Order in Z_n" };
    if ((mm = g.match(/^(\d+)$/))) return { math: `elementorder(${a}, ${mm[1]}, 1)`, interpretation: "Multiplicative order" };
    return null;
  }
  if ((m = t.match(/^(?:is\s+)?U\s*\(\s*(\d+)\s*\)\s*(?:cyclic|a cyclic group)?$/i)) || (m = t.match(/^(?:is\s+)?(?:the\s+)?(?:group\s+)?(?:\(\s*Z\s*\/\s*(\d+)\s*Z\s*\)\s*\*)\s*(?:cyclic|a cyclic group)$/i)) || (m = t.match(/^(?:find\s+|list\s+|what are\s+)?(?:all\s+)?(?:the\s+)?(?:primitive roots?|generators of U\s*\(\s*\d+\s*\))\s+(?:mod(?:ulo)?|of|for)\s+(\d+)$/i)) || (m = t.match(/^(?:structure|order) of (?:the (?:unit|multiplicative) group\s+)?U\s*\(\s*(\d+)\s*\)$/i))) {
    const n = m[1] || (t.match(/U\s*\(\s*(\d+)/i) || [])[1];
    if (!n) return null;
    return { math: `unitgroup(${n})`, interpretation: `The unit group U(${n})` };
  }
  if ((m = t.match(/^(?:find\s+|list\s+|what are\s+)?(?:all\s+)?(?:the\s+)?(generators|subgroups)\s+of\s+(?:the\s+(?:cyclic\s+)?group\s+)?Z\s*_\s*\{?(\d+)\}?$/i)) || (m = t.match(/^(?:find\s+|list\s+)?(?:all\s+)?(?:the\s+)?(generators|subgroups)\s+of\s+(?:the\s+)?Z\s*\/\s*(\d+)\s*Z$/i))) return { math: `cyclicgroup(${m[2]})`, interpretation: `The cyclic group Z_${m[2]}` };
  if ((m = t.match(/^(?:list\s+|find\s+|classify\s+)?(?:all\s+)?(?:the\s+)?abelian groups of order (\d+)(?: up to isomorphism)?$/i)) || (m = t.match(/^how many (?:non-isomorphic\s+)?abelian groups (?:are there\s+)?of order (\d+)(?: are there)?(?: up to isomorphism)?$/i))) return { math: `abeliangroups(${m[1]})`, interpretation: `Abelian groups of order ${m[1]}` };
  return null;
}

function recogniseFields(t) {
  let m;
  // quotient rings
  if ((m = t.match(/^is\s+(.+?\[\s*[a-z]\s*\]\s*\/\s*\(.+\))\s+a\s+(field|integral domain)$/i)) || (m = t.match(/^(?:is\s+)?(.+?\[\s*[a-z]\s*\]\s*\/\s*\(.+\))\s+(?:a\s+)?(field|integral domain)\??$/i))) {
    const spec = m[1].trim();
    const z = spec.match(/^Z\s*\[\s*([a-z])\s*\]\s*\/\s*\((.+)\)$/i);
    if (z) return { math: `quotientring(${z[2]})`, interpretation: `Z[${z[1]}]/(${z[2]})` };
    const f = fieldSpec(spec);
    if (f && f.mod) return { math: `quotientring(${f.mod}, ${f.p})`, interpretation: `Z_${f.p}[x]/(${f.mod})` };
    return null;
  }
  // GF arithmetic: "in <field> compute/multiply/..."
  if ((m = t.match(/^in\s+(.+?)\s*,?\s+(compute|calculate|evaluate|find|multiply|add|divide|simplify)\s+(.+)$/i))) {
    const f = fieldSpec(m[1]);
    if (!f) return null;
    let expr = m[3].trim();
    const op = m[2].toLowerCase();
    const two = expr.match(/^(.+?)\s+(?:and|by)\s+(.+)$/i);
    if (op === "multiply" && two) expr = `(${two[1]})*(${two[2]})`;
    else if (op === "add" && two) expr = `(${two[1]})+(${two[2]})`;
    else if (op === "divide" && two) expr = `(${two[1]})/(${two[2]})`;
    const inv = expr.match(/^(?:the\s+)?inverse of\s+(.+)$/i);
    if (inv) expr = `(${inv[1]})^(-1)`;
    return { math: gfCall(expr, f), interpretation: `Arithmetic in ${m[1]}` };
  }
  if ((m = t.match(/^(?:find\s+|what is\s+)?(?:the\s+)?(?:multiplicative\s+)?inverse of\s+(.+?)\s+in\s+(.+)$/i))) {
    const f = fieldSpec(m[2]);
    if (!f || (!f.mod && !/^\s*-?\d+\s*$/.test(m[1]))) return null;
    return { math: gfCall(`(${m[1]})^(-1)`, f), interpretation: `Inverse in ${m[2]}` };
  }
  // factoring / irreducibility over GF(p) or Q
  if ((m = t.match(/^(?:factor|factorise|factorize|completely factor)\s+(.+)$/i))) {
    const o = overPrime(m[1]);
    if (o && polyish(o.poly)) return { math: `factormod(${o.poly}, ${o.p})`, interpretation: `Factor over GF(${o.p})` };
    return null;
  }
  if ((m = t.match(/^is\s+(.+?)\s+irreducible\s+(?:over|in|mod|modulo)\s+(.+)$/i))) {
    const poly = m[1].trim();
    if (!polyish(poly)) return null;
    const over = m[2].trim();
    if (/^(?:Q|the rationals|ℚ|Q\s*\[\s*x\s*\]|Z|the integers|ℤ|Z\s*\[\s*x\s*\])$/i.test(over)) return { math: `isirreducible(${poly}, 0)`, interpretation: "Irreducible over Q?" };
    const f = /^\d+$/.test(over) ? { p: over } : fieldSpec(over);
    return f && !f.mod ? { math: `isirreducible(${poly}, ${f.p})`, interpretation: `Irreducible over GF(${f.p})?` } : null;
  }
  return null;
}

function recogniseGauss(t) {
  let m;
  if ((m = t.match(/^(?:find\s+|compute\s+)?(?:the\s+)?(?:gcd|greatest common divisor) of\s+(.+?)\s+and\s+(.+?)\s+(?:in|over)\s+(?:the\s+)?(?:gaussian integers|Z\s*\[\s*i\s*\])$/i))) {
    if (!gaussish(m[1]) || !gaussish(m[2])) return null;
    return { math: `gaussgcd(${m[1]}, ${m[2]})`, interpretation: "Gaussian gcd" };
  }
  if ((m = t.match(/^(?:factor|factorise|factorize)\s+(.+?)\s+(?:in|over|into)\s+(?:the\s+)?(?:gaussian (?:integers|primes)|Z\s*\[\s*i\s*\])$/i))) {
    if (!gaussish(m[1])) return null;
    return { math: `gaussfactor(${m[1]})`, interpretation: "Factor in Z[i]" };
  }
  return null;
}
