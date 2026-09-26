// Cryptography phrasings -> canonical commands (see crypto.js).

import { callForm, keyArgs } from "./lang-util.js";

const NUM = String.raw`\d+(?:\s*\^\s*\d+)?`;
const clean = (s) => String(s).replace(/\s+/g, "");
// "p = 61, q = 53" anywhere in the text -> { p: "61", ... } (single-letter keys, lowercase)
function assignments(t) {
  const out = {};
  const re = new RegExp(String.raw`\b([a-zA-Z])\s*=\s*(${NUM})\b`, "g"); let m;
  while ((m = re.exec(t))) { const k = m[1]; const key = k === "A" || k === "B" ? k : k.toLowerCase(); if (!(key in out)) out[key] = clean(m[2]); }
  return out;
}

export function recogniseCrypto(text) {
  const t = text;
  const cf = callForm(t);
  if (cf) {
    const { named, pos } = keyArgs(cf.args);
    const get = (keys) => keys.map((k) => named[k]);
    const all = (xs) => xs.every((x) => x !== undefined && x !== "");
    switch (cf.name) {
      case "rsa": case "rsakeys": {
        const [p, q, e] = pos.length >= 3 ? pos.slice(0, 3) : get(["p", "q", "e"]);
        const m = pos[3] || named.m || named.message;
        if (!all([p, q, e])) return null;
        return { math: `rsakeys(${p}, ${q}, ${e}${m ? `, ${m}` : ""})`, interpretation: "RSA" };
      }
      case "rsadecrypt": { const xs = pos.length === 3 ? pos : get(["c", "n", "d"]); return all(xs) ? { math: `rsadecrypt(${xs.join(", ")})`, interpretation: "RSA decryption" } : null; }
      case "rsacrt": { const xs = pos.length === 4 ? pos : get(["c", "p", "q", "d"]); return all(xs) ? { math: `rsacrt(${xs.join(", ")})`, interpretation: "RSA decryption with the CRT" } : null; }
      case "modpow": case "powermod": { const xs = pos.length === 3 ? pos : null; return xs && all(xs) ? { math: `modpow(${xs.join(", ")})`, interpretation: "Modular exponentiation" } : null; }
      case "modinverse": case "inversemod": { return pos.length === 2 ? { math: `modinverse(${pos.join(", ")})`, interpretation: "Modular inverse" } : null; }
      case "dlog": case "discretelog": { return pos.length === 3 ? { math: `dlog(${pos.join(", ")})`, interpretation: "Discrete logarithm" } : null; }
      case "diffiehellman": case "dh": { const xs = pos.length === 4 ? pos : get(["p", "g", "a", "b"]); return all(xs) ? { math: `diffiehellman(${xs.join(", ")})`, interpretation: "Diffie-Hellman" } : null; }
    }
  }
  let m;
  // RSA family
  if (/\bRSA\b|\bdecrypt\b|\bencrypt\b/i.test(t)) {
    const a = assignments(t);
    if (/\bdecrypt/i.test(t) && /\bCRT\b|chinese remainder/i.test(t) && a.c && a.p && a.q && a.d) return { math: `rsacrt(${a.c}, ${a.p}, ${a.q}, ${a.d})`, interpretation: "RSA decryption with the CRT" };
    if (/\bdecrypt/i.test(t) && a.c && a.n && a.d) return { math: `rsadecrypt(${a.c}, ${a.n}, ${a.d})`, interpretation: "RSA decryption" };
    if (/\bRSA\b/i.test(t) && a.p && a.q && a.e) return { math: `rsakeys(${a.p}, ${a.q}, ${a.e}${a.m ? `, ${a.m}` : ""})`, interpretation: "RSA" };
    return null;
  }
  if (/diffie[- ]?hellman/i.test(t)) {
    const a = assignments(t);
    return a.p && a.g && a.a && a.b ? { math: `diffiehellman(${a.p}, ${a.g}, ${a.a}, ${a.b})`, interpretation: "Diffie-Hellman key exchange" } : null;
  }
  // modular power: "compute 4^13 mod 497", "3^200 mod 13", "4^13 (mod 497)"
  if ((m = t.match(new RegExp(String.raw`^(?:compute|calculate|evaluate|find|what is)?\s*(-?\d+)\s*\^\s*(-?${NUM}|\(\s*-?\d+\s*\))\s*(?:mod|modulo|\(\s*mod)\s*(${NUM})\s*\)?$`, "i")))) {
    return { math: `modpow(${m[1]}, ${clean(m[2]).replace(/[()]/g, "")}, ${clean(m[3])})`, interpretation: "Modular exponentiation" };
  }
  // modular inverse
  if ((m = t.match(new RegExp(String.raw`^(?:find\s+|compute\s+|what is\s+)?(?:the\s+)?(?:multiplicative\s+|modular\s+)?inverse of\s+(-?${NUM})\s+(?:mod|modulo)\s+(${NUM})$`, "i")))) return { math: `modinverse(${clean(m[1])}, ${clean(m[2])})`, interpretation: "Modular inverse" };
  // discrete logarithm
  if ((m = t.match(new RegExp(String.raw`^(?:find\s+|compute\s+)?(?:the\s+)?discrete\s+log(?:arithm)?\s+of\s+(${NUM})\s+(?:to\s+the\s+)?base\s+(${NUM})\s+(?:mod|modulo)\s+(${NUM})$`, "i")))) return { math: `dlog(${clean(m[2])}, ${clean(m[1])}, ${clean(m[3])})`, interpretation: "Discrete logarithm" };
  if ((m = t.match(new RegExp(String.raw`^(?:solve\s+)?(${NUM})\s*\^\s*x\s*(?:≡|=|==)\s*(${NUM})\s*\(?\s*mod(?:ulo)?\s+(${NUM})\s*\)?$`, "i")))) return { math: `dlog(${clean(m[1])}, ${clean(m[2])}, ${clean(m[3])})`, interpretation: "Discrete logarithm" };
  return null;
}
