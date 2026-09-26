// Topology phrasings -> canonical homology / Euler characteristic commands (see topology.js).
// Named spaces become explicit triangulations; topology.js re-identifies each named surface by the
// classification of surfaces before trusting the name.

import { callForm, splitTop, matchClose, keyArgs } from "./lang-util.js";

// grid triangulation of the torus (twist = false) or Klein bottle (twist = true), n x m squares
function grid(n, m, twist) {
  const P = (i, j) => { let jj = ((j % m) + m) % m; let ii = i; if (ii === n) { ii = 0; if (twist) jj = (m - jj) % m; } return ii * m + jj + 1; };
  const tris = [];
  for (let i = 0; i < n; i++) for (let j = 0; j < m; j++) { tris.push([P(i, j), P(i + 1, j), P(i + 1, j + 1)]); tris.push([P(i, j), P(i, j + 1), P(i + 1, j + 1)]); }
  return tris;
}
const SPACES = {
  torus: () => grid(3, 3, false),
  klein: () => grid(3, 4, true),
  rp2: () => [[1, 2, 3], [1, 3, 4], [1, 4, 5], [1, 5, 6], [1, 6, 2], [2, 3, 5], [3, 4, 6], [4, 5, 2], [5, 6, 3], [6, 2, 4]],
  mobius: () => [[1, 2, 3], [2, 3, 4], [3, 4, 5], [4, 5, 1], [5, 1, 2]],
  sphere: () => [[1, 2, 3], [1, 2, 4], [1, 3, 4], [2, 3, 4]],
  disk: () => [[1, 2, 3]],
  annulus: () => [[1, 2, 4], [2, 4, 5], [2, 3, 5], [3, 5, 6], [3, 1, 6], [1, 6, 4]],
  circle: () => [[1, 2], [2, 3], [1, 3]],
  point: () => [[1]],
};
const NAMES = [
  [/^(?:the\s+)?(?:2-?)?torus$|^T\^?2$/i, "torus"],
  [/^(?:the\s+)?klein bottle$/i, "klein"],
  [/^(?:the\s+)?(?:real\s+)?projective plane$|^RP\s*\^?\s*2$|^ℝP\s*\^?\s*2$|^P\^?2$/i, "rp2"],
  [/^(?:the\s+)?m[oö]e?bius (?:band|strip)$/i, "mobius"],
  [/^(?:the\s+)?(?:2-?)?sphere$|^S\s*\^\s*2$|^S2$|^(?:the\s+)?(?:boundary|surface) of (?:a|the) tetrahedron$/i, "sphere"],
  [/^(?:the\s+)?(?:closed\s+)?(?:2-?)?disk$|^D\s*\^\s*2$/i, "disk"],
  [/^(?:the\s+)?annulus$|^(?:the\s+)?cylinder$/i, "annulus"],
  [/^(?:the\s+)?circle$|^S\s*\^\s*1$|^S1$/i, "circle"],
  [/^(?:a|the)\s+point$/i, "point"],
];
const code = (s) => `vlabel(${[...s].map((c) => c.charCodeAt(0)).join(", ")})`;
function namedSpace(s) {
  const hit = NAMES.find(([re]) => re.test(s.trim()));
  if (!hit) return null;
  const tris = SPACES[hit[1]]();
  const surface = ["torus", "klein", "rp2", "mobius", "sphere", "disk", "annulus"].includes(hit[1]);
  return `homology(${surface ? `${code(hit[1])}, ` : ""}${tris.map((t) => `[${t.join(", ")}]`).join(", ")})`;
}
// "{1,2,3}, {2,3,4}" or "[1,2,3], [2,3,4]" -> "[1, 2, 3], [2, 3, 4]"
function facetList(s) {
  const parts = splitTop(s.trim().replace(/\s+and\s+/g, ", "));
  const out = [];
  for (const p of parts) {
    const q = p.trim();
    if (!/^[{[]/.test(q) || matchClose(q, 0) !== q.length - 1) return null;
    const vs = q.slice(1, -1).split(",").map((x) => x.trim());
    if (!vs.length || vs.some((v) => !/^(?:\d+|[A-Za-z]\d*)$/.test(v))) return null;
    out.push(`[${vs.join(", ")}]`);
  }
  return out.length ? out.join(", ") : null;
}

export function recogniseTopology(text) {
  const t = text;
  const cf = callForm(t);
  if (cf && cf.name === "homology") {
    if (cf.args.length === 1) { const n = namedSpace(cf.args[0]); if (n) return { math: n, interpretation: `Homology of the ${cf.args[0]}` }; }
    const fl = facetList(cf.args.join(", "));
    return fl ? { math: `homology(${fl})`, interpretation: "Simplicial homology" } : null;
  }
  if (cf && (cf.name === "eulerchar" || cf.name === "eulercharacteristic")) {
    const { named, pos } = keyArgs(cf.args);
    const xs = pos.length ? pos : [named.v, named.e, named.f].filter((x) => x !== undefined);
    return xs.length >= 1 && xs.every((x) => /^\d+$/.test(x)) ? { math: `eulerchar(${xs.join(", ")})`, interpretation: "Euler characteristic" } : null;
  }
  let m;
  if ((m = t.match(/^(?:compute\s+|find\s+|what (?:is|are)\s+)?(?:the\s+)?(homology(?: groups)?|betti numbers|euler characteristic)\s+of\s+(.+)$/i))) {
    const what = m[1].toLowerCase(), obj = m[2].trim();
    if (what === "euler characteristic") {
      const v = obj.match(/(\d+)\s+vertices/i), e = obj.match(/(\d+)\s+edges/i), f = obj.match(/(\d+)\s+(?:faces|triangles)/i);
      if (v && e && f && /polyhedron|polytope|graph|map|surface|solid|complex with \d/i.test(obj)) return { math: `eulerchar(${v[1]}, ${e[1]}, ${f[1]})`, interpretation: "Euler characteristic V - E + F" };
    }
    const n = namedSpace(obj);
    if (n) return { math: n, interpretation: `${m[1]} of the ${obj.replace(/^the\s+/i, "")}` };
    const fm = obj.match(/^(?:the\s+|a\s+)?(?:simplicial\s+)?complex\s+(?:with|whose)\s+(?:facets|maximal faces|triangles|simplices|faces|edges|tetrahedra)(?:\s+are)?\s*:?\s*(.+)$/i);
    if (fm) { const fl = facetList(fm[1]); if (fl) return { math: `homology(${fl})`, interpretation: "Simplicial homology" }; }
  }
  return null;
}
