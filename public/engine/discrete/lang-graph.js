// Graph phrasings -> canonical graph commands (see graph.js for the graph argument forms).

import { callForm, splitTop, matchClose, lab } from "./lang-util.js";

const EDGE = String.raw`([A-Za-z0-9_]+)\s*(->|-)\s*([A-Za-z0-9_]+)(?:\s*:\s*(-?\d+(?:\.\d+)?(?:/\d+)?))?`;
const EDGE_ONE = new RegExp(`^${EDGE}$`);

// one edge token -> "[u, v]" / "[u, v, w]" plus its direction, or null
function edgeTok(t) {
  const m = t.trim().match(EDGE_ONE);
  if (m) return { text: `[${lab(m[1])}, ${lab(m[3])}${m[4] ? `, ${m[4]}` : ""}]`, directed: m[2] === "->" };
  const p = t.trim().match(/^\(\s*([A-Za-z0-9_]+)\s*,\s*([A-Za-z0-9_]+)\s*(?:,\s*(-?\d+(?:\/\d+)?))?\s*\)$/);
  if (p) return { text: `[${lab(p[1])}, ${lab(p[2])}${p[3] ? `, ${p[3]}` : ""}]`, directed: false };
  return null;
}
function edgesToGraph(toks, forceDirected = false) {
  const es = toks.map(edgeTok);
  if (!es.length || es.some((e) => !e)) return null;
  const dir = es.map((e) => e.directed);
  if (dir.some(Boolean) && !dir.every(Boolean)) return null; // mixed graphs are not supported
  return `${dir[0] || forceDirected ? "arclist" : "edgelist"}(${es.map((e) => e.text).join(", ")})`;
}

// named graphs
export function namedGraph(s) {
  s = s.trim().replace(/^(?:the|a|an)\s+/i, "").replace(/\s+graph$/i, "").trim();
  let m;
  if (/^petersen$/i.test(s)) return "petersengraph(5, 2)";
  if ((m = s.match(/^K_?\{?\s*(\d+)\s*,\s*(\d+)\s*\}?$/))) return `completebipartite(${m[1]}, ${m[2]})`;
  if ((m = s.match(/^K_?\{?(\d+)\}?$/))) return `completegraph(${m[1]})`;
  if ((m = s.match(/^C_?\{?(\d+)\}?$/))) return `cyclegraph(${m[1]})`;
  if ((m = s.match(/^P_?\{?(\d+)\}?$/))) return `pathgraph(${m[1]})`;
  if ((m = s.match(/^W_?\{?(\d+)\}?$/))) return `wheelgraph(${m[1]})`;
  if ((m = s.match(/^Q_?\{?(\d+)\}?$/))) return `hypercubegraph(${m[1]})`;
  if ((m = s.match(/^complete (?:bipartite )?graph (?:on|with) (\d+) vertices$/i))) return `completegraph(${m[1]})`;
  if ((m = s.match(/^(?:cycle|wheel|hypercube|path)\s+(?:graph\s+)?([CWQP]_?\{?\d+\}?)$/i))) return namedGraph(m[1]);
  return null;
}

// any graph description -> canonical text or null
export function graphText(s) {
  s = s.trim();
  if (!s) return null;
  const named = namedGraph(s);
  if (named) return named;
  if (s.startsWith("[[") && matchClose(s, 0) === s.length - 1) return `adjmatrix(${s})`;
  let m;
  if ((m = s.match(/^(?:the\s+)?(?:graph\s+|digraph\s+|directed graph\s+)?(?:with\s+)?adjacency matrix\s+(\[\[.*\]\])$/i))) return `adjmatrix(${m[1]})`;
  if (s.startsWith("{") && matchClose(s, 0) === s.length - 1) return edgesToGraph(splitTop(s.slice(1, -1)));
  const directed = /\b(?:directed|digraph|network)\b/i.test(s);
  const body = s.replace(/^(?:the\s+)?(?:(?:directed|undirected|weighted)\s+)*(?:graph|digraph|network)\s*(?:with\s+)?(?:(?:edges|arcs)\s*)?/i, "").replace(/^(?:edges|arcs)\s+/i, "");
  const toks = splitTop(body, [",", " and "]).filter(Boolean);
  if (toks.length) return edgesToGraph(toks, directed && toks.every((t) => /->/.test(t)));
  return null;
}

const FRIENDLY = {
  degrees: "graphdegrees", degree: "graphdegrees", graphdegrees: "graphdegrees",
  components: "graphcomponents", connected: "graphcomponents", graphcomponents: "graphcomponents",
  shortestpath: "shortestpath", dijkstra: "shortestpath",
  mst: "minspantree", minspantree: "minspantree", spanningtree: "minspantree",
  spanningtrees: "countspanningtrees", countspanningtrees: "countspanningtrees",
  bipartite: "isbipartite", isbipartite: "isbipartite",
  eulerpath: "eulerpath", euler: "eulerpath", eulercircuit: "eulerpath",
  hamiltonian: "hamiltonpath", hamiltonpath: "hamiltonpath", hamiltoncycle: "hamiltonpath",
  chromaticnumber: "chromaticnumber", chromaticpoly: "chromaticpoly", chromaticpolynomial: "chromaticpoly",
  planar: "isplanar", isplanar: "isplanar",
  maxflow: "maxflow", toposort: "toposort", topologicalsort: "toposort",
  isomorphic: "isisomorphic", isisomorphic: "isisomorphic",
};
const TWO_LABELS = new Set(["shortestpath", "maxflow"]);

export function recogniseGraph(text) {
  const cf = callForm(text);
  if (cf && FRIENDLY[cf.name]) {
    const cmd = FRIENDLY[cf.name];
    if (cmd === "isisomorphic") {
      if (cf.args.length !== 2) return null;
      const [a, b] = cf.args.map(graphText);
      return a && b ? { math: `isisomorphic(${a}, ${b})`, interpretation: "Are the two graphs isomorphic?" } : null;
    }
    const g = graphText(cf.args[0] || "");
    if (!g) return null;
    if (TWO_LABELS.has(cmd)) {
      if (cf.args.length !== 3) return null;
      return { math: `${cmd}(${g}, ${lab(cf.args[1])}, ${lab(cf.args[2])})`, interpretation: `${cmd === "maxflow" ? "Maximum flow" : "Shortest path"} from ${cf.args[1]} to ${cf.args[2]}` };
    }
    if (cf.args.length !== 1) return null;
    return { math: `${cmd}(${g})`, interpretation: cmd };
  }
  return recogniseGraphWords(text);
}

function recogniseGraphWords(text) {
  const t = text;
  const low = t.toLowerCase();
  const graphish = /\b(?:graph|digraph|network|vertex|vertices|edges|petersen|planar|bipartite|euler|hamilton(?:ian)?|chromatic|spanning trees?|isomorphic|topological)\b/i.test(t) || /\bK_?\{?\d/.test(t);
  if (!graphish) return null;

  // isomorphism of two graphs
  if (/\bisomorphic\b/i.test(t)) {
    let m = t.match(/^(?:are|is)\s+(?:the\s+)?(?:graphs?\s+)?(.+?)\s+(?:and|isomorphic to)\s+(?:the\s+)?(?:graph\s+)?(.+?)(?:\s+isomorphic)?$/i);
    if (m) {
      const a = graphText(m[1]), b = graphText(m[2]);
      if (a && b) return { math: `isisomorphic(${a}, ${b})`, interpretation: "Are the two graphs isomorphic?" };
    }
    return null;
  }
  const withFromTo = (cmd, re) => {
    const m = t.match(re);
    if (!m) return null;
    const g = graphText(m.groups.g);
    if (!g) return null;
    return { math: `${cmd}(${g}, ${lab(m.groups.s)}, ${lab(m.groups.t)})`, interpretation: `${cmd === "maxflow" ? "Maximum flow" : "Shortest path"} from ${m.groups.s} to ${m.groups.t}` };
  };
  if (/shortest path|shortest distance|dijkstra/i.test(t)) {
    return withFromTo("shortestpath", /(?:shortest (?:path|distance)|dijkstra)\s+from\s+(?<s>[A-Za-z0-9_]+)\s+to\s+(?<t>[A-Za-z0-9_]+)\s+(?:in|on|for)\s+(?<g>.+)$/i)
      || withFromTo("shortestpath", /(?:shortest (?:path|distance))\s+(?:in|on)\s+(?<g>.+?)\s+from\s+(?<s>[A-Za-z0-9_]+)\s+to\s+(?<t>[A-Za-z0-9_]+)$/i);
  }
  if (/max(?:imum)? flow|min(?:imum)? cut/i.test(t)) {
    return withFromTo("maxflow", /(?:max(?:imum)? flow|min(?:imum)? cut)\s+from\s+(?<s>[A-Za-z0-9_]+)\s+to\s+(?<t>[A-Za-z0-9_]+)\s+(?:in|on|for)\s+(?<g>.+)$/i)
      || withFromTo("maxflow", /(?:max(?:imum)? flow|min(?:imum)? cut)\s+(?:in|on|of)\s+(?<g>.+?)\s+from\s+(?<s>[A-Za-z0-9_]+)\s+to\s+(?<t>[A-Za-z0-9_]+)$/i);
  }
  const rules = [
    [/(?:number of|how many|count(?: the)?)\s+spanning trees/i, "countspanningtrees"],
    [/minimum (?:weight )?spanning (?:tree|forest)|\bmst\b/i, "minspantree"],
    [/chromatic polynomial/i, "chromaticpoly"],
    [/chromatic number/i, "chromaticnumber"],
    [/euler(?:ian)? (?:path|circuit|trail|tour|cycle)|\beulerian\b/i, "eulerpath"],
    [/hamilton(?:ian)? (?:path|cycle|circuit)|\bhamiltonian\b/i, "hamiltonpath"],
    [/\bbipartite\b/i, "isbipartite"],
    [/\bplanar\b/i, "isplanar"],
    [/topological (?:sort|order|ordering)/i, "toposort"],
    [/\bdegrees?\b|degree sequence/i, "graphdegrees"],
    [/\bconnected\b|connected components|\bcomponents\b/i, "graphcomponents"],
  ];
  const hit = rules.find(([re]) => re.test(t));
  if (!hit) return null;
  const cmd = hit[1];
  const g = findGraph(t);
  if (!g) return null;
  void low;
  return { math: `${cmd}(${g})`, interpretation: cmd };
}

// locate the graph inside a sentence
function findGraph(t) {
  let m;
  // adjacency matrix
  if ((m = t.match(/adjacency matrix\s+(\[\[.*\]\])/i))) return `adjmatrix(${m[1]})`;
  // brace edge set
  const b = t.indexOf("{");
  if (b >= 0) { const e = matchClose(t, b); if (e > b) { const g = graphText(t.slice(b, e + 1)); if (g) return g; } }
  // edge list after "edges" / "graph" / "network"
  if ((m = t.match(/\b(?:edges|arcs|(?:directed |weighted |undirected )*(?:graph|digraph|network))\s+((?:\(?[A-Za-z0-9_]+\s*(?:->|-|,)\s*[A-Za-z0-9_]+\)?(?:\s*:\s*-?[\d./]+)?(?:\s*,\s*|\s+and\s+)?)+)(.*)$/i))) {
    const toks = splitTop(m[1].trim().replace(/,\s*$/, ""), [",", " and "]).filter(Boolean);
    // trailing words such as "connected" / "bipartite" are allowed after the list
    const last = toks[toks.length - 1];
    const lm = last && last.match(new RegExp(`^(${EDGE})\\s+[a-z].*$`, "i"));
    if (lm) toks[toks.length - 1] = lm[1];
    const directed = /\b(?:directed|digraph|network)\b/i.test(t) && toks.every((x) => /->/.test(x));
    const g = edgesToGraph(toks, directed);
    if (g) return g;
  }
  // named graph mentions
  const named = [/\b(the\s+)?petersen(?:\s+graph)?\b/i, /\bK_?\{\s*\d+\s*,\s*\d+\s*\}/, /\bK_?\d+\s*,\s*\d+\b/, /\b[KCPWQ]_?\{?\d+\}?(?![\d,])/];
  for (const re of named) { const mm = t.match(re); if (mm) { const g = namedGraph(mm[0]); if (g) return g; } }
  if ((m = t.match(/complete graph (?:on|with) (\d+) vertices/i))) return `completegraph(${m[1]})`;
  return null;
}
