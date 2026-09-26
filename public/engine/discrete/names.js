// Names used by the advanced discrete-mathematics commands (strategies/advanced-discrete.js).
//
// This module has NO imports: parse.js and identify.js read these lists, so it must not pull in
// anything that depends on them.
//
// COMMANDS are top-level call forms (classify() turns them into command cards). HELPERS only occur
// inside a command's arguments (graphs, logic connectives, named graph families, ...). All of them
// are parsed as whole identifiers only. They are deliberately NOT ordinary English words ("graph",
// "union", "implies"): the language engine treats every parser function name as a known math word,
// and a common word there could make an English request look like a formula.

export const ADV_DISCRETE_COMMANDS = [
  // recurrences, generating functions, sequences
  "rsolve", "genfunc", "seriescoeff", "findsequence",
  // graph theory
  "graphdegrees", "graphcomponents", "shortestpath", "minspantree", "countspanningtrees", "isbipartite", "eulerpath", "hamiltonpath",
  "chromaticnumber", "chromaticpoly", "isplanar", "maxflow", "toposort", "isisomorphic",
  // logic and Boolean algebra
  "truthtable", "istautology", "issatisfiable", "logicequiv", "cnf", "dnf", "minsop", "validargument",
  // sets, relations, functions
  "setcalc", "divcount", "unionsize", "relprops", "funcprops", "fcompose",
  // abstract algebra
  "perminfo", "permcompose", "elementorder", "unitgroup", "cyclicgroup", "abeliangroups", "gfcalc", "factormod", "isirreducible",
  "gaussgcd", "gaussfactor", "quotientring",
  // linear programming and game theory
  "linprog", "intprog", "matrixgame", "nashequilibria",
  // cryptography
  "rsakeys", "rsadecrypt", "rsacrt", "modpow", "modinverse", "dlog", "diffiehellman",
  // algebraic topology
  "homology", "eulerchar",
  // proof-style requests
  "provedivisible", "proveidentity", "provesum", "provebound", "provealwaysprime", "provefinite", "proveequiv", "proofrequest",
];

export const ADV_DISCRETE_HELPERS = [
  "edgelist", "arclist", "adjmatrix", "vlabel", "vertexset",
  "completegraph", "completebipartite", "cyclegraph", "pathgraph", "wheelgraph", "hypercubegraph", "petersengraph",
  "LAND", "LOR", "LNOT", "LXOR", "LIMP", "LIFF", "LNAND", "LNOR", "mterms", "dcterms", "bvars",
  "SUNION", "SINTER", "SMINUS", "SSYMDIFF", "SCOMPL", "SCART", "SPOWER",
  "reldivides", "relcongmod", "relleq", "rellt", "fromformula",
  "pcycle", "objmax", "objmin", "intvars",
];

export const ADV_DISCRETE_NAMES = [...ADV_DISCRETE_COMMANDS, ...ADV_DISCRETE_HELPERS];
