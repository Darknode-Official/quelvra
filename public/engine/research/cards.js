// Quelvra research lab: expository cards for famous problems.
//
// Rules for this file: accurate, neutral, no hype. Open problems are described as open. The words
// "proved" / "solved" appear only in explicitly historical statements (with a name and year) or in
// negations ("no proof is known"). Quelvra never claims a proof of an open problem.

const MILLENNIUM = "US $1,000,000 Millennium Prize (Clay Mathematics Institute, announced 2000)";

export const CARDS = {
  riemann: {
    id: "riemann", title: "Riemann hypothesis", open: true, millennium: true,
    statement: "Every nontrivial zero of the Riemann zeta function zeta(s) has real part 1/2. (The nontrivial zeros are the zeros in the critical strip 0 < Re s < 1; the trivial zeros are s = -2, -4, -6, ...)",
    status: "Open. One of the seven Millennium Prize Problems.",
    whatIsKnown: [
      "Riemann (1859) stated the conjecture in his paper linking the zeros of zeta to the distribution of primes.",
      "Hadamard and de la Vallee Poussin (1896) showed there are no zeros on the line Re s = 1, which gives the prime number theorem.",
      "Hardy (1914) showed that infinitely many zeros lie on the critical line.",
      "Conrey (1989) showed that more than 40% of the nontrivial zeros lie on the critical line; later work raised the proportion slightly.",
      "Numerical verification: the first 10^13 zeros lie on the line (Gourdon, 2004), and Platt and Trudgian (2021) verified that all zeros with imaginary part up to 3 * 10^12 lie on it.",
      "The hypothesis is equivalent to the error bound pi(x) = Li(x) + O(sqrt(x) log x) (von Koch, 1901), and to many other statements in number theory.",
    ],
    whyHard: "The zeros are defined analytically but control arithmetic information about primes. Known methods give zero-free regions that shrink toward Re s = 1 as the height grows, and density theorems show that most zeros are close to the line, but no technique rules out a single zero off the line at arbitrary height. Numerical checks, however large, cover only finitely many zeros.",
    whatQuelvraCanCompute: [
      { command: "riemann zeros up to 1000", what: "Locate every zero with 0 < Im s < T, show each one is a sign change of Hardy's Z function (so it lies on the critical line), and match the total against the Riemann-von Mangoldt count N(T). Numerical evidence up to height T only." },
      { command: "zeta(0.5 + 14.134725i)", what: "Evaluate zeta(s) at any complex s (Euler-Maclaurin summation)." },
    ],
    prize: MILLENNIUM,
  },
  pvsnp: {
    id: "pvsnp", title: "P versus NP", open: true, millennium: true,
    statement: "Is every decision problem whose yes-instances can be verified in polynomial time by a deterministic Turing machine (the class NP) also decidable in polynomial time (the class P)? In short: does P = NP?",
    status: "Open. One of the seven Millennium Prize Problems. Most researchers expect P != NP, but that is a belief, not a theorem.",
    whatIsKnown: [
      "Cook (1971) and Levin (1973) showed that Boolean satisfiability (SAT) is NP-complete: a polynomial-time algorithm for SAT would give one for every problem in NP.",
      "Karp (1972) showed 21 classical combinatorial problems to be NP-complete; thousands are known today.",
      "Three barriers rule out broad families of techniques: relativization (Baker, Gill and Solovay, 1975), natural proofs (Razborov and Rudich, 1994) and algebrization (Aaronson and Wigderson, 2008).",
      "Strong lower bounds are known only for restricted models, for example constant-depth circuits (Furst, Saxe and Sipser, 1984; Ajtai, 1983; Hastad, 1986) and monotone circuits (Razborov, 1985).",
    ],
    whyHard: "Separating P from NP requires showing that no algorithm among infinitely many runs in polynomial time on some problem, and the known barriers show that the standard diagonalization and combinatorial circuit techniques cannot do this on their own.",
    whatQuelvraCanCompute: [
      { command: null, what: "Nothing that bears on the question. P versus NP is a statement about all algorithms and all input sizes; no finite computation can settle it, and Quelvra does not pretend otherwise." },
    ],
    prize: MILLENNIUM,
  },
  navierstokes: {
    id: "navierstokes", title: "Navier-Stokes existence and smoothness", open: true, millennium: true,
    statement: "For the incompressible Navier-Stokes equations in three space dimensions, with smooth divergence-free initial velocity (decaying suitably at infinity, or periodic), does a smooth solution with bounded energy exist for all time, or can a solution develop a singularity in finite time? The official problem (stated by Fefferman) asks for an answer either way.",
    status: "Open. One of the seven Millennium Prize Problems.",
    whatIsKnown: [
      "Leray (1934) showed that global weak solutions exist; whether they are unique and smooth is unknown.",
      "Smooth solutions exist for a short time for any smooth data, and for all time when the initial data are small.",
      "In two space dimensions smooth solutions exist for all time (Ladyzhenskaya and others, 1960s).",
      "Caffarelli, Kohn and Nirenberg (1982): the possible singular set of a suitable weak solution has one-dimensional parabolic Hausdorff measure zero.",
      "Tao (2016) constructed finite-time blowup for an averaged version of the equations, indicating that methods using only the energy identity and the general structure of the nonlinearity cannot settle the problem.",
      "Buckmaster and Vicol (2019) showed that certain very weak solutions are not unique.",
      "For the related inviscid Euler equations with a boundary, Chen and Hou (2022) gave a computer-assisted proof of finite-time blowup from smooth data; this does not decide the Navier-Stokes question.",
    ],
    whyHard: "The equations are supercritical: the quantities that are known to stay bounded (the energy) are too weak, relative to the scaling of the equations, to control the small-scale behaviour where a singularity could form.",
    whatQuelvraCanCompute: [
      { command: null, what: "Nothing that bears on the question. Numerical fluid simulations cannot distinguish a true singularity from very large but finite values, and Quelvra does not attempt them." },
    ],
    prize: MILLENNIUM,
  },
  bsd: {
    id: "bsd", title: "Birch and Swinnerton-Dyer conjecture", open: true, millennium: true,
    statement: "For an elliptic curve E over the rational numbers, the rank of the group E(Q) of rational points equals the order of vanishing of its L-function L(E, s) at s = 1. The refined form predicts the leading Taylor coefficient at s = 1 in terms of the regulator, the order of the Tate-Shafarevich group, the Tamagawa numbers, the real period and the torsion subgroup.",
    status: "Open. One of the seven Millennium Prize Problems.",
    whatIsKnown: [
      "Birch and Swinnerton-Dyer formulated the conjecture in the early 1960s from computer experiments.",
      "Coates and Wiles (1977): for curves with complex multiplication, if L(E, 1) != 0 then E(Q) is finite.",
      "Gross and Zagier (1986) together with Kolyvagin (1988): if the analytic rank is 0 or 1, then the rank equals the analytic rank and the Tate-Shafarevich group is finite.",
      "The modularity theorem (Wiles, and Taylor and Wiles, 1995; Breuil, Conrad, Diamond and Taylor, 2001) guarantees that L(E, s) is defined at s = 1 for every elliptic curve over Q.",
      "Bhargava and Shankar (2010s) showed that the average rank of elliptic curves over Q is bounded; with further work, a positive proportion of curves satisfy the rank part of the conjecture.",
    ],
    whyHard: "When the analytic rank is 2 or more there is no general method to construct the predicted rational points, and finiteness of the Tate-Shafarevich group is not known in general.",
    whatQuelvraCanCompute: [
      { command: null, what: "Not yet: Quelvra has no elliptic-curve L-function or rank computation." },
    ],
    prize: MILLENNIUM,
  },
  hodge: {
    id: "hodge", title: "Hodge conjecture", open: true, millennium: true,
    statement: "On a nonsingular complex projective algebraic variety, every rational cohomology class of type (p, p) (a Hodge class) is a rational linear combination of the classes of algebraic subvarieties (algebraic cycles).",
    status: "Open. One of the seven Millennium Prize Problems.",
    whatIsKnown: [
      "The Lefschetz (1,1) theorem (1924) settles the case p = 1; with the hard Lefschetz theorem this covers every variety of dimension at most 3.",
      "The integral version of the statement is false (Atiyah and Hirzebruch, 1962).",
      "The analogous statement for compact Kahler manifolds that are not projective is false (Voisin, 2002).",
      "Deligne (1982) showed that Hodge classes on abelian varieties are absolute Hodge classes, a weaker property predicted by the conjecture.",
    ],
    whyHard: "There is no general method to produce algebraic subvarieties from topological or analytic data about a variety.",
    whatQuelvraCanCompute: [
      { command: null, what: "Nothing that bears on the question: it concerns all smooth projective varieties and is not a finite computation." },
    ],
    prize: MILLENNIUM,
  },
  yangmills: {
    id: "yangmills", title: "Yang-Mills existence and mass gap", open: true, millennium: true,
    statement: "Show that for every compact simple gauge group G a quantum Yang-Mills theory on four-dimensional spacetime R^4 exists, satisfying axioms at least as strong as the Wightman (or Osterwalder-Schrader) axioms, and that it has a mass gap Delta > 0: every state orthogonal to the vacuum has energy at least Delta.",
    status: "Open. One of the seven Millennium Prize Problems.",
    whatIsKnown: [
      "Classical Yang-Mills theory (Yang and Mills, 1954) is the basis of the Standard Model of particle physics.",
      "Asymptotic freedom (Gross and Wilczek; Politzer, 1973) describes the theory at short distances.",
      "Lattice gauge theory (Wilson, 1974) and large numerical simulations strongly indicate confinement and a mass gap, but they are not a mathematical construction of the continuum theory.",
      "Rigorous constructions of interacting quantum field theories are known in two and three spacetime dimensions for some models (Glimm, Jaffe and others); no interacting four-dimensional gauge theory has been constructed rigorously.",
    ],
    whyHard: "Constructing an interacting quantum field theory in four dimensions requires controlling renormalization non-perturbatively, and the mass gap is an intrinsically non-perturbative phenomenon.",
    whatQuelvraCanCompute: [
      { command: null, what: "Nothing that bears on the question: lattice simulations are evidence about physics, not a construction, and are outside Quelvra's scope." },
    ],
    prize: MILLENNIUM,
  },
  poincare: {
    id: "poincare", title: "Poincare conjecture (solved by Perelman, 2002-2003)", open: false, millennium: true,
    statement: "Every simply connected, closed 3-dimensional manifold is homeomorphic to the 3-sphere.",
    status: "Solved in 2002-2003 by Grigori Perelman, completing Richard Hamilton's Ricci flow program. The Clay Millennium Prize was awarded to Perelman in 2010; he declined it.",
    whatIsKnown: [
      "Poincare posed the question in 1904.",
      "Smale (1961) settled the analogue in dimensions 5 and higher, and Freedman (1982) in dimension 4.",
      "Perelman's work (2002-2003) also established Thurston's geometrization conjecture.",
    ],
    whyHard: "Three-dimensional topology resisted the surgery methods that work in higher dimensions; Perelman's approach required controlling singularities of the Ricci flow.",
    whatQuelvraCanCompute: [{ command: null, what: "Nothing: this is a theorem of geometric topology." }],
    prize: "Millennium Prize awarded in 2010 (declined).",
  },
  collatz: {
    id: "collatz", title: "Collatz conjecture (3n + 1 problem)", open: true,
    statement: "Let T(n) = n/2 for even n and T(n) = 3n + 1 for odd n. For every positive integer n, repeatedly applying T eventually reaches 1.",
    status: "Open.",
    whatIsKnown: [
      "Lothar Collatz posed the problem in 1937.",
      "Computer verification has reached every starting value below 2^68, about 2.95 * 10^20 (Barina, 2020-2021).",
      "Terras (1976) and Everett (1977): almost all n (in natural density) eventually fall below their starting value.",
      "Tao (2019): almost all orbits, in logarithmic density, attain almost bounded values.",
      "Eliahou (1993) showed that any cycle other than 1 -> 4 -> 2 -> 1 would have at least 17,087,915 elements; later work has raised such bounds.",
      "Conway (1972) showed that a natural generalisation of the Collatz map leads to algorithmically undecidable questions.",
    ],
    whyHard: "Multiplication by 3 and division by 2 interact like a pseudo-random process. Heuristics predict that orbits shrink on average, but no known technique controls every individual orbit.",
    whatQuelvraCanCompute: [
      { command: "collatz 27", what: "The full trajectory of one starting value of any size: steps, peak, stopping time." },
      { command: "verify collatz up to 10^7", what: "Check that every n up to a bound reaches 1, with records for the longest trajectory and highest peak. Evidence, not a proof." },
    ],
    prize: "No institutional prize comparable to the Millennium Prizes; various informal prizes have been offered by individuals and companies.",
  },
  goldbach: {
    id: "goldbach", title: "Goldbach conjecture (strong / binary)", open: true,
    statement: "Every even integer greater than 2 is the sum of two primes.",
    status: "Open. (The weak or ternary Goldbach conjecture, that every odd integer greater than 5 is a sum of three primes, was proved by Harald Helfgott in 2013.)",
    whatIsKnown: [
      "Goldbach proposed the conjecture in a 1742 letter to Euler.",
      "It has been verified for every even number up to 4 * 10^18 (Oliveira e Silva, Herzog and Pardi, 2014).",
      "Chen (1973): every sufficiently large even number is the sum of a prime and a number with at most two prime factors.",
      "Vinogradov (1937) proved that every sufficiently large odd number is a sum of three primes; Helfgott (2013) removed the 'sufficiently large' condition, which settles the weak conjecture.",
      "Almost all even numbers are sums of two primes: the possible exceptions have density zero (van der Corput, Chudakov and Estermann, 1937-1938).",
    ],
    whyHard: "Sieve methods cannot distinguish primes from numbers with two prime factors (the parity problem), and the circle method, which handles three primes, does not give a usable error term for two.",
    whatQuelvraCanCompute: [
      { command: "goldbach 1000000", what: "A decomposition n = p + q of one even number of any size (primality certified below 3.3 * 10^24)." },
      { command: "verify goldbach up to 10^7", what: "Check every even number up to a bound, with the least prime needed and the hardest case. Evidence, not a proof." },
    ],
    prize: "None currently. A publisher offered US $1,000,000 as a promotion in 2000-2002; it expired unclaimed.",
  },
  twinprimes: {
    id: "twinprimes", title: "Twin prime conjecture", open: true,
    statement: "There are infinitely many primes p such that p + 2 is also prime.",
    status: "Open. The weaker statement that some fixed gap occurs between primes infinitely often was established in 2013 (bounded gaps between primes).",
    whatIsKnown: [
      "Brun (1919): the sum of the reciprocals of the twin primes converges (Brun's constant, about 1.902).",
      "Chen (1973): there are infinitely many primes p for which p + 2 is either prime or a product of two primes.",
      "Zhang (2013): infinitely many pairs of consecutive primes differ by at most 70,000,000.",
      "Maynard (2013) and, independently, Tao gave a simpler method; the Polymath8b project (2014) reduced the gap bound to 246.",
      "Under a generalised Elliott-Halberstam conjecture the bound would be 6; the parity problem blocks reaching 2 by these methods.",
      "The Hardy-Littlewood conjecture predicts pi_2(x) ~ 2 C_2 x / (ln x)^2 with C_2 = 0.6601618...",
    ],
    whyHard: "Sieve methods run into the parity problem: they cannot tell whether p + 2 has an odd or even number of prime factors, which is exactly what is needed.",
    whatQuelvraCanCompute: [
      { command: "twin primes up to 10^7", what: "Exact count pi_2(N), first and last pairs, the partial Brun sum, and maximal prime gaps up to N." },
    ],
    prize: "None.",
  },
  eulerbrick: {
    id: "eulerbrick", title: "Perfect cuboid (perfect Euler brick)", open: true,
    statement: "Is there a perfect cuboid: a box with integer edges a, b, c whose three face diagonals and space diagonal sqrt(a^2 + b^2 + c^2) are all integers?",
    status: "Open. Euler bricks (integer edges and integer face diagonals) exist in infinite families; whether any perfect cuboid exists is unknown.",
    whatIsKnown: [
      "The smallest Euler brick, with edges 44, 117, 240, was found by Paul Halcke in 1719.",
      "Saunderson (1740) and Euler gave parametric families of Euler bricks, so there are infinitely many.",
      "Any perfect cuboid must satisfy many congruence and divisibility conditions; these restrict but do not exclude it.",
      "Extensive computer searches, far beyond the bounds computed here, have found no perfect cuboid.",
    ],
    whyHard: "The problem asks for integer points on a surface defined by four simultaneous quadratic conditions; no general method decides whether such a Diophantine system has solutions.",
    whatQuelvraCanCompute: [
      { command: "euler bricks up to 10000", what: "Every Euler brick with largest edge up to a bound (exact), each checked for a perfect space diagonal. Evidence, not a proof." },
    ],
    prize: "None.",
  },
  sofa: {
    id: "sofa", title: "Moving sofa problem", open: true,
    statement: "What is the largest area of a rigid planar shape that can be moved around a right-angled corner in a hallway of width 1? (Moser, 1966)",
    status: "Gerver's sofa (area about 2.21953) is conjectured to be optimal. In late 2024 Jineon Baek posted a claimed proof of that optimality, which is under review; Quelvra treats the question as open pending that review.",
    whatIsKnown: [
      "Hammersley (1968) gave a sofa of area pi/2 + 2/pi (about 2.2074) and showed that no sofa has area above 2 sqrt 2.",
      "Gerver (1992) constructed a sofa bounded by 18 curve pieces with area about 2.21953 and conjectured it is optimal.",
      "Kallus and Romik (2018) gave a computer-assisted upper bound of 2.37.",
      "Romik (2018) derived Gerver's sofa from a system of differential equations and described a conjectured optimal shape for the two-corner (ambidextrous) variant.",
      "Jineon Baek (late 2024) posted a claimed proof that Gerver's sofa is optimal; it is under review, and Quelvra takes no position on its correctness.",
    ],
    whyHard: "The admissible shapes form an infinite-dimensional family, and the area is not a concave function of the motion, so local optimality does not imply global optimality.",
    whatQuelvraCanCompute: [
      { command: "moving sofa", what: "Exact areas of the semicircle and Hammersley's sofa, Gerver's four defining parameters recomputed, and the known bounds." },
    ],
    prize: "None.",
  },
  kaprekar: {
    id: "kaprekar", title: "Kaprekar's routine (6174)", open: false,
    statement: "Write a number with d digits (leading zeros allowed), subtract the number formed by its digits in ascending order from the number formed by them in descending order, and repeat. For d = 4 every number that is not a repdigit reaches 6174 within 7 steps.",
    status: "Not an open problem. For each fixed digit count and base the routine is a finite dynamical system, so its complete behaviour is decided by exhaustive computation.",
    whatIsKnown: [
      "D. R. Kaprekar described the constant 6174 in 1949.",
      "3 digits: every non-repdigit reaches 495. 4 digits: every non-repdigit reaches 6174 within 7 steps.",
      "5 digits: there is no fixed point; every non-repdigit enters one of three cycles.",
      "6 digits: two fixed points (549945 and 631764) and one cycle of length 7.",
    ],
    whyHard: "It is not hard: each digit count is a finite check. What has no simple answer is a formula for the fixed points and cycles for every digit count at once.",
    whatQuelvraCanCompute: [
      { command: "kaprekar 5", what: "The complete classification for a digit count (up to about 20 decimal digits): every fixed point and cycle, basin sizes and the maximum number of steps." },
    ],
    prize: "None.",
  },
  millennium: {
    id: "millennium", title: "The Millennium Prize Problems", open: true,
    statement: "Seven problems selected by the Clay Mathematics Institute in 2000: the Riemann hypothesis, P versus NP, Navier-Stokes existence and smoothness, the Birch and Swinnerton-Dyer conjecture, the Hodge conjecture, Yang-Mills existence and mass gap, and the Poincare conjecture.",
    status: "Six are open. The Poincare conjecture was proved by Grigori Perelman (2002-2003); the prize was awarded in 2010 and declined.",
    whatIsKnown: [
      "Open: Riemann hypothesis, P versus NP, Navier-Stokes, Birch and Swinnerton-Dyer, Hodge, Yang-Mills mass gap.",
      "Each prize is US $1,000,000, awarded only after publication and a waiting period for acceptance by the mathematical community.",
    ],
    whyHard: "Each problem sits at a point where the available methods are known to fall short.",
    whatQuelvraCanCompute: [
      { command: "riemann zeros up to 1000", what: "Numerical evidence for the Riemann hypothesis up to a height. For the other open Millennium problems no finite computation bears on the question." },
    ],
    prize: MILLENNIUM,
  },
};

export const CARD_ALIASES = [
  [/riemann hypothesis|riemann conjecture|\brh\b|riemann'?s? (?:problem|zeta hypothesis)|zeros of (?:the )?(?:riemann )?zeta function lie on/, "riemann"],
  [/\bp\s*(?:vs\.?|versus|=|!=|=\/=|≠|equals?|<>)\s*np\b|p versus np|\bp\s*and\s*np\b/, "pvsnp"],
  [/navier[\s-]*stokes/, "navierstokes"],
  [/birch|swinnerton|\bbsd\b/, "bsd"],
  [/\bhodge\b/, "hodge"],
  [/yang[\s-]*mills|mass gap/, "yangmills"],
  [/poincar[eé]/, "poincare"],
  [/collatz|(?:^|[\s(])3[nx]\s*\+\s*1(?:\s+(?:problem|conjecture|map|sequence))|^3[nx]\s*\+\s*1$|syracuse problem|hailstone/, "collatz"],
  [/goldbach/, "goldbach"],
  [/twin[\s-]*primes?/, "twinprimes"],
  [/perfect (?:cuboid|box|euler brick)|euler brick/, "eulerbrick"],
  [/sofa/, "sofa"],
  [/kaprekar|\b6174\b/, "kaprekar"],
  [/millennium|open problems?|unsolved problems?/, "millennium"],
];
export function cardIdFor(text) {
  const t = String(text || "").toLowerCase();
  for (const [re, id] of CARD_ALIASES) if (re.test(t)) return id;
  return null;
}

// The honest reply when someone asks Quelvra to prove or solve an open problem.
export function honestNote(card) {
  if (!card.open) return card.id === "kaprekar"
    ? "This one is not an open problem: for a fixed number of digits Quelvra can settle it completely by exhaustive computation."
    : `This is not an open problem. ${card.status}`;
  return `No proof of the ${card.title.replace(/ \(.*\)$/, "")} is known to anyone, and Quelvra cannot produce one. It will not invent a proof, and it never presents a computation as a proof of an open problem. Below is an accurate summary of what is known and what Quelvra can compute as evidence.`;
}

// Text honesty check used by tests (and available to the UI): sentences that use proof words must be
// historical (a year or a named claimed proof) or negated.
const PROOF_WORD = /\b(proved|proven|proves|prove|proof|proofs|solved|solves|solve|settled|settles|settle)\b/i;
const OK_CONTEXT = /\b(1[5-9]\d\d|20\d\d)\b|\b(no|not|never|nor|without|cannot|can't|claimed|will not|won't|unknown|neither|remains open|does not|is open)\b/i;
export function honestyViolations(text) {
  const out = [];
  for (const s of String(text).split(/(?<=[.!?;:])\s+|\n+/)) if (PROOF_WORD.test(s) && !OK_CONTEXT.test(s)) out.push(s.trim());
  return out;
}
export function cardText(card) {
  return [card.title, card.statement, card.status, ...card.whatIsKnown, card.whyHard, ...card.whatQuelvraCanCompute.map((w) => w.what), card.prize].join("\n");
}
