// Quelvra explainer: turns a solver result into one of three presentations.
//   answer : the result, its verification status and any conditions
//   steps  : the recorded transformations (compacted), each with before/after
//   teach  : steps plus the idea behind each rule family, the classification reasoning and a
//            "check it yourself" section built from the verifier's checks
// The explainer never invents steps: it only formats step records produced by the engines.

import { toText, toLatex } from "./print.js";
import { compact } from "./steps.js";

// Concept notes keyed by rule-id prefix (longest prefix wins).
const CONCEPTS = {
  "diff.sum": "The derivative of a sum is the sum of the derivatives.",
  "diff.const": "Constant factors pass through the derivative unchanged.",
  "diff.power": "Power rule: d/dx x^n = n x^(n-1).",
  "diff.chain": "Chain rule: differentiate the outer function, keep the inside, then multiply by the derivative of the inside.",
  "diff.product": "Product rule: (uv)' = u'v + uv'.",
  "diff.quotient": "Quotient rule: (u/v)' = (u'v - uv')/v^2.",
  "diff.exp": "The exponential function is its own derivative; other bases pick up a factor ln(b).",
  "diff.log": "d/dx ln(x) = 1/x; logarithmic differentiation handles variable exponents.",
  "diff.trig": "Standard trigonometric derivatives: (sin x)' = cos x, (cos x)' = -sin x, (tan x)' = sec^2 x.",
  "int.table": "Some integrals are read straight from a table of known antiderivatives.",
  "int.linear": "Integration is linear: split sums and pull out constant factors.",
  "int.usub": "Substitution reverses the chain rule: when the derivative of an inner expression appears as a factor, rename the inner expression u.",
  "int.parts": "Integration by parts reverses the product rule: integral of u dv = uv - integral of v du.",
  "int.partial": "Partial fractions split a rational function into simpler fractions that integrate to logarithms and arctangents.",
  "int.trig": "Trigonometric identities rewrite powers of sine and cosine into forms that integrate directly.",
  "int.ftc": "Fundamental theorem of calculus: a definite integral is F(b) - F(a) for any antiderivative F.",
  "lim.direct": "If the function is continuous at the point, the limit is the value there.",
  "lim.lhopital": "L'Hopital's rule: for 0/0 or oo/oo, the limit of f/g equals the limit of f'/g' when that exists.",
  "lim.series": "Replacing functions by their Taylor expansions reveals the leading behaviour near the point.",
  "lim.dominant": "At infinity, the fastest-growing terms decide the limit.",
  "solve.linear": "A linear equation is solved by undoing operations in reverse order, doing the same to both sides.",
  "solve.quadratic": "A quadratic ax^2 + bx + c = 0 has solutions x = (-b +- sqrt(b^2 - 4ac))/(2a); the discriminant b^2 - 4ac says how many are real.",
  "solve.factor": "If a product is zero, at least one factor is zero.",
  "solve.poly": "Polynomial roots come from the rational root test, factoring, and exact formulas; the rest are isolated and certified numerically.",
  "solve.radical": "Isolate the root and raise both sides to a power. This can introduce extraneous solutions, so every candidate is checked in the original equation.",
  "solve.abs": "|u| = c splits into u = c or u = -c (only when c >= 0).",
  "solve.exp": "Take logarithms of both sides to bring the unknown down from the exponent.",
  "solve.log": "Rewrite log_b(u) = c as u = b^c, then check that every logarithm's argument stays positive.",
  "solve.trig": "Find the principal solutions, then add the period to describe every solution.",
  "solve.rational": "Multiply by the common denominator, solve, then discard values that make a denominator zero.",
  "solve.numeric": "No exact method applies, so the root is bracketed and refined numerically with a certified error bound.",
  "solve.system": "Eliminate variables one at a time (Gaussian elimination) until each unknown is determined.",
  "solve.ineq": "Find where each side is equal or undefined; those points split the line into intervals whose sign is tested.",
  "simp": "Simplification rewrites the expression into an equal, shorter canonical form.",
  "expand": "Expanding multiplies out brackets.",
  "factor": "Factoring writes a polynomial as a product of irreducible pieces.",
  "verify": "The answer is substituted back into the original problem as an independent check.",
};
export function conceptFor(rule) {
  let best = null;
  for (const k of Object.keys(CONCEPTS)) if ((rule === k || rule.startsWith(k + ".") || rule.startsWith(k)) && (!best || k.length > best.length)) best = k;
  return best ? CONCEPTS[best] : null;
}

const STATUS_TEXT = {
  "verified-exact": "Verified exactly: substituting the answer into the original problem gives a true statement.",
  "verified-numeric": "Verified numerically: the original problem holds at the answer to within the stated tolerance.",
  "partially-verified": "Some parts were verified; see the checks below.",
  inconclusive: "Could not be verified independently.",
  failed: "Verification FAILED. This answer is not trustworthy.",
  unverified: "Not verified.",
  passed: "Verified: an independent check against the original problem passed.",
  partial: "Partly verified; see the checks below.",
  "not-applicable": "No independent check applies to this kind of result.",
};
export const statusText = (s, level) => (s === "passed" && level === "numeric" ? STATUS_TEXT["verified-numeric"] : s === "passed" && level === "exact" ? STATUS_TEXT["verified-exact"] : STATUS_TEXT[s] || s);

function fmtAnswer(a) {
  if (a.label && a.tree) return `${a.label} = ${toText(a.tree)}`;
  if (a.tree) return toText(a.tree);
  if (a.approx) return `${a.label ? a.label + " ~ " : "~ "}${a.approx.value}${a.approx.errorBound ? ` (error < ${a.approx.errorBound})` : ""}`;
  if (a.text) return a.text;
  return "";
}

// Build a presentation for the result in the requested mode. Output is plain data the UI renders.
export function explain(result, mode = "steps") {
  const out = {
    mode,
    headline: result.classification ? result.classification.label : "",
    answers: (result.answers || []).map((a) => ({ ...a, text: fmtAnswer(a), latex: a.tree ? (a.label ? `${a.label} = ` : "") + toLatex(a.tree) : null })),
    status: result.verification ? result.verification.status : "unverified",
    statusText: statusText(result.verification ? result.verification.status : "unverified", result.verification && result.verification.level),
    confidence: result.confidence || null,
    conditions: (result.conditions || []).map((c) => (c && c.k ? toText(c) : typeof c === "string" ? c : c && c.node ? `${toText(c.node)} ${c.rel === "!=0" ? "!= 0" : c.rel}` : String(c))),
    rejected: (result.rejected || []).map((r) => ({ text: r.tree ? toText(r.tree) : String(r.value), reason: r.reason })),
    steps: [],
    teach: null,
  };
  if (mode === "answer") return out;
  out.steps = compact(result.steps || []);
  if (mode === "teach") {
    const concepts = [];
    const seen = new Set();
    const walk = (ss) => ss.forEach((s) => {
      const c = conceptFor(s.rule);
      if (c && !seen.has(c)) { seen.add(c); concepts.push({ rule: s.rule, idea: c }); }
      if (s.sub) walk(s.sub);
    });
    walk(out.steps);
    const cls = result.classification || {};
    out.teach = {
      recognise: cls.label ? `This is a ${cls.label.toLowerCase()}.${cls.notes && cls.notes.length ? " " + cls.notes.join(" ") : ""}` : "",
      why: whyThisMethod(cls),
      concepts,
      check: (result.verification && result.verification.checks || []).map((c) => c.detail).filter(Boolean),
      pitfalls: pitfallsFor(cls),
    };
  }
  return out;
}

function whyThisMethod(cls) {
  const f = cls.family || "";
  const map = {
    linear: "The unknown appears only to the first power, so isolating it with inverse operations always works.",
    quadratic: "The highest power is 2, so factoring or the quadratic formula gives every solution exactly.",
    cubic: "Degree 3: look for a rational root first; if one exists the rest reduce to a quadratic.",
    quartic: "Degree 4: try rational roots and factoring; otherwise the roots are isolated and certified numerically.",
    polynomial: "Degree 5 or more has no general formula, so exact factors are found where possible and the rest are certified numerically.",
    rational: "The unknown appears in a denominator, so multiply through by the common denominator and reject values that make it zero.",
    radical: "The unknown is under a root, so isolate the root and raise to a power, then check for extraneous solutions.",
    "absolute-value": "Absolute value splits into two cases, one for each sign of the inside.",
    exponential: "The unknown is in an exponent, so logarithms bring it down.",
    logarithmic: "The unknown is inside a logarithm, so exponentiate both sides and check the domain.",
    trigonometric: "Trigonometric equations have infinitely many solutions: find the principal ones and add the period.",
    transcendental: "The unknown appears both inside and outside a transcendental function, so no algebraic method isolates it; a certified numerical method is used.",
    "linear-system": "Every equation is linear, so elimination solves the system exactly or proves it has no or infinitely many solutions.",
    "nonlinear-system": "Substitution or elimination reduces the system to a single equation in one unknown.",
  };
  return map[f] || "";
}
function pitfallsFor(cls) {
  const f = cls.family || "";
  const p = {
    radical: ["Squaring both sides can create solutions that do not satisfy the original equation. Always check."],
    rational: ["Never keep a value that makes a denominator zero."],
    logarithmic: ["Logarithms are only defined for positive arguments; check every candidate."],
    quadratic: ["Dividing both sides by x loses the solution x = 0. Factor instead."],
    "absolute-value": ["|u| = c has no solution when c < 0."],
    trigonometric: ["Give every solution (with the period), not just one."],
  };
  const out = p[f] ? [...p[f]] : [];
  if (cls.kind === "inequality") out.push("Multiplying or dividing an inequality by a negative number reverses its direction.");
  return out;
}
