// Recognition corpus: realistic ways people write math, each with the meaning Quelvra must read.
//
// Every entry is [group, input, expected]:
//   expected = "canonical math"  -> the recognised tree equals parse(canonical) (raw, or after
//                                   simplify, or for relations the expanded difference of sides)
//   expected = { kind, goal, command, family, variable }  -> fields of classify() on the tree
//   expected = REFUSE            -> recognition must refuse (never read words as letter products)
// Recognition mirrors orchestrate.js recognise(): translate() first, then the unknown-word guard,
// then the parser.

import { test, ok } from "./harness.js";
import { translate } from "../public/engine/language.js";
import { parse, parseDetailed, unknownWords } from "../public/engine/parse.js";
import { classify } from "../public/engine/identify.js";
import { simplify, expand } from "../public/engine/simplify.js";
import { toText } from "../public/engine/print.js";
import * as X from "../public/engine/expr.js";

export const REFUSE = { refuse: true };
const R = String.raw;

export function recog(src) {
  const t = translate(src);
  if (t.ok && t.pattern !== "math") {
    try {
      const { node, warnings } = parseDetailed(t.math);
      return { tree: node, warnings, goal: t.goal, variable: t.variable, t };
    } catch (_) { /* fall through, as orchestrate does */ }
  }
  const words = unknownWords(src);
  if (words.length >= 2 || words.some((w) => w.length >= 4)) return { error: `unknown words: ${words.join(", ")}`, t };
  try {
    const { node, warnings } = parseDetailed(src);
    return { tree: node, warnings, t };
  } catch (e) { return { error: e.message, t }; }
}

const safe = (f) => { try { return f(); } catch (_) { return null; } };
function sameMeaning(a, b) {
  if (a === b) return true;
  const sa = safe(() => simplify(a)), sb = safe(() => simplify(b));
  if (sa && sa === sb) return true;
  const rel = (u) => u.k === "eq" || (u.k === "rel");
  if (rel(a) && rel(b) && a.k === b.k && (a.k === "eq" || a.op === b.op)) {
    const d = (u) => safe(() => simplify(expand(simplify(X.sub(u.args[0], u.args[1])))));
    const da = d(a), db = d(b);
    if (da && da === db) return true;
  }
  if ((a.k === "system" || a.k === "tuple") && a.k === b.k && a.args.length === b.args.length) return a.args.every((x, i) => sameMeaning(x, b.args[i]));
  if (a.k === "fn" && b.k === "fn" && a.name === b.name && a.args.length === b.args.length) return a.args.every((x, i) => sameMeaning(x, b.args[i]));
  return false;
}

export function check([, src, want]) {
  const r = recog(src);
  if (want && want.refuse) return r.error ? { pass: true } : { pass: false, got: `accepted as ${toText(r.tree)}` };
  if (r.error) return { pass: false, got: `refused: ${r.error}` };
  if (typeof want === "string") {
    let canon;
    try { canon = parse(want); } catch (e) { return { pass: false, got: `canonical "${want}" does not parse: ${e.message}` }; }
    return sameMeaning(r.tree, canon) ? { pass: true } : { pass: false, got: toText(r.tree) };
  }
  const card = safe(() => classify(r.tree, { variable: r.variable, goal: r.goal || undefined }));
  if (!card) return { pass: false, got: "classify failed" };
  for (const k of Object.keys(want)) {
    const v = k === "variable" ? card.unknowns && card.unknowns[0] : card[k];
    if (v !== want[k]) return { pass: false, got: `${k}=${v} (tree ${toText(r.tree)})` };
  }
  return { pass: true };
}

export const CORPUS = [
  // ------------------------------------------------------------ notations: implicit multiplication
  ["notation", "2x", "2*x"], ["notation", "2 x", "2*x"], ["notation", "2(x+1)", "2*(x+1)"], ["notation", "(x+1)(x-1)", "(x+1)*(x-1)"],
  ["notation", "x(x+1)", "x*(x+1)"], ["notation", "x (x - 1)(x + 2)", "x*(x-1)*(x+2)"], ["notation", "3xy", "3*x*y"], ["notation", "-2x^2", "-(2*x^2)"],
  ["notation", "2sinx", "2*sin(x)"], ["notation", "2 sin x", "2*sin(x)"], ["notation", "sin2x", "sin(2*x)"], ["notation", "sin 2x", "sin(2*x)"],
  ["notation", "cos3x", "cos(3*x)"], ["notation", "tan 3θ", "tan(3*theta)"], ["notation", "sin^2 x", "sin(x)^2"], ["notation", "sin^2(x)", "sin(x)^2"],
  ["notation", "sin²x", "sin(x)^2"], ["notation", "sin^-1 x", "asin(x)"], ["notation", "sin^{-1}(x)", "asin(x)"], ["notation", "sin⁻¹(x)", "asin(x)"],
  ["notation", "tan^-1(1)", "atan(1)"], ["notation", "sin(x)^2", "(sin(x))^2"], ["notation", "cos x^2", "cos(x^2)"], ["notation", "sin x cos x", "sin(x)*cos(x)"],
  ["notation", "x sin x", "x*sin(x)"], ["notation", "sin(x)cos(x)", "sin(x)*cos(x)"], ["notation", "2π", "2*pi"], ["notation", "2πr", "2*pi*r"],
  ["notation", "xe^x", "x*e^x"], ["notation", "3(x-1)^2", "3*(x-1)^2"], ["notation", "(2)(3)", "6"], ["notation", "2·3", "6"],
  ["notation", "ln2", "ln(2)"], ["notation", "sqrt2", "sqrt(2)"], ["notation", "2sqrt(x)", "2*sqrt(x)"], ["notation", "x√2", "x*sqrt(2)"],
  // mixed numbers, grouping, scientific notation, percent, factorial
  ["notation", "2 1/2", "5/2"], ["notation", "3 3/4 + 1 1/4", "5"], ["notation", "-2 1/2", "-5/2"], ["notation", "2½", "5/2"],
  ["notation", "1,000", "1000"], ["notation", "1,000,000", "1000000"], ["notation", "1,250 + 2,500", "3750"], ["notation", "2,500.75", "2500.75"],
  ["notation", "3.2e-5", "32/1000000"], ["notation", "3.2E5", "320000"], ["notation", "1e3", "1000"], ["notation", "3.2 x 10^-5", "3.2*10^(-5)"],
  ["notation", "3.2×10⁻⁵", "3.2*10^(-5)"], ["notation", "6.02 × 10^23", "6.02*10^23"], ["notation", "6.02*10^23", "602*10^21"], ["notation", "3.2·10^-5", "3.2*10^(-5)"],
  ["notation", "50%", "1/2"], ["notation", "15% * 80", "12"], ["notation", "x + 10%", "x + 1/10"], ["notation", "5!", "factorial(5)"],
  ["notation", "n!", "factorial(n)"], ["notation", "(n+1)!", "factorial(n+1)"], ["notation", "5!/(2!3!)", "10"], ["notation", "0.5", "1/2"],
  ["notation", ".25", "1/4"], ["notation", "-.5", "-1/2"],
  // absolute value, floor, ceiling
  ["notation", "|x|", "abs(x)"], ["notation", "|x - 3|", "abs(x-3)"], ["notation", "|x - |x||", "abs(x - abs(x))"], ["notation", "2|x-1|", "2*abs(x-1)"],
  ["notation", "|x| + |y|", "abs(x)+abs(y)"], ["notation", "|-5|", "5"], ["notation", "⌊x⌋", "floor(x)"], ["notation", "⌈x/2⌉", "ceil(x/2)"],
  ["notation", "⌊2.5⌋ + ⌈2.5⌉", "5"], ["notation", "floor(x)", "floor(x)"], ["notation", "⌊⌊x⌋/2⌋", "floor(floor(x)/2)"],
  // roots
  ["notation", "∛8", "2"], ["notation", "∛(x+1)", "(x+1)^(1/3)"], ["notation", "root(8, 3)", "2"], ["notation", "x^(1/3)", "cbrt(x)"],
  ["notation", "∜16", "2"], ["notation", "√(x+1)", "sqrt(x+1)"], ["notation", "√2", "sqrt(2)"], ["notation", "cbrt(27)", "3"],
  ["notation", "sqrt(16)", "4"], ["notation", "3√x", "3*sqrt(x)"],
  // logs and exponentials
  ["notation", "log2(8)", "log(2, 8)"], ["notation", "log_2 8", "log(2, 8)"], ["notation", "log_2(8)", "log(2, 8)"], ["notation", "log_{2}(8)", "log(2, 8)"],
  ["notation", "log10(100)", "log(10, 100)"], ["notation", "log(100)", "log(10, 100)"], ["notation", "lg 100", "log(10, 100)"], ["notation", "ln e", "1"],
  ["notation", "ln(x^2)", "ln(x^2)"], ["notation", "log₂8", "log(2, 8)"], ["notation", "log(2, 8)", "3"], ["notation", "ln x", "ln(x)"],
  ["notation", "e^x", "exp(x)"], ["notation", "exp(2x)", "e^(2x)"], ["notation", "e^(x+1)", "exp(x+1)"], ["notation", "2e", "2*e"],
  ["notation", "e^{-x^2}", "exp(-x^2)"], ["notation", "eˣ", "exp(x)"],
  // constants and symbols
  ["notation", "pi/2", "pi/2"], ["notation", "π/2", "pi/2"], ["notation", "∞", "oo"], ["notation", "-∞", "-oo"], ["notation", "infinity", "oo"],
  ["notation", "3 ≤ x", "3 <= x"], ["notation", "x ≥ 2", "x >= 2"], ["notation", "x ≠ 1", "x != 1"], ["notation", "x ± 1", "x +- 1"],
  ["notation", "x ∓ 1", "x +- (-1)"], ["notation", "2 · 3", "6"], ["notation", "2 × 3", "6"], ["notation", "6 ÷ 2", "3"], ["notation", "5 − 3", "2"],
  ["notation", "x ⋅ y", "x*y"], ["notation", "x ≤ 5 ≤ y", "x <= 5 <= y"],
  // superscripts and subscripts
  ["notation", "x²", "x^2"], ["notation", "x³ + 2x²", "x^3 + 2x^2"], ["notation", "x⁻¹", "1/x"], ["notation", "x¹⁰", "x^10"], ["notation", "2⁵", "32"],
  ["notation", "x₁ + x₂", "x_1 + x_2"], ["notation", "a₁₀", "a_10"], ["notation", "x_1 + x_2 = 3", "x_1 + x_2 = 3"], ["notation", "x_(n+1)", "x_(n+1)"],
  ["notation", "theta2", "theta_2"], ["notation", "x2 + x1", "x_2 + x_1"],
  // derivatives: primes, Leibniz, partials
  ["notation", "f'(x)", "diff(f(x), x)"], ["notation", "f''(x)", "diff(f(x), x, 2)"], ["notation", "dy/dx = x y^2", { kind: "equation" }], ["notation", "dy/dx = y", "d/dx y = y"],
  ["notation", "d^2y/dx^2 + y = 0", "diff(y, x, 2) + y = 0"], ["notation", "y' = y", { kind: "equation" }], ["notation", "y'' + y = 0", { kind: "equation" }],
  ["notation", "d/dx (x^2)", "diff(x^2, x)"], ["notation", "d/dx x^3", "diff(x^3, x)"], ["notation", "d/dt sin(t)", "diff(sin(t), t)"], ["notation", "∂/∂x (x^2 y)", "diff(x^2 y, x)"],
  ["notation", "∂/∂y (x y^2)", "diff(x y^2, y)"], ["notation", "d^2/dx^2 x^4", "diff(x^4, x, 2)"], ["notation", "diff(x^2, x)", "d/dx x^2"],
  // integrals, sums, products, limits (plain and Unicode)
  ["notation", "∫ x^2 dx", "integrate(x^2, x)"], ["notation", "∫_0^1 x dx", "integrate(x, x, 0, 1)"], ["notation", "∫₀¹ x² dx", "integrate(x^2, x, 0, 1)"],
  ["notation", "int_0^pi sin(x) dx", "integrate(sin(x), x, 0, pi)"], ["notation", "∫ sin(t) dt", "integrate(sin(t), t)"], ["notation", "integrate(x^2, x, 0, 1)", "integrate(x^2, x, 0, 1)"],
  ["notation", "∑_{k=1}^{n} k", "sum(k, k, 1, n)"], ["notation", "∑_(k=1)^n k^2", "sum(k^2, k, 1, n)"], ["notation", "Σ_{n=1}^{∞} 1/n^2", "sum(1/n^2, n, 1, oo)"],
  ["notation", "∏_{k=1}^{5} k", "prod(k, k, 1, 5)"], ["notation", "sum(k, k, 1, 10)", "sum(k, k, 1, 10)"], ["notation", "lim x->0 sin(x)/x", "limit(sin(x)/x, x, 0)"],
  ["notation", "lim_(x->0^+) 1/x", { kind: "limit", family: "one-sided-limit" }], ["notation", "lim x→∞ 1/x", "limit(1/x, x, oo)"],
  // sets, intervals, vectors, piecewise
  ["notation", "{1, 2, 3}", "{1, 2, 3}"], ["notation", "{x | x > 0}", "x > 0"], ["notation", "{x : x^2 < 4}", "x^2 < 4"], ["notation", "[0, 1)", { kind: "interval" }],
  ["notation", "(0, 1]", { kind: "interval" }], ["notation", "<1,2,3>", "[1,2,3]"], ["notation", "⟨1, 2⟩", "[1, 2]"], ["notation", "[1, 2, 3]", "[1,2,3]"],
  ["notation", "piecewise(x, x > 0, -x, x <= 0)", { kind: "expression" }], ["notation", "dot([1,2,3],[4,5,6])", { kind: "command", command: "dot" }],
  ["notation", "cross([1,0,0],[0,1,0])", { kind: "command", command: "cross" }],
  // function definition then evaluation
  ["notation", "f(x) = x^2; f(3)", "9"], ["notation", "f(x) = 2x + 1; f(4)", "9"], ["notation", "g(t) = t^2 - 1; g(2) + g(3)", "11"],
  ["notation", "f(x) = x^2; f(x) = 4", "x^2 = 4"], ["notation", "f(x) = x^3; f'(x)", "diff(x^3, x)"], ["notation", "f(x)=x^2+1", { kind: "function-definition" }],
  // degrees and congruences
  ["notation", "30°", "pi/6"], ["notation", "sin 30°", "sin(pi/6)"], ["notation", "sin(45°)", "sin(pi/4)"], ["notation", "90 deg", "pi/2"],
  ["notation", "3x ≡ 2 (mod 7)", "mod(3x, 7) = 2"], ["notation", "3x = 2 (mod 7)", "mod(3x, 7) = 2"], ["notation", "3x = 2 mod 7", "mod(3x, 7) = 2"],
  ["notation", "x ≡ 10 (mod 3)", "mod(x, 3) = 1"], ["notation", "2x + 1 ≡ 0 mod 5", "mod(2x + 1, 5) = 0"], ["notation", "x ≡ 2 (mod 3), x ≡ 3 (mod 5)", "mod(x,3) = 2, mod(x,5) = 3"],
  ["notation", "x mod 5", "mod(x, 5)"], ["notation", "17 mod 5", "2"], ["notation", "y = x mod 5", "y = mod(x, 5)"],

  // ------------------------------------------------------------ LaTeX
  ["latex", R`\int_0^1 x^2 \, dx`, "integrate(x^2, x, 0, 1)"], ["latex", R`\int x \mathrm{d}x`, "integrate(x, x)"], ["latex", R`\int_{0}^{\pi} \sin x \, dx`, "integrate(sin(x), x, 0, pi)"],
  ["latex", R`\sum_{k=1}^{n} k^2`, "sum(k^2, k, 1, n)"], ["latex", R`\sum_{n=1}^{\infty} \frac{1}{n^2}`, "sum(1/n^2, n, 1, oo)"], ["latex", R`\prod_{k=1}^{5} k`, "prod(k, k, 1, 5)"],
  ["latex", R`\lim_{x \to 0} \frac{\sin x}{x}`, "limit(sin(x)/x, x, 0)"], ["latex", R`\lim_{x \to \infty} \frac{1}{x}`, "limit(1/x, x, oo)"], ["latex", R`\lim_{x \to 0^+} \frac{1}{x}`, { kind: "limit", family: "one-sided-limit" }],
  ["latex", R`\frac{a}{b}`, "a/b"], ["latex", R`\dfrac{1}{2}`, "1/2"], ["latex", R`\tfrac{1}{2}`, "1/2"], ["latex", R`\frac{x+1}{x-1}`, "(x+1)/(x-1)"],
  ["latex", R`\sqrt{x}`, "sqrt(x)"], ["latex", R`\sqrt[3]{x}`, "cbrt(x)"], ["latex", R`\sqrt[3]{8}`, "2"], ["latex", R`\sqrt{x^2+1}`, "sqrt(x^2+1)"],
  ["latex", R`2 \cdot 3`, "6"], ["latex", R`2 \times 3`, "6"], ["latex", R`6 \div 2`, "3"], ["latex", R`\left( x + 1 \right)^2`, "(x+1)^2"],
  ["latex", R`\operatorname{sin} x`, "sin(x)"], ["latex", R`\ln x`, "ln(x)"], ["latex", R`\log_{2} 8`, "log(2, 8)"], ["latex", R`\log_2 8`, "log(2, 8)"],
  ["latex", R`\log_{10}(x)`, "log(10, x)"], ["latex", R`\binom{5}{2}`, "10"], ["latex", R`\begin{pmatrix} 1 & 2 \\ 3 & 4 \end{pmatrix}`, "[[1,2],[3,4]]"],
  ["latex", R`\begin{bmatrix} 1 & 2 \\ 3 & 4 \end{bmatrix}`, "[[1,2],[3,4]]"], ["latex", R`\sin^2 x + \cos^2 x`, "sin(x)^2 + cos(x)^2"], ["latex", R`\cos^{-1}(x)`, "acos(x)"],
  ["latex", R`e^{i\pi}`, "-1"], ["latex", R`x^{2}`, "x^2"], ["latex", R`\pi r^2`, "pi*r^2"], ["latex", R`x \leq 3`, "x <= 3"], ["latex", R`x \geq 3`, "x >= 3"],
  ["latex", R`x \neq 3`, "x != 3"], ["latex", R`x \pm 2`, "x +- 2"], ["latex", R`\frac{d}{dx} x^2`, "diff(x^2, x)"], ["latex", R`\frac{dy}{dx} = y`, "d/dx y = y"],
  ["latex", R`\frac{d^2y}{dx^2} + y = 0`, "diff(y, x, 2) + y = 0"], ["latex", R`\frac{\partial}{\partial x} (x^2 y)`, "diff(x^2 y, x)"], ["latex", R`\frac{\mathrm{d}}{\mathrm{d}x} \sin x`, "diff(sin(x), x)"],
  ["latex", R`\left| x - 1 \right|`, "abs(x-1)"], ["latex", R`\lfloor x \rfloor`, "floor(x)"], ["latex", R`\lceil x \rceil`, "ceil(x)"], ["latex", R`\infty`, "oo"],
  ["latex", R`\alpha + \beta`, "alpha + beta"], ["latex", R`\theta^2`, "theta^2"], ["latex", R`\mathrm{e}^{x}`, "exp(x)"], ["latex", R`\exp(x)`, "exp(x)"],
  ["latex", R`\begin{cases} x & x > 0 \\ -x & x \le 0 \end{cases}`, { kind: "expression" }], ["latex", R`\int_{-1}^{1} |x| \, dx`, "integrate(abs(x), x, -1, 1)"],
  ["latex", R`\sqrt{\frac{1}{4}}`, "1/2"], ["latex", R`\frac{1}{2}x`, "x/2"], ["latex", R`3x \equiv 2 \pmod{7}`, "mod(3x, 7) = 2"], ["latex", R`x^2 \cdot x^3`, "x^5"],
  ["latex", R`\tan\theta`, "tan(theta)"], ["latex", R`\arcsin(1)`, "pi/2"], ["latex", R`10^{-3}`, "1/1000"], ["latex", R`90^\circ`, "pi/2"],

  // ------------------------------------------------------------ English: evaluation and algebra
  ["english", "what is 2 + 2", "4"], ["english", "What is 2+2?", "4"], ["english", "calculate 3 * 4", "12"], ["english", "evaluate sin(pi/2)", "1"],
  ["english", "compute 2^10", "1024"], ["english", "what's 7 times 8", "56"], ["english", "how much is 15 divided by 3", "5"], ["english", "please calculate 12 / 4", "3"],
  ["english", "can you evaluate 3^4?", "81"], ["english", "hey quelvra, what is 9 * 9", "81"], ["english", "what is 10 minus 4", "6"], ["english", "what is 3 plus 4 times 2", "11"],
  ["english", "2+2=", "4"], ["english", "what is 2+2=?", "4"], ["english", "find the value of 2^5", "32"], ["english", "what is 100 over 4", "25"],
  ["english", "what is x squared when x is 3", REFUSE], ["english", "x squared", "x^2"], ["english", "x cubed", "x^3"], ["english", "x to the power of 4", "x^4"],
  ["english", "x to the 4th power", "x^4"], ["english", "x raised to the power of 3", "x^3"], ["english", "what is five squared plus three", "28"], ["english", "(x + 1) squared", "(x+1)^2"],
  ["english", "the square root of 16", "4"], ["english", "what is the square root of 144", "12"], ["english", "cube root of 8", "2"], ["english", "what is the cube root of 27", "3"],
  ["english", "square root of x plus 1", "sqrt(x) + 1"], ["english", "2 times x plus 3 equals 11", "2x + 3 = 11"], ["english", "half of 10", "5"], ["english", "what is half of 12", "6"],
  ["english", "twice 7", "14"], ["english", "what is twice 8", "16"], ["english", "two thirds of 9", "6"], ["english", "the sum of 3 and 4", "7"],
  ["english", "what is the sum of 3 and 4", "7"], ["english", "the product of 3 and 4", "12"], ["english", "the difference between 10 and 4", "6"], ["english", "the quotient of 10 and 2", "5"],
  ["english", "what is 15% of 80", "12"], ["english", "20 percent of 50", "10"], ["english", "what is 12.5% of 64", "8"], ["english", "30 is what percent of 120", "p/100*120 = 30"],
  ["english", "is 97 prime", "isprime(97)"], ["english", "is 91 a prime number?", "isprime(91)"], ["english", "Is 2 prime?", "isprime(2)"], ["english", "prime factorization of 360", "factorint(360)"],
  ["english", "find the prime factorization of 84", "factorint(84)"], ["english", "prime factors of 60", "factorint(60)"], ["english", "gcd of 12 and 18", "gcd(12, 18)"], ["english", "GCD of 12 and 18", "gcd(12, 18)"],
  ["english", "what is the greatest common divisor of 48 and 36", "gcd(48, 36)"], ["english", "lcm of 4 and 6", "lcm(4, 6)"], ["english", "LCM of 4, 6 and 8", "lcm(4, 6, 8)"], ["english", "least common multiple of 3 and 5", "lcm(3, 5)"],
  ["english", "factorial of 5", "120"], ["english", "what is the factorial of 6", "720"], ["english", "5 factorial", "120"], ["english", "what is 17 mod 5", "2"],
  ["english", "17 modulo 5", "2"], ["english", "remainder when 17 is divided by 5", "2"], ["english", "divisors of 12", "divisors(12)"], ["english", "mean of 3, 5, 7, 9", "mean(3, 5, 7, 9)"],
  ["english", "average of 2, 4 and 6", "mean(2, 4, 6)"], ["english", "median of 1, 3, 2", "median(1, 3, 2)"],
  // solving
  ["english", "solve x^2 - 5x + 6 = 0", { kind: "equation", goal: "solve", variable: "x" }], ["english", "solve for x: 2x + 3 = 11", { kind: "equation", goal: "solve", variable: "x" }],
  ["english", "solve for x 2x+3=11", "2x + 3 = 11"], ["english", "solve 2x + 3 = 11 for x", "2x + 3 = 11"], ["english", "solve a x + b = c for x", { kind: "equation", variable: "x" }],
  ["english", "find x if 2x + 3 = 11", { kind: "equation", variable: "x" }], ["english", "find x: 3x = 12", "3x = 12"], ["english", "find the value of x if 2x = 10", "2x = 10"],
  ["english", "what is x if 5x = 20", "5x = 20"], ["english", "find the roots of x^2 - 4", "x^2 - 4 = 0"], ["english", "find the solutions of x^2 = 9", "x^2 = 9"], ["english", "roots of x^2 - 5x + 6", "x^2 - 5x + 6 = 0"],
  ["english", "for what values of x is x^2 < 4", "x^2 < 4"], ["english", "for which x is 2x + 1 > 5", "2x + 1 > 5"], ["english", "when does x^2 equal 9", "x^2 = 9"], ["english", "when is x^2 - 1 = 0", "x^2 - 1 = 0"],
  ["english", "solve the equation 3x - 7 = 2", "3x - 7 = 2"], ["english", "solve the inequality 2x - 3 > 5", "2x - 3 > 5"], ["english", "solve the system x + y = 3 and x - y = 1", "x + y = 3, x - y = 1"],
  ["english", "solve x + y = 3 and x - y = 1", { kind: "system" }], ["english", "solve the system of equations 2x + y = 5, x - y = 1", { kind: "system", family: "linear-system" }],
  ["english", "solve y' = y with y(0) = 1", "y' = y, y(0) = 1"], ["english", "solve the differential equation y'' + y = 0", "y'' + y = 0"], ["english", "solve x > 0 and x < 5", { kind: "inequality" }],
  ["english", "please solve 2x = 4", "2x = 4"], ["english", "can you solve x^2 = 16?", "x^2 = 16"], ["english", "Solve: x^2 - 1 = 0", "x^2 - 1 = 0"], ["english", "solve for t: t^2 = 4", { kind: "equation", variable: "t" }],
  // calculus
  ["english", "derivative of x^3 + 2x", "diff(x^3 + 2x, x)"], ["english", "find the derivative of sin(x) with respect to x", "diff(sin(x), x)"], ["english", "derivative of t^3 with respect to t", "diff(t^3, t)"],
  ["english", "second derivative of x^4", "diff(x^4, x, 2)"], ["english", "the 2nd derivative of sin x", "diff(sin(x), x, 2)"], ["english", "third derivative of x^5", "diff(x^5, x, 3)"],
  ["english", "first derivative of x^2", "diff(x^2, x)"], ["english", "d/dx of x^2", "diff(x^2, x)"], ["english", "differentiate x^2 sin x", "diff(x^2 sin(x), x)"],
  ["english", "differentiate e^(2t) with respect to t", "diff(e^(2t), t)"], ["english", "derivative of f(x) = x^3", "diff(x^3, x)"], ["english", "find f'(x) if f(x) = x^3 + x", "diff(x^3 + x, x)"],
  ["english", "find dy/dx if y = x^2 + 1", "diff(x^2 + 1, x)"], ["english", "partial derivative of x^2 y with respect to y", "diff(x^2 y, y)"], ["english", "what is the derivative of ln x", "diff(ln(x), x)"],
  ["english", "antiderivative of 2x", "integrate(2x, x)"], ["english", "find the antiderivative of cos x", "integrate(cos(x), x)"], ["english", "integral of x^2", "integrate(x^2, x)"],
  ["english", "integral of x^2 dx", "integrate(x^2, x)"], ["english", "integral of t^2 dt", "integrate(t^2, t)"], ["english", "integral of x^2 from 0 to 3", "integrate(x^2, x, 0, 3)"],
  ["english", "integral from 0 to 1 of x^2", "integrate(x^2, x, 0, 1)"], ["english", "definite integral of sin x from 0 to pi", "integrate(sin(x), x, 0, pi)"], ["english", "integrate e^x", "integrate(e^x, x)"],
  ["english", "integrate x^2 from 0 to 1", "integrate(x^2, x, 0, 1)"], ["english", "integrate 1/x dx", "integrate(1/x, x)"], ["english", "indefinite integral of 1/x", "integrate(1/x, x)"],
  ["english", "area under x^2 from 0 to 1", "integrate(x^2, x, 0, 1)"], ["english", "the area under the curve y = x^3 from 0 to 2", "integrate(x^3, x, 0, 2)"],
  ["english", "limit of sin(x)/x as x approaches 0", "limit(sin(x)/x, x, 0)"], ["english", "limit of 1/x as x approaches 0 from the right", { kind: "limit", family: "one-sided-limit" }],
  ["english", "limit of 1/x as x goes to infinity", "limit(1/x, x, oo)"], ["english", "limit as x approaches 0 of sin(x)/x", "limit(sin(x)/x, x, 0)"], ["english", "lim as x -> 2 of x^2", "limit(x^2, x, 2)"],
  ["english", "limit of (1 + 1/n)^n as n tends to infinity", "limit((1+1/n)^n, n, oo)"], ["english", "limit of e^x as x approaches negative infinity", "limit(e^x, x, -oo)"],
  ["english", "sum of k^2 from k=1 to n", "sum(k^2, k, 1, n)"], ["english", "the sum of 1/n^2 from n = 1 to infinity", "sum(1/n^2, n, 1, oo)"], ["english", "sum from k = 1 to 10 of k", "sum(k, k, 1, 10)"],
  ["english", "product of k from k=1 to 5", "prod(k, k, 1, 5)"], ["english", "Taylor series of e^x at 0 to order 5", "taylor(e^x, x, 0, 5)"], ["english", "taylor series of sin x about x = 0 up to order 7", "taylor(sin(x), x, 0, 7)"],
  ["english", "Maclaurin series of cos x", "taylor(cos(x), x, 0, 5)"], ["english", "taylor polynomial of ln(x) around x = 1 of degree 3", "taylor(ln(x), x, 1, 3)"], ["english", "series expansion of 1/(1-x)", "series(1/(1-x), x, 0, 5)"],
  // simplification commands
  ["english", "expand (x+1)^3", "expand((x+1)^3)"], ["english", "factor x^2 - 9", "factor(x^2 - 9)"], ["english", "factorise x^2 + 5x + 6", "factor(x^2 + 5x + 6)"], ["english", "simplify (x^2-1)/(x-1)", "simplify((x^2-1)/(x-1))"],
  ["english", "simplify the expression 2x + 3x", "simplify(2x + 3x)"], ["english", "fully factor x^3 - x", "factor(x^3 - x)"], ["english", "expand and simplify (x+2)(x-2)", "expand((x+2)(x-2))"],
  ["english", "rationalize 1/(1 + sqrt(2))", "simplify(1/(1 + sqrt(2)))"], ["english", "reduce 12/18", "simplify(12/18)"],
  // matrices and vectors
  ["english", "determinant of the matrix [[1,2],[3,4]]", "det([[1,2],[3,4]])"], ["english", "find the determinant of [[2,0],[0,3]]", "det([[2,0],[0,3]])"], ["english", "inverse of the matrix [[2,1],[1,1]]", "inv([[2,1],[1,1]])"],
  ["english", "eigenvalues of [[2,0],[0,3]]", "eigenvalues([[2,0],[0,3]])"], ["english", "eigenvectors of the matrix [[1,0],[0,2]]", "eigenvectors([[1,0],[0,2]])"], ["english", "transpose of [[1,2],[3,4]]", "transpose([[1,2],[3,4]])"],
  ["english", "rank of [[1,2],[2,4]]", "rank([[1,2],[2,4]])"], ["english", "dot product of [1,2,3] and [4,5,6]", "dot([1,2,3],[4,5,6])"], ["english", "cross product of <1,0,0> and <0,1,0>", "cross([1,0,0],[0,1,0])"],
  // unit conversion is intercepted by quelvra.js (units.convertText) before recognition; the recogniser itself must refuse, not misread
  ["english", "convert 5 km to miles", REFUSE], ["english", "convert 100 fahrenheit to celsius", REFUSE],
  // polite and conversational framings
  ["english", "please find the derivative of x^2", "diff(x^2, x)"], ["english", "could you please integrate x^3", "integrate(x^3, x)"], ["english", "hey quelvra, solve x + 1 = 2", "x + 1 = 2"],
  ["english", "can you factor x^2 - 1 for me?", "factor(x^2 - 1)"], ["english", "I need to solve 2x = 8", "2x = 8"], ["english", "help me simplify 2x + x", "simplify(2x + x)"],
  ["english", "what is the limit of x^2 as x approaches 3?", "limit(x^2, x, 3)"], ["english", "Quelvra, what is 6 * 7?", "42"],

  // ------------------------------------------------------------ English: function analysis
  ["analysis", "domain of 1/(x-2)", "domain(1/(x-2), x)"], ["analysis", "find the domain of f(x) = sqrt(x - 1)", "domain(sqrt(x-1), x)"], ["analysis", "what is the domain of ln(x)", "domain(ln(x), x)"],
  ["analysis", "find the domain of the function g(t) = 1/t", "domain(1/t, t)"], ["analysis", "range of x^2 + 1", "range(x^2 + 1, x)"], ["analysis", "what is the range of f(x) = sin x", "range(sin(x), x)"],
  ["analysis", "zeros of x^2 - 4", "zeros(x^2 - 4, x)"], ["analysis", "find the zeros of f(x) = x^3 - x", "zeros(x^3 - x, x)"], ["analysis", "find the x-intercepts of y = x^2 - 4", "intercepts(x^2 - 4, x)"],
  ["analysis", "y-intercept of y = 2x + 3", "intercepts(2x + 3, x)"], ["analysis", "intercepts of x^2 - 1", "intercepts(x^2 - 1, x)"], ["analysis", "find the asymptotes of f(x) = 1/(x-2)", "asymptotes(1/(x-2), x)"],
  ["analysis", "vertical asymptotes of (x+1)/(x^2-1)", "asymptotes((x+1)/(x^2-1), x)"], ["analysis", "horizontal asymptote of (2x+1)/(x-3)", "asymptotes((2x+1)/(x-3), x)"],
  ["analysis", "maximum of x(10 - x)", "maximize(x(10-x), x)"], ["analysis", "find the minimum of x^2 - 4x + 1", "minimize(x^2 - 4x + 1, x)"], ["analysis", "maximum value of sin x + cos x", "maximize(sin(x) + cos(x), x)"],
  ["analysis", "maximize x(10 - x)", "maximize(x(10 - x), x)"], ["analysis", "minimize x^2 + 2x", "minimize(x^2 + 2x, x)"], ["analysis", "maximize f(t) = -t^2 + 4t", "maximize(-t^2 + 4t, t)"],
  ["analysis", "maximum of x^3 - 3x on [0, 3]", "maximize(x^3 - 3x, x, 0, 3)"], ["analysis", "local extrema of x^3 - 3x", "extrema(x^3 - 3x, x)"], ["analysis", "find the local maxima and minima of x^3 - 3x", "extrema(x^3 - 3x, x)"],
  ["analysis", "extrema of x^2 - 2x on [0, 3]", "extrema(x^2 - 2x, x, 0, 3)"], ["analysis", "relative extrema of f(x) = x^4 - 2x^2", "extrema(x^4 - 2x^2, x)"], ["analysis", "inflection points of x^3", "inflection(x^3, x)"],
  ["analysis", "find the points of inflection of f(x) = x^4 - 6x^2", "inflection(x^4 - 6x^2, x)"], ["analysis", "critical points of x^3 - 3x", "critical(x^3 - 3x, x)"], ["analysis", "find the critical numbers of f(x) = x^2 - 4x", "critical(x^2 - 4x, x)"],
  ["analysis", "where is f(x) = x^2 increasing", "monotonic(x^2, x)"], ["analysis", "where is x^3 - 3x decreasing?", "monotonic(x^3 - 3x, x)"], ["analysis", "intervals where x^2 - 4x is increasing", "monotonic(x^2 - 4x, x)"],
  ["analysis", "tangent line to x^2 at x = 2", "tangent(x^2, x, 2)"], ["analysis", "find the equation of the tangent line to y = x^3 at x = 1", "tangent(x^3, x, 1)"], ["analysis", "tangent to f(x) = sin x at x = 0", "tangent(sin(x), x, 0)"],
  ["analysis", "normal line to x^2 at x = 1", "normal(x^2, x, 1)"], ["analysis", "equation of the normal to y = x^2 at x = 2", "normal(x^2, x, 2)"], ["analysis", "inverse of f(x) = 2x + 3", "inverse(2x + 3, x)"],
  ["analysis", "find the inverse function of y = (x - 1)/2", "inverse((x-1)/2, x)"], ["analysis", "complete the square x^2 + 6x + 5", "completesquare(x^2 + 6x + 5, x)"], ["analysis", "complete the square for x^2 - 4x", "completesquare(x^2 - 4x, x)"],
  ["analysis", "partial fractions of 1/(x^2 - 1)", "apart(1/(x^2-1), x)"], ["analysis", "partial fraction decomposition of (x+3)/(x^2+x)", "apart((x+3)/(x^2+x), x)"], ["analysis", "decompose 1/(x(x+1)) into partial fractions", "apart(1/(x(x+1)), x)"],
  ["analysis", "is sin^2 x + cos^2 x = 1 an identity", "identity(sin(x)^2 + cos(x)^2, 1)"], ["analysis", "prove that sin^2 x + cos^2 x = 1", "identity(sin(x)^2 + cos(x)^2, 1)"], ["analysis", "verify that (x+1)^2 = x^2 + 2x + 1", "identity((x+1)^2, x^2 + 2x + 1)"],
  ["analysis", "show that tan x = sin x / cos x", "identity(tan(x), sin(x)/cos(x))"], ["analysis", "slope between (1,2) and (3,4)", "slope(1, 2, 3, 4)"], ["analysis", "find the slope of the line through (0, 1) and (2, 5)", "slope(0, 1, 2, 5)"],
  ["analysis", "line through (1,2) and (3,4)", "line(1, 2, 3, 4)"], ["analysis", "equation of the line passing through (0,0) and (1,3)", "line(0, 0, 1, 3)"], ["analysis", "distance between (1,2) and (4,6)", "distance(1, 2, 4, 6)"],
  ["analysis", "what is the distance from (0,0) to (3,4)", "distance(0, 0, 3, 4)"], ["analysis", "midpoint of (1,2) and (3,4)", "midpoint(1, 2, 3, 4)"], ["analysis", "midpoint between (-1, 5) and (3, -1)", "midpoint(-1, 5, 3, -1)"],
  ["analysis", "arc length of y = x^2 from 0 to 1", "arclength(x^2, x, 0, 1)"], ["analysis", "length of the curve y = x^(3/2) from 0 to 4", "arclength(x^(3/2), x, 0, 4)"], ["analysis", "arc length of sin x on [0, pi]", "arclength(sin(x), x, 0, pi)"],
  ["analysis", "area between y=x^2 and y=x", "areabetween(x^2, x, x)"], ["analysis", "area between the curves y = x and y = x^3 from 0 to 1", "areabetween(x, x^3, x, 0, 1)"], ["analysis", "area between x^2 and 2x", "areabetween(x^2, 2x, x)"],
  ["analysis", "volume of revolution of y = x^2 from 0 to 1", "volume(x^2, x, 0, 1)"], ["analysis", "volume of the solid formed by rotating y = sqrt(x) about the x-axis from 0 to 4", "volume(sqrt(x), x, 0, 4)"],
  ["analysis", "volume of the solid obtained by revolving y = x around the y-axis from 0 to 1", REFUSE], ["analysis", "average value of sin x from 0 to pi", "avgvalue(sin(x), x, 0, pi)"],
  ["analysis", "average value of f(x) = x^2 on [0, 3]", "avgvalue(x^2, x, 0, 3)"], ["analysis", "find the average value of t^2 over [0, 2]", "avgvalue(t^2, t, 0, 2)"],
  ["analysis", "domain(1/x, x)", "domain(1/x, x)"], ["analysis", "asymptotes(1/(x-1), x)", { kind: "command", command: "asymptotes" }], ["analysis", "extrema(x^3 - 3x, x)", { kind: "command", command: "extrema" }],
  ["analysis", "tangent(x^2, x, 1)", { kind: "command", command: "tangent" }], ["analysis", "maximize(x(10-x), x)", { kind: "command", command: "maximize" }], ["analysis", "areabetween(x^2, x, x, 0, 1)", { kind: "command", command: "areabetween" }],
  ["analysis", "apart(1/(x^2-1), x)", { kind: "command", command: "apart" }], ["analysis", "completesquare(x^2 + 2x, x)", { kind: "command", command: "completesquare" }], ["analysis", "zeros of e^x", "zeros(e^x, x)"],
  ["analysis", "domain of sqrt(t - 3)", "domain(sqrt(t-3), t)"], ["analysis", "range of e^(-y^2)", "range(e^(-y^2), y)"],

  // ------------------------------------------------------------ word problems
  ["word", "a number plus 7 is 19", "x + 7 = 19"], ["word", "twice a number minus 3 is 11", "2x - 3 = 11"], ["word", "3 times a number is 27", "3x = 27"],
  ["word", "the sum of two numbers is 20 and their difference is 4", "x + y = 20, x - y = 4"], ["word", "the sum of three consecutive integers is 72", "n + (n+1) + (n+2) = 72"],
  ["word", "the sum of two consecutive integers is 41", "n + (n+1) = 41"], ["word", "the sum of three consecutive odd integers is 51", "n + (n+2) + (n+4) = 51"],
  ["word", "find two consecutive integers whose sum is 41", "n + (n+1) = 41"], ["word", "three consecutive even numbers add up to 48", "n + (n+2) + (n+4) = 48"],
  ["word", "Tom is 4 years older than Ann. In 5 years, Tom will be twice as old as Ann. How old is Ann now?", "(y + 4) + 5 = 2(y + 5)"],
  ["word", "Maria is 3 times as old as her son. The sum of their ages is 48. How old is her son?", "3y + y = 48"],
  ["word", "a car travels 120 km in 2 hours. what is its speed", "120/2"], ["word", "how long does it take to travel 300 km at 60 km/h", "300/60"],
  ["word", "how far does a car travel in 3 hours at 50 km/h", "3*50"],
  ["word", "what is the simple interest on $1000 at 5% per year for 3 years", "1000*5/100*3"], ["word", "simple interest on 500 at 4% for 2 years", "500*4/100*2"],
  ["word", "$1000 is invested at 5% compounded annually for 10 years. what is the final amount", "1000 (1 + 5/(100*1))^(1*10)"],
  ["word", "a rectangle has perimeter 30 and length is 3 more than width. find the dimensions", "2(w + 3) + 2w = 30"],
  ["word", "a rectangle has length 5 and width 3. what is its area", "5*3"], ["word", "a rectangle has length 5 and width 3. what is its perimeter", "2(5 + 3)"],
  ["word", "the length of a rectangle is twice its width and its perimeter is 36. find the width", "2(2w) + 2w = 36"],
  ["word", "how many liters of a 20% solution must be mixed with 10 liters of a 50% solution to get a 30% solution", "20/100 x + 50/100*10 = 30/100 (x + 10)"],
  ["word", "a train leaves at 3pm going 60 mph. when does it arrive?", REFUSE], ["word", "john has some apples and gives some away. how many does he have", REFUSE],
  ["word", "a rectangle is big. find its area", REFUSE], ["word", "the sum of some numbers is large", REFUSE], ["word", "two trains leave stations. which is faster", REFUSE],
  ["word", "a number is multiplied by something. what is it", REFUSE], ["word", "how old is the universe", REFUSE], ["word", "if I have 3 cats and 2 dogs how many legs", REFUSE],

  // ------------------------------------------------------------ must refuse
  ["refuse", "tell me a joke", REFUSE], ["refuse", "what is love", REFUSE], ["refuse", "what is the meaning of life", REFUSE], ["refuse", "tell me a story about dragons", REFUSE],
  ["refuse", "asdfghjkl", REFUSE], ["refuse", "qwerty uiop", REFUSE], ["refuse", "print('hello world')", REFUSE], ["refuse", "for (i = 0; i < 10; i++) { sum += i }", REFUSE],
  ["refuse", "def f(x): return x", REFUSE], ["refuse", "SELECT * FROM users", REFUSE], ["refuse", "console.log(x)", REFUSE], ["refuse", "import numpy as np", REFUSE],
  ["refuse", "<div>hello</div>", REFUSE], ["refuse", "rm -rf /", REFUSE], ["refuse", "what is the capital of France", REFUSE], ["refuse", "how are you", REFUSE],
  ["refuse", "who are you", REFUSE], ["refuse", "good morning", REFUSE], ["refuse", "why is the sky blue", REFUSE], ["refuse", "my name is John", REFUSE],
  ["refuse", "John", REFUSE], ["refuse", "Alice and Bob", REFUSE], ["refuse", "the quick brown fox", REFUSE], ["refuse", "banana", REFUSE],
  ["refuse", "I love math", REFUSE], ["refuse", "solve my problems", REFUSE], ["refuse", "find my keys", REFUSE], ["refuse", "integrate the team", REFUSE],
  ["refuse", "differentiate between cats and dogs", REFUSE], ["refuse", "limit of my patience", REFUSE], ["refuse", "factor in the cost", REFUSE], ["refuse", "plot twist", REFUSE],
  ["refuse", "expand the business", REFUSE], ["refuse", "simplify your life", REFUSE], ["refuse", "the sum of all fears", REFUSE], ["refuse", "what is the derivative of love", REFUSE],
  ["refuse", "Paris", REFUSE], ["refuse", "what's up", REFUSE], ["refuse", "open the door", REFUSE], ["refuse", "let me think", REFUSE],
  ["refuse", "x = foo(bar)", REFUSE], ["refuse", "while true do", REFUSE], ["refuse", "hello world", REFUSE], ["refuse", "what time is it", REFUSE],
  ["refuse", "domain of expertise", REFUSE], ["refuse", "range of motion", REFUSE], ["refuse", "prove that you are smart", REFUSE], ["refuse", "inverse of love", REFUSE],
  ["refuse", "maximize profit", REFUSE], ["refuse", "the area of my house", REFUSE], ["refuse", "volume of music", REFUSE], ["refuse", "the slope of the hill", REFUSE],
  ["refuse", "tangent line to happiness at x = 2", REFUSE], ["refuse", "is it prime time", REFUSE], ["refuse", "calculate my taxes", REFUSE], ["refuse", "evaluate the situation", REFUSE],
  ["refuse", "what is the square root of evil", REFUSE], ["refuse", "Theorem: every cat is black", REFUSE], ["refuse", "lorem ipsum dolor sit amet", REFUSE], ["refuse", "please help", REFUSE],
];

for (const e of CORPUS) {
  test(`recognition [${e[0]}] ${e[1]}`, () => {
    const r = check(e);
    ok(r.pass, `${e[1]} -> ${r.got}`);
  });
}
test("recognition corpus has at least 400 inputs", () => ok(CORPUS.length >= 400, `only ${CORPUS.length}`));
