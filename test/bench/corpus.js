// Quelvra benchmark corpus. Each entry: [category, input, expected, options?]
// expected forms:
//   { value: "expr" }                 single exact value / expression (compared by equivalence)
//   { roots: ["2", "3"], var: "x" }   full solution set of an equation (order-free, exact or approx)
//   { none: true }                    no real solution
//   { set: "x < -2 or x > 2", var }   solution set of an inequality (compared by probing)
//   { system: {x: "2", y: "1"} }      unique solution of a system
//   { anti: "x^3/3" , var: "x" }      antiderivative (compared up to a constant)
//   { approx: 0.739085133, tol: 1e-8 } numeric value
//   { refuse: true }                  must NOT produce an answer
// The metric counts only answers that are both correct AND verified by Quelvra.

export const CORPUS = [
  // ---------- arithmetic ----------
  ["arith", "1/3 + 1/6", { value: "1/2" }], ["arith", "2^64", { value: "18446744073709551616" }], ["arith", "0.1 + 0.2", { value: "3/10" }],
  ["arith", "sqrt(50) - sqrt(8)", { value: "3sqrt(2)" }], ["arith", "(2/3)^(-2)", { value: "9/4" }], ["arith", "20!", { value: "2432902008176640000" }],
  ["arith", "sin(pi/6) + cos(pi/3)", { value: "1" }], ["arith", "log_2(1024)", { value: "10" }], ["arith", "e^(ln(7))", { value: "7" }],
  ["arith", "|-5| + |3 - 10|", { value: "12" }], ["arith", "gcd(84, 126)", { value: "42" }], ["arith", "binomial(52, 5)", { value: "2598960" }],
  ["arith", "i^7", { value: "-i" }], ["arith", "27^(2/3)", { value: "9" }], ["arith", "1/(sqrt(3) - 1)", { value: "(sqrt(3) + 1)/2" }],
  ["arith", "15% of 80", { value: "12" }], ["arith", "what is 15% of 80", { value: "12" }], ["arith", "tan(pi/4)^2 + 1", { value: "2" }],

  // ---------- simplification ----------
  ["simp", "(x+1)^2 - x^2", { value: "2x + 1" }], ["simp", "(x^2 - 1)/(x - 1)", { value: "x + 1" }], ["simp", "x/x^3", { value: "1/x^2" }],
  ["simp", "sin(x)^2 + cos(x)^2", { value: "1" }], ["simp", "2x + 3x - x", { value: "4x" }], ["simp", "expand (a+b)^3", { value: "a^3 + 3a^2 b + 3a b^2 + b^3" }],
  ["simp", "1/x + 1/(x+1)", { value: "(2x+1)/(x(x+1))" }], ["simp", "sqrt(x^2)", { value: "|x|" }], ["simp", "ln(e^(3x))", { value: "3x" }],
  ["simp", "factor x^2 - 5x + 6", { value: "(x-2)(x-3)" }], ["simp", "factor x^3 - 8", { value: "(x-2)(x^2+2x+4)" }], ["simp", "factor x^4 - 1", { value: "(x-1)(x+1)(x^2+1)" }],

  // ---------- linear equations ----------
  ["linear", "2x + 3 = 7", { roots: ["2"] }], ["linear", "3(x - 2) = 2x + 5", { roots: ["11"] }], ["linear", "x/3 + 1 = 5", { roots: ["12"] }],
  ["linear", "0.5x - 2 = 1.5", { roots: ["7"] }], ["linear", "5 - 2x = 3x + 20", { roots: ["-3"] }], ["linear", "x + 1 = x + 2", { none: true }],
  ["linear", "a number plus 7 is 19", { roots: ["12"] }], ["linear", "twice a number minus 3 is 11", { roots: ["7"] }],
  ["linear", "the sum of three consecutive integers is 72", { system: { a: "23", b: "24", c: "25" } }], ["linear", "solve a x + b = c for x", { roots: ["(c - b)/a"] }],

  // ---------- quadratics ----------
  ["quad", "x^2 - 5x + 6 = 0", { roots: ["2", "3"] }], ["quad", "x^2 = 2", { roots: ["sqrt(2)", "-sqrt(2)"] }], ["quad", "x^2 + 1 = 0", { none: true }],
  ["quad", "2x^2 + 3x - 2 = 0", { roots: ["1/2", "-2"] }], ["quad", "x^2 - 6x + 9 = 0", { roots: ["3"] }], ["quad", "x^2 + 4x + 1 = 0", { roots: ["-2 + sqrt(3)", "-2 - sqrt(3)"] }],
  ["quad", "x^2 = 3x", { roots: ["0", "3"] }], ["quad", "(x - 1)(x + 4) = 0", { roots: ["1", "-4"] }], ["quad", "x(x+2) = 15", { roots: ["3", "-5"] }],
  ["quad", "x^2 + 1 = 0", { roots: ["i", "-i"] }, { domain: "complex" }],

  // ---------- polynomials ----------
  ["poly", "x^3 - 6x^2 + 11x - 6 = 0", { roots: ["1", "2", "3"] }], ["poly", "x^3 = 8", { roots: ["2"] }], ["poly", "x^4 - 5x^2 + 4 = 0", { roots: ["1", "-1", "2", "-2"] }],
  ["poly", "x^3 - 2 = 0", { roots: ["cbrt(2)"] }], ["poly", "x^5 - x - 1 = 0", { roots: ["1.1673039782614187"] }], ["poly", "x^4 + 1 = 0", { none: true }],
  ["poly", "2x^3 - 3x^2 - 11x + 6 = 0", { roots: ["3", "-2", "1/2"] }],

  // ---------- rational / radical / abs ----------
  ["rational", "1/x + 1/2 = 1", { roots: ["2"] }], ["rational", "x/(x-1) = 1/(x-1)", { none: true }], ["rational", "(x^2-4)/(x-2) = 5", { roots: ["3"] }],
  ["radical", "sqrt(x + 2) = x", { roots: ["2"] }], ["radical", "sqrt(2x + 3) = 3", { roots: ["3"] }], ["radical", "sqrt(x) = -1", { none: true }],
  ["radical", "sqrt(x+5) - sqrt(x) = 1", { roots: ["4"] }],
  ["abs", "|x - 3| = 5", { roots: ["8", "-2"] }], ["abs", "|2x + 1| = -3", { none: true }], ["abs", "|x| = |2x - 3|", { roots: ["1", "3"] }],

  // ---------- exponential / log ----------
  ["explog", "2^x = 8", { roots: ["3"] }], ["explog", "e^x = 5", { roots: ["ln(5)"] }], ["explog", "3^(2x-1) = 27", { roots: ["2"] }],
  ["explog", "ln(x) = 2", { roots: ["e^2"] }], ["explog", "log_2(x) + log_2(x - 2) = 3", { roots: ["4"] }], ["explog", "ln(x) + ln(x - 2) = ln(3)", { roots: ["3"] }],
  ["explog", "4^x - 3*2^x + 2 = 0", { roots: ["0", "1"] }], ["explog", "2^x = 3^(x-1)", { roots: ["ln(3)/(ln(3) - ln(2))"] }],

  // ---------- trig ----------
  ["trig", "sin(x) = 1/2", { general: true, contains: ["pi/6", "5pi/6"] }], ["trig", "2cos(x) - 1 = 0", { general: true, contains: ["pi/3", "-pi/3"] }],
  ["trig", "tan(x) = 1", { general: true, contains: ["pi/4"] }], ["trig", "sin(x) = 2", { none: true }],

  // ---------- transcendental (numeric, certified) ----------
  ["numeric", "x = cos(x)", { roots: ["0.7390851332151607"] }], ["numeric", "x e^x = 1", { roots: ["0.5671432904097838"] }],
  ["numeric", "e^x = 3 - x", { roots: ["0.7920599064083"] }],

  // ---------- inequalities ----------
  ["ineq", "2x + 1 > 5", { set: "x > 2" }], ["ineq", "-2x < 6", { set: "x > -3" }], ["ineq", "x^2 - 4 > 0", { set: "x < -2 or x > 2" }],
  ["ineq", "x^2 <= 9", { set: "-3 <= x and x <= 3" }], ["ineq", "|x - 1| < 3", { set: "-2 < x and x < 4" }], ["ineq", "(x-1)/(x+2) >= 0", { set: "x < -2 or x >= 1" }],
  ["ineq", "x^2 + 1 < 0", { set: "x != x" }],

  // ---------- systems ----------
  ["system", "2x + y = 5, x - y = 1", { system: { x: "2", y: "1" } }], ["system", "x + y + z = 6, x - y = 0, x + z = 4", { system: { x: "2", y: "2", z: "2" } }],
  ["system", "x + y = 2, 2x + 2y = 5", { none: true }], ["system", "the sum of two numbers is 20 and their difference is 4", { system: { x: "12", y: "8" } }],
  ["system", "x^2 + y^2 = 25, y = x + 1", { solutions: [{ x: "3", y: "4" }, { x: "-4", y: "-3" }] }],

  // ---------- derivatives ----------
  ["diff", "d/dx x^3", { value: "3x^2" }], ["diff", "d/dx sin(x^2)", { value: "2x cos(x^2)" }], ["diff", "d/dx x ln(x)", { value: "ln(x) + 1" }],
  ["diff", "d/dx e^(2x)", { value: "2e^(2x)" }], ["diff", "d/dx (x^2+1)/(x-1)", { value: "(x^2 - 2x - 1)/(x-1)^2" }], ["diff", "d/dx x^x", { value: "x^x (ln(x) + 1)" }],
  ["diff", "derivative of tan(x)", { value: "sec(x)^2" }], ["diff", "d/dx atan(x)", { value: "1/(1+x^2)" }],

  // ---------- integrals ----------
  ["int", "int x^2 dx", { anti: "x^3/3" }], ["int", "int cos(x) dx", { anti: "sin(x)" }], ["int", "int 1/x dx", { anti: "ln(|x|)" }],
  ["int", "int e^(3x) dx", { anti: "e^(3x)/3" }], ["int", "int x e^x dx", { anti: "(x - 1) e^x" }], ["int", "int 2x cos(x^2) dx", { anti: "sin(x^2)" }],
  ["int", "int 1/(x^2 + 1) dx", { anti: "atan(x)" }], ["int", "int 1/(x^2 - 1) dx", { anti: "ln(|x - 1|)/2 - ln(|x + 1|)/2" }], ["int", "int ln(x) dx", { anti: "x ln(x) - x" }],
  ["int", "int sin(x)^2 dx", { anti: "x/2 - sin(2x)/4" }], ["int", "int_0^1 x^2 dx", { value: "1/3" }], ["int", "int_0^pi sin(x) dx", { value: "2" }],
  ["int", "int_1^oo 1/x^2 dx", { value: "1" }], ["int", "int_0^1 e^(-x^2) dx", { approx: 0.7468241328124270, tol: 1e-10 }], ["int", "integral of x from 0 to 4", { value: "8" }],
  ["int", "int sqrt(1 - x^2) dx", { anti: "(x sqrt(1-x^2) + asin(x))/2" }], ["int", "int 1/sqrt(1 - x^2) dx", { anti: "asin(x)" }],

  // ---------- limits ----------
  ["lim", "lim x->0 sin(x)/x", { value: "1" }], ["lim", "lim x->oo (3x^2 + 1)/(x^2 - 2)", { value: "3" }], ["lim", "lim x->0 (1 - cos(x))/x^2", { value: "1/2" }],
  ["lim", "lim x->oo (1 + 1/x)^x", { value: "e" }], ["lim", "lim x->2 (x^2 - 4)/(x - 2)", { value: "4" }], ["lim", "lim_(x->0^+) 1/x", { value: "oo" }],
  ["lim", "lim x->0 1/x", { value: "undefined" }], ["lim", "lim x->0 x ln(x)", { value: "0" }], ["lim", "lim x->oo x/e^x", { value: "0" }],

  // ---------- series / sums ----------
  ["sum", "sum_(i=1)^(100) i", { value: "5050" }], ["sum", "sum_(n=1)^(oo) 1/n^2", { value: "pi^2/6" }], ["sum", "sum_(k=0)^(oo) (1/2)^k", { value: "2" }],
  ["sum", "sum_(i=1)^(n) i", { value: "n(n+1)/2" }],

  // ---------- linear algebra ----------
  ["linalg", "det([[1,2],[3,4]])", { value: "-2" }], ["linalg", "inv([[2,1],[1,1]])", { value: "[[1,-1],[-1,2]]" }], ["linalg", "rank([[1,2],[2,4]])", { value: "1" }],

  // ---------- number theory / stats ----------
  ["nt", "is 97 prime", { value: "true" }], ["nt", "prime factorization of 360", { value: "2^3 * 3^2 * 5" }], ["nt", "lcm(4, 6, 10)", { value: "60" }],
  ["stats", "mean of 3, 5, 7, 9", { value: "6" }], ["stats", "median(1, 9, 3, 7)", { value: "5" }],


  // ---------- LLM-hard (expected values from an independent oracle, checked offline) ----------
  ["hard", "3^200 mod 1000003", { value: "333986" }], ["hard", "2^127 - 1", { value: "170141183460469231731687303715884105727" }],
  ["hard", "factorint(2^64 + 1)", { value: "274177 * 67280421310721" }], ["hard", "isprime(2^89 - 1)", { value: "true" }],
  ["hard", "isprime(3215031751)", { value: "false" }], ["hard", "gcd(2^120 - 1, 2^84 - 1)", { value: "4095" }], ["hard", "100!/98!", { value: "9900" }],
  ["hard", "binomial(100, 50)", { value: "100891344545564193334812497256" }],
  ["hard", "det([[2,-1,0,3,1],[1,4,2,-2,0],[0,3,5,1,-1],[3,0,-2,4,2],[1,1,1,1,1]])", { value: "72" }],
  ["hard", "sqrt(3 + 2sqrt(2))", { value: "1 + sqrt(2)" }], ["hard", "sum_(k=1)^(1000) k^3", { value: "250500250000" }],
  ["hard", "d/dx x^(x^x)", { value: "x^(x^x) (x^x (ln(x) + 1) ln(x) + x^x/x)" }],
  ["hard", "x^3 - 3x + 1 = 0", { roots: ["2cos(2pi/9)", "2cos(4pi/9)", "2cos(8pi/9)"] }],
  ["hard", "x^4 - 10x^2 + 1 = 0", { roots: ["sqrt(3) - sqrt(2)", "sqrt(2) - sqrt(3)", "sqrt(3) + sqrt(2)", "-sqrt(3) - sqrt(2)"] }],
  ["hard", "sqrt(x + 7) = x - 5", { roots: ["9"] }], ["hard", "x^2/(x-2) = 4/(x-2)", { roots: ["-2"] }],
  ["hard", "2^x = x^2", { roots: ["2", "4", "-0.766664695962123"] }],
  ["hard", "int 1/(x^4 + 1) dx", { anti: "sqrt(2)/8 ln(x^2 + sqrt(2)x + 1) - sqrt(2)/8 ln(x^2 - sqrt(2)x + 1) + sqrt(2)/4 atan(sqrt(2)x + 1) + sqrt(2)/4 atan(sqrt(2)x - 1)" }],
  ["hard", "int_0^(2pi) 1/(2 + cos(x)) dx", { value: "2pi/sqrt(3)" }], ["hard", "int_(-1)^1 1/x^2 dx", { diverges: true }],
  ["hard", "lim x->0 (tan(x) - sin(x))/x^3", { value: "1/2" }], ["hard", "lim x->oo (1 + 1/x)^(x^2) e^(-x)", { value: "e^(-1/2)" }],
  ["hard", "sum_(n=1)^(oo) 1/n^4", { value: "pi^4/90" }], ["hard", "(x+1)/(x-1) > 2", { set: "1 < x and x < 3" }],
  ["hard", "x^2 + y^2 = 5, x y = 2", { solutions: [{ x: "1", y: "2" }, { x: "2", y: "1" }, { x: "-1", y: "-2" }, { x: "-2", y: "-1" }] }],
  // ---------- must refuse / must not guess ----------
  ["refuse", "tell me a joke", { refuse: true }], ["refuse", "what is the meaning of life", { refuse: true }], ["refuse", "(x + 1", { refuse: true }],
  ["refuse", "5 m + 3 s", { refuse: true }],
];
