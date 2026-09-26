// Quelvra polynomial engine (public entry point).
//   poly-core.js    representations, arithmetic, gcd family, resultants, Sturm / real roots,
//                   interpolation, multivariate (sparse + recursive) arithmetic, tree conversion
//   poly-factor.js  factorisation over Q (Zassenhaus, Kronecker), factorTree, factorSteps
//   poly-roots.js   closed-form roots, solvePolynomial, complex roots (Aberth)
//   poly-apart.js   partial fractions, cancel
export * from "./poly-core.js";
export * from "./poly-factor.js";
export * from "./poly-roots.js";
export * from "./poly-apart.js";
