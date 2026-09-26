// Advanced continuous mathematics: the call-form command names.
//
// parse.js registers these as bracket-only whole-word function names and identify.js as commands
// (one small block in each); strategies/advanced-continuous.js implements them. No dependencies,
// so both shared files can import it without cycles.

export const ADVANCED_CONTINUOUS_COMMANDS = [
  // multivariable calculus
  "pdiff", "grad", "dirderiv", "jacobian", "jacobiandet", "hessian", "laplacian", "totaldiff", "tangentplane", "lagrange",
  "dblint", "tplint", "polarint", "cylint", "sphint",
  // vector calculus
  "div", "curl", "lineint", "conservative", "potential", "surfint", "flux",
  // transforms
  "laplace", "invlaplace", "lapsolve", "fourier", "fouriertransform", "ztransform",
  // complex analysis
  "residue", "laurent", "contourint", "residueint", "analytic", "cauchyriemann",
  // numerical methods
  "newton", "bisection", "secant", "fixedpoint", "trapezoid", "simpson", "eulermethod", "rungekutta", "poweriter",
  // curves
  "curvature", "torsion", "unittangent", "unitnormal", "binormal", "arcparam",
  // PDE basics
  "pdecheck", "classifypde", "heat", "wave",
];
// functions (not commands) that the advanced modules understand inside expressions
export const ADVANCED_CONTINUOUS_FUNCTIONS = ["heaviside"];
