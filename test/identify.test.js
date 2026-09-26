import { test, eq } from "./harness.js";
import { parse } from "../public/engine/parse.js";
import { classify } from "../public/engine/identify.js";

const cases = [
  ["2x+3=7", "equation", "linear"], ["x^2-5x+6=0", "equation", "quadratic"], ["x^3=8", "equation", "cubic"],
  ["x^4-1=0", "equation", "quartic"], ["x^5+x=1", "equation", "polynomial"],
  ["sqrt(x+1)=3", "equation", "radical"], ["|x-2|<5", "inequality", "absolute-value"], ["2^x=8", "equation", "exponential"],
  ["ln(x)=2", "equation", "logarithmic"], ["sin(x)=1/2", "equation", "trigonometric"], ["x=cos(x)", "equation", "transcendental"],
  ["x e^x = 1", "equation", "transcendental"], ["1/x+1=3", "equation", "rational"], ["2x+y=5, x-y=1", "system", "linear-system"],
  ["x^2+y^2=1, y=x", "system", "nonlinear-system"], ["xy=1, x+y=3", "system", "nonlinear-system"],
  ["d/dx x^2", "derivative", "derivative"], ["int x dx", "integral", "indefinite-integral"],
  ["int_0^1 x dx", "integral", "definite-integral"], ["int_1^oo 1/x^2 dx", "integral", "improper-integral"],
  ["lim x->0 sin(x)/x", "limit", "limit"], ["lim x->oo 1/x", "limit", "limit-at-infinity"], ["3+4", "arithmetic", "arithmetic"],
  ["x^2+2x", "expression", "polynomial"], ["a x + b = 0", "equation", "linear"], ["sum_(n=1)^oo 1/n^2", "sum", "infinite-series"],
  ["[[1,2],[3,4]]", "matrix", "matrix"], ["f(x)=x^2", "function-definition", "function"], ["solve(x^2=4, x)", "equation", "quadratic"],
  ["x^2 - 4 > 0", "inequality", "quadratic"], ["2 = 2", "equation", "constant"],
];
for (const [src, kind, family] of cases) test(`classify ${src}`, () => { const c = classify(parse(src)); eq(c.kind, kind, src); eq(c.family, family, src); });
test("classify picks x over a", () => eq(classify(parse("a x^2 + b x + c = 0")).unknowns[0], "x"));
test("classify explicit variable", () => eq(classify(parse("a x + b = 0"), { variable: "a" }).unknowns[0], "a"));
