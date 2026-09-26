// Quelvra research lab: the moving sofa problem (Moser 1966).
//
// What is the largest area of a rigid planar shape that can be moved around a right-angled corner in a
// hallway of width 1? Exact areas are given for the semicircle and Hammersley's sofa; Gerver's sofa is
// reproduced partially (its four defining parameters are solved here) and its area constant is quoted from
// the literature, clearly marked as such.

import { asBudget } from "./budget.js";

export const GERVER_AREA = "2.21953166887197";   // Gerver (1992); value as reported by Romik (2018)
export const UPPER_BOUND = "2.37";                // Kallus and Romik (2018), computer-assisted proof

// Gerver's system for (A, B, phi, theta) (see Romik 2018, "Differential equations and exact solutions in the moving sofa problem").
function gerverF([A, B, p, t]) {
  const { cos, sin } = Math;
  return [
    A * (cos(t) - cos(p)) - 2 * B * sin(p) + (t - p - 1) * cos(t) - sin(t) + cos(p) + sin(p),
    A * (3 * sin(t) + sin(p)) - 2 * B * cos(p) + 3 * (t - p - 1) * sin(t) + 3 * cos(t) - sin(p) + cos(p),
    A * cos(p) - (sin(p) + 0.5 - 0.5 * cos(p) + B * sin(p)),
    (A + Math.PI / 2 - p - t) - (B - 0.5 * (t - p) * (1 + A) - 0.25 * (t - p) ** 2),
  ];
}
export function gerverParameters() {
  let x = [0.1, 1.4, 0.04, 0.7];
  let res = Infinity, it = 0;
  for (; it < 60; it++) {
    const f = gerverF(x);
    res = Math.max(...f.map(Math.abs));
    if (res < 1e-15) break;
    const M = [0, 1, 2, 3].map((i) => [0, 0, 0, 0, -f[i]]);
    for (let j = 0; j < 4; j++) {
      const h = 1e-7 * Math.max(1, Math.abs(x[j]));
      const y = x.slice(); y[j] += h;
      const fp = gerverF(y); y[j] = x[j] - h; const fm = gerverF(y);
      for (let i = 0; i < 4; i++) M[i][j] = (fp[i] - fm[i]) / (2 * h);
    }
    for (let c = 0; c < 4; c++) {
      let p = c; for (let r = c + 1; r < 4; r++) if (Math.abs(M[r][c]) > Math.abs(M[p][c])) p = r;
      [M[c], M[p]] = [M[p], M[c]];
      for (let r = 0; r < 4; r++) if (r !== c) { const q = M[r][c] / M[c][c]; for (let k = c; k < 5; k++) M[r][k] -= q * M[c][k]; }
    }
    for (let i = 0; i < 4; i++) x[i] += M[i][4] / M[i][i];
  }
  const [A, B, phi, theta] = x;
  return { A, B, phi, theta, residual: Math.max(...gerverF(x).map(Math.abs)), iterations: it };
}

// Hammersley's sofa, independent numerical area from its height profile h(x) (symmetric in x):
//   |x| <= r:          h = 1 - sqrt(r^2 - x^2)    (block minus the removed half disc), r = 2/pi
//   r < |x| <= r + 1:  h = sqrt(1 - (|x| - r)^2)  (quarter discs)
// integrated by Simpson's rule after the substitutions x = r sin(u) and x = r + sin(u), which remove the
// square-root endpoint singularities (so the quadrature converges fast).
export function hammersleyAreaNumeric(n = 2000) {
  const r = 2 / Math.PI;
  const simpson = (f, a, b, m) => { const dx = (b - a) / m; let s = f(a) + f(b); for (let i = 1; i < m; i++) s += (i % 2 ? 4 : 2) * f(a + i * dx); return (s * dx) / 3; };
  const inner = simpson((u) => (1 - r * Math.cos(u)) * r * Math.cos(u), 0, Math.PI / 2, n);   // int_0^r h dx
  const outer = simpson((u) => Math.cos(u) * Math.cos(u), 0, Math.PI / 2, n);                   // int_r^{r+1} h dx
  return 2 * (inner + outer);
}

export function movingSofa(opts = {}) {
  const budget = asBudget(opts, "moving sofa");
  const g = gerverParameters();
  const semicircle = Math.PI / 2;
  const hammersley = Math.PI / 2 + 2 / Math.PI;
  budget.tick(1);
  return {
    semicircle: { exact: "pi/2", value: semicircle, note: "a half disc of radius 1 rotates around the corner" },
    hammersley: { exact: "pi/2 + 2/pi", value: hammersley, numeric: hammersleyAreaNumeric(), note: "Hammersley (1968): two quarter discs of radius 1 joined by a 4/pi by 1 block with a half disc of radius 2/pi removed" },
    gerver: { value: GERVER_AREA, source: "Gerver (1992); constant as reported by Romik (2018). Quoted from the literature, not recomputed here.", parameters: g,
      note: "Gerver's sofa is bounded by 18 analytic curve pieces; Quelvra recomputes the solution of its four defining equations for A, B, phi, theta." },
    upperBound: { value: UPPER_BOUND, source: "Kallus and Romik (2018), computer-assisted proof that the maximal area is at most 2.37" },
    status: "Gerver's sofa is conjectured to be optimal. In late 2024 Jineon Baek posted a claimed proof that Gerver's sofa is optimal; it is a claimed proof under review, and Quelvra does not treat the problem as settled.",
    ms: budget.elapsed(),
  };
}
