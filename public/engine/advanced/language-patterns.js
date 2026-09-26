// Plain-English phrasings for the advanced continuous commands. language.js spreads these at the
// START of its PATTERNS list (they are specific enough not to shadow the existing patterns: each
// build() returns null when the phrase is not really about its command).
//
// H: helpers from language.js (expr, mathOf, bound, guessVar, looksLikeMath).

import { parse } from "../parse.js";

export function advancedPatterns(H) {
  const { expr, mathOf, bound, looksLikeMath } = H;
  // split at top-level commas
  const splitTop = (s) => {
    const out = [];
    let depth = 0, cur = "";
    for (const ch of s) {
      if ("([{".includes(ch)) depth++;
      if (")]}".includes(ch)) depth--;
      if (ch === "," && depth === 0) { out.push(cur); cur = ""; } else cur += ch;
    }
    out.push(cur);
    return out.map((t) => t.trim()).filter((t) => t.length);
  };
  // "(a, b)", "<a, b>", "[a, b]", "⟨a, b⟩" -> "[a, b]" in math text
  const vec = (s0) => {
    let s = String(s0).trim().replace(/^(?:the )?(?:vector )?(?:field )?(?:[A-Za-z]\s*(?:\(\s*[a-z](?:\s*,\s*[a-z])*\s*\))?\s*=\s*)?/i, "");
    const m = s.match(/^[(<[⟨]\s*(.+?)\s*[)>\]⟩]$/);
    if (!m) return null;
    const parts = splitTop(m[1]).map((p) => mathOf(p));
    if (parts.length < 2 || parts.some((p) => !p)) return null;
    return `[${parts.join(", ")}]`;
  };
  // "f(x, y) = body", "f = body", "z = body", "u = body" or just the body
  const fn = (s0) => {
    let s = String(s0).trim().replace(/^(?:the )?(?:function|expression|scalar field)\s+/i, "");
    let m;
    if ((m = s.match(/^[a-zA-Z]\s*\(\s*[a-z](?:\s*,\s*[a-z])*\s*\)\s*=\s*(.+)$/))) s = m[1];
    else if ((m = s.match(/^[fgzuwFG]\s*=\s*(.+)$/))) s = m[1];
    const t = mathOf(s);
    return t && !/[=<>]/.test(t) ? t : null;
  };
  const vars = (t) => { try { const set = new Set(); const walk = (u) => { if (u.k === "sym") set.add(u.name); for (const a of u.args || []) walk(a); }; walk(parse(t)); return set; } catch (_) { return new Set(); } };
  const multi = (t) => [...vars(t)].filter((v) => ["x", "y", "z", "w"].includes(v)).length >= 2;
  const varList = (s) => String(s).split(/\s*(?:,|\band then\b|\bthen\b|\band\b)\s*/).map((v) => v.trim()).filter(Boolean);
  const cmd = (name, args, interpretation, goal = name) => ({ math: `${name}(${args.join(", ")})`, goal, interpretation: interpretation || `${name}(${args.join(", ")})` });
  const FIND = String.raw`(?:(?:find|compute|calculate|determine|evaluate|what is|give|get|state)\s+)?(?:the\s+)?`;
  const P = String.raw`([(<[⟨][^()<>[\]⟨⟩]*[)>\]⟩])`;
  const V = String.raw`([(<[⟨](?:[^()<>[\]⟨⟩]|\([^()]*\))*[)>\]⟩])`;
  const eqMath = (s) => { const t = mathOf(s); return t && /=/.test(t) ? t : null; };
  const lhsMinusRhs = (t) => { const m = t.match(/^(.+?)=(.+)$/); return m ? `${m[1].trim()} - (${m[2].trim()})` : t; };
  const ORD = { first: 1, second: 2, third: 3 };

  const pats = [
    // ---------------- multivariable: partial derivatives
    { id: "partial", re: new RegExp(`^${FIND}(first |second |third )?(?:order )?(?:mixed )?partial derivatives? of (.+?) with respect to (.+)$`, "i"),
      build: (m) => {
        const f = fn(m[2]); if (!f) return null;
        let vs = varList(m[3].replace(/\btwice\b/i, "").trim());
        if (!vs.length || vs.some((v) => !/^[a-z]$|^theta$/.test(v))) return null;
        const ord = m[1] ? ORD[m[1].trim().toLowerCase()] : null;
        if (ord && vs.length === 1) vs = Array(ord).fill(vs[0]);
        if (/\btwice\b/i.test(m[3]) && vs.length === 1) vs = [vs[0], vs[0]];
        if (ord && vs.length !== ord) return null;
        if (vs.length === 1) return null; // a first-order partial is the core diff(f, v) (language.js handles it)
        return cmd("pdiff", [f, ...vs], `partial derivative of ${f} with respect to ${vs.join(", then ")}`);
      } },
    { id: "partial", re: /^(?:find |compute )?f_([a-z]{1,4}) (?:of|for) (.+)$/i,
      build: (m) => { const f = fn(m[2]); return f ? cmd("pdiff", [f, ...m[1].split("")], `f_${m[1]} for f = ${f}`) : null; } },
    { id: "gradient", re: new RegExp(`^${FIND}(?:gradient|grad)(?: vector)? of (.+?)(?: at (?:the point )?${P})?$`, "i"),
      build: (m) => { const f = fn(m[1]); if (!f) return null; const pt = m[2] ? vec(m[2]) : null; if (m[2] && !pt) return null; return cmd("grad", pt ? [f, pt] : [f], `gradient of ${f}${pt ? ` at ${pt}` : ""}`); } },
    { id: "dirderiv", re: new RegExp(`^${FIND}directional derivative of (.+?) at (?:the point )?${P},? (?:in the direction|along)(?: of)?(?: the vector)? ${P}$`, "i"),
      build: (m) => { const f = fn(m[1]), pt = vec(m[2]), d = vec(m[3]); return f && pt && d ? cmd("dirderiv", [f, d, pt], `directional derivative of ${f} at ${pt} along ${d}`) : null; } },
    { id: "dirderiv", re: new RegExp(`^${FIND}directional derivative of (.+?),? (?:in the direction|along)(?: of)?(?: the vector)? ${P},? at (?:the point )?${P}$`, "i"),
      build: (m) => { const f = fn(m[1]), d = vec(m[2]), pt = vec(m[3]); return f && pt && d ? cmd("dirderiv", [f, d, pt], `directional derivative of ${f} at ${pt} along ${d}`) : null; } },
    { id: "jacobiandet", re: new RegExp(`^${FIND}jacobian determinant of (.+?)(?: with respect to (.+))?$`, "i"),
      build: (m) => { const F = vec(m[1]); if (!F) return null; const vs = m[2] ? varList(m[2]) : null; return cmd("jacobiandet", vs ? [F, `[${vs.join(", ")}]`] : [F]); } },
    { id: "jacobian", re: new RegExp(`^${FIND}jacobian(?: matrix)? of (.+?)(?: with respect to (.+))?$`, "i"),
      build: (m) => { const F = vec(m[1]); if (!F) return null; const vs = m[2] ? varList(m[2]) : null; return cmd("jacobian", vs ? [F, `[${vs.join(", ")}]`] : [F]); } },
    { id: "hessian", re: new RegExp(`^${FIND}hessian(?: matrix)? of (.+)$`, "i"), build: (m) => { const f = fn(m[1]); return f ? cmd("hessian", [f]) : null; } },
    { id: "laplacian", re: new RegExp(`^${FIND}laplacian of (.+)$`, "i"), build: (m) => { const f = fn(m[1]); return f ? cmd("laplacian", [f]) : null; } },
    { id: "totaldiff", re: new RegExp(`^${FIND}total differential of (.+)$`, "i"), build: (m) => { const f = fn(m[1]); return f ? cmd("totaldiff", [f]) : null; } },
    { id: "tangentplane", re: new RegExp(`^${FIND}(?:equation of (?:the )?)?tangent plane (?:to|of|for) (?:the )?(?:surface |graph (?:of )?)?(.+?) at (?:the point )?${P}$`, "i"),
      build: (m) => {
        const pt = vec(m[2]); if (!pt) return null;
        const t = mathOf(m[1]); if (!t) return null;
        const g = t.match(/^z\s*=\s*(.+)$/);
        if (g && !/=/.test(g[1])) return cmd("tangentplane", [g[1], pt], `tangent plane to z = ${g[1]} at ${pt}`);
        return cmd("tangentplane", [t, pt], `tangent plane to ${t} at ${pt}`);
      } },
    { id: "critical-multivariable", re: /^(?:find and classify|classify|find|determine|locate)?\s*(?:all )?(?:the )?(?:critical points|stationary points|saddle points|local extrema|relative extrema|local maxima and minima|local (?:maximum|minimum) and (?:maximum|minimum)(?: values| points)?) (?:of|for) (.+)$/i,
      build: (m) => { const f = fn(m[1]); return f && multi(f) ? cmd("critical", [f], `critical points of ${f} (second-derivative test)`) : null; } },
    { id: "lagrange", re: /^(?:use (?:the method of )?lagrange multipliers to )?(?:find |determine )?(?:the )?(maximize|minimize|maximise|minimise|extreme values of|extrema of|maximum and minimum(?: values)? of|minimum and maximum(?: values)? of|max and min of|maximum of|minimum of) (.+?),? (?:subject to (?:the constraint )?|on the (?:circle|curve|sphere|ellipse|ellipsoid|surface|line|plane) |with (?:the )?constraint |constrained (?:to|by) )(.+)$/i,
      build: (m) => { const f = fn(m[2]), g = eqMath(m[3]); return f && g ? cmd("lagrange", [f, g], `extreme values of ${f} subject to ${g} (Lagrange multipliers)`) : null; } },

    // ---------------- multiple integrals
    { id: "dblint-box", re: /^(?:find |compute |evaluate )?(?:the )?(double|triple) integral of (.+?) over (?:the (?:rectangle|box|region) )?(\[[^\]]+\](?:\s*(?:x|×)\s*\[[^\]]+\])+)$/i,
      build: (m) => {
        const f = mathOf(m[2]); if (!f) return null;
        const boxes = m[3].split(/\s*(?:x|×)\s*/).map((b) => b.replace(/^\[|\]$/g, "").split(/\s*,\s*/));
        const n = m[1].toLowerCase() === "triple" ? 3 : 2;
        if (boxes.length !== n || boxes.some((b) => b.length !== 2)) return null;
        const names = ["x", "y", "z"].slice(0, n);
        const args = [f];
        for (let i = 0; i < n; i++) { const a = bound(boxes[i][0]), b = bound(boxes[i][1]); if (!a || !b) return null; args.push(names[i], a, b); }
        return cmd(n === 3 ? "tplint" : "dblint", args, `${m[1].toLowerCase()} integral of ${f} over ${m[3]}`);
      } },
    { id: "dblint-ineq", re: /^(?:integrate|(?:find |compute |evaluate )?(?:the )?(?:double|triple) integral of) (.+?) over (?:the (?:rectangle|box|region) )?((?:[^,]+? <=? [a-z] <=? [^,]+?)(?:(?:,| and) [^,]+? <=? [a-z] <=? [^,]+?)+)$/i,
      build: (m) => {
        const f = mathOf(m[1]); if (!f) return null;
        const parts = m[2].split(/\s*(?:,|\band\b)\s*/);
        const args = [f];
        for (const p of parts) { const q = p.match(/^(.+?) <=? ([a-z]) <=? (.+)$/); if (!q) return null; const a = bound(q[1]), b = bound(q[3]); if (!a || !b) return null; args.push(q[2], a, b); }
        if (parts.length < 2 || parts.length > 3) return null;
        return cmd(parts.length === 3 ? "tplint" : "dblint", args);
      } },
    { id: "dblint-iter", re: /^(?:find |compute |evaluate )?(?:the )?(double|triple|iterated) integral of (.+?) for ([a-z]) from (.+?) to (.+?),? and ([a-z]) from (.+?) to (.+?)(?:,? and ([a-z]) from (.+?) to (.+?))?$/i,
      build: (m) => {
        const f = mathOf(m[2]); if (!f) return null;
        const args = [f];
        for (const [v, a, b] of [[m[3], m[4], m[5]], [m[6], m[7], m[8]], [m[9], m[10], m[11]]]) { if (!v) continue; const A = bound(a), B = bound(b); if (!A || !B) return null; args.push(v, A, B); }
        return cmd(args.length === 10 ? "tplint" : "dblint", args);
      } },
    { id: "polarint", re: /^(?:integrate|(?:find |compute |evaluate )?(?:the )?(?:double )?integral of) (.+?) over the (unit disk|unit disc|disk (.+?)|disc (.+?))(?:,? (?:using|in) polar coordinates)?$/i,
      build: (m) => {
        const f = mathOf(m[1]); if (!f) return null;
        let R = "1";
        const d = m[3] || m[4];
        if (d) { const q = d.replace(/^of radius /i, "r = ").match(/^(?:x\^2 \+ y\^2 <=? (.+)|r = (.+))$/i); if (!q) return null; R = q[1] ? `sqrt(${mathOf(q[1])})` : mathOf(q[2]); if (!R || R === "sqrt(null)") return null; }
        return cmd("polarint", [f, "0", R, "0", "2pi"], `integral of ${f} over the disk of radius ${R} (polar coordinates)`);
      } },
    { id: "sphint", re: /^(?:integrate|(?:find |compute |evaluate )?(?:the )?(?:triple )?integral of) (.+?) over the (unit ball|ball (.+?))(?:,? (?:using|in) spherical coordinates)?$/i,
      build: (m) => {
        const f = mathOf(m[1]); if (!f) return null;
        let R = "1";
        if (m[3]) { const q = m[3].replace(/^of radius /i, "r = ").match(/^(?:x\^2 \+ y\^2 \+ z\^2 <=? (.+)|r = (.+))$/i); if (!q) return null; R = q[1] ? `sqrt(${mathOf(q[1])})` : mathOf(q[2]); if (!R || R === "sqrt(null)") return null; }
        return cmd("sphint", [f, "0", R, "0", "2pi", "0", "pi"], `integral of ${f} over the ball of radius ${R} (spherical coordinates)`);
      } },

    // ---------------- vector calculus
    { id: "div", re: new RegExp(`^${FIND}(?:divergence|div) of (.+)$`, "i"), build: (m) => { const F = vec(m[1]); return F ? cmd("div", [F]) : null; } },
    { id: "curl", re: new RegExp(`^${FIND}curl of (.+)$`, "i"), build: (m) => { const F = vec(m[1]); return F ? cmd("curl", [F]) : null; } },
    { id: "lineint", re: new RegExp(String.raw`^(?:find |compute |evaluate )?(?:the )?(?:line integral of|work done by) (.+?) (?:along|over|on) (?:the curve )?(?:r\(t\) = )?${V},? (?:for |from )?(?:t from |t = )?(.+?) (?:to|<=? t <=?) (?:t = )?(.+)$`, "i"),
      build: (m) => {
        const C = vec(m[2]); if (!C) return null;
        let F = vec(m[1]);
        if (!F) { const s = m[1].replace(/\s*\bds$/i, ""); F = mathOf(s); if (!F || /=/.test(F)) return null; }
        const a = bound(m[3]), b = bound(m[4]); if (!a || !b) return null;
        return cmd("lineint", [F, C, "t", a, b], `line integral of ${F} along ${C} for t from ${a} to ${b}`);
      } },
    { id: "conservative", re: /^(?:is|determine whether|check whether|check if) (.+?) (?:is )?(?:a )?conservative(?: field| vector field)?$/i,
      build: (m) => { const F = vec(m[1]); return F ? cmd("conservative", [F], `is ${F} conservative`) : null; } },
    { id: "potential", re: /^(?:find |compute |determine )?(?:a |the )?potential(?: function)? (?:for|of) (.+)$/i,
      build: (m) => { const F = vec(m[1]); return F ? cmd("potential", [F]) : null; } },
    { id: "flux-sphere", re: /^(?:find |compute |evaluate )?(?:the )?(?:outward )?flux of (.+?) (?:through|across|out of) the (unit sphere|sphere (?:of radius |x\^2 \+ y\^2 \+ z\^2 = )(.+))$/i,
      build: (m) => {
        const F = vec(m[1]); if (!F) return null;
        let R = "1";
        if (m[3]) { const t = mathOf(m[3]); if (!t) return null; R = /x\^2/.test(m[2]) ? `sqrt(${t})` : t; }
        const r = R === "1" ? "" : `${R}*`;
        return cmd("flux", [F, `[${r}sin(u)*cos(v), ${r}sin(u)*sin(v), ${r}cos(u)]`, "u", "0", "pi", "v", "0", "2pi"], `outward flux of ${F} through the sphere of radius ${R}`);
      } },
    { id: "surfint-sphere", re: /^(?:find |compute |evaluate )?(?:the )?surface integral of (.+?) over the (unit sphere|sphere of radius (.+))$/i,
      build: (m) => {
        const g = mathOf(m[1]); if (!g) return null;
        const R = m[3] ? mathOf(m[3]) : "1"; if (!R) return null;
        const r = R === "1" ? "" : `${R}*`;
        return cmd("surfint", [g, `[${r}sin(u)*cos(v), ${r}sin(u)*sin(v), ${r}cos(u)]`, "u", "0", "pi", "v", "0", "2pi"], `surface integral of ${g} over the sphere of radius ${R}`);
      } },

    // ---------------- transforms
    { id: "invlaplace", re: new RegExp(`^${FIND}inverse laplace(?: transform)? of (.+)$`, "i"), build: (m) => { const F = mathOf(m[1]); return F ? cmd("invlaplace", [F], `inverse Laplace transform of ${F}`) : null; } },
    { id: "laplace", re: new RegExp(`^${FIND}laplace transform of (.+)$`, "i"), build: (m) => { const f = fn(m[1]); return f ? cmd("laplace", [f], `Laplace transform of ${f}`) : null; } },
    { id: "lapsolve", re: /^(?:use (?:the )?laplace transforms? to solve|solve) (.+?)(?:,| with| given| where)? ((?:[a-z]'*\([^)]*\) = [^,]+?)(?:(?:,| and) [a-z]'*\([^)]*\) = [^,]+?)*)(?:,? (?:using|by|with|via) (?:the )?laplace transforms?)?$/i,
      build: (m) => {
        if (!/laplace/i.test(m[0])) return null;
        const ode = mathOf(m[1].replace(/,\s*$/, "")); if (!ode || !/'/.test(ode)) return null;
        const ics = m[2].split(/\s*(?:,|\band\b)\s*/).map((c) => mathOf(c));
        if (ics.some((c) => !c)) return null;
        return cmd("lapsolve", [ode, ...ics], `solve ${ode} with ${ics.join(", ")} by the Laplace transform`);
      } },
    { id: "fouriertransform", re: new RegExp(`^${FIND}fourier transform of (.+)$`, "i"), build: (m) => { const f = fn(m[1]); return f ? cmd("fouriertransform", [f], `Fourier transform of ${f}`) : null; } },
    { id: "fourier", re: new RegExp(`^${FIND}fourier (?:series|coefficients|series coefficients) of (.+?) (?:on|over|for) (?:the interval )?(?:\\[\\s*-\\s*(.+?)\\s*,\\s*(.+?)\\s*\\]|-\\s*(.+?) <=? ([a-z]) <=? (.+?)|\\(\\s*-\\s*(.+?)\\s*,\\s*(.+?)\\s*\\))$`, "i"),
      build: (m) => {
        const f = fn(m[1]); if (!f) return null;
        const L1 = m[2] || m[4] || m[7], L2 = m[3] || m[6] || m[8];
        const a = bound(L1), b = bound(L2);
        if (!a || !b || a.replace(/\s/g, "") !== b.replace(/\s/g, "")) return null;
        const v = m[5] || H.guessVar(f);
        return cmd("fourier", [f, v, a], `Fourier series of ${f} on [-${a}, ${a}]`);
      } },
    { id: "ztransform", re: new RegExp(`^${FIND}z[- ]?transform of (.+)$`, "i"), build: (m) => { const f = fn(m[1]); return f ? cmd("ztransform", [f], `Z-transform of ${f}`) : null; } },

    // ---------------- complex analysis
    { id: "residue", re: new RegExp(`^${FIND}residue of (.+?) at (?:z = )?(.+)$`, "i"),
      build: (m) => { const f = fn(m[1]), a = bound(m[2]); return f && a ? cmd("residue", [f, "z", a], `residue of ${f} at z = ${a}`) : null; } },
    { id: "residues", re: new RegExp(`^${FIND}residues of (.+)$`, "i"), build: (m) => { const f = fn(m[1]); return f ? cmd("residue", [f, "z"], `residues of ${f} at all its poles`) : null; } },
    { id: "laurent", re: new RegExp(`^${FIND}laurent (?:series|expansion) of (.+?) (?:about|at|around|centered at|near) (?:z = )?(.+)$`, "i"),
      build: (m) => { const f = fn(m[1]), a = bound(m[2]); return f && a ? cmd("laurent", [f, "z", a, "2"], `Laurent series of ${f} about z = ${a} (terms below z^2)`) : null; } },
    { id: "contourint", re: /^(?:find |compute |evaluate )?(?:the )?(?:contour )?integral of (.+?) (?:around|over|along) (?:the (?:positively oriented )?circle )?\|\s*z\s*(?:([+-])\s*(.+?))?\s*\|\s*=\s*(.+)$/i,
      build: (m) => {
        const f = fn(m[1]); if (!f) return null;
        const c = m[2] ? mathOf(`${m[2] === "-" ? "" : "-"}(${m[3]})`) : "0";
        const r = bound(m[4]);
        return c && r ? cmd("contourint", [f, "z", c, r], `contour integral of ${f} around |z - (${c})| = ${r}`) : null;
      } },
    { id: "residueint", re: /^(?:find |compute |evaluate )?(?:the )?integral of (.+?) (?:from|over) (?:-\s*infinity|minus infinity|-oo|negative infinity) to (?:infinity|oo|\+infinity)(?:,? (?:using|by|via|with) (?:the )?(?:residues?|residue theorem|contour integration))$/i,
      build: (m) => { const f = fn(m[1]); return f ? cmd("residueint", [f], `integral of ${f} over the real line by residues`) : null; } },
    { id: "analytic", re: /^(?:is|determine whether|check whether|check if) (.+?) (?:is )?(?:analytic|holomorphic)(?: everywhere)?$/i,
      build: (m) => { const f = fn(m[1].replace(/^f\(z\)\s*=\s*/i, "")); return f ? cmd("analytic", [f], `is ${f} analytic`) : null; } },
    { id: "cauchyriemann", re: /^(?:check|verify|test) (?:the |whether )?cauchy[- ]riemann(?: equations)?(?: hold)? for u = (.+?),? and v = (.+)$/i,
      build: (m) => { const u = mathOf(m[1]), v = mathOf(m[2]); return u && v ? cmd("cauchyriemann", [u, v], `Cauchy-Riemann equations for u = ${u}, v = ${v}`) : null; } },

    // ---------------- numerical methods
    { id: "newton", re: /^(?:use |apply )?newton(?:'s|s)?(?:-raphson)? method (?:to (?:find|approximate) (?:a |the )?(?:root|zero|solution) (?:of|to) |to solve |for |on )(.+?),? (?:starting (?:at|from|with)|with|from|and) (?:an initial guess (?:of )?)?(?:([a-z])_?0 = )?(.+)$/i,
      build: (m) => {
        const t = mathOf(m[1]); if (!t) return null;
        const g = /=/.test(t) ? lhsMinusRhs(t) : t;
        const v = m[2] || H.guessVar(g);
        const x0 = bound(m[3]); if (!x0) return null;
        return cmd("newton", [g, v, x0], `Newton's method on ${g} = 0 from ${v}0 = ${x0}`);
      } },
    { id: "bisection", re: /^(?:use |apply )?(?:the )?bisection method (?:to (?:find|approximate) (?:a |the )?(?:root|zero) (?:of|to) |for |on )(.+?) (?:on|in|over) (?:the interval )?\[\s*(.+?)\s*,\s*(.+?)\s*\]$/i,
      build: (m) => { const t = mathOf(m[1]); if (!t) return null; const g = /=/.test(t) ? lhsMinusRhs(t) : t; const a = bound(m[2]), b = bound(m[3]); return a && b ? cmd("bisection", [g, H.guessVar(g), a, b]) : null; } },
    { id: "secant", re: /^(?:use |apply )?(?:the )?secant method (?:to (?:find|approximate) (?:a |the )?(?:root|zero) (?:of|to) |for |on )(.+?),? with ([a-z])_?0 = (.+?),? and \2_?1 = (.+)$/i,
      build: (m) => { const t = mathOf(m[1]); if (!t) return null; const g = /=/.test(t) ? lhsMinusRhs(t) : t; const a = bound(m[3]), b = bound(m[4]); return a && b ? cmd("secant", [g, m[2], a, b]) : null; } },
    { id: "fixedpoint", re: /^(?:use |apply )?(?:the )?fixed[- ]point iteration (?:for|on|to solve) ([a-z]) = (.+?),? (?:starting (?:at|from|with)|with|from) (?:[a-z]_?0 = )?(.+)$/i,
      build: (m) => { const g = mathOf(m[2]), x0 = bound(m[3]); return g && x0 ? cmd("fixedpoint", [g, m[1], x0], `fixed-point iteration ${m[1]} = ${g} from ${x0}`) : null; } },
    { id: "trapezoid", re: /^(?:use |apply )?(?:the )?(trapezoidal|trapezoid|simpson(?:'s|s)?) rule (?:with n = (\d+) )?(?:for|on|to approximate) (?:the integral of )?(.+?) from (.+?) to (.+?)(?:,? with n = (\d+))?$/i,
      build: (m) => {
        const n = m[2] || m[6]; if (!n) return null;
        const f = mathOf(m[3]), a = bound(m[4]), b = bound(m[5]); if (!f || !a || !b) return null;
        return cmd(/simpson/i.test(m[1]) ? "simpson" : "trapezoid", [f, H.guessVar(f), a, b, n]);
      } },
    { id: "odestep", re: /^(?:use |apply )?(?:the )?(euler(?:'s|s)? method|rk4|runge[- ]kutta(?: 4| method)?|fourth[- ]order runge[- ]kutta(?: method)?) with (?:h|step size|step) =? ?(.+?) to (?:approximate|estimate|find) y\((.+?)\),? (?:for|where|given|if) y' = (.+?),? (?:and |with )?y\((.+?)\) = (.+)$/i,
      build: (m) => {
        const F = mathOf(m[4]), h = bound(m[2]), x1 = bound(m[3]), x0 = bound(m[5]), y0 = bound(m[6]);
        if (!F || !h || !x1 || !x0 || !y0) return null;
        const vs = vars(F);
        const x = vs.has("x") ? "x" : vs.has("t") ? "t" : "x";
        return cmd(/euler/i.test(m[1]) ? "eulermethod" : "rungekutta", [F, x, "y", x0, y0, h, x1]);
      } },
    { id: "poweriter", re: /^(?:use |apply )?(?:the )?power (?:method|iteration) (?:for|on|to) (?:the matrix )?(\[\[.+\]\])$/i,
      build: (m) => { const A = mathOf(m[1]); return A ? cmd("poweriter", [A], `power iteration on ${A}`) : null; } },

    // ---------------- curves
    { id: "curve-graph", re: new RegExp(`^${FIND}curvature of (?:the curve |the graph of )?y = (.+?)(?: at ([a-z]) = (.+))?$`, "i"),
      build: (m) => { const f = mathOf(m[1]); if (!f) return null; const x = m[2] || H.guessVar(f); const a = m[3] ? bound(m[3]) : null; return cmd("curvature", a ? [f, x, a] : [f, x]); } },
    { id: "curve", re: new RegExp(`^${FIND}(curvature|torsion|unit tangent(?: vector)?|(?:principal )?(?:unit )?normal(?: vector)?|binormal(?: vector)?|arc length parametri[sz]ation) (?:of|for) (?:the (?:curve|helix|circle|line) )?(?:r\\(t\\) = )?(.+?)(?: at t = (.+))?$`, "i"),
      build: (m) => {
        const r = vec(m[2]); if (!r) return null;
        const w = m[1].toLowerCase();
        const name = /curvature/.test(w) ? "curvature" : /torsion/.test(w) ? "torsion" : /tangent/.test(w) ? "unittangent" : /binormal/.test(w) ? "binormal" : /normal/.test(w) ? "unitnormal" : "arcparam";
        const a = m[3] ? bound(m[3]) : null;
        if (m[3] && !a) return null;
        if (name === "arcparam" && a) return null;
        return cmd(name, a ? [r, "t", a] : [r, "t"]);
      } },
    { id: "arclength-param", re: new RegExp(`^${FIND}(?:arc ?length|length) of (?:the (?:curve|helix) )?(?:r\\(t\\) = )?${V},? (?:for |from )?(?:t from |t = )?(.+?) (?:to|<=? t <=?) (?:t = )?(.+)$`, "i"),
      build: (m) => { const r = vec(m[1]); if (!r) return null; const a = bound(m[2]), b = bound(m[3]); return a && b ? { ...cmd("arclength", [r, "t", a, b]), goal: "arclength" } : null; } },

    // ---------------- PDE
    { id: "pdecheck", re: /^(?:verify that|show that|check that|check whether|check if|does|is) u(?:\([a-z, ]+\))? = (.+?) (?:satisfies|satisfy|a solution of|a solution to|solves|solve) (?:the (?:pde|equation) )?(.+)$/i,
      build: (m) => { const u = mathOf(m[1]), pde = mathOf(m[2]); return u && pde && /u_/.test(pde) && /=/.test(pde) ? cmd("pdecheck", [u, pde], `does u = ${u} satisfy ${pde}`) : null; } },
    { id: "classifypde", re: /^classify (?:the )?(?:pde |equation |partial differential equation )?(.+)$/i,
      build: (m) => { const pde = mathOf(m[1]); return pde && /u_/.test(pde) && /=/.test(pde) ? cmd("classifypde", [pde], `classify ${pde}`) : null; } },
    { id: "heat", re: /^(?:solve )?(?:the )?heat equation u_t = (?:(.+?) ?\*? ?)?u_xx (?:on|for) (?:0 < x < (.+?)|\[\s*0\s*,\s*(.+?)\s*\]),? with (?:u\(0, ?t\) = u\(\2\3, ?t\) = 0|zero (?:boundary conditions|dirichlet conditions|end temperatures)|homogeneous (?:dirichlet )?boundary conditions) and u\(x, ?0\) = (.+)$/i,
      build: (m) => {
        const L = bound(m[2] || m[3]), f = mathOf(m[4]), k = m[1] ? mathOf(m[1]) : "1";
        return L && f && k ? cmd("heat", [f, "x", "t", L, k], `heat equation u_t = ${k} u_xx on 0 < x < ${L}, u = 0 at both ends, u(x, 0) = ${f}`) : null;
      } },
    { id: "wave", re: /^(?:solve )?(?:the )?wave equation u_tt = (?:(.+?) ?\*? ?)?u_xx (?:on|for) (?:0 < x < (.+?)|\[\s*0\s*,\s*(.+?)\s*\]),? with (?:u\(0, ?t\) = u\(\2\3, ?t\) = 0|zero boundary conditions|fixed ends),? u\(x, ?0\) = (.+?),? and u_t\(x, ?0\) = (.+)$/i,
      build: (m) => {
        const L = bound(m[2] || m[3]), f = mathOf(m[4]), g = mathOf(m[5]), c2 = m[1] ? mathOf(m[1]) : "1";
        return L && f && g && c2 ? cmd("wave", [f, g, "x", "t", L, `sqrt(${c2})`], `wave equation u_tt = ${c2} u_xx on 0 < x < ${L}, fixed ends, u(x, 0) = ${f}, u_t(x, 0) = ${g}`) : null;
      } },
  ];
  // the (\2\3) back-references above need whichever of the two interval groups matched; normalise
  for (const p of pats) if (p.id === "heat" || p.id === "wave") {
    const src = p.re.source.replace("u\\(\\2\\3, ?t\\)", "u\\([^,]+, ?t\\)");
    p.re = new RegExp(src, "i");
  }
  void looksLikeMath; void expr;
  return pats;
}
