#!/usr/bin/env python3
"""Test oracle for tools/fuzz.mjs (sympy + mpmath, local only, never shipped).

Reads a JSON list of records on stdin: { id, task: {...}, claim: {...} } and prints a JSON list of
{ id, verdict, detail } where verdict is one of
  ok            the verified claim is correct
  wrong         the verified claim is wrong (the serious bug class)
  unknown       the oracle could not decide (timeouts, unsupported answer form)
Only verified claims are judged; unverified ones are passed through as "unverified".

Real-domain semantics follow Quelvra: odd roots of negatives are real, even roots of negatives and
logs of non-positive numbers are undefined, log(x) with one argument is base 10.
"""
import json, sys, signal, math, re, os, multiprocessing as mproc
import mpmath as mp
import sympy as sp
from sympy.parsing.sympy_parser import parse_expr

mp.mp.dps = 50
DPS = 50


class Timeout(BaseException):
    """BaseException so that sympy's and mpmath's own `except Exception` blocks cannot swallow it"""
    pass


def _alarm(signum, frame):
    raise Timeout()


def with_timeout(sec, fn, *a):
    """Run fn under a wall-clock limit; nests correctly (an inner limit never cancels an outer one)."""
    import time
    outer = signal.getitimer(signal.ITIMER_REAL)[0]
    t0 = time.monotonic()
    old = signal.signal(signal.SIGALRM, _alarm)
    signal.setitimer(signal.ITIMER_REAL, min(sec, outer) if outer > 0 else sec)
    try:
        return fn(*a)
    finally:
        signal.setitimer(signal.ITIMER_REAL, 0)
        signal.signal(signal.SIGALRM, old)
        if outer > 0:
            left = outer - (time.monotonic() - t0)
            signal.setitimer(signal.ITIMER_REAL, max(left, 0.01))


# ------------------------------------------------------------------ parsing
class _cbrt(sp.Function):
    nargs = 1


class _acot(sp.Function):
    nargs = 1


class _asec(sp.Function):
    nargs = 1


class _acsc(sp.Function):
    nargs = 1


SYMS = {}


def sym(name):
    if name not in SYMS:
        SYMS[name] = sp.Symbol(name, real=True)
    return SYMS[name]


BASE_NS = {name: getattr(sp, name) for name in dir(sp) if not name.startswith("_")}
BASE_NS.update({"_cbrt": _cbrt, "_acot": _acot, "_asec": _asec, "_acsc": _acsc, "true": sp.true, "false": sp.false})


def P(s, evaluate=False):
    if s is None:
        return None
    ns = dict(BASE_NS)
    for m in set(re.findall(r"_s_([A-Za-z][A-Za-z0-9_]*)", s)):
        ns["_s_" + m] = sym(m)
    return parse_expr(s, local_dict=ns, global_dict={}, evaluate=evaluate)


def to_sympy_real(e):
    """Rewrite into plain sympy with real semantics where sympy differs (odd roots, cbrt)."""
    def rw(u):
        if not u.args:
            return u
        args = [rw(a) for a in u.args]
        if isinstance(u, sp.Pow):
            b, ex = args
            if ex.is_Rational and not ex.is_Integer and ex.q % 2 == 1:
                r = sp.Abs(b) ** ex
                return r * sp.sign(b) if ex.p % 2 else r
            return sp.Pow(b, ex)
        if isinstance(u, _cbrt):
            return sp.real_root(args[0], 3)
        if isinstance(u, _acot):
            return sp.atan(1 / args[0])
        if isinstance(u, _asec):
            return sp.acos(1 / args[0])
        if isinstance(u, _acsc):
            return sp.asin(1 / args[0])
        return u.func(*args)
    return rw(e)


# ------------------------------------------------------------------ real evaluator (mpmath, 50 digits)
class Undefined(Exception):
    pass


def isreal(z):
    if isinstance(z, mp.mpf):
        return True
    return abs(z.imag) <= mp.mpf(10) ** (-30) * max(1, abs(z.real))


def R(z):
    if isinstance(z, (mp.mpf,)):
        if not mp.isfinite(z):
            raise Undefined()
        return z
    if isinstance(z, mp.mpc):
        if not isreal(z) or not mp.isfinite(z.real):
            raise Undefined()
        return z.real
    return mp.mpf(z)


FN1 = {
    sp.sin: mp.sin, sp.cos: mp.cos, sp.exp: mp.exp, sp.atan: mp.atan, sp.sinh: mp.sinh, sp.cosh: mp.cosh, sp.tanh: mp.tanh,
    sp.asinh: mp.asinh, sp.erf: mp.erf, sp.Abs: abs, sp.sign: mp.sign, sp.floor: mp.floor, sp.ceiling: mp.ceil,
}


def ev(e, env):
    """Evaluate a sympy tree at env (dict Symbol->mpf) with real semantics; raises Undefined."""
    if e.is_Number:
        if e.is_Rational:
            return mp.mpf(e.p) / e.q
        if e is sp.nan or e is sp.zoo or e in (sp.oo, -sp.oo):
            raise Undefined()
        return mp.mpf(str(e.evalf(DPS)))
    if e.is_Symbol:
        if e in env:
            return env[e]
        raise Undefined()
    if e is sp.pi:
        return +mp.pi
    if e is sp.E:
        return +mp.e
    if e is sp.EulerGamma:
        return +mp.euler
    if e is sp.I:
        raise Undefined()
    if isinstance(e, sp.Add):
        return mp.fsum([ev(a, env) for a in e.args])
    if isinstance(e, sp.Mul):
        r = mp.mpf(1)
        for a in e.args:
            r *= ev(a, env)
        return r
    if isinstance(e, sp.Pow):
        b, x = e.args
        bv = ev(b, env)
        if x.is_Rational:
            if bv == 0 and x < 0:
                raise Undefined()
            if x.is_Integer:
                return bv ** int(x)
            if bv < 0:
                if x.q % 2 == 0:
                    raise Undefined()
                v = (-bv) ** (mp.mpf(x.p) / x.q)
                return v if x.p % 2 == 0 else -v
            return bv ** (mp.mpf(x.p) / x.q)
        xv = ev(x, env)
        if bv < 0:
            if xv == mp.nint(xv):
                return bv ** int(mp.nint(xv))
            raise Undefined()
        if bv == 0:
            if xv > 0:
                return mp.mpf(0)
            raise Undefined()
        return R(mp.power(bv, xv))
    if isinstance(e, sp.log):
        if len(e.args) == 2:
            a, b = ev(e.args[0], env), ev(e.args[1], env)
            if a <= 0 or b <= 0 or b == 1:
                raise Undefined()
            return mp.log(a) / mp.log(b)
        a = ev(e.args[0], env)
        if a <= 0:
            raise Undefined()
        return mp.log(a)
    f = e.func
    if f in FN1:
        return R(FN1[f](ev(e.args[0], env)))
    a = [ev(t, env) for t in e.args]
    if f is sp.tan:
        c = mp.cos(a[0])
        if abs(c) < mp.mpf(10) ** -40:
            raise Undefined()
        return mp.tan(a[0])
    if f is sp.cot:
        s = mp.sin(a[0])
        if abs(s) < mp.mpf(10) ** -40:
            raise Undefined()
        return mp.cot(a[0])
    if f is sp.sec:
        c = mp.cos(a[0])
        if abs(c) < mp.mpf(10) ** -40:
            raise Undefined()
        return 1 / c
    if f is sp.csc:
        s = mp.sin(a[0])
        if abs(s) < mp.mpf(10) ** -40:
            raise Undefined()
        return 1 / s
    if f is sp.asin:
        if abs(a[0]) > 1:
            raise Undefined()
        return mp.asin(a[0])
    if f is sp.acos:
        if abs(a[0]) > 1:
            raise Undefined()
        return mp.acos(a[0])
    if f is sp.acosh:
        if a[0] < 1:
            raise Undefined()
        return mp.acosh(a[0])
    if f is sp.atanh:
        if abs(a[0]) >= 1:
            raise Undefined()
        return mp.atanh(a[0])
    if f is _cbrt:
        return mp.cbrt(a[0]) if a[0] >= 0 else -mp.cbrt(-a[0])
    if f is _acot:
        return mp.pi / 2 if a[0] == 0 else mp.atan(1 / a[0])
    if f is _asec:
        if abs(a[0]) < 1:
            raise Undefined()
        return mp.acos(1 / a[0])
    if f is _acsc:
        if abs(a[0]) < 1:
            raise Undefined()
        return mp.asin(1 / a[0])
    if f is sp.coth:
        return 1 / mp.tanh(a[0])
    if f is sp.sech:
        return 1 / mp.cosh(a[0])
    if f is sp.csch:
        return 1 / mp.sinh(a[0])
    if f is sp.gamma:
        if a[0] <= 0 and a[0] == mp.nint(a[0]):
            raise Undefined()
        return mp.gamma(a[0])
    if f is sp.factorial:
        if a[0] < 0 and a[0] == mp.nint(a[0]):
            raise Undefined()
        return mp.gamma(a[0] + 1)
    if f is sp.erfi:
        return R(mp.erfi(a[0]))
    if f is sp.erfc:
        return mp.erfc(a[0])
    if f is sp.Si:
        return mp.si(a[0])
    if f is sp.Ci:
        if a[0] <= 0:
            raise Undefined()
        return mp.ci(a[0])
    if f is sp.Ei:
        return R(mp.ei(a[0]))
    if f is sp.li:
        return R(mp.li(a[0]))
    if f is sp.Shi:
        return mp.shi(a[0])
    if f is sp.Chi:
        return R(mp.chi(a[0]))
    if f is sp.fresnels:
        return mp.fresnels(a[0])
    if f is sp.fresnelc:
        return mp.fresnelc(a[0])
    if f is sp.LambertW:
        return R(mp.lambertw(a[0]))
    if f is sp.zeta:
        return mp.zeta(a[0])
    if f is sp.binomial:
        return mp.binomial(a[0], a[1])
    if f is sp.Max:
        return max(a)
    if f is sp.Min:
        return min(a)
    if f is sp.real_root:
        return mp.cbrt(a[0]) if a[0] >= 0 else -mp.cbrt(-a[0])
    raise Undefined("unsupported " + str(f))


def evs(e, env):
    try:
        return ev(e, env)
    except (Undefined, ZeroDivisionError, OverflowError, ValueError):
        return None


def defined_all(e, env):
    """Every subexpression of e (the ORIGINAL problem) is defined at env."""
    for sub in sp.preorder_traversal(e):
        if sub.is_Atom or isinstance(sub, (sp.Eq, sp.Rel, sp.Tuple)):
            continue
        if evs(sub, env) is None:
            return False
    return True


def mpN(e, dps=45):
    """sympy constant -> mpf (None when not a finite real)"""
    try:
        v = sp.N(e, dps)
        re_, im_ = v.as_real_imag()
        if abs(complex(sp.N(im_, 20))) > 1e-30:
            return None
        r = mp.mpf(str(sp.N(re_, dps)))
        return r if mp.isfinite(r) else None
    except Exception:
        return None


def close(a, b, tol):
    return abs(a - b) <= tol * max(1, abs(a), abs(b))


# ------------------------------------------------------------------ answers
def point_answers(claim, var):
    """(points, families, flags) from a claim. points: list of (mpf, text); families: [(expr, param)]"""
    pts, fams, flags = [], [], set()
    for a in claim.get("answers", []):
        k = a.get("kind")
        if k == "none":
            flags.add("none")
            continue
        if k == "all":
            flags.add("all")
            continue
        if a.get("unconvertible"):
            flags.add("unconvertible")
            continue
        if k == "general" and a.get("py"):
            fams.append((P(a["py"]), a.get("param") or "k"))
            continue
        if k in ("exact",) and a.get("py"):
            e = P(a["py"])
            v = evs(e, {})
            if v is None:
                flags.add("nonreal:" + a.get("text", ""))
            else:
                pts.append((v, a.get("text", ""), True))
            continue
        if k == "set" and a.get("py"):
            fams.append((P(a["py"]), "__set__"))
            continue
        if k == "approx" and a.get("approx"):
            pts.append((mp.mpf(a["approx"]), a["approx"], False))
            continue
        flags.add("kind:" + str(k))
    return pts, fams, flags


# ------------------------------------------------------------------ equation roots (oracle)
def numeric_roots(fexpr, x, lo, hi, n=24001):
    """Real zeros of f on [lo, hi]: sign changes + near-zero local minima, refined at 50 digits."""
    import numpy as np
    fr = to_sympy_real(fexpr)
    try:
        g = sp.lambdify(x, fr, modules=["numpy"])
        xs = np.linspace(lo, hi, n)
        with np.errstate(all="ignore"):
            ys = np.asarray(g(xs), dtype=complex) * np.ones_like(xs)
        ys = np.where(np.abs(ys.imag) < 1e-9 * np.maximum(1, np.abs(ys.real)), ys.real, np.nan)
    except Exception:
        return None
    cands = []
    for i in range(n - 1):
        a, b = ys[i], ys[i + 1]
        if np.isfinite(a) and np.isfinite(b):
            if a == 0:
                cands.append(("pt", xs[i]))
            elif a * b < 0:
                cands.append(("br", xs[i], xs[i + 1]))
    ay = np.abs(ys)
    for i in range(1, n - 1):
        if np.isfinite(ay[i - 1]) and np.isfinite(ay[i]) and np.isfinite(ay[i + 1]) and ay[i] <= ay[i - 1] and ay[i] <= ay[i + 1] and ay[i] < 1e-2:
            cands.append(("min", xs[i]))
    # domain edges (sqrt(x - a) = 0 at the edge of the domain)
    for i in range(n - 1):
        if np.isfinite(ys[i]) != np.isfinite(ys[i + 1]):
            cands.append(("edge", xs[i], xs[i + 1]))
    f = lambda t: ev(fexpr, {x: t})
    roots = []
    for c in cands:
        r = None
        try:
            if c[0] == "br":
                a, b = mp.mpf(c[1]), mp.mpf(c[2])
                fa = f(a)
                for _ in range(200):
                    m = (a + b) / 2
                    fm = f(m)
                    if fm == 0:
                        a = b = m
                        break
                    if (fm < 0) == (fa < 0):
                        a, fa = m, fm
                    else:
                        b = m
                r = (a + b) / 2
            elif c[0] == "pt":
                r = mp.mpf(c[1])
            elif c[0] == "min":
                try:
                    r = mp.findroot(f, mp.mpf(c[1]), tol=mp.mpf(10) ** -40, maxsteps=200)
                except Exception:
                    # tangential root: minimise |f| via the derivative's zero
                    try:
                        r = mp.findroot(lambda t: mp.diff(f, t), mp.mpf(c[1]), tol=mp.mpf(10) ** -30)
                    except Exception:
                        r = None
            elif c[0] == "edge":
                # bisect the definedness boundary, then test f there
                a, b = mp.mpf(c[1]), mp.mpf(c[2])
                da = evs(fexpr, {x: a}) is not None
                for _ in range(170):
                    m = (a + b) / 2
                    if (evs(fexpr, {x: m}) is not None) == da:
                        a = m
                    else:
                        b = m
                r = a if da else b
                # an exact rational edge
                q = sp.nsimplify(float(r), rational=True, tolerance=1e-12)
                if evs(fexpr, {x: mp.mpf(q.p) / q.q}) is not None:
                    r = mp.mpf(q.p) / q.q
        except Exception:
            r = None
        if r is None or not (lo - 1e-9 <= r <= hi + 1e-9):
            continue
        if is_root(fexpr, x, r):
            if not any(close(r, s, 1e-12) for s in roots):
                roots.append(r)
    return sorted(roots)


def is_root(fexpr, x, r, tol_digits=20):
    v = evs(fexpr, {x: r})
    if v is None:
        return False
    # scale by the size of the terms
    scale = mp.mpf(1)
    for a in (fexpr.args if isinstance(fexpr, sp.Add) else [fexpr]):
        t = evs(a, {x: r})
        if t is not None:
            scale = max(scale, abs(t))
    return abs(v) <= mp.mpf(10) ** (-tol_digits) * scale


def poly_roots(fx, x):
    """All real roots of a rational function's numerator when f is polynomial / rational in x."""
    try:
        num, den = sp.fraction(sp.together(fx))
        if not num.is_polynomial(x):
            return None
        p = sp.Poly(sp.expand(num), x)
        rs = []
        for r in sp.real_roots(p):
            rs.append(mp.mpf(str(sp.N(r, 60))))
        return rs
    except Exception:
        return None


def judge_eq(task, claim):
    x = sym(task["x"])
    L, Rr = P(task["lhs"]), P(task["rhs"])
    orig = sp.Tuple(L, Rr)
    fexpr = sp.Add(L, sp.Mul(-1, Rr, evaluate=False), evaluate=False)
    rng = task.get("R", 40)
    pts, fams, flags = point_answers(claim, task["x"])
    if "unconvertible" in flags:
        return "unknown", "answer not convertible"
    for fl in flags:
        if fl.startswith("nonreal:"):
            return "wrong", "answer is not a real number: " + fl[8:]
    # 1. every claimed point satisfies the ORIGINAL equation and is in its domain
    for v, text, exact in pts:
        if not defined_all(orig, {x: v}):
            return "wrong", f"{task['x']} = {text} is outside the domain of the original"
        if exact:
            if not is_root(fexpr, x, v, 30):
                return "wrong", f"{task['x']} = {text} does not satisfy the equation (residual {mp.nstr(evs(fexpr, {x: v}), 5)})"
        else:
            if not is_root(fexpr, x, v, 12):
                return "wrong", f"{task['x']} ~ {text} does not satisfy the equation to 12 digits"
    sets = [fe for fe, k in fams if k == "__set__"]
    fams = [(fe, k) for fe, k in fams if k != "__set__"]
    in_set = lambda t: any(truth_rel(p, {x: t}) for p in sets)
    if sets:
        grid = [mp.mpf(i) / 20 + mp.mpf("0.0013") for i in range(-20 * rng, 20 * rng + 1)]
        for p in sets:
            for sub in sp.preorder_traversal(p):
                if isinstance(sub, sp.Rel):
                    for side in sub.args:
                        if not side.has(x):
                            v = evs(side, {})
                            if v is not None:
                                grid += [v, v + mp.mpf("1e-9"), v - mp.mpf("1e-9")]
        for t in grid:
            ins = in_set(t)
            ok = defined_all(orig, {x: t}) and is_root(fexpr, x, t, 25)
            if ins and not ok:
                return "wrong", f"the answer set contains {mp.nstr(t, 12)} but the equation fails there"
            if ok and not ins and not any(close(t, v, 1e-12) for v, _, _ in pts):
                return "wrong", f"{mp.nstr(t, 12)} solves the equation but is not in the answer"
    for fe, k in fams:
        ks = sym(k)
        for kk in range(-3, 4):
            v = evs(fe, {ks: mp.mpf(kk)})
            if v is None:
                return "wrong", f"family member k={kk} undefined"
            if not defined_all(orig, {x: v}) or not is_root(fexpr, x, v, 25):
                return "wrong", f"family {sp.sstr(fe)} member k={kk} ({mp.nstr(v, 10)}) does not satisfy the equation"
    if "all" in flags:
        # identity: check at several points in the domain
        bad = 0
        for t in [0.37, 1.3, -2.2, 3.7, -0.61, 5.9]:
            if defined_all(orig, {x: mp.mpf(t)}) and not is_root(fexpr, x, mp.mpf(t), 25):
                return "wrong", f"claimed identity fails at {t}"
        return "ok", "identity"
    # 2. completeness on [-R, R]
    fx = to_sympy_real(P(task["lhs"], True) - P(task["rhs"], True))
    exact = None
    try:
        exact = with_timeout(4, poly_roots, fx, x)
    except Timeout:
        exact = None
    oracle = []
    if exact is not None:
        oracle = [r for r in exact if defined_all(orig, {x: r}) and is_root(fexpr, x, r, 25)]
        # a polynomial/rational equation: exact on the whole line
        window = None
    else:
        nr = numeric_roots(fexpr, x, -rng, rng)
        if nr is None:
            return "unknown", "oracle could not scan"
        oracle = nr
        window = rng
    claimed = [v for v, _, _ in pts]
    for fe, k in fams:
        ks = sym(k)
        for kk in range(-60, 61):
            v = evs(fe, {ks: mp.mpf(kk)})
            if v is not None:
                claimed.append(v)
    for r in oracle:
        if window is not None and abs(r) > window - 0.5:
            continue
        if sets and in_set(r):
            continue
        if not any(close(r, c, 1e-9) for c in claimed):
            return "wrong", f"missing root {mp.nstr(r, 15)}" + (" (claimed no solution)" if "none" in flags else "")
    if "none" in flags and (pts or fams):
        return "wrong", "claims no solution and solutions"
    # duplicates are a presentation bug, not wrong: ignore
    return "ok", f"{len(oracle)} roots"


# ------------------------------------------------------------------ inequalities
def judge_ineq(task, claim):
    x = sym(task["x"])
    L, Rr = P(task["lhs"]), P(task["rhs"])
    op = task["op"]
    ans = [a for a in claim.get("answers", []) if a.get("kind") == "set"]
    if not ans:
        if claim.get("noSolution") or any(a.get("kind") == "none" for a in claim.get("answers", [])):
            ans_pred = lambda t: False
        else:
            return "unknown", "no set answer"
    else:
        if any(a.get("unconvertible") for a in ans):
            return "unknown", "unconvertible"
        preds = [P(a["py"]) for a in ans]
        ans_pred = lambda t: any(truth_rel(p, {x: t}) for p in preds)

    def orig(t):
        l, r = evs(L, {x: t}), evs(Rr, {x: t})
        if l is None or r is None or not defined_all(sp.Tuple(L, Rr), {x: t}):
            return None
        d = l - r
        z = abs(d) <= mp.mpf(10) ** -40 * max(1, abs(l), abs(r))
        if op == "<":
            return (not z) and d < 0
        if op == "<=":
            return z or d < 0
        if op == ">":
            return (not z) and d > 0
        return z or d > 0
    # critical points: roots of lhs - rhs, domain edges, endpoints mentioned by the answer
    fexpr = sp.Add(L, sp.Mul(-1, Rr, evaluate=False), evaluate=False)
    fx = to_sympy_real(P(task["lhs"], True) - P(task["rhs"], True))
    crit = poly_roots(fx, x)
    if crit is None:
        crit = numeric_roots(fexpr, x, -60, 60) or []
    else:
        num, den = sp.fraction(sp.together(fx))
        try:
            crit += [mp.mpf(str(sp.N(r, 60))) for r in sp.real_roots(sp.Poly(den, x))] if den.has(x) else []
        except Exception:
            pass
    for a in ans:
        for n in re.findall(r"-?\d+(?:\.\d+)?", a.get("text", "")):
            pass
        for sub in sp.preorder_traversal(P(a["py"])):
            if isinstance(sub, sp.Rel):
                for side in sub.args:
                    if not side.has(x):
                        v = evs(side, {})
                        if v is not None:
                            crit.append(v)
    # domain edges by scanning
    import numpy as np
    pts = set()
    for c in crit:
        for e in [0, mp.mpf('1e-15'), -mp.mpf('1e-15'), 1e-6, -1e-6, 0.3, -0.3]:
            pts.add(c + e)
    for i in range(-400, 401):
        pts.add(mp.mpf(i) / 10 + mp.mpf("0.00731"))
    for c in [1e3, -1e3, 1e6, -1e6]:
        pts.add(mp.mpf(c))
    for t in sorted(pts):
        o = orig(t)
        a = ans_pred(t)
        if o is None:
            if a:
                return "wrong", f"answer contains {mp.nstr(t, 12)} where the original is undefined"
            continue
        if bool(o) != bool(a):
            return "wrong", f"at {task['x']} = {mp.nstr(t, 15)} the inequality is {o} but the answer says {a}"
    return "ok", ""


def truth_rel(p, env):
    if p is sp.true or p == True:
        return True
    if p is sp.false or p == False:
        return False
    if isinstance(p, sp.And):
        return all(truth_rel(a, env) for a in p.args)
    if isinstance(p, sp.Or):
        return any(truth_rel(a, env) for a in p.args)
    if isinstance(p, sp.Not):
        return not truth_rel(p.args[0], env)
    if isinstance(p, sp.Rel):
        l, r = evs(p.lhs, env), evs(p.rhs, env)
        if l is None or r is None:
            return False
        d = l - r
        z = abs(d) <= mp.mpf(10) ** -40 * max(1, abs(l), abs(r))
        op = p.rel_op
        return {"<": (not z) and d < 0, "<=": z or d < 0, ">": (not z) and d > 0, ">=": z or d > 0, "==": z, "!=": not z}[op]
    raise Undefined("pred " + str(p))


# ------------------------------------------------------------------ systems
def judge_sys(task, claim):
    eqs = [(P(l), P(r)) for l, r in task["eqs"]]
    present = set()
    for l, r in eqs:
        present |= l.free_symbols | r.free_symbols
    vars_ = [sym(v) for v in task["vars"] if sym(v) in present]
    sols = []
    fams = False
    for a in claim.get("answers", []):
        if a.get("kind") == "solution" and a.get("values"):
            sols.append({sym(k): P(v) for k, v in a["values"]})
        elif a.get("kind") == "family":
            fams = True
            sols.append({sym(k): P(v) for k, v in a.get("values", [])})
        elif a.get("kind") == "none":
            pass
        elif a.get("unconvertible"):
            return "unknown", "unconvertible"
    none = claim.get("noSolution") or any(a.get("kind") == "none" for a in claim.get("answers", []))
    # substitution
    for s in sols:
        params = set()
        for v in s.values():
            params |= {t for t in v.free_symbols}
        trials = [dict()] if not params else [{p: mp.mpf(t) for p in params} for t in (0.3, -1.7, 2.9)]
        for tr in trials:
            env = {}
            for k, v in s.items():
                val = evs(v, tr)
                if val is None:
                    return "wrong", f"solution value {sp.sstr(v)} not real"
                env[k] = val
            for vv in vars_:
                if vv not in env:
                    if fams:
                        env[vv] = mp.mpf("0.123")
                    else:
                        return "wrong", f"solution misses {vv}"
            for l, r in eqs:
                lv, rv = evs(l, env), evs(r, env)
                if lv is None or rv is None or not close(lv, rv, mp.mpf(10) ** -25):
                    return "wrong", f"solution {s} fails {sp.sstr(l)} = {sp.sstr(r)}"
    # completeness with sympy
    try:
        ref = with_timeout(8, lambda: sp.solve([sp.Eq(to_sympy_real(P(l_, True)), to_sympy_real(P(r_, True))) for l_, r_ in task["eqs"]], vars_, dict=True))
    except Timeout:
        return "ok", "substitution only (sympy timeout)"
    real_ref = []
    for d in ref:
        if any(not d.get(v, v).free_symbols <= set() and d.get(v, v) != v for v in vars_):
            pass
        if len(d) < len(vars_) or any(d[v].free_symbols for v in vars_ if v in d):
            if not fams and not none:
                return "wrong", "sympy finds infinitely many solutions, claim lists points"
            if none:
                return "wrong", "claims no solution but sympy finds a family"
            return "ok", "family"
        vals = {}
        ok_ = True
        for v in vars_:
            z = complex(sp.N(d[v], 30))
            if abs(z.imag) > 1e-12:
                ok_ = False
            vals[v] = z.real
        if ok_:
            real_ref.append(vals)
    if fams:
        if real_ref:
            return "wrong", "claims a family but sympy finds isolated solutions"
        return "ok", "family"
    if none:
        return ("wrong", f"claims no solution; sympy: {real_ref}") if real_ref else ("ok", "none")
    got = []
    for s in sols:
        got.append({k: float(evs(v, {})) for k, v in s.items()})
    for rr in real_ref:
        if not any(all(abs(g[v] - rr[v]) < 1e-8 * max(1, abs(rr[v])) for v in vars_) for g in got):
            return "wrong", f"missing solution {rr}"
    return "ok", ""


# ------------------------------------------------------------------ calculus
PROBES = [mp.mpf(t) for t in ("0.37", "1.13", "-0.71", "2.29", "-1.87", "0.83", "3.1", "-2.6", "0.19", "1.73")]


def judge_simp(task, claim, which="simp"):
    x = sym(task["x"])
    e = P(task["expr"])
    ans = [a for a in claim.get("answers", []) if a.get("kind") == "exact"]
    if not ans:
        return "unknown", "no exact answer"
    if ans[0].get("unconvertible"):
        return "unknown", "unconvertible"
    a = P(ans[0]["py"])
    n = 0
    for t in PROBES:
        v0 = evs(e, {x: t})
        v1 = evs(a, {x: t})
        if v0 is None:
            continue  # simplification may extend the domain (a condition is reported)
        if v1 is None:
            return "wrong", f"answer undefined at {task['x']} = {t} where the input is {mp.nstr(v0, 10)}"
        if not close(v0, v1, mp.mpf(10) ** -25):
            return "wrong", f"differs at {task['x']} = {t}: {mp.nstr(v0, 15)} vs {mp.nstr(v1, 15)}"
        n += 1
    if n < 2:
        # nowhere real (sqrt(-3) + w): compare sympy's principal complex values at a few points
        try:
            ec, ac = to_sympy_real(P(task["expr"], True)), P(ans[0]["py"], True)
            xs = [s for s in ec.free_symbols | ac.free_symbols if s.name == task["x"]]
            for t in [sp.Rational(7, 3), sp.Rational(-5, 2), sp.Rational(29, 7), sp.Rational(-41, 9)]:
                sub = {s: t for s in xs}
                wc = complex(sp.N(ec.subs(sub), 30))
                gc = complex(sp.N(ac.subs(sub), 30))
                if wc != wc or gc != gc or abs(wc) > 1e12:
                    continue
                if abs(wc - gc) > 1e-12 * max(1, abs(wc)):
                    return "wrong", f"complex value differs at {task['x']} = {t}: {gc} vs {wc}"
                n += 1
        except Exception:
            pass
    return ("ok" if n >= 2 else "unknown"), f"{n} points"


def judge_value(task, claim):
    e = P(task["expr"])
    try:
        want = ev(e, {})
    except (Undefined, ZeroDivisionError, ValueError):
        want = None
    ex = [a for a in claim.get("answers", []) if a.get("kind") in ("exact", "approx")]
    if not ex:
        if want is None:
            return "ok", "undefined, answered none"
        return "unknown", "no value"
    for a in ex:
        if a.get("unconvertible"):
            continue
        if a.get("py"):
            got = evs(P(a["py"]), {})
            if want is None:
                # Quelvra's real domain still does complex arithmetic (sqrt(-4)^2 = -4): compare with
                # sympy's principal complex value
                try:
                    wc = complex(sp.N(to_sympy_real(P(task["expr"], True)), 30))
                    gc = complex(sp.N(P(a["py"], True), 30))
                    if abs(wc - gc) <= 1e-12 * max(1, abs(wc)):
                        continue
                    return "wrong", f"{a.get('text')} = {gc} but the value is {wc}"
                except Exception:
                    return "unknown", "complex value"
            if got is None:
                # a complex answer to a real-undefined input is acceptable only when flagged; call it wrong
                return "wrong", f"answer {a.get('text')} is not real but the value is {mp.nstr(want, 15)}"
            if not close(got, want, mp.mpf(10) ** -25):
                return "wrong", f"{a.get('text')} = {mp.nstr(got, 15)} but the value is {mp.nstr(want, 20)}"
        elif a.get("approx"):
            av = a["approx"].replace(" ", "")
            if av == "undefined":
                if want is None:
                    continue
                return "wrong", f"approximation says undefined but the value is {mp.nstr(want, 15)}"
            if av.endswith("i"):
                try:
                    gc = complex(av.replace("i", "j"))
                    wc = complex(sp.N(to_sympy_real(P(task["expr"], True)), 30))
                    if abs(wc - gc) <= 1e-12 * max(1, abs(wc)):
                        continue
                    return "wrong", f"~{a['approx']} but the value is {wc}"
                except Exception:
                    return "unknown", "complex approx"
            got = mp.mpf(a["approx"])
            if want is None:
                try:
                    wc = complex(sp.N(to_sympy_real(P(task["expr"], True)), 30))
                    if abs(wc - complex(float(got))) <= 1e-12 * max(1, abs(wc)):
                        continue
                except Exception:
                    return "unknown", "complex value"
            if want is None or not close(got, want, mp.mpf(10) ** -15):
                return "wrong", f"~{a['approx']} but the value is {mp.nstr(want, 20) if want is not None else 'undefined'}"
    return "ok", ""


def judge_diff(task, claim):
    x = sym(task["x"])
    e = P(task["expr"])
    ans = [a for a in claim.get("answers", []) if a.get("kind") == "exact"]
    if not ans or ans[0].get("unconvertible"):
        return "unknown", "no convertible answer"
    a = P(ans[0]["py"])
    n = 0
    for t in PROBES:
        # true derivative numerically (the function must be defined around t)
        if evs(e, {x: t}) is None or evs(e, {x: t + mp.mpf("1e-8")}) is None or evs(e, {x: t - mp.mpf("1e-8")}) is None:
            continue
        try:
            d = mp.diff(lambda s: ev(e, {x: s}), t)
        except Exception:
            continue
        v = evs(a, {x: t})
        if v is None:
            return "wrong", f"derivative undefined at {t} where f is smooth"
        if not close(d, v, mp.mpf(10) ** -20):
            return "wrong", f"at {task['x']} = {t}: f' = {mp.nstr(d, 15)} but answer {mp.nstr(v, 15)}"
        n += 1
    return ("ok" if n >= 2 else "unknown"), f"{n} points"


def judge_anti(task, claim):
    x = sym(task["x"])
    e = P(task["expr"])
    ans = [a for a in claim.get("answers", []) if a.get("kind") == "exact"]
    if not ans or ans[0].get("unconvertible"):
        return "unknown", "no convertible answer"
    F = P(ans[0]["py"])
    n = 0
    for t in PROBES:
        fv = evs(e, {x: t})
        if fv is None:
            continue
        if evs(F, {x: t + mp.mpf("1e-10")}) is None or evs(F, {x: t - mp.mpf("1e-10")}) is None:
            return "wrong", f"antiderivative undefined at {t} where the integrand is {mp.nstr(fv, 10)}"
        try:
            d = mp.diff(lambda s: ev(F, {x: s}), t)
        except Exception:
            return "wrong", f"antiderivative not differentiable at {t}"
        if not close(d, fv, mp.mpf(10) ** -20):
            return "wrong", f"F'({t}) = {mp.nstr(d, 15)} but f = {mp.nstr(fv, 15)}"
        n += 1
    return ("ok" if n >= 2 else "unknown"), f"{n} points"


def quad(e, x, lo, hi):
    f = lambda s: ev(e, {x: s})
    # split at the points where the integrand is not smooth (|.|, sqrt edges) is left to tanh-sinh
    return mp.quad(f, [lo, hi], maxdegree=10, error=True)


def judge_defint(task, claim):
    x = sym(task["x"])
    e = P(task["expr"])
    lo, hi = P(task["lo"], True), P(task["hi"], True)
    ans = [a for a in claim.get("answers", []) if a.get("kind") in ("exact", "approx")]
    nonelab = " ".join((a.get("label") or "") + " " + (a.get("text") or "") for a in claim.get("answers", []))
    lo_v = -mp.inf if lo == -sp.oo else ev(lo, {})
    hi_v = mp.inf if hi == sp.oo else ev(hi, {})
    # the integrand must be defined (finite) on the open interval; sample it
    samples = [lo_v + (hi_v - lo_v) * mp.mpf(i) / 997 for i in range(1, 997)] if mp.isfinite(hi_v) else [lo_v + mp.mpf(i) / 7 for i in range(1, 997)]
    undefined = [s for s in samples if evs(e, {x: s}) is None]
    # sympy's own verdict as a second opinion
    ref = None
    try:
        ref = with_timeout(6, lambda: sp.integrate(to_sympy_real(P(task["expr"], True)), (x, lo, hi)))
        if ref.has(sp.Integral):
            ref = None
        elif isinstance(ref, sp.AccumBounds) or ref.has(sp.AccumBounds, sp.oo, -sp.oo, sp.zoo, sp.nan):
            ref = sp.oo  # oscillates or diverges: no finite value

    except (Exception, Timeout):
        ref = None
    if not ans:
        if re.search(r"diverg|does not exist|undefined|not converge|infinite", nonelab, re.I):
            # check divergence numerically
            if undefined:
                return "ok", "integrand undefined in the interval"
            try:
                v, err = with_timeout(20, quad, e, x, lo_v, hi_v)
                if (lo_v == -mp.inf or hi_v == mp.inf) and ref is None:
                    return "unknown", "divergence claim on an infinite range, sympy undecided"
                if mp.isfinite(v) and err < 1e-10 * max(1, abs(v)) and (ref is None or ref.is_finite):
                    return "wrong", f"claims divergence but quadrature gives {mp.nstr(v, 15)} (err {mp.nstr(err, 3)})"
            except (Timeout, Undefined, ZeroDivisionError, ValueError, OverflowError):
                pass
            return "ok", "divergent"
        return "unknown", "no value"
    a = ans[0]
    if a.get("unconvertible"):
        return "unknown", "unconvertible"
    got = evs(P(a["py"]), {}) if a.get("py") else mp.mpf(a["approx"])
    if got is None:
        return "wrong", f"answer {a.get('text')} not real"
    if undefined:
        return "wrong", f"integrand undefined at {mp.nstr(undefined[0], 8)} inside the interval but answer {a.get('text')}"
    try:
        v, err = with_timeout(20, quad, e, x, lo_v, hi_v)
    except (Timeout, Undefined, ZeroDivisionError, ValueError, OverflowError):
        v, err = None, None
    refv = None
    if ref is not None:
        refv = mpN(ref)
    infinite = not (mp.isfinite(lo_v) and mp.isfinite(hi_v))
    if infinite and ref is not None and not ref.is_finite:
        return "unknown", "sympy says divergent/oscillatory"
    if v is not None and err < mp.mpf(10) ** -12 * max(1, abs(v)) and not (infinite and ref is None):
        if not close(got, v, mp.mpf(10) ** -10):
            if refv is not None and close(got, refv, mp.mpf(10) ** -20):
                return "unknown", "quadrature disagrees but sympy agrees"
            return "wrong", f"{a.get('text')} = {mp.nstr(got, 15)} but quadrature gives {mp.nstr(v, 15)}"
        return "ok", ""
    if refv is not None:
        return ("ok", "sympy") if close(got, refv, mp.mpf(10) ** -20) else ("wrong", f"{mp.nstr(got, 15)} but sympy {mp.nstr(refv, 15)} (quadrature inconclusive)")
    return "unknown", "quadrature inconclusive"


def judge_limit(task, claim):
    x = sym(task["x"])
    e = P(task["expr"])
    pt = P(task["pt"], True)
    ans = claim.get("answers", [])
    try:
        ref = with_timeout(8, lambda: sp.limit(to_sympy_real(P(task["expr"], True)), x, pt))
    except (Exception, Timeout):
        ref = None
    # two-sided numeric probe
    f = lambda s: evs(e, {x: s})
    if pt == sp.oo:
        seq = [f(mp.mpf(10) ** k) for k in (6, 9, 12, 15)]
    else:
        p0 = ev(pt, {})
        seq = [f(p0 + mp.mpf(10) ** -k) for k in (8, 12, 16)] + [f(p0 - mp.mpf(10) ** -k) for k in (8, 12, 16)]
    ex = [a for a in ans if a.get("kind") == "exact"]
    none = [a for a in ans if a.get("kind") == "none"]
    if ex:
        a = ex[0]
        if a.get("unconvertible"):
            return "unknown", "unconvertible"
        g = P(a["py"], True)
        if g in (sp.oo, -sp.oo):
            if ref is not None and ref != g and ref.is_finite:
                return "wrong", f"claims {g} but sympy {ref}"
            return "ok", "infinite"
        got = evs(P(a["py"]), {})
        if got is None:
            return "unknown", "value not real"
        if ref is not None and ref.is_finite and ref.is_real:
            rv = mp.mpf(str(sp.N(ref, 40)))
            return ("ok", "") if close(got, rv, mp.mpf(10) ** -20) else ("wrong", f"{a.get('text')} but sympy {ref}")
        if ref is not None and ref in (sp.oo, -sp.oo, sp.zoo):
            return "wrong", f"{a.get('text')} but sympy {ref}"
        vals = [s for s in seq if s is not None]
        if vals and all(close(v, got, mp.mpf(10) ** -5) for v in vals):
            return "ok", "numeric"
        return "unknown", f"sympy {ref}"
    if none:
        if ref is not None and ref.is_finite and ref.is_real:
            # one-sided limits may differ even though sympy (right-sided by default) gives one
            if pt != sp.oo:
                p0 = ev(pt, {})
                l = [f(p0 - mp.mpf(10) ** -k) for k in (10, 14)]
                r = [f(p0 + mp.mpf(10) ** -k) for k in (10, 14)]
                if None not in l and None not in r and close(l[-1], r[-1], mp.mpf(10) ** -6):
                    return "wrong", f"claims no limit but it is {ref}"
                return "ok", "one-sided limits differ"
            return "wrong", f"claims no limit but sympy {ref}"
        return "ok", ""
    return "unknown", "no answer"


def judge_sum(task, claim):
    n = sym(task["n"])
    e = P(task["expr"])
    lo, hi = P(task["lo"], True), P(task["hi"], True)
    ans = [a for a in claim.get("answers", []) if a.get("kind") in ("exact", "approx")]
    labs = " ".join((a.get("label") or "") + " " + (a.get("text") or "") for a in claim.get("answers", []))
    if hi.free_symbols:
        # symbolic upper limit: check against direct sums for several n
        if not ans or ans[0].get("unconvertible"):
            return "unknown", "no answer"
        S = P(ans[0]["py"])
        hs = list(hi.free_symbols)[0]
        for N_ in range(int(lo), int(lo) + 8):
            direct = mp.fsum([ev(e, {n: mp.mpf(k)}) for k in range(int(lo), N_ + 1)])
            got = evs(S, {hs: mp.mpf(N_)})
            if got is None or not close(direct, got, mp.mpf(10) ** -25):
                return "wrong", f"at n = {N_}: direct {direct} vs {got}"
        return "ok", ""
    if hi == sp.oo:
        try:
            ref = with_timeout(8, lambda: sp.summation(to_sympy_real(P(task["expr"], True)), (n, lo, hi)))
        except (Exception, Timeout):
            ref = None
        refv = None
        if ref is not None and not ref.has(sp.Sum):
            refv = "inf" if ref in (sp.oo, -sp.oo) else mpN(ref)
        if not ans:
            if re.search(r"diverg|infin", labs, re.I):
                return ("wrong", f"claims divergence but sympy {ref}") if isinstance(refv, mp.mpf) else ("ok", "")
            return "unknown", "no value"
        a = ans[0]
        if a.get("unconvertible"):
            return "unknown", "unconvertible"
        got = evs(P(a["py"]), {}) if a.get("py") else mp.mpf(a["approx"])
        if a.get("py") and P(a["py"], True) in (sp.oo, -sp.oo):
            return ("ok", "") if refv == "inf" or refv is None else ("wrong", f"claims infinite; sympy {ref}")
        if got is None:
            return "unknown", "not real"
        if isinstance(refv, mp.mpf):
            return ("ok", "") if close(got, refv, mp.mpf(10) ** -20) else ("wrong", f"{a.get('text')} but sympy {ref}")
        if refv == "inf":
            return "wrong", f"{a.get('text')} but the sum diverges"
        try:
            v = mp.nsum(lambda k: ev(e, {n: k}), [int(lo), mp.inf])
            return ("ok", "nsum") if close(got, v, mp.mpf(10) ** -12) else ("unknown", f"nsum {v}")
        except Exception:
            return "unknown", ""
    # finite
    direct = mp.fsum([ev(e, {n: mp.mpf(k)}) for k in range(int(lo), int(hi) + 1)])
    if not ans:
        return "unknown", "no value"
    a = ans[0]
    got = evs(P(a["py"]), {}) if a.get("py") else mp.mpf(a["approx"])
    if got is None or not close(got, direct, mp.mpf(10) ** -25):
        return "wrong", f"{a.get('text')} but the sum is {direct}"
    return "ok", ""


def judge_ode(task, claim):
    X = sym("x")
    ans = [a for a in claim.get("answers", []) if a.get("kind") == "exact" and a.get("py")]
    if not ans:
        return "unknown", "no answer"
    y = P(ans[0]["py"])
    consts = sorted([s for s in y.free_symbols if s != X], key=lambda s: s.name)
    order = task["order"]
    if not task["ics"] and len(consts) < order:
        return "wrong", f"general solution of an order-{order} ODE has {len(consts)} constants"
    if task["ics"] and consts:
        return "wrong", f"initial value problem left constants {consts}"
    ode = parse_expr(task["ode"], local_dict={"Y0": sp.Symbol("Y0"), "Y1": sp.Symbol("Y1"), "Y2": sp.Symbol("Y2"), "X": X, "exp": sp.exp, "sin": sp.sin, "cos": sp.cos})
    for trial in range(3):
        cv = {c: mp.mpf(["0.7", "-1.3", "2.1"][(trial + i) % 3]) for i, c in enumerate(consts)}
        for t in PROBES[:5]:
            env = dict(cv)
            env[X] = t
            f = lambda s: ev(y, {**cv, X: s})
            try:
                y0 = f(t)
                y1 = mp.diff(f, t)
                y2 = mp.diff(f, t, 2)
            except Exception:
                continue
            r = ev(ode, {sp.Symbol("Y0"): y0, sp.Symbol("Y1"): y1, sp.Symbol("Y2"): y2, X: t})
            if abs(r) > mp.mpf(10) ** -15 * max(1, abs(y0), abs(y1), abs(y2)):
                return "wrong", f"residual {mp.nstr(r, 5)} at x = {t}"
    for d, x0, v in task["ics"]:
        f = lambda s: ev(y, {X: s})
        got = f(mp.mpf(x0)) if d == 0 else mp.diff(f, mp.mpf(x0), d)
        if not close(got, mp.mpf(v), mp.mpf(10) ** -15):
            return "wrong", f"initial condition y{chr(39) * d}({x0}) = {v} fails: {mp.nstr(got, 10)}"
    return "ok", ""


def judge_matrix(task, claim):
    M = sp.Matrix(task["M"])
    op = task["op"]
    ans = [a for a in claim.get("answers", []) if a.get("kind") == "exact"]
    labs = " ".join((a.get("label") or "") + " " + (a.get("text") or "") for a in claim.get("answers", []))
    if op == "inv" and M.det() == 0:
        return ("wrong", "inverse of a singular matrix") if ans else ("ok", "singular")
    if not ans or ans[0].get("unconvertible"):
        return "unknown", "no answer"
    got = P(ans[0]["py"], True)
    want = {"det": lambda: M.det(), "inv": lambda: M.inv(), "rank": lambda: M.rank(), "transpose": lambda: M.T, "trace": lambda: M.trace(), "square": lambda: M * M}[op]()
    if isinstance(got, list):
        got = sp.Matrix(got)
    try:
        same = sp.simplify(sp.Matrix(got) - want) == sp.zeros(*want.shape) if hasattr(want, "shape") else sp.simplify(got - want) == 0
    except Exception as e:
        return "wrong", f"shape/type mismatch: {got} vs {want}"
    return ("ok", "") if same else ("wrong", f"{ans[0].get('text')} but {want}")


JUDGES = {"eq": judge_eq, "ineq": judge_ineq, "sys": judge_sys, "simp": judge_simp, "value": judge_value, "diff": judge_diff,
          "anti": judge_anti, "defint": judge_defint, "limit": judge_limit, "sum": judge_sum, "ode": judge_ode, "matrix": judge_matrix}


def judge_one(rec):
    task, claim = rec["task"], rec["claim"]
    if not claim.get("verified"):
        return {"id": rec["id"], "verdict": "unverified", "detail": ""}
    try:
        v, d = with_timeout(60, JUDGES[task["kind"]], task, claim)
    except Timeout:
        v, d = "unknown", "oracle timeout"
    except Exception as e:
        v, d = "unknown", "oracle error: " + repr(e)[:200]
    return {"id": rec["id"], "verdict": v, "detail": d}


def main():
    recs = json.load(sys.stdin)
    jobs = int(os.environ.get("ORACLE_JOBS", "12"))
    if jobs > 1 and len(recs) > 20:
        with mproc.Pool(jobs) as pool:
            out = list(pool.imap_unordered(judge_one, recs, chunksize=1))
    else:
        out = [judge_one(r) for r in recs]
    json.dump(out, sys.stdout)


if __name__ == "__main__":
    main()
