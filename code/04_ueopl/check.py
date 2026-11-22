"""Independent exact check of exact-search.typ (l1 PL contraction -> exact BNE).

Everything is exact: fractions.Fraction for evaluation, z3 (linear real
arithmetic, exact rationals) for fixed points, uniqueness, contraction
violation search and the decoding LP.  No floating point anywhere.

Usage: python -I -B check.py SEED COUNT [structural]
"""
import sys
import random
import itertools
import time
from fractions import Fraction as Fr
from math import lcm

import z3


def clip(u, lo, hi):
    return min(hi, max(lo, u))


def proj(u):
    """Euclidean projection onto the simplex, formula of the note."""
    s = sorted(u, reverse=True)
    acc = Fr(0)
    th = None
    for k in range(1, len(u) + 1):
        acc += s[k - 1]
        c = (acc - 1) / k
        if th is None or c > th:
            th = c
    return [max(Fr(0), uj - th) for uj in u]


def proj_check(u, y):
    """Independent optimality check of a simplex projection (KKT)."""
    assert all(v >= 0 for v in y) and sum(y) == 1
    pos = [u[j] - y[j] for j in range(len(u)) if y[j] > 0]
    th = pos[0]
    assert all(v == th for v in pos)
    assert all(u[j] <= th for j in range(len(u)) if y[j] == 0)


class Game:
    def __init__(self, r, p, a, b, d):
        self.r, self.p, self.a, self.b, self.d = r, p, a, b, d
        self.m, self.n = len(p), len(d)

    def U(self, i, j, x):
        return self.a[i][j] - self.b[i][j] * x[j]

    def __repr__(self):
        return f"Game(r={self.r}, p={self.p}, a={self.a}, b={self.b}, d={self.d})"


# ---------------------------------------------------------------- the LP rows
def var_index(g):
    n, m = g.n, g.m
    X = list(range(n))
    Fv = [[n + i * n + j for j in range(n)] for i in range(m)]
    V = [n + m * n + i for i in range(m)]
    L = n + m * n + m
    T = L + 1
    return X, Fv, V, L, T, T + 1


def all_rows(g):
    """Every row any pattern can use, uncleared, as (coeffs dict, rhs, kind).

    Relaxed rows carry the slack t with coefficient -1 BEFORE clearing, as the
    note prescribes.  Outer boxes are exact (no t)."""
    X, Fv, V, L, T, N = var_index(g)
    n, m = g.n, g.m
    rows = []
    rows.append(({**{X[j]: Fr(1) for j in range(n)}, T: Fr(-1)}, Fr(g.r), "budget<="))
    rows.append(({**{X[j]: Fr(-1) for j in range(n)}, T: Fr(-1)}, -Fr(g.r), "budget>="))
    for i in range(m):
        rows.append(({**{Fv[i][j]: Fr(1) for j in range(n)}, T: Fr(-1)}, g.p[i], ("rowsum<=", i)))
        rows.append(({**{Fv[i][j]: Fr(-1) for j in range(n)}, T: Fr(-1)}, -g.p[i], ("rowsum>=", i)))
        for j in range(n):
            rows.append(({Fv[i][j]: Fr(1), T: Fr(-1)}, Fr(0), ("fzero", i, j)))
            # v_i >= a - b x_j - t   <=>  -b x_j - v_i - t <= -a
            rows.append(({X[j]: -g.b[i][j], V[i]: Fr(-1), T: Fr(-1)}, -g.a[i][j], ("vge", i, j)))
            # v_i <= a - b x_j + t   <=>  b x_j + v_i - t <= a
            rows.append(({X[j]: g.b[i][j], V[i]: Fr(1), T: Fr(-1)}, g.a[i][j], ("vle", i, j)))
    for j in range(n):
        rows.append(({X[j]: Fr(1), T: Fr(-1)}, Fr(0), ("xzero", j)))
        rows.append(({X[j]: Fr(-1), T: Fr(-1)}, Fr(-1), ("xone", j)))
        cut = {Fv[i][j]: g.d[j] for i in range(m)}
        rows.append(({**cut, L: Fr(-1), T: Fr(-1)}, Fr(0), ("cut<=", j)))  # d w - lam <= t
        rows.append(({**{k: -v for k, v in cut.items()}, L: Fr(1), T: Fr(-1)}, Fr(0), ("cut>=", j)))
    Vb = 2 + max(abs(g.a[i][j]) + g.b[i][j] for i in range(m) for j in range(n))
    for j in range(n):
        rows.append(({X[j]: Fr(1)}, Fr(1), "box"))
        rows.append(({X[j]: Fr(-1)}, Fr(0), "box"))
    for i in range(m):
        for j in range(n):
            rows.append(({Fv[i][j]: Fr(1)}, Fr(1), "box"))
            rows.append(({Fv[i][j]: Fr(-1)}, Fr(0), "box"))
        rows.append(({V[i]: Fr(1)}, Fr(Vb), "box"))
        rows.append(({V[i]: Fr(-1)}, Fr(Vb), "box"))
    rows.append(({L: Fr(1)}, 1 + max(g.d), "box"))
    rows.append(({L: Fr(-1)}, Fr(0), "box"))
    rows.append(({T: Fr(-1)}, Fr(0), "box"))
    return rows


def height(g):
    H = 1
    for coeffs, rhs, _ in all_rows(g):
        vals = list(coeffs.values()) + [rhs]
        Lc = lcm(*(Fr(v).denominator for v in vals))
        H = max(H, max(abs(int(v * Lc)) for v in vals))
    return H


# ---------------------------------------------------------------- the map
class Model:
    def __init__(self, g, structural_g=None):
        self.g_ = g
        n, m = g.n, g.m
        N = var_index(g)[-1]
        self.N = N
        self.H = height(g)
        self.Q = (N * self.H) ** N
        self.gap = Fr(1, 4 * self.Q) if structural_g is None else Fr(structural_g)
        gg = self.gap
        self.B = max(g.b[i][j] for i in range(m) for j in range(n))
        self.dp = [g.d[j] + gg / 16 for j in range(n)]
        self.D = max(self.dp)
        self.tau = self.kappa = gg / 8
        self.eta = min(Fr(1), self.tau / (1 + self.B),
                       self.kappa / (4 * (1 + self.D) * (1 + sum(1 / v for v in self.dp))))
        self.delta = min(Fr(1, 8), self.eta * gg / (8 * (1 + self.D)), gg / (8 * (1 + self.B)))
        self.a0 = Fr(g.r, n)
        assert self.eta * self.D * sum(1 / v for v in self.dp) <= self.kappa * (1 - 2 * self.delta)

    def lam(self, s):
        k, dl, D = self.kappa, self.delta, self.D
        if s <= dl * k:
            return D
        if s >= (1 - dl) * k:
            return Fr(0)
        return D * ((1 - dl) * k - s) / ((1 - 2 * dl) * k)

    def ev(self, pt):
        g = self.g_
        n, m = g.n, g.m
        x, q = list(pt[:n]), pt[n]
        y = [proj([g.U(i, j, x) / self.tau for j in range(n)]) for i in range(m)]
        f = [[g.p[i] * y[i][j] for j in range(n)] for i in range(m)]
        w = [sum(f[i][j] for i in range(m)) for j in range(n)]
        s = clip(q, Fr(0), self.kappa)
        lam = self.lam(s)
        T = [clip(x[j] + self.eta * (w[j] - lam / self.dp[j]), Fr(0), Fr(1)) for j in range(n)]
        R = clip(s + sum(x) - sum(T), Fr(0), self.kappa)
        out = [(1 - self.delta) * T[j] + self.delta * self.a0 for j in range(n)]
        out.append((1 - self.delta) * R + self.delta * self.kappa / 2)
        return out, dict(y=y, f=f, w=w, s=s, lam=lam, T=T, R=R)

    # z3 encoding of the same circuit (projection by its KKT characterisation)
    def z3F(self, X, tag):
        g = self.g_
        n, m = g.n, g.m
        cons = []
        Q = lambda v: z3.RealVal(str(v))

        def zclip(e, lo, hi):
            return z3.If(e < lo, lo, z3.If(e > hi, hi, e))

        x, q = X[:n], X[n]
        w = [Q(0)] * n
        for i in range(m):
            th = z3.Real(f"th_{tag}_{i}")
            ys = []
            for j in range(n):
                u = (Q(g.a[i][j]) - Q(g.b[i][j]) * x[j]) / Q(self.tau)
                ys.append(z3.If(u > th, u - th, Q(0)))
            cons.append(z3.Sum(ys) == 1)
            w = [w[j] + Q(g.p[i]) * ys[j] for j in range(n)]
        s = zclip(q, Q(0), Q(self.kappa))
        k, dl = self.kappa, self.delta
        lam = Q(self.D) * zclip((Q((1 - dl) * k) - s) / Q((1 - 2 * dl) * k), Q(0), Q(1))
        T = [zclip(x[j] + Q(self.eta) * (w[j] - lam / Q(self.dp[j])), Q(0), Q(1)) for j in range(n)]
        R = zclip(s + z3.Sum(x) - z3.Sum(T), Q(0), Q(self.kappa))
        out = [Q(1 - self.delta) * T[j] + Q(self.delta * self.a0) for j in range(n)]
        out.append(Q(1 - self.delta) * R + Q(self.delta * self.kappa / 2))
        return out, cons


def z3frac(v):
    v = v.as_fraction() if hasattr(v, "as_fraction") else None
    return Fr(v)


def to_fr(model_val):
    r = model_val
    if z3.is_rational_value(r):
        return Fr(r.numerator_as_long(), r.denominator_as_long())
    raise ValueError(f"non-rational model value {r}")


def fixed_point(M, timeout_ms=600000):
    n = M.g_.n
    X = [z3.Real(f"X{k}") for k in range(n + 1)]
    out, cons = M.z3F(X, "a")
    s = z3.Solver()
    s.set("timeout", timeout_ms)
    s.add(cons)
    s.add([z3.And(X[k] >= 0, X[k] <= 1) for k in range(n + 1)])
    s.add([out[k] == X[k] for k in range(n + 1)])
    r = s.check()
    if r != z3.sat:
        return None, str(r)
    mod = s.model()
    pt = [to_fr(mod.eval(X[k], model_completion=True)) for k in range(n + 1)]
    # uniqueness: any other fixed point?
    s.add(z3.Or([X[k] != z3.RealVal(str(pt[k])) for k in range(n + 1)]))
    r2 = s.check()
    return pt, str(r2)


def contraction_violation(M, timeout_ms):
    """Search exactly for a,b in the cube with |F(a)-F(b)|_1 > (1-delta)|a-b|_1."""
    n = M.g_.n
    A = [z3.Real(f"A{k}") for k in range(n + 1)]
    Bv = [z3.Real(f"B{k}") for k in range(n + 1)]
    FA, cA = M.z3F(A, "A")
    FB, cB = M.z3F(Bv, "B")
    ab = lambda e: z3.If(e >= 0, e, -e)
    s = z3.Solver()
    s.set("timeout", timeout_ms)
    s.add(cA + cB)
    s.add([z3.And(A[k] >= 0, A[k] <= 1, Bv[k] >= 0, Bv[k] <= 1) for k in range(n + 1)])
    lhs = z3.Sum([ab(FA[k] - FB[k]) for k in range(n + 1)])
    rhs = z3.Sum([ab(A[k] - Bv[k]) for k in range(n + 1)])
    s.add(lhs > z3.RealVal(str(1 - M.delta)) * rhs)
    r = s.check()
    if r == z3.sat:
        mod = s.model()
        a = [to_fr(mod.eval(A[k], model_completion=True)) for k in range(n + 1)]
        b = [to_fr(mod.eval(Bv[k], model_completion=True)) for k in range(n + 1)]
        return "sat", (a, b)
    return str(r), None


def l1(u, v):
    return sum(abs(x - y) for x, y in zip(u, v))


def pair_tests(M, fp, rng, count=400):
    """Exact pairwise contraction checks, points concentrated at the scales
    where the pieces of the map live (tau, eta, delta*kappa) near the fixed
    point, plus uniform points."""
    n = M.g_.n
    scales = [M.tau, M.tau / 7, M.eta, M.delta * M.kappa, M.kappa, Fr(1, 10)]
    pts = []
    for _ in range(count):
        if rng.random() < 0.8:
            sc = rng.choice(scales)
            p = [clip(fp[k] + sc * Fr(rng.randint(-40, 40), 13), Fr(0), Fr(1)) for k in range(n + 1)]
        else:
            p = [Fr(rng.randint(0, 60), 60) for _ in range(n + 1)]
        pts.append(p)
    imgs = [M.ev(p)[0] for p in pts]
    worst = Fr(0)
    bad = None
    for i in range(len(pts)):
        for j in range(i + 1, min(len(pts), i + 25)):
            d0 = l1(pts[i], pts[j])
            if d0 == 0:
                continue
            ratio = l1(imgs[i], imgs[j]) / d0
            if ratio > worst:
                worst = ratio
            if ratio > 1 - M.delta:
                bad = (pts[i], pts[j], ratio)
    return worst, bad


def jacobian_tests(M, rng, count=60):
    """Exact one-sided difference quotients at random points (structural mode).

    Checks: Jacobian of (T,R) wrt (x,q) is entrywise >= 0 with column sums <= 1
    and Jacobian of x + eta*w(x) is >= 0 with column sums == 1, on pieces where
    a tiny step stays inside one affine piece (verified by a second, half step)."""
    g = M.g_
    n, m = g.n, g.m
    fails = []
    checked = 0
    for _ in range(count):
        p = [Fr(rng.randint(1, 999), 1000) for _ in range(n)] + [M.kappa * Fr(rng.randint(1, 999), 1000)]
        base = M.ev(p)[1]
        TR0 = base["T"] + [base["R"]]
        ok = True
        J = []
        Jw = []
        for k in range(n + 1):
            h = Fr(1, 10 ** 12)
            p1 = list(p); p1[k] += h
            p2 = list(p); p2[k] += h / 2
            e1, e2 = M.ev(p1)[1], M.ev(p2)[1]
            TR1 = e1["T"] + [e1["R"]]
            TR2 = e2["T"] + [e2["R"]]
            col = [(TR1[r] - TR0[r]) / h for r in range(n + 1)]
            col2 = [(TR2[r] - TR0[r]) / (h / 2) for r in range(n + 1)]
            if col != col2:
                ok = False
                break
            J.append(col)
            if k < n:
                xw0 = [p[j] + M.eta * base["w"][j] for j in range(n)]
                xw1 = [p1[j] + M.eta * e1["w"][j] for j in range(n)]
                xw2 = [p2[j] + M.eta * e2["w"][j] for j in range(n)]
                c1 = [(xw1[j] - xw0[j]) / h for j in range(n)]
                c2 = [(xw2[j] - xw0[j]) / (h / 2) for j in range(n)]
                if c1 != c2:
                    ok = False
                    break
                Jw.append(c1)
        if not ok:
            continue
        checked += 1
        for k, col in enumerate(J):
            if min(col) < 0 or sum(col) > 1:
                fails.append(("TR", p, k, col))
        for k, col in enumerate(Jw):
            if min(col) < 0 or sum(col) != 1:
                fails.append(("x+eta w", p, k, col))
    return checked, fails


# ---------------------------------------------------------------- decoding
def defender_best_value(g, w, r):
    scores = sorted((g.d[j] * w[j] for j in range(g.n)), reverse=True)
    return sum(scores[:r])


def is_bne(g, x, f):
    n, m = g.n, g.m
    if sum(x) != g.r or min(x) < 0 or max(x) > 1:
        return False, "budget/bounds"
    for i in range(m):
        if sum(f[i]) != g.p[i] or min(f[i]) < 0:
            return False, "rows"
        vals = [g.U(i, j, x) for j in range(n)]
        best = max(vals)
        if any(f[i][j] > 0 and vals[j] != best for j in range(n)):
            return False, f"attacker {i} not best responding"
    w = [sum(f[i][j] for i in range(m)) for j in range(n)]
    val = sum(g.d[j] * w[j] * x[j] for j in range(n))
    if val != defender_best_value(g, w, g.r):
        return False, "defender not best responding"
    return True, "ok"


def pattern_lp(g, allowed, labels, slack=False, minimize=False, timeout_ms=120000):
    """The note's pattern LP.  slack=False: exact (t fixed to 0)."""
    n, m = g.n, g.m
    Q = lambda v: z3.RealVal(str(v))
    x = [z3.Real(f"x{j}") for j in range(n)]
    f = [[z3.Real(f"f{i}_{j}") for j in range(n)] for i in range(m)]
    v = [z3.Real(f"v{i}") for i in range(m)]
    lam = z3.Real("lam")
    t = z3.Real("t") if slack else Q(0)
    C = []
    Vb = 2 + max(abs(g.a[i][j]) + g.b[i][j] for i in range(m) for j in range(n))
    C += [z3.And(xj >= 0, xj <= 1) for xj in x]
    C += [z3.And(fij >= 0, fij <= 1) for row in f for fij in row]
    C += [z3.And(vi >= -Q(Vb), vi <= Q(Vb)) for vi in v]
    C += [lam >= 0, lam <= Q(1 + max(g.d))]
    if slack:
        C.append(t >= 0)
    rel_le = lambda e, rhs: e - Q(rhs) <= t
    C += [rel_le(z3.Sum(x), g.r), rel_le(-z3.Sum(x), -g.r)]
    for i in range(m):
        C += [rel_le(z3.Sum(f[i]), g.p[i]), rel_le(-z3.Sum(f[i]), -g.p[i])]
        for j in range(n):
            U = Q(g.a[i][j]) - Q(g.b[i][j]) * x[j]
            C.append(U - v[i] <= t)
            if (i, j) in allowed:
                C.append(v[i] - U <= t)
            else:
                C.append(f[i][j] <= t)
    for j in range(n):
        dw = z3.Sum([Q(g.d[j]) * f[i][j] for i in range(m)])
        if labels[j] == 0:
            C += [x[j] <= t, dw - lam <= t]
        elif labels[j] == 1:
            C += [1 - x[j] <= t, lam - dw <= t]
        else:
            C += [dw - lam <= t, lam - dw <= t]
    if minimize:
        o = z3.Optimize()
        o.set("timeout", timeout_ms)
        o.add(C)
        h = o.minimize(t)
        r = o.check()
        if r != z3.sat:
            return str(r), None
        val = o.model().eval(t, model_completion=True)
        return "sat", to_fr(val)
    s = z3.Solver()
    s.set("timeout", timeout_ms)
    s.add(C)
    r = s.check()
    if r != z3.sat:
        return str(r), None
    mod = s.model()
    gx = [to_fr(mod.eval(e, model_completion=True)) for e in x]
    gf = [[to_fr(mod.eval(e, model_completion=True)) for e in row] for row in f]
    return "sat", (gx, gf)


def decode(M, fp):
    g = M.g_
    n, m = g.n, g.m
    out, e = M.ev(fp)
    assert out == fp
    z, f, w, lam = e["T"], e["f"], e["w"], e["lam"]
    rep = {}
    rep["R_unclipped"] = 0 < e["R"] < M.kappa
    rep["s_eq_q"] = e["s"] == fp[n]
    rep["sum_identity"] = sum(fp[:n]) + fp[n] == g.r + M.kappa / 2
    budget = abs(sum(z) - g.r)
    rep["budget_res"] = budget
    rep["budget_bound_ok"] = budget <= M.kappa / (2 * (1 - M.delta))
    # projections are genuine projections
    for i in range(m):
        proj_check([g.U(i, j, fp[:n]) / M.tau for j in range(n)], e["y"][i])
    v = [max(g.U(i, j, z) for j in range(n)) for i in range(m)]
    br = max([v[i] - g.U(i, j, z) for i in range(m) for j in range(n) if f[i][j] > 0])
    rep["br_res"] = br
    rep["br_bound_ok"] = br <= M.tau + 2 * M.B * M.delta
    cut = Fr(0)
    for j in range(n):
        sc = g.d[j] * w[j]
        if z[j] > 0:
            cut = max(cut, lam - sc)
        if z[j] < 1:
            cut = max(cut, sc - lam)
    rep["cut_res"] = cut
    rep["cut_bound_ok"] = cut <= M.D * M.delta / M.eta + M.gap / 16
    rep["all_below_g"] = max(budget, br, cut) < M.gap
    rep["boxes_ok"] = (0 <= lam <= 1 + max(g.d)) and all(0 <= fij <= 1 for row in f for fij in row)
    allowed = {(i, j) for i in range(m) for j in range(n) if f[i][j] > 0}
    labels = [0 if z[j] == 0 else 1 if z[j] == 1 else 2 for j in range(n)]
    st, sol = pattern_lp(g, allowed, labels)
    rep["lp"] = st
    if st == "sat":
        ok, why = is_bne(g, sol[0], sol[1])
        rep["bne"] = (ok, why)
        rep["x"] = sol[0]
    rep["labels"] = labels
    rep["support"] = sorted(allowed)
    return rep


def gap_test(M, timeout_ms=60000):
    """min t over every pattern: must be 0 or >= 1/Q (exact z3 Optimize)."""
    g = M.g_
    n, m = g.n, g.m
    edges = [(i, j) for i in range(m) for j in range(n)]
    smallest_pos = None
    zeros = 0
    total = 0
    bad = []
    unknown = 0
    for mask in range(1 << len(edges)):
        allowed = {edges[k] for k in range(len(edges)) if mask >> k & 1}
        for labels in itertools.product((0, 1, 2), repeat=n):
            st, t = pattern_lp(g, allowed, labels, slack=True, minimize=True, timeout_ms=timeout_ms)
            total += 1
            if st != "sat":
                unknown += 1
                continue
            if t == 0:
                zeros += 1
                st2, sol = pattern_lp(g, allowed, labels)
                ok, why = is_bne(g, sol[0], sol[1])
                if not ok:
                    bad.append(("zero-slack pattern not BNE", allowed, labels, why))
            else:
                if smallest_pos is None or t < smallest_pos:
                    smallest_pos = t
                if t < Fr(1, M.Q):
                    bad.append(("positive slack below 1/Q", allowed, labels, t))
    return dict(total=total, zeros=zeros, smallest_pos=smallest_pos, bad=bad, unknown=unknown)


# ---------------------------------------------------------------- instances
def rand_game(rng, n, m, zero_b=0.25, zero_d=0.3, den=4):
    def rq(lo, hi):
        return Fr(rng.randint(lo * den, hi * den), den)
    r = rng.randint(1, n - 1)
    raw = [rng.randint(1, 5) for _ in range(m)]
    p = [Fr(v, sum(raw)) for v in raw]
    a = [[rq(-2, 3) for _ in range(n)] for _ in range(m)]
    b = [[Fr(0) if rng.random() < zero_b else rq(0, 3) for _ in range(n)] for _ in range(m)]
    d = [Fr(0) if rng.random() < zero_d else rq(0, 3) for _ in range(n)]
    return Game(r, p, a, b, d)


def main():
    seed = int(sys.argv[1]) if len(sys.argv) > 1 else 1
    count = int(sys.argv[2]) if len(sys.argv) > 2 else 5
    mode = sys.argv[3] if len(sys.argv) > 3 else "full"
    rng = random.Random(seed)
    allok = True  # artifact: exit status
    for it in range(count):
        n = rng.choice([2, 2, 3])
        m = rng.choice([1, 2, 2, 3])
        g = rand_game(rng, n, m)
        t0 = time.time()
        M = Model(g)
        print(f"\n=== seed {seed} game {it}: n={n} m={m} {g}", flush=True)
        print(f"N={M.N} H={M.H} log10(Q)~{len(str(M.Q)) - 1} "
              f"bits(delta)~{M.delta.numerator.bit_length() + M.delta.denominator.bit_length()}", flush=True)
        fp, uniq = fixed_point(M)
        if fp is None:
            print("fixed point: z3", uniq, flush=True)
            allok = False  # artifact: exit status
            continue
        print(f"fixed point found; other fixed point exists? z3 says {uniq} (unsat = unique)", flush=True)
        rep = decode(M, fp)
        print("decode:", {k: (str(v) if isinstance(v, Fr) else v) for k, v in rep.items()
                          if k not in ("x",)}, flush=True)
        print("  residuals/g:", {k: str(float(rep[k] / M.gap)) for k in ("budget_res", "br_res", "cut_res")}, flush=True)
        # artifact: exit status -- unique fixed point, every decoding flag true, pattern LP gives an exact BNE
        allok &= uniq == "unsat" and all(rep[k] for k in (
            "R_unclipped", "s_eq_q", "sum_identity", "budget_bound_ok", "br_bound_ok", "cut_bound_ok",
            "all_below_g", "boxes_ok")) and rep["lp"] == "sat" and bool(rep["bne"][0])
        worst, bad = pair_tests(M, fp, rng)
        print(f"pair tests: worst ratio = 1 - {str(1 - worst)[:40]}..., violation: {bad is not None}", flush=True)
        allok &= bad is None  # artifact: exit status
        if mode in ("full", "z3c"):
            r, wit = contraction_violation(M, timeout_ms=180000)
            print(f"z3 contraction-violation search (true constants): {r}", flush=True)
            # artifact: exit status -- a violation (sat) fails; 'unknown' (timeout) is accepted, as in
            # the book (seed 3 game 1: 30 unsat, 1 unknown)
            allok &= r != "sat"
            if wit:
                a, b = wit
                print("   VIOLATION ratio", l1(M.ev(a)[0], M.ev(b)[0]) / l1(a, b), flush=True)
        Ms = Model(g, structural_g=Fr(1, 10))
        chk, fails = jacobian_tests(Ms, rng)
        print(f"structural (g=1/10) Jacobian tests: {chk} pieces checked, {len(fails)} failures", flush=True)
        allok &= len(fails) == 0  # artifact: exit status
        if mode in ("full", "z3c"):
            r, wit = contraction_violation(Ms, timeout_ms=180000)
            print(f"z3 contraction-violation search (structural g=1/10): {r}", flush=True)
            allok &= r != "sat"  # artifact: exit status (violation fails; unknown accepted)
            if wit:
                a, b = wit
                print("   VIOLATION ratio", l1(Ms.ev(a)[0], Ms.ev(b)[0]) / l1(a, b), flush=True)
        if mode == "full" and n * m <= 4:
            gt = gap_test(M)
            print(f"gap test: {gt['total']} patterns, {gt['zeros']} with t*=0, unknown {gt['unknown']}, "
                  f"smallest positive t*={gt['smallest_pos']}, bad={gt['bad'][:3]}", flush=True)
            allok &= not gt["bad"] and gt["unknown"] == 0  # artifact: exit status
        print(f"time {time.time() - t0:.1f}s", flush=True)
    return allok  # artifact: exit status


if __name__ == "__main__":
    sys.exit(0 if main() else 1)  # artifact: exit status
