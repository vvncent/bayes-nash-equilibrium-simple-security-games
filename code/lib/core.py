"""Exact implementation of matching.typ sections 1-5 and 7 (game -> market direction).

All arithmetic is in Fractions. z3 is used only as an exact rational LP / LRA solver and as an
M1 equilibrium oracle. Every result is re-checked directly in Fractions against the definitions.
"""
from fractions import Fraction as Fr
from math import lcm, ceil, log2
import random
import z3


def R(q):
    q = Fr(q)
    return z3.RealVal(f"{q.numerator}/{q.denominator}")


def val(model, e):
    return model.eval(e, model_completion=True).as_fraction()


# ----------------------------------------------------------------------------------------------
# Game data and direct checks
# ----------------------------------------------------------------------------------------------
class Game:
    def __init__(self, p, a, b, d, r):
        self.p = [Fr(v) for v in p]
        self.a = [[Fr(v) for v in row] for row in a]
        self.b = [[Fr(v) for v in row] for row in b]
        self.d = [Fr(v) for v in d]
        self.r = r
        self.m = len(p)
        self.n = len(d)
        assert sum(self.p) == 1 and all(v > 0 for v in self.p)
        assert all(v > 0 for row in self.b for v in row) and all(v > 0 for v in self.d)
        assert 0 < r < self.n

    def U(self, i, j, xj):
        return self.a[i][j] - self.b[i][j] * xj


def loads(G, f):
    return [sum(f[i][j] for i in range(G.m)) for j in range(G.n)]


def best_response_ok(G, x, f):
    for i in range(G.m):
        if sum(f[i]) != G.p[i] or any(v < 0 for v in f[i]):
            return False
        V = max(G.U(i, k, x[k]) for k in range(G.n))
        for j in range(G.n):
            if f[i][j] > 0 and G.U(i, j, x[j]) != V:
                return False
    return True


def check_box(G, c, l, h, x, f):
    """Box-market equilibrium (matching.typ §1). Zero-width coordinates have no load condition."""
    if not all(l[j] <= x[j] <= h[j] for j in range(G.n)):
        return False, "price outside box"
    if not best_response_ok(G, x, f):
        return False, "buyer not best responding / row sum"
    w = loads(G, f)
    for j in range(G.n):
        if l[j] == h[j]:
            continue
        if x[j] > l[j] and w[j] < c[j]:
            return False, f"good {j} above floor but underloaded"
        if x[j] < h[j] and w[j] > c[j]:
            return False, f"good {j} below ceiling but overloaded"
    return True, "ok"


def check_bne(G, x, f):
    """Direct BNE check from the game definition, no cutoff variable.
    Defender: x maximizes sum d_j w_j x_j over {0<=x<=1, sum x = r} (compare with greedy top-r value).
    Attackers: every positive f_ij maximizes U_ij(x). Also realize x as a mixture of r-subsets."""
    if sum(x) != G.r or not all(0 <= v <= 1 for v in x):
        return False, "coverage infeasible"
    if not best_response_ok(G, x, f):
        return False, "attacker not best responding"
    w = loads(G, f)
    score = [G.d[j] * w[j] for j in range(G.n)]
    got = sum(score[j] * x[j] for j in range(G.n))
    best = sum(sorted(score, reverse=True)[: G.r])
    if got != best:
        return False, f"defender not best responding {got} < {best}"
    mix = realize(x, G.r)
    tot = [Fr(0)] * G.n
    for prob, S in mix:
        assert len(S) == G.r and len(set(S)) == G.r
        for j in S:
            tot[j] += prob
    if tot != list(x) or sum(pr for pr, _ in mix) != 1:
        return False, "realization mismatch"
    return True, "ok"


def realize(x, r):
    """§1 interval construction: rational mixture of pure defenses of size r."""
    ends = [Fr(0)]
    for v in x:
        ends.append(ends[-1] + v)
    cuts = sorted(set([Fr(0), Fr(1)] + [e - (e.numerator // e.denominator) for e in ends]))
    mix = []
    for lo, hi in zip(cuts, cuts[1:]):
        if hi <= lo:
            continue
        s = (lo + hi) / 2
        S = []
        for q in range(r):
            pt = s + q
            for j in range(len(x)):
                if ends[j] <= pt < ends[j + 1]:
                    S.append(j)
        mix.append((hi - lo, tuple(S)))
    return mix


# ----------------------------------------------------------------------------------------------
# M1 oracle (brief arrival-switch.md "Market model"), exact via z3
# ----------------------------------------------------------------------------------------------
def m1_check(p, c, a, b, P, v, F):
    m, n = len(p), len(c)
    if any(q < 0 for q in P) or any(q < 0 for q in v):
        return False
    for i in range(m):
        rs = sum(F[i])
        if rs > p[i] or (v[i] > 0 and rs != p[i]):
            return False
        for j in range(n):
            u = a[i][j] - b[i][j] * P[j]
            if v[i] < u or F[i][j] < 0 or (F[i][j] > 0 and v[i] != u):
                return False
    for j in range(n):
        cs = sum(F[i][j] for i in range(m))
        if cs > c[j] or (P[j] > 0 and cs != c[j]):
            return False
    return True


class M1Oracle:
    """Returns an exact M1 equilibrium. mode: 'plain', 'opt' (random linear objective, extreme point),
    'interior' (random convex combination of extreme points of the chosen complementary piece)."""

    def __init__(self, mode="opt", seed=0):
        self.mode = mode
        self.rng = random.Random(seed)
        self.calls = 0

    def _base(self, p, c, a, b, solver):
        m, n = len(p), len(c)
        P = [z3.Real(f"P{j}") for j in range(n)]
        v = [z3.Real(f"v{i}") for i in range(m)]
        F = [[z3.Real(f"F{i}_{j}") for j in range(n)] for i in range(m)]
        for j in range(n):
            solver.add(P[j] >= 0)
            cs = z3.Sum([F[i][j] for i in range(m)])
            solver.add(cs <= R(c[j]), z3.Or(P[j] == 0, cs == R(c[j])))
        for i in range(m):
            solver.add(v[i] >= 0)
            rs = z3.Sum(F[i])
            solver.add(rs <= R(p[i]), z3.Or(v[i] == 0, rs == R(p[i])))
            for j in range(n):
                u = R(a[i][j]) - R(b[i][j]) * P[j]
                solver.add(F[i][j] >= 0, v[i] >= u, z3.Or(F[i][j] == 0, v[i] == u))
        return P, v, F

    def _rand_obj(self, P, v, F):
        terms = []
        for e in P + v + [x for row in F for x in row]:
            terms.append(R(Fr(self.rng.randint(-5, 5), self.rng.randint(1, 3))) * e)
        return z3.Sum(terms)

    def solve(self, p, c, a, b):
        self.calls += 1
        m, n = len(p), len(c)
        if self.mode == "plain":
            s = z3.Solver()
            s.set("random_seed", self.rng.randint(0, 10**6))
            P, v, F = self._base(p, c, a, b, s)
            assert s.check() == z3.sat
            mod = s.model()
        else:
            s = z3.Optimize()
            P, v, F = self._base(p, c, a, b, s)
            (s.maximize if self.rng.random() < 0.5 else s.minimize)(self._rand_obj(P, v, F))
            assert s.check() == z3.sat
            mod = s.model()
        Pv = [val(mod, e) for e in P]
        vv = [val(mod, e) for e in v]
        Fv = [[val(mod, e) for e in row] for row in F]
        if self.mode == "interior":
            Pv, vv, Fv = self._interior(p, c, a, b, Pv, vv, Fv)
        assert m1_check(p, c, a, b, Pv, vv, Fv), "oracle produced a non-equilibrium"
        return Pv, vv, Fv

    def _interior(self, p, c, a, b, P0, v0, F0):
        """Fix the complementary piece of (P0,v0,F0) and average random extreme points of it."""
        m, n = len(p), len(c)
        pts = [(P0, v0, F0)]
        for _ in range(2):
            s = z3.Optimize()
            P = [z3.Real(f"P{j}") for j in range(n)]
            v = [z3.Real(f"v{i}") for i in range(m)]
            F = [[z3.Real(f"F{i}_{j}") for j in range(n)] for i in range(m)]
            for j in range(n):
                cs = z3.Sum([F[i][j] for i in range(m)])
                s.add(P[j] >= 0, cs <= R(c[j]))
                if P0[j] > 0:
                    s.add(cs == R(c[j]))
                else:
                    s.add(P[j] == 0)
            for i in range(m):
                rs = z3.Sum(F[i])
                s.add(v[i] >= 0, rs <= R(p[i]))
                if v0[i] > 0:
                    s.add(rs == R(p[i]))
                else:
                    s.add(v[i] == 0)
                for j in range(n):
                    u = R(a[i][j]) - R(b[i][j]) * P[j]
                    tight = v0[i] == a[i][j] - b[i][j] * P0[j]
                    s.add(F[i][j] >= 0)
                    if tight:
                        s.add(v[i] == u)
                    else:
                        s.add(v[i] >= u, F[i][j] == 0)
            (s.maximize if self.rng.random() < 0.5 else s.minimize)(self._rand_obj(P, v, F))
            assert s.check() == z3.sat
            mod = s.model()
            pts.append(([val(mod, e) for e in P], [val(mod, e) for e in v],
                        [[val(mod, e) for e in row] for row in F]))
        wts = [Fr(self.rng.randint(1, 7)) for _ in pts]
        W = sum(wts)
        wts = [q / W for q in wts]
        P = [sum(wt * pt[0][j] for wt, pt in zip(wts, pts)) for j in range(n)]
        v = [sum(wt * pt[1][i] for wt, pt in zip(wts, pts)) for i in range(m)]
        F = [[sum(wt * pt[2][i][j] for wt, pt in zip(wts, pts)) for j in range(n)] for i in range(m)]
        return P, v, F


# ----------------------------------------------------------------------------------------------
# §7: implement a box query by one M1 instance, decode any answer
# ----------------------------------------------------------------------------------------------
def box_query(G, c, l, h, oracle, log=None):
    assert all(cj > 0 for cj in c) and all(l[j] <= h[j] for j in range(G.n))
    m, n = G.m, G.n
    v0 = [max(G.a[i][k] - G.b[i][k] * h[k] for k in range(n)) for i in range(m)]
    a1 = [[G.a[i][j] - G.b[i][j] * l[j] - v0[i] for j in range(n)] for i in range(m)]
    P1, v1, F = oracle.solve(G.p, c, a1, G.b)
    x = [P1[j] + l[j] for j in range(n)]
    f = [row[:] for row in F]
    for i in range(m):
        slack = G.p[i] - sum(F[i])
        if slack > 0:
            assert v1[i] == 0
            ks = [k for k in range(n) if G.a[i][k] - G.b[i][k] * h[k] == v0[i]]
            k = ks[0]
            assert x[k] == h[k], "decode: reservation maximizer not at ceiling"
            f[i][k] += slack
    ok, why = check_box(G, c, l, h, x, f)
    assert ok, "decode failed: " + why
    if log is not None:
        log.append(("M1", [list(map(str, x))]))
    return x, f


# ----------------------------------------------------------------------------------------------
# Exact LP helpers (z3 Optimize over LRA = exact rational simplex)
# ----------------------------------------------------------------------------------------------
def lp_opt(cons_builder, obj_builder, sense, nvars_builder):
    s = z3.Optimize()
    V = nvars_builder()
    cons_builder(s, V)
    o = obj_builder(V)
    h = s.minimize(o) if sense == "min" else s.maximize(o)
    r = s.check()
    if r != z3.sat:
        return None
    mod = s.model()
    return mod, V


def lex_vertex(cons_builder, nvars_builder, order_builder):
    """Lexicographic minimum over all variables: an extreme point of the (bounded) polytope."""
    s = z3.Optimize()
    s.set(priority="lex")
    V = nvars_builder()
    cons_builder(s, V)
    for e in order_builder(V):
        s.minimize(e)
    if s.check() != z3.sat:
        return None
    return s.model(), V


def row_int_bound(rows):
    """rows: list of (list of Fraction coefficients, Fraction rhs). Clear each row's denominators."""
    H = 1
    for coefs, rhs in rows:
        L = 1
        for q in list(coefs) + [rhs]:
            L = lcm(L, Fr(q).denominator)
        for q in list(coefs) + [rhs]:
            H = max(H, abs(int(Fr(q) * L)))
    return H


def bits(q):
    q = Fr(q)
    return max(abs(q.numerator).bit_length(), q.denominator.bit_length())


# ----------------------------------------------------------------------------------------------
# §2 lattice operations
# ----------------------------------------------------------------------------------------------
def meet(G, x, f, y, g):
    S = [x[j] > y[j] for j in range(G.n)]
    z = [y[j] if S[j] else x[j] for j in range(G.n)]
    h = [[g[i][j] if S[j] else f[i][j] for j in range(G.n)] for i in range(G.m)]
    return z, h


def join(G, x, f, y, g):
    S = [x[j] > y[j] for j in range(G.n)]
    z = [x[j] if S[j] else y[j] for j in range(G.n)]
    h = [[f[i][j] if S[j] else g[i][j] for j in range(G.n)] for i in range(G.m)]
    return z, h


def br_flow(G, x):
    f = [[Fr(0)] * G.n for _ in range(G.m)]
    for i in range(G.m):
        V = max(G.U(i, k, x[k]) for k in range(G.n))
        k = [k for k in range(G.n) if G.U(i, k, x[k]) == V][0]
        f[i][k] = G.p[i]
    return f
