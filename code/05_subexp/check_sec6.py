"""Exact checks of the section 6 contraction of subexponential.typ.

For small random games (n = 3 targets, m = 2 types, some zero slopes/gains),
with a toy threshold g (the real g = 1/(4 D0) is astronomically small; the
contraction and decoding arguments use only the stated inequalities between
the constants, not the size of g):
 (a) z3 searches for u, u' with ||F(u)-F(u')||_1 > (1-delta)||u-u'||_1
     (expect unsat), plus exact random-pair sampling;
 (b) z3 computes the exact fixed point and the decoding claims are checked:
     0 < q < kappa, R unclipped, sum x + q = r + kappa/2,
     |sum T - r| <= kappa/(2(1-delta)), payoff residual <= sigma + 2 B0 delta,
     cutoff residual <= D1 delta/eta + g/16, all residuals < g.
"""
import random
import itertools
from fractions import Fraction as Fr
import z3

random.seed(7)


def build(n, m, a, b, d, p, r, g):
    B0 = max(max(row) for row in b)
    dp = [dj + g / 16 for dj in d]
    D1 = max(dp)
    sigma = kappa = g / 8
    inv = sum(1 / t for t in dp)
    eta = min(Fr(1), sigma / (1 + B0), kappa / (4 * (1 + D1) * (1 + inv)))
    delta = min(Fr(1, 8), eta * g / (8 * (1 + D1)), g / (8 * (1 + B0)))
    assert eta * D1 * inv <= kappa * (1 - 2 * delta)
    C = dict(B0=B0, dp=dp, D1=D1, sigma=sigma, kappa=kappa, eta=eta, delta=delta)
    subsets = [S for k in range(1, n + 1) for S in itertools.combinations(range(n), k)]

    def lam(s, mx, mn):
        lo, hi = delta * kappa, (1 - delta) * kappa
        mid = D1 * (hi - s) / (hi - lo)
        return mn(D1, mx(Fr(0) if mx is max else z3.RealVal(0), mid))

    def F(u, mx, mn, num):
        x, q = u[:n], u[n]
        clip = lambda lo, hi, t: mn(hi, mx(lo, t))
        w = [num(0)] * n
        flows = []
        for i in range(m):
            uu = [(a[i][j] - b[i][j] * x[j]) / sigma for j in range(n)]
            terms = [(sum(uu[j] for j in S) - 1) / len(S) for S in subsets]
            t = terms[0]
            for tt in terms[1:]:
                t = mx(t, tt)
            y = [mx(num(0), uu[j] - t) for j in range(n)]
            flows.append([p[i] * yj for yj in y])
            for j in range(n):
                w[j] = w[j] + p[i] * y[j]
        s = clip(num(0), num(kappa), q)
        lo, hi = delta * kappa, (1 - delta) * kappa
        ls = mn(num(D1), mx(num(0), D1 * (hi - s) / (hi - lo)))
        T = [clip(num(0), num(1), x[j] + eta * (w[j] - ls / dp[j])) for j in range(n)]
        R = clip(num(0), num(kappa), s + sum(x) - sum(T))
        out = [(1 - delta) * T[j] + delta * Fr(r, n) for j in range(n)] + [(1 - delta) * R + delta * kappa / 2]
        return out, dict(T=T, R=R, s=s, lam=ls, w=w, flows=flows, Runc=s + sum(x) - sum(T))

    return F, C


def zmax(u, v):
    return z3.If(u >= v, u, v)


def zmin(u, v):
    return z3.If(u <= v, u, v)


def zabs(u):
    return z3.If(u >= 0, u, -u)


def RV(t):
    return z3.RealVal(str(t)) if isinstance(t, Fr) else t


def lift(F):
    def Fz(u):
        out, aux = F(u, zmax, zmin, lambda t: z3.RealVal(str(t)))
        return out, aux
    return Fz


def fr(v):
    return Fr(v.numerator_as_long(), v.denominator_as_long())


def instance():
    n, m = 3, 2
    a = [[Fr(random.randint(-4, 4), 2) for _ in range(n)] for _ in range(m)]
    b = [[Fr(random.randint(0, 4), 2) for _ in range(n)] for _ in range(m)]
    b[0][random.randrange(n)] = Fr(0)  # a zero slope
    d = [Fr(random.randint(0, 3), 2) for _ in range(n)]
    d[random.randrange(n)] = Fr(0)  # a zero gain
    p1 = Fr(random.randint(1, 9), 10)
    p = [p1, 1 - p1]
    r = random.choice([1, 2])
    return n, m, a, b, d, p, r


def run(num_inst=6, g=Fr(1, 2)):
    results = []
    for it in range(num_inst):
        n, m, a, b, d, p, r = instance()
        F, C = build(n, m, a, b, d, p, r, g)
        # coerce python Fractions into z3 terms inside F via wrappers
        def Fz(u):
            def mx(s, t):
                return zmax(RV(s), RV(t))

            def mn(s, t):
                return zmin(RV(s), RV(t))
            return F(u, mx, mn, lambda t: z3.RealVal(str(t)))

        # (a) contraction counterexample search
        u = [z3.Real(f"u{j}") for j in range(n + 1)]
        v = [z3.Real(f"v{j}") for j in range(n + 1)]
        s = z3.Solver()
        s.set("timeout", 60000)
        for t in u + v:
            s.add(t >= 0, t <= 1)
        Fu, _ = Fz(u)
        Fv, _ = Fz(v)
        lhs = z3.Sum([zabs(Fu[j] - Fv[j]) for j in range(n + 1)])
        rhs = RV(1 - C["delta"]) * z3.Sum([zabs(u[j] - v[j]) for j in range(n + 1)])
        s.add(lhs > rhs)
        ca = s.check()
        # exact random pairs
        worst = Fr(0)
        for _ in range(300):
            uu = [Fr(random.randint(0, 64), 64) for _ in range(n + 1)]
            vv = [min(Fr(1), max(Fr(0), t + Fr(random.randint(-3, 3), 256))) for t in uu]
            if uu == vv:
                continue
            fu, _ = F(uu, max, min, Fr)
            fv, _ = F(vv, max, min, Fr)
            ratio = sum(abs(x - y) for x, y in zip(fu, fv)) / sum(abs(x - y) for x, y in zip(uu, vv))
            worst = max(worst, ratio)
        # (b) exact fixed point and decoding claims
        s2 = z3.Solver()
        for t in u:
            s2.add(t >= 0, t <= 1)
        Fu2, aux = Fz(u)
        for j in range(n + 1):
            s2.add(u[j] == Fu2[j])
        assert s2.check() == z3.sat
        mdl = s2.model()
        uval = [fr(mdl.eval(t, model_completion=True)) for t in u]
        out, ax = F(uval, max, min, Fr)
        assert out == uval
        x, q = uval[:n], uval[n]
        kappa, delta, eta, D1, B0, sigma = C["kappa"], C["delta"], C["eta"], C["D1"], C["B0"], C["sigma"]
        checks = {}
        checks["0<q<kappa"] = 0 < q < kappa
        checks["R unclipped"] = 0 < ax["Runc"] < kappa
        checks["sum x + q = r + kappa/2"] = sum(x) + q == r + kappa / 2
        z = ax["T"]
        checks["|sum T - r| <= kappa/(2(1-delta))"] = abs(sum(z) - r) <= kappa / (2 * (1 - delta))
        checks["|z-x|<=delta"] = all(abs(zj - xj) <= delta for zj, xj in zip(z, x))
        pay = Fr(0)
        for i in range(m):
            U = [a[i][j] - b[i][j] * z[j] for j in range(n)]
            for j in range(n):
                if ax["flows"][i][j] > 0:
                    pay = max(pay, max(U) - U[j])
        checks["payoff residual <= sigma+2B0delta"] = pay <= sigma + 2 * B0 * delta
        lam = ax["lam"]
        cut = Fr(0)
        for j in range(n):
            sc = d[j] * ax["w"][j]
            if z[j] > 0:
                cut = max(cut, lam - sc)
            if z[j] < 1:
                cut = max(cut, sc - lam)
        checks["cutoff residual <= D1 delta/eta + g/16"] = cut <= D1 * delta / eta + g / 16
        checks["all residuals < g"] = max(pay, cut, abs(sum(z) - r)) < g
        results.append((it, str(ca), float(worst), all(checks.values()), {k: v for k, v in checks.items() if not v}))
    return results


if __name__ == "__main__":
    import sys  # artifact: exit status
    allok = True  # artifact: exit status
    for row in run():
        print(row)
        allok &= row[1] == "unsat" and row[3] is True  # artifact: exit status (no violating pair; decoding ok)
    sys.exit(0 if allok else 1)  # artifact: exit status
