"""Exact-rational checks of Theorem 1 steps in subexponential.typ.

1. l1 halfspace: sign formula (section 1) vs the definition.
2. Protected grid point (section 3): with ||h - T(c)||_1 <= e and a failed
   stopping test ||h - c||_1 > tau/2, the rounded fixed point z is never in
   H(c, c - h).
3. Full recursive pipeline for d = 2 and d = 3 with block size 1 (median =
   1/2-deep point), the precision chain of section 2, and continued-fraction
   recovery (section 5) with D = the true denominator bound; compared with
   the exact fixed point from z3.
All arithmetic uses fractions.Fraction; z3 is used only for ground truth.
"""
import random
from fractions import Fraction as Fr
from math import ceil, log2
import z3

random.seed(20261121)


def l1(u):
    return sum(abs(t) for t in u)


def sub(u, w):
    return [a - b for a, b in zip(u, w)]


def sgn(t):
    return (t > 0) - (t < 0)


def in_H_formula(z, c, v):
    s = 0
    for zi, ci, vi in zip(z, c, v):
        si = sgn(zi - ci)
        s += si * vi if si != 0 else abs(vi)
    return s >= 0


def in_H_definition(z, c, v):
    # phi(eps) = ||z - c + eps v||_1 is convex PL; phi(eps) >= phi(0) for all
    # eps > 0 iff it holds just right of 0 (below the first breakpoint).
    bps = [(ci - zi) / vi for zi, ci, vi in zip(z, c, v) if vi != 0 and (ci - zi) / vi > 0]
    eps = (min(bps) / 2) if bps else Fr(1)
    phi0 = l1(sub(z, c))
    ok_small = l1([zi - ci + eps * vi for zi, ci, vi in zip(z, c, v)]) >= phi0
    # also check a spread of larger eps (must agree by convexity)
    for e2 in [Fr(1, 7), Fr(1, 2), Fr(1), Fr(3), Fr(10)]:
        val = l1([zi - ci + e2 * vi for zi, ci, vi in zip(z, c, v)]) >= phi0
        if ok_small and not val:
            raise AssertionError("convexity violated?")
    return ok_small


def check_halfspace(trials=20000):
    bad = 0
    for _ in range(trials):
        k = random.randint(1, 4)
        z = [Fr(random.randint(-3, 3), random.randint(1, 3)) for _ in range(k)]
        c = [Fr(random.randint(-3, 3), random.randint(1, 3)) for _ in range(k)]
        if random.random() < 0.3:  # force ties on some coordinates
            for i in range(k):
                if random.random() < 0.5:
                    z[i] = c[i]
        v = [Fr(random.randint(-3, 3), random.randint(1, 2)) for _ in range(k)]
        if all(t == 0 for t in v):
            continue
        if in_H_formula(z, c, v) != in_H_definition(z, c, v):
            bad += 1
    return bad


def rand_contraction_matrix(k, alpha):
    # max column abs sum <= alpha  => l1 operator norm <= alpha
    A = [[Fr(0)] * k for _ in range(k)]
    for h in range(k):
        w = [Fr(random.randint(-5, 5)) for _ in range(k)]
        s = sum(abs(t) for t in w) or Fr(1)
        scale = alpha * Fr(random.randint(1, 10), 10) / s
        if random.random() < 0.4:
            scale = alpha / s  # extremal column
        for i in range(k):
            A[i][h] = w[i] * scale
    return A


def check_protected(trials=6000):
    """Section 3 lemma, exact, with adversarial approximations h."""
    violations = 0
    tested_cuts = 0
    for _ in range(trials):
        k = random.randint(1, 3)
        delta = Fr(1, random.choice([2, 3, 4, 8, 16]))
        alpha = 1 - delta
        tau = Fr(1, random.choice([4, 8, 16, 32]))
        e = delta * tau / 16
        beta = ceil(log2(16 * k / (delta * tau)))
        N = 2 ** beta
        xs = [Fr(random.randint(0, 10 ** 6), 10 ** 6) for _ in range(k)]
        A = rand_contraction_matrix(k, alpha)

        def T(x):
            d = sub(x, xs)
            return [xs[i] + sum(A[i][h] * d[h] for h in range(k)) for i in range(k)]

        z = [Fr(round(t * N), N) for t in xs]  # coordinatewise rounding
        assert l1(sub(z, xs)) <= Fr(k, N) <= e
        for _ in range(20):
            # tested centers: random grid points, often close to x*
            if random.random() < 0.5:
                c = [Fr(random.randint(0, N), N) for _ in range(k)]
            else:
                rad = random.choice([1, 2, 4, 8, 16, 64])
                c = [min(Fr(1), max(Fr(0), zi + Fr(random.randint(-rad, rad), N))) for zi in z]
            Tc = T(c)
            # adversarial h: push the error e toward making z look "behind" c
            best = None
            for _ in range(6):
                dirv = [Fr(random.randint(-4, 4)) for _ in range(k)]
                if random.random() < 0.5:
                    dirv = [ci - zi for ci, zi in zip(c, z)]  # move h toward z's far side
                nd = l1(dirv)
                if nd == 0:
                    continue
                h = [t + e * dv / nd for t, dv in zip(Tc, dirv)]
                assert l1(sub(h, Tc)) <= e
                if l1(sub(h, c)) > tau / 2:
                    tested_cuts += 1
                    v = sub(c, h)
                    if in_H_formula(z, c, v):
                        violations += 1
                        best = (k, delta, tau, c, h, z)
            if best:
                print("VIOLATION", best)
    return violations, tested_cuts


# ---------------- full pipeline (block size 1) ----------------

def make_instance(d, delta):
    """F_i(x) = (1-delta)*clip01(max(A_i x + b_i, A'_i x + b'_i)) + delta/2."""
    alpha = 1 - delta
    A = rand_contraction_matrix(d, Fr(1))
    A2 = rand_contraction_matrix(d, Fr(1))
    # enforce sum_i max(|A_ih|,|A2_ih|) <= 1 per column
    for h in range(d):
        s = sum(max(abs(A[i][h]), abs(A2[i][h])) for i in range(d))
        if s > 1:
            for i in range(d):
                A[i][h] /= s
                A2[i][h] /= s
    b = [Fr(random.randint(-10, 20), 20) for _ in range(d)]
    b2 = [Fr(random.randint(-10, 20), 20) for _ in range(d)]

    def F(x):
        out = []
        for i in range(d):
            p1 = sum(A[i][h] * x[h] for h in range(d)) + b[i]
            p2 = sum(A2[i][h] * x[h] for h in range(d)) + b2[i]
            m = max(p1, p2)
            m = min(Fr(1), max(Fr(0), m))
            out.append(alpha * m + delta / 2)
        return out

    def F_z3(xv):
        out = []
        for i in range(d):
            p1 = z3.Sum([z3.RealVal(str(A[i][h])) * xv[h] for h in range(d)]) + z3.RealVal(str(b[i]))
            p2 = z3.Sum([z3.RealVal(str(A2[i][h])) * xv[h] for h in range(d)]) + z3.RealVal(str(b2[i]))
            m = z3.If(p1 >= p2, p1, p2)
            m = z3.If(m >= 1, z3.RealVal(1), z3.If(m <= 0, z3.RealVal(0), m))
            out.append(z3.RealVal(str(alpha)) * m + z3.RealVal(str(delta / 2)))
        return out

    return F, F_z3


def z3_fixed_point(d, F_z3):
    xv = [z3.Real(f"x{i}") for i in range(d)]
    s = z3.Solver()
    for i in range(d):
        s.add(xv[i] >= 0, xv[i] <= 1)
    fx = F_z3(xv)
    for i in range(d):
        s.add(xv[i] == fx[i])
    assert s.check() == z3.sat
    mdl = s.model()
    sol = []
    for i in range(d):
        r = mdl.eval(xv[i], model_completion=True)
        sol.append(Fr(r.numerator_as_long(), r.denominator_as_long()))
    # uniqueness check
    s.add(z3.Or([xv[i] != z3.RealVal(str(sol[i])) for i in range(d)]))
    assert s.check() == z3.unsat
    return sol


STATS = {"calls": 0, "tests": 0, "max_tests": 0, "z_removed": 0}


def solve(F, d, prefix, tau, delta, xstar):
    """Block size 1: returns dyadic point u (remaining coords) with residual <= tau."""
    STATS["calls"] += 1
    rem = d - len(prefix)
    k = 1
    theta = delta * delta * tau / 16
    e = delta * tau / 16
    beta = ceil(log2(16 * k / (delta * tau)))
    N = 2 ** beta
    lo, hi = 0, N  # candidate integer interval (contains z by the lemma)
    # protected point for the TRUE block fixed point is unknown in general; we
    # check survival only at the top level, where x* is known.
    ntests = 0
    while True:
        w = (lo + hi) // 2  # median of candidates = 1/2-deep point
        c = Fr(w, N)
        if rem > 1:
            y = solve(F, d, prefix + [c], theta, delta, None)
        else:
            y = []
        full = prefix + [c] + y
        h = F(full)[len(prefix)]
        ntests += 1
        STATS["tests"] += 1
        if abs(h - c) <= tau / 2:
            STATS["max_tests"] = max(STATS["max_tests"], ntests)
            res = l1(sub([c] + y, F(full)[len(prefix):]))
            assert res <= tau, (res, tau)
            return [c] + y
        if h > c:
            newlo, newhi = w + 1, hi  # remove H(c, c-h) = {z <= c}
        else:
            newlo, newhi = lo, w - 1  # remove {z >= c}
        if xstar is not None:
            zt = round(xstar[0] * N)
            if not (newlo <= zt <= newhi):
                STATS["z_removed"] += 1
        lo, hi = newlo, newhi
        assert lo <= hi, "candidate set emptied"


def cf_recover(u, D):
    """Return the unique fraction with denominator <= D within 1/(8D^2) of u."""
    p0, q0, p1, q1 = 0, 1, 1, 0
    x = u
    best = None
    while True:
        a = x.numerator // x.denominator
        p0, q0, p1, q1 = p1, q1, a * p1 + p0, a * q1 + q0
        cand = Fr(p1, q1)
        if q1 <= D and abs(cand - u) <= Fr(1, 8 * D * D):
            best = cand
        if x == a or q1 > D:
            break
        x = 1 / (x - a)
    return best


def check_cf(trials=20000):
    bad = 0
    for _ in range(trials):
        D = random.randint(1, 10 ** 6)
        q = random.randint(1, D)
        p = random.randint(0, q)
        t = Fr(p, q)
        B = ceil(log2(8 * D * D)) + random.randint(0, 3)
        # dyadic approximation within 1/(8D^2)
        u = Fr(round(t * 2 ** B) + random.choice([-1, 0, 1]), 2 ** B)
        if abs(u - t) > Fr(1, 8 * D * D):
            continue
        if cf_recover(u, D) != t:
            bad += 1
    return bad


def pipeline(trials, d):
    ok = 0
    for _ in range(trials):
        delta = Fr(1, random.choice([2, 4, 8]))
        F, F_z3 = make_instance(d, delta)
        xs = z3_fixed_point(d, F_z3)
        D = max(t.denominator for t in xs)  # smallest valid D for this instance
        B = 0
        while Fr(1, 2 ** B) > delta / (8 * D * D):
            B += 1
        tau = Fr(1, 2 ** B)
        u = solve(F, d, [], tau, delta, xs)
        assert l1(sub(u, xs)) <= tau / delta <= Fr(1, 8 * D * D)
        rec = [cf_recover(t, D) for t in u]
        assert rec == xs, (rec, xs)
        assert F(rec) == rec
        ok += 1
    return ok


if __name__ == "__main__":
    import sys  # artifact: exit status
    # artifact: results kept in variables for the exit status (same calls, same order, same output)
    hs = check_halfspace()
    print("halfspace formula/definition mismatches:", hs)
    v, n = check_protected()
    print("protected-point violations:", v, "of", n, "failed-test cuts")
    cf = check_cf()
    print("continued-fraction recovery failures:", cf)
    p2 = pipeline(12, 2)
    zr2 = STATS["z_removed"]
    print("pipeline d=2 exact recoveries:", p2, dict(STATS))
    STATS.update({"calls": 0, "tests": 0, "max_tests": 0, "z_removed": 0})
    p3 = pipeline(3, 3)
    print("pipeline d=3 exact recoveries:", p3, dict(STATS))
    # artifact: exit status -- no mismatches, no protected-point violations, no CF failures,
    # 12/12 and 3/3 exact recoveries, protected point never removed
    sys.exit(0 if (hs == 0 and v == 0 and cf == 0 and p2 == 12 and p3 == 3 and zr2 == 0
                   and STATS["z_removed"] == 0) else 1)
