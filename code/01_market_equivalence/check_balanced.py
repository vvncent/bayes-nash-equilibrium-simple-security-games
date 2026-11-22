"""§7 'Balanced form with one price anchor': every balanced anchored equilibrium decodes to an M1
equilibrium of the singles instance. Random box queries are first mapped to M1 by §7.
Usage: $PY -I -B check_balanced.py N seed"""
import sys, os, random
import os as _os, sys as _sys; _HERE = _os.path.dirname(_os.path.abspath(__file__)); _sys.path[:0] = [_HERE, _os.path.join(_HERE, "..", "lib")]  # artifact: path bootstrap (relative to this file)
from fractions import Fraction as Fr
import z3
from core import R, val, m1_check


def solve_balanced(p, c, A, b, rng, force_pos_dummy=False):
    """Balanced market: buyers = real (masses p) + dummy (mass sum c); sellers = real (caps c) + D
    (cap sum p), P_D = 0. Real buyer payoff A_ij - b_ij P_j on real goods, -P_D on D. Dummy payoff -P_j
    on every good. All rows and columns filled; flow only on best goods. Prices free in sign."""
    m, n = len(p), len(c)
    s = z3.Optimize()
    P = [z3.Real(f"P{j}") for j in range(n)] + [z3.RealVal(0)]
    u = [z3.Real(f"u{i}") for i in range(m + 1)]
    F = [[z3.Real(f"F{i}_{j}") for j in range(n + 1)] for i in range(m + 1)]
    mass = list(p) + [sum(c)]
    cap = list(c) + [sum(p)]

    def pay(i, j):
        if i == m or j == n:
            return -P[j]
        return R(A[i][j]) - R(b[i][j]) * P[j]

    for i in range(m + 1):
        s.add(z3.Sum(F[i]) == R(mass[i]))
        for j in range(n + 1):
            s.add(F[i][j] >= 0, u[i] >= pay(i, j), z3.Or(F[i][j] == 0, u[i] == pay(i, j)))
    for j in range(n + 1):
        s.add(z3.Sum([F[i][j] for i in range(m + 1)]) == R(cap[j]))
    if force_pos_dummy:
        s.add(u[m] > 0)
    obj = z3.Sum([R(Fr(rng.randint(-4, 4))) * e for e in P[:n] + u])
    (s.maximize if rng.random() < .5 else s.minimize)(obj)
    r = s.check()
    if r != z3.sat:
        return None
    mod = s.model()
    return ([val(mod, e) for e in P[:n]], [val(mod, e) for e in u],
            [[val(mod, e) for e in row] for row in F])


def decode(p, c, A, b, P, u, F):
    m, n = len(p), len(c)
    if u[m] > 0:  # case s>0 of the proof: reset real prices and dummy utility to zero
        s = u[m]
        assert all(P[j] == -s for j in range(n))
        assert all(A[i][j] + b[i][j] * s <= 0 for i in range(m) for j in range(n))
        P = [Fr(0)] * n
    assert all(q >= 0 for q in P)
    v = [max([Fr(0)] + [A[i][j] - b[i][j] * P[j] for j in range(n)]) for i in range(m)]
    Fm = [[F[i][j] for j in range(n)] for i in range(m)]
    return P, v, Fm


if __name__ == "__main__":
    N = int(sys.argv[1]); seed = int(sys.argv[2])
    rng = random.Random(seed)
    pos = 0
    for t in range(N):
        m, n = rng.randint(1, 3), rng.randint(1, 3)
        p = [Fr(rng.randint(1, 4), rng.randint(1, 3)) for _ in range(m)]
        c = [Fr(rng.randint(1, 4), rng.randint(1, 3)) for _ in range(n)]
        neg = rng.random() < 0.3
        A = [[Fr(rng.randint(-6, 0 if neg else 6), rng.randint(1, 3)) for _ in range(n)] for _ in range(m)]
        b = [[Fr(rng.randint(1, 5), rng.randint(1, 2)) for _ in range(n)] for _ in range(m)]
        for force in (False, True):
            out = solve_balanced(p, c, A, b, rng, force)
            if out is None:
                assert force
                continue
            P, u, F = out
            pos += u[m] > 0
            Pd, v, Fm = decode(p, c, A, b, P, u, F)
            assert m1_check(p, c, A, b, Pd, v, Fm), (t, force, P, u, F)
    print(f"balanced anchor decode OK on {N} markets ({pos} equilibria with positive dummy utility)")
