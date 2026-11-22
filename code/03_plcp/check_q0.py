"""Exact check of the Q0 argument: zero-margin markets have LCP solutions, built by the findings' recipe.

Run: python -I -B 03_plcp/check_q0.py
Recipe: delete zero-margin buyers/goods, solve the positive submarket exactly, restore deleted goods at price
max(0, max_i a_ij/b_ij) with zero flow, then deleted buyers at utility max(0, max_j a_ij - b_ij P_j).
"""
from fractions import Fraction as F
from pathlib import Path
import random
import sys

import os as _os, sys as _sys  # artifact: path bootstrap (relative to this file)
_HERE = _os.path.dirname(_os.path.abspath(__file__))
_sys.path[:0] = [_HERE, _os.path.join(_HERE, "..", "lib")]
from check_plcp import build, solve_unique, decode, epsilon_of


def lcp_ok(M, q, z):
    w = [q[r] + sum(M[r][s] * z[s] for s in range(len(z))) for r in range(len(z))]
    return all(x >= 0 for x in z) and all(x >= 0 for x in w) and all(x * y == 0 for x, y in zip(z, w))


def solve_positive(p, c, a, b):
    M, q, edges = build(p, c, a, b)
    eps, *_ = epsilon_of(M, q, p, a, b, edges)
    sol, unique = solve_unique(M, q, eps)
    assert unique
    z = decode(M, q, {k for k, x in enumerate(sol) if x > 0})
    E, m = len(edges), len(p)
    return {e: z[k] for k, e in enumerate(edges)}, z[E:E + m], z[E + m:]


def recipe(p, c, a, b):
    m, n = len(p), len(c)
    I = [i for i in range(m) if p[i] > 0]
    J = [j for j in range(n) if c[j] > 0]
    f = {(i, j): F(0) for i in range(m) for j in range(n)}
    u, P = [F(0)] * m, [F(0)] * n
    if I and J:
        sf, su, sP = solve_positive([p[i] for i in I], [c[j] for j in J],
                                    [[a[i][j] for j in J] for i in I], [[b[i][j] for j in J] for i in I])
        for (ii, jj), x in sf.items():
            f[(I[ii], J[jj])] = x
        for ii, i in enumerate(I):
            u[i] = su[ii]
        for jj, j in enumerate(J):
            P[j] = sP[jj]
    for j in range(n):
        if j not in J:
            P[j] = max([F(0)] + [F(a[i][j]) / b[i][j] for i in range(m)])
    for i in range(m):
        if i not in I:
            u[i] = max([F(0)] + [F(a[i][j]) - b[i][j] * P[j] for j in range(n)])
    z = [f[(i, j)] for i in range(m) for j in range(n)] + u + P
    return z


if __name__ == "__main__":
    rng = random.Random(7)
    for trial in range(40):
        m, n = rng.choice([(1, 2), (2, 2), (2, 3), (3, 2)])
        p = [F(rng.choice([0, 0, 1, 2]), rng.choice([1, 2])) for _ in range(m)]
        c = [F(rng.choice([0, 1, 3]), rng.choice([1, 4])) for _ in range(n)]
        a = [[F(rng.randint(-3, 8), rng.choice([1, 2])) for _ in range(n)] for _ in range(m)]
        b = [[F(rng.randint(1, 8), rng.choice([1, 3])) for _ in range(n)] for _ in range(m)]
        M, q, edges = build(p, c, a, b)
        z = recipe(p, c, a, b)
        assert lcp_ok(M, q, z), trial
    print("Q0 recipe: 40 random markets with zero margins, restored point solves LCP(q, M) exactly")
