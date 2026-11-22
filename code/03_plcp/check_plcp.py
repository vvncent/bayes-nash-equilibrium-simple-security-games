"""Independent exact check of the M1 -> P-matrix LCP reduction (monitor findings, regular pass 16).

Written from the statement only; it shares no code with check_lemke_rays.py.
Run: python -I -B 03_plcp/check_plcp.py

For each market it
  1. builds (M, q) of the claimed LCP with Fractions;
  2. checks every principal minor of M is >= 0 (P0) and that M + eps I has every principal minor > 0;
  3. computes eps = 1 / (2 ceil(U) (dC)^d) exactly as in the findings;
  4. solves LCP(q, M + eps I) exactly (z3 QF_LRA) and proves the solution unique (second solution unsat);
     on small inputs also by enumerating all 2^N complementary bases with Fractions;
  5. decodes with system (1) and checks the result against the M1 equilibrium definition directly;
  6. checks the uniform bound z^eps <= U - 1 at several eps in (0, 1];
  7. negative control: a market where the same decoder FAILS at eps = 1, so the size of eps matters.
"""
from fractions import Fraction as F
from itertools import combinations
from math import ceil, lcm
import random
import sys
import os as _os, sys as _sys  # artifact: path bootstrap (relative to this file)
_HERE = _os.path.dirname(_os.path.abspath(__file__))
_sys.path[:0] = [_HERE, _os.path.join(_HERE, "..", "lib")]

import z3


def build(p, c, a, b, edges=None):
    m, n = len(p), len(c)
    if edges is None:
        edges = [(i, j) for i in range(m) for j in range(n)]
    E = len(edges)
    N = E + m + n
    M = [[F(0)] * N for _ in range(N)]
    q = [F(0)] * N
    for e, (i, j) in enumerate(edges):
        M[e][E + i] = F(1)
        M[e][E + m + j] = F(b[i][j])
        q[e] = -F(a[i][j])
        M[E + i][e] = F(-1)
        M[E + m + j][e] = F(-1)
    for i in range(m):
        q[E + i] = F(p[i])
    for j in range(n):
        q[E + m + j] = F(c[j])
    return M, q, edges


def det(A):
    A = [row[:] for row in A]
    k = len(A)
    sign, result = 1, F(1)
    for col in range(k):
        piv = next((r for r in range(col, k) if A[r][col] != 0), None)
        if piv is None:
            return F(0)
        if piv != col:
            A[col], A[piv] = A[piv], A[col]
            sign = -sign
        result *= A[col][col]
        inv = 1 / A[col][col]
        for r in range(col + 1, k):
            if A[r][col] != 0:
                factor = A[r][col] * inv
                A[r] = [x - factor * y for x, y in zip(A[r], A[col])]
    return sign * result


def principal_minors(M):
    N = len(M)
    for size in range(1, N + 1):
        for S in combinations(range(N), size):
            yield S, det([[M[r][s] for s in S] for r in S])


def epsilon_of(M, q, p, a, b, edges):
    N = len(M)
    entries = [x for row in M for x in row] + q
    D = lcm(*(x.denominator for x in entries))
    C = D * max([F(1)] + [abs(x) for x in entries])
    assert C.denominator == 1
    C = int(C)
    d = N + 1
    H = max([F(0)] + [F(a[i][j]) for i, j in edges])
    bmin = min(F(b[i][j]) for i, j in edges)
    U = 1 + max(max(F(x) for x in p) + H, H / bmin)
    return F(1, 2 * ceil(U) * (d * C) ** d), U, d, C


def zr(x):
    x = F(x)
    return z3.RealVal(f"{x.numerator}/{x.denominator}")


def lcp_solver(M, q, diag):
    N = len(M)
    z = [z3.Real(f"z{k}") for k in range(N)]
    s = z3.SolverFor("QF_LRA")
    ws = []
    for k in range(N):
        w = zr(q[k]) + z3.Sum([zr(M[k][l]) * z[l] for l in range(N) if M[k][l] != 0]) + zr(diag) * z[k]
        ws.append(w)
        s.add(z[k] >= 0, w >= 0, z3.Or(z[k] == 0, w == 0))
    return s, z, ws


def frac(model, x):
    return model.eval(x, model_completion=True).as_fraction()


def solve_unique(M, q, eps):
    s, z, _ = lcp_solver(M, q, eps)
    assert s.check() == z3.sat
    sol = [frac(s.model(), x) for x in z]
    s.add(z3.Or([x != zr(v) for x, v in zip(z, sol)]))
    unique = s.check() == z3.unsat
    return sol, unique


def enumerate_bases(M, q, eps):
    """All solutions of LCP(q, M + eps I) by complementary-basis enumeration (Fractions)."""
    N = len(M)
    Mt = [[M[r][s] + (eps if r == s else 0) for s in range(N)] for r in range(N)]
    found = set()
    for size in range(N + 1):
        for A in combinations(range(N), size):
            z = [F(0)] * N
            if A:
                sub = [[Mt[r][s] for s in A] + [-q[r]] for r in A]
                k = len(A)
                ok = True
                for col in range(k):  # Gauss-Jordan
                    piv = next((r for r in range(col, k) if sub[r][col] != 0), None)
                    if piv is None:
                        ok = False
                        break
                    sub[col], sub[piv] = sub[piv], sub[col]
                    inv = 1 / sub[col][col]
                    sub[col] = [x * inv for x in sub[col]]
                    for r in range(k):
                        if r != col and sub[r][col] != 0:
                            f = sub[r][col]
                            sub[r] = [x - f * y for x, y in zip(sub[r], sub[col])]
                if not ok:
                    continue
                for idx, r in enumerate(A):
                    z[r] = sub[idx][k]
            if any(x < 0 for x in z):
                continue
            w = [q[r] + sum(Mt[r][s] * z[s] for s in range(N)) for r in range(N)]
            if all(x >= 0 for x in w):
                found.add(tuple(z))
    return found


def decode(M, q, support):
    N = len(M)
    z = [z3.Real(f"y{k}") for k in range(N)]
    s = z3.SolverFor("QF_LRA")
    for k in range(N):
        w = zr(q[k]) + z3.Sum([zr(M[k][l]) * z[l] for l in range(N) if M[k][l] != 0])
        s.add(z[k] >= 0, w >= 0)
        if k in support:
            s.add(w == 0)
        else:
            s.add(z[k] == 0)
    if s.check() != z3.sat:
        return None
    return [frac(s.model(), x) for x in z]


def is_m1_equilibrium(p, c, a, b, edges, z):
    """Check the brief's M1 definition directly (no LCP algebra)."""
    E, m, n = len(edges), len(p), len(c)
    f = {e: z[k] for k, e in enumerate(edges)}
    v = z[E:E + m]
    P = z[E + m:]
    if any(x < 0 for x in z):
        return False
    for (i, j), x in f.items():
        payoff = F(a[i][j]) - F(b[i][j]) * P[j]
        if v[i] < payoff:
            return False
        if x > 0 and v[i] != payoff:
            return False
    for i in range(m):
        row = sum(x for (ii, _), x in f.items() if ii == i)
        if row > p[i] or (v[i] > 0 and row != p[i]):
            return False
    for j in range(n):
        col = sum(x for (_, jj), x in f.items() if jj == j)
        if col > c[j] or (P[j] > 0 and col != c[j]):
            return False
    return True


def run(name, p, c, a, b, edges=None, enumerate_small=False, minors=True):
    M, q, edges = build(p, c, a, b, edges)
    N = len(M)
    eps, U, d, C = epsilon_of(M, q, p, a, b, edges)
    if minors:
        positive = 0
        for S, value in principal_minors(M):
            assert value >= 0, (name, S, value)
            positive += value > 0
        assert positive > 0
        # M + eps I: every principal minor strictly positive (eps of the findings, and eps = 1/3)
        for e in ((eps, F(1, 3)) if N <= 8 else (F(1, 3),)):
            Me = [[M[r][s] + (e if r == s else 0) for s in range(N)] for r in range(N)]
            for S, value in principal_minors(Me):
                assert value > 0, (name, S)
    sol, unique = solve_unique(M, q, eps)
    assert unique, name
    if enumerate_small:
        assert enumerate_bases(M, q, eps) == {tuple(sol)}, name
    for e in (F(1), F(1, 2), F(1, 7), eps):
        other, uniq = solve_unique(M, q, e)
        assert uniq and max(other) <= U - 1, (name, e)
    support = {k for k, x in enumerate(sol) if x > 0}
    z = decode(M, q, support)
    assert z is not None, name
    assert is_m1_equilibrium(p, c, a, b, edges, z), name
    bits = max(eps.denominator.bit_length(), 1)
    return N, bits, positive if minors else None


def negative_control():
    # one buyer, one good, p=1, c=2, a=1, b=1: unique equilibrium f=1, v=1, P=0.
    p, c, a, b = [1], [2], [[1]], [[1]]
    M, q, edges = build(p, c, a, b)
    sol, unique = solve_unique(M, q, F(1))
    assert unique
    support = {k for k, x in enumerate(sol) if x > 0}
    bad = decode(M, q, support)
    eps, *_ = epsilon_of(M, q, p, a, b, edges)
    good_sol, _ = solve_unique(M, q, eps)
    good = decode(M, q, {k for k, x in enumerate(good_sol) if x > 0})
    assert bad is None and good is not None and is_m1_equilibrium(p, c, a, b, edges, good)
    return sol


def random_market(rng, m, n, scale=F(1), balanced=False, sparse=False):
    p = [scale * rng.choice([1, 2, 3]) / rng.choice([1, 2]) for _ in range(m)]
    if balanced:
        c = [p[0]] + [scale * rng.choice([1, 2]) for _ in range(n - 1)]
    else:
        c = [scale * F(rng.randint(1, 5), rng.choice([1, 2, 4])) for _ in range(n)]
    a = [[F(rng.randint(-3, 9), rng.choice([1, 2, 3])) for _ in range(n)] for _ in range(m)]
    if rng.random() < 0.5:  # ties
        a[0][-1] = a[0][0]
    b = [[F(rng.randint(1, 9), rng.choice([1, 2, 4, 8])) for _ in range(n)] for _ in range(m)]
    edges = None
    if sparse:
        edges = [(i, j) for i in range(m) for j in range(n) if rng.random() < 0.7] or [(0, 0)]
    return p, c, a, b, edges


if __name__ == "__main__":
    rng = random.Random(20261121)
    sol = negative_control()
    print("negative control: at eps=1 the support", sol, "gives an infeasible system (1); the findings' eps decodes")
    # Hand-made degenerate markets
    cases = [
        ("1x1 tie u+P=2", [1], [1], [[2]], [[1]]),
        ("1x2 two goods", [1], [1, 1], [[2, 1]], [[1, 1]]),
        ("2x2 balanced p(I)=c(J)", [1, 1], [1, 1], [[3, 3], [3, 3]], [[1, 2], [2, 1]]),
        ("2x2 negative intercepts", [1, 2], [2, 1], [[-1, 4], [5, -2]], [[F(1, 4), 3], [7, F(1, 3)]]),
        ("2x2 all zero intercepts", [1, 1], [1, 1], [[0, 0], [0, 0]], [[1, 2], [3, 4]]),
        ("2x2 binary scale", [F(1, 2**40)] * 2, [F(1, 2**40)] * 2, [[3, F(5, 2)], [F(1, 2), 4]],
         [[1, 1 + F(1, 2**60)], [1, 1]]),
    ]
    for name, p, c, a, b in cases:
        N, bits, pos = run(name, p, c, a, b, enumerate_small=True)
        print(f"{name}: N={N}, eps has {bits} bits, {pos} positive principal minors, unique P-LCP solution, decoded M1 equilibrium")
    count = 0
    for trial in range(60):
        m, n = rng.choice([(1, 2), (2, 1), (2, 2), (1, 3), (3, 1), (2, 3), (3, 2)])
        args = random_market(rng, m, n, balanced=trial % 3 == 0, sparse=trial % 4 == 1)
        small = len(args[0]) * len(args[1]) + m + n <= 8
        run(f"random {trial}", *args, enumerate_small=small, minors=(m * n + m + n <= 11))
        count += 1
    print(f"random: {count} markets (ties, balances, negative intercepts, sparse edges): all checks pass")
    # larger markets: skip minor enumeration, keep LCP uniqueness + decode
    for trial in range(8):
        m, n = rng.choice([(3, 3), (4, 3), (3, 4)])
        args = random_market(rng, m, n, scale=F(1, 2**30), balanced=trial % 2 == 0)
        N, bits, _ = run(f"large {trial}", *args, minors=False)
    print(f"large: 8 markets up to N={N}, eps up to {bits} bits: unique P-LCP solution and exact decode")
    print("ALL CHECKS PASSED")
