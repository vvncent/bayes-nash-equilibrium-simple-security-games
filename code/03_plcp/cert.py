"""Exact P-LCP solver by certified complementary basis, for LCP(q, M + delta I) with the reduction's delta.

1. Candidate basis: support of z3's solution of LCP(q, M + delta' I) for a cheap delta' (small bit size).
2. Exact sparse Gaussian elimination (Fractions) of (M + delta I)_AA z_A = -q_A at the ACTUAL delta.
3. Exact check of z >= 0, w = q + (M + delta I) z >= 0 and z_k w_k = 0 for every k.
4. If some sign fails, Murty's least-index principal pivoting (finite for P-matrices) from that basis.
Because M + delta I is a P-matrix, the certified point is THE unique solution, however the basis was found.
"""
import sys
import time
from fractions import Fraction as F

sys.set_int_max_str_digits(0)
import os as _os, sys as _sys  # artifact: path bootstrap (relative to this file)
_HERE = _os.path.dirname(_os.path.abspath(__file__))
_sys.path[:0] = [_HERE, _os.path.join(_HERE, "..", "lib")]
from e2e import solve_plcp, wvec  # noqa: E402


def solve_on_basis(rows, q, delta, A):
    """Solve rows A of q + (M + delta I) z = 0 with z_notA = 0, exactly. Sparse elimination, min-degree."""
    A = sorted(A)
    Aset = set(A)
    eq = {}
    for k in A:
        r = {l: v for l, v in rows[k].items() if l in Aset and v != 0}
        r[k] = r.get(k, F(0)) + delta
        if r[k] == 0:
            del r[k]
        eq[k] = [r, -q[k]]
    colrows = {}
    for k, (r, _) in eq.items():
        for l in r:
            colrows.setdefault(l, set()).add(k)
    order = []
    remaining = set(eq)
    unknowns = set(A)
    while unknowns:
        c = min(unknowns, key=lambda l: (len(colrows.get(l, ())), l))
        cand = [k for k in colrows.get(c, ()) if k in remaining]
        if not cand:
            raise ZeroDivisionError("singular basis matrix")
        pr = min(cand, key=lambda k: (len(eq[k][0]), k))
        prow, prhs = eq[pr]
        piv = prow[c]
        remaining.discard(pr)
        unknowns.discard(c)
        for k in list(colrows[c]):
            if k == pr or k not in remaining:
                continue
            r, rhs = eq[k]
            fct = r[c] / piv
            for l, v in prow.items():
                nv = r.get(l, F(0)) - fct * v
                if nv == 0:
                    if l in r:
                        del r[l]
                        colrows[l].discard(k)
                else:
                    if l not in r:
                        colrows.setdefault(l, set()).add(k)
                    r[l] = nv
            eq[k][1] = rhs - fct * prhs
        order.append((c, pr))
    z = [F(0)] * len(q)
    for c, pr in reversed(order):
        r, rhs = eq[pr]
        s = rhs - sum(v * z[l] for l, v in r.items() if l != c)
        z[c] = s / r[c]
    return z


def certify(rows, q, delta, A, max_iter=2000, log=None):
    """Murty least-index principal pivoting from basis A, exact. Returns (z, iterations)."""
    A = set(A)
    for it in range(max_iter):
        z = solve_on_basis(rows, q, delta, A)
        w = wvec(rows, q, z, delta)
        bad = [k for k in range(len(q)) if (k in A and z[k] < 0) or (k not in A and w[k] < 0)]
        if log:
            log(f"  basis iteration {it}: |A|={len(A)}, sign violations={len(bad)}")
        if not bad:
            assert all(x >= 0 for x in z) and all(x >= 0 for x in w) and all(a * b == 0 for a, b in zip(z, w))
            return z, it
        k = bad[0]
        A ^= {k}
    raise RuntimeError("no certified basis within max_iter")


def exact_plcp(rows, q, delta, delta_guess=F(1, 2 ** 16), log=None):
    """delta_guess = 0 means: start Murty from the support of an M1 equilibrium (z3 on LCP(q, M))."""
    t = time.time()
    zg, st = solve_plcp(rows, q, delta_guess)
    if zg is None:
        raise RuntimeError("guess solve failed: " + st)
    A = {k for k, x in enumerate(zg) if x > 0}
    t_guess = time.time() - t
    z, it = certify(rows, q, delta, A, log=log)
    return z, dict(t_guess=t_guess, t_cert=time.time() - t - t_guess, murty_iterations=it,
                   guess_support=len(A), guess_bits=delta_guess.denominator.bit_length())
