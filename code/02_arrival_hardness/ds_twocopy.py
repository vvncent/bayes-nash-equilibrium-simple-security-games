"""Exact test of the two-copy construction.

Core network: source s; copy A = Disser-Skutella counting network G_m from s to sink a;
copy B = a second G_m from s to sink b, with +eps on every arc entering b.
If G_m's parametric min-cost-flow increments delta_1 < ... < delta_{2^m} are strictly
increasing with minimum gap g, and 0 < eps < g, then greedy merging of the a-increments
(delta_i) and b-increments (delta_i + eps) alternates a, b, a, b, ... so the unique optimum
sends ceil(x/2) to a for every x in 0..K, K = 2^(m+1).
"""
import os
import sys

import os as _os, sys as _sys  # artifact: path bootstrap (relative to this file)
_HERE = _os.path.dirname(_os.path.abspath(__file__))
_sys.path[:0] = [_HERE, _os.path.join(_HERE, "..", "lib")]
from ds_twosink import mcf  # noqa: E402


def ds(m, base, src, sink, prefix, sink_extra=0, start=0):
    """Arcs of G_m with named endpoints. Returns (arcs, node_names)."""
    def S(k):
        return src if k == m else f"{prefix}s{k}"

    def T(k):
        return sink if k == m else f"{prefix}t{k}"

    def extra(head):
        return sink_extra if head == sink else 0

    arcs = [(S(0), T(0), 1, 0 + extra(T(0)))]
    for k in range(1, m + 1):
        c, w = 2 ** (k - 1), base ** k
        for (u, v, cost) in ((S(k), S(k - 1), 0), (T(k - 1), T(k), 0),
                             (S(k), T(k - 1), w), (S(k - 1), T(k), w)):
            arcs.append((u, v, c, cost + extra(v)))
    return arcs


def increments(m, base):
    arcs = ds(m, base, "s", "t", "")
    names = sorted({u for a in arcs for u in a[:2]})
    idx = {v: i for i, v in enumerate(names)}
    ia = [(idx[u], idx[v], c, w) for (u, v, c, w) in arcs]
    F = [mcf(len(names), ia, idx["s"], {idx["t"]: y}) for y in range(2 ** m + 1)]
    return [F[i + 1] - F[i] for i in range(2 ** m)]


def two_copy(m, base, eps, C=0):
    arcs = ds(m, base, "s", "a", "A", sink_extra=C) + ds(m, base, "s", "b", "B", sink_extra=C + eps)
    return arcs


def check_two_copy(m, base, eps, C=0):
    arcs = two_copy(m, base, eps, C)
    names = sorted({u for a in arcs for u in a[:2]})
    idx = {v: i for i, v in enumerate(names)}
    ia = [(idx[u], idx[v], c, w) for (u, v, c, w) in arcs]
    K = 2 ** (m + 1)
    ok, gap = True, None
    for x in range(K + 1):
        G = {A: mcf(len(names), ia, idx["s"], {idx["a"]: A, idx["b"]: x - A}) for A in range(x + 1)}
        feas = {A: g for A, g in G.items() if g is not None}
        best = min(feas.values())
        arg = [A for A, g in feas.items() if g == best]
        want = (x + 1) // 2
        if arg != [want]:
            ok = False
            print(f"   FAIL x={x}: argmin {arg}, want {want}")
        else:
            nb = [feas[A] - best for A in (want - 1, want + 1) if A in feas]
            if nb:
                gap = min(nb) if gap is None else min(gap, min(nb))
    return ok, gap, len(arcs), len(names)


if __name__ == "__main__":
    base = 3
    allok = True  # artifact: exit status
    for m in range(1, 7):
        inc = increments(m, base)
        strict = all(inc[i] < inc[i + 1] for i in range(len(inc) - 1))
        g = min(inc[i + 1] - inc[i] for i in range(len(inc) - 1))
        allok &= strict and g == 6  # artifact: exit status (strictly increasing, min gap 6)
        print(f"G_{m}: {2**m} increments, strictly increasing={strict}, min gap={g}, "
              f"first={inc[:8]}")
    for m in range(1, 6):
        inc = increments(m, base)
        g = min(inc[i + 1] - inc[i] for i in range(len(inc) - 1))
        eps = g // 2
        ok, kink, narcs, nnodes = check_two_copy(m, base, eps)
        allok &= ok  # artifact: exit status (two-copy PASS)
        print(f"two-copy m={m} K={2**(m+1)} eps={eps}: {'PASS' if ok else 'FAIL'}; "
              f"min kink={kink}; arcs={narcs}; nodes={nnodes}")
    sys.exit(0 if allok else 1)  # artifact: exit status
