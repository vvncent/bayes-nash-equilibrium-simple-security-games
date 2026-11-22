"""Independent exact check of the increment lemma for the Disser-Skutella network G_m (base 3).

(1) Increments from the proved recursion: D_0 = (0); D_k = D_{k-1} followed by
    (2*3^k - d for d in reversed(D_{k-1})).
(2) Exact LP values F_m(y), y = 0..2^m, by z3 Optimize (linear real arithmetic, exact rationals),
    on the arc list copied from twocopy_gadget.ds_arcs, plus F_m at half-integers to confirm linearity
    between integer breakpoints.
Usage: incr_check.py MMAX
"""
import sys
from fractions import Fraction as F

import z3


def ds_arcs(m, base=3):
    def S(k):
        return "s" if k == m else f"s{k}"

    def T(k):
        return "t" if k == m else f"t{k}"

    arcs = [(S(0), T(0), 1, 0)]
    for k in range(1, m + 1):
        c, w = 2 ** (k - 1), base ** k
        arcs += [(S(k), S(k - 1), c, 0), (T(k - 1), T(k), c, 0),
                 (S(k), T(k - 1), c, w), (S(k - 1), T(k), c, w)]
    return arcs


def recursion(m):
    D = [0]
    for k in range(1, m + 1):
        D = D + [2 * 3 ** k - d for d in reversed(D)]
    return D


def lp_value(m, y):
    arcs = ds_arcs(m)
    o = z3.Optimize()
    f = [z3.Real(f"f{i}") for i in range(len(arcs))]
    nodes = {u for a in arcs for u in a[:2]}
    for i, (_, _, c, _) in enumerate(arcs):
        o.add(f[i] >= 0, f[i] <= c)
    for v in nodes:
        out = z3.Sum([f[i] for i, a in enumerate(arcs) if a[0] == v] or [z3.RealVal(0)])
        inn = z3.Sum([f[i] for i, a in enumerate(arcs) if a[1] == v] or [z3.RealVal(0)])
        rhs = {"s": y, "t": -y}.get(v, 0)
        o.add(out - inn == z3.RealVal(str(F(rhs))))
    cost = z3.Sum([a[3] * f[i] for i, a in enumerate(arcs)])
    h = o.minimize(cost)
    assert o.check() == z3.sat
    return F(o.lower(h).as_string())


if __name__ == "__main__":
    mmax = int(sys.argv[1]) if len(sys.argv) > 1 else 5
    allok = True
    for m in range(1, mmax + 1):
        D = recursion(m)
        Fv = [lp_value(m, y) for y in range(2 ** m + 1)]
        inc = [Fv[i + 1] - Fv[i] for i in range(2 ** m)]
        half = all(lp_value(m, F(2 * y + 1, 2)) == (Fv[y] + Fv[y + 1]) / 2 for y in range(2 ** m))
        gaps = [D[i + 1] - D[i] for i in range(len(D) - 1)]
        ok = inc == D and half and min(gaps) == 6 and D[-1] == 2 * 3 ** m and D[0] == 0
        allok &= ok
        print(f"m={m}: LP increments == recursion: {inc == D}; linear between integers: {half}; "
              f"min gap {min(gaps)}; max increment {D[-1]} (2*3^m = {2 * 3 ** m}); first {D[:8]}")
    print("ALL OK" if allok else "MISMATCH")
    sys.exit(0 if allok else 1)  # artifact: exit status
