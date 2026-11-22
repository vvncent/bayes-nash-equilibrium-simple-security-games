"""Exact (z3, linear real arithmetic) verifier for ARRIVAL switch gadgets in the ordinary market M1.

A gadget is: input good 'p' (capacity cp, external load x), private goods (capacities), two port goods
'a','b' (prices are free parameters in [0,U], no clearing condition), buyers (mass, {good: (a_ij, b_ij)}),
outside option 0 for every buyer.

check(g, K, U) certifies, by unsatisfiability over ALL (x, P_a, P_b, prices, values, flows) -- i.e. over
every policy chamber at once, including ties, zero prices, box endpoints and degenerate margins:
  S1  for every x in [0,K], (P_a,P_b) in [0,U]^2, every equilibrium has A = h0(x), B = h1(x), P_p <= U;
  S2  for every x in [K, cp)  (x = cp is excluded by the network sizing rule S3), (P_a,P_b) in [0,U]^2, every equilibrium has A,B >= K/2, A+B <= x, P_p <= U;
plus a non-vacuity check (an equilibrium exists at a sample point of each piece).
"""
from fractions import Fraction as F
import z3


def Q(v):
    v = F(v)
    return z3.RealVal(f"{v.numerator}/{v.denominator}")


def equilibrium(g, x, Pa, Pb, s, tag=""):
    """Add M1 equilibrium constraints of gadget g (with port prices Pa, Pb and external load x) to s.
    Returns (A, B, Pp)."""
    goods = dict(g["goods"])  # private goods name -> capacity
    price = {j: z3.Real(f"P_{j}{tag}") for j in list(goods) + ["p"]}
    price["a"], price["b"] = Pa, Pb
    for j in list(goods) + ["p"]:
        s.add(price[j] >= 0)
    load = {j: [] for j in list(goods) + ["p", "a", "b"]}
    for i, (m, edges) in enumerate(g["buyers"]):
        v = z3.Real(f"v_{i}{tag}")
        s.add(v >= 0)
        row = []
        for j, (aij, bij) in edges.items():
            f = z3.Real(f"f_{i}_{j}{tag}")
            s.add(f >= 0)
            u = Q(aij) - Q(bij) * price[j]
            s.add(v >= u)
            s.add(z3.Or(f == 0, v == u))
            row.append(f)
            load[j].append(f)
        rs = z3.Sum(row) if row else Q(0)
        s.add(rs <= Q(m))
        s.add(z3.Or(v == 0, rs == Q(m)))
    for j, c in goods.items():
        L = z3.Sum(load[j]) if load[j] else Q(0)
        s.add(L <= Q(c))
        s.add(z3.Or(price[j] == 0, L == Q(c)))
    Lp = (z3.Sum(load["p"]) if load["p"] else Q(0)) + x
    s.add(Lp <= Q(g["cp"]))
    s.add(z3.Or(price["p"] == 0, Lp == Q(g["cp"])))
    A = z3.Sum(load["a"]) if load["a"] else Q(0)
    B = z3.Sum(load["b"]) if load["b"] else Q(0)
    return A, B, price["p"]


def h(x):
    """Exact h0,h1 for rational x >= 0."""
    x = F(x)
    z = x.numerator // (2 * x.denominator)  # floor(x/2)
    r = x - 2 * z
    return (z + min(r, 1), z + max(r - 1, 0))


def check(g, K, U, verbose=False):
    U = F(U)
    results = []
    pieces = [(k, k + 1) for k in range(K)] + [(K, g["cp"])]
    for (lo, hi) in pieces:
        s = z3.Solver()
        x, Pa, Pb = z3.Real("x"), z3.Real("Pa"), z3.Real("Pb")
        s.add(x >= Q(lo), (x <= Q(hi)) if lo < K else (x < Q(hi)), Pa >= 0, Pa <= Q(U), Pb >= 0, Pb <= Q(U))
        A, B, Pp = equilibrium(g, x, Pa, Pb, s)
        if lo < K:
            z = lo // 2
            if lo % 2 == 0:
                H0, H1 = Q(z) + (x - Q(lo)), Q(z)
            else:
                H0, H1 = Q(z + 1), Q(z) + (x - Q(lo))
            bad = z3.Or(A != H0, B != H1, Pp > Q(U))
        else:
            bad = z3.Or(A < Q(F(K, 2)), B < Q(F(K, 2)), A + B > x, Pp > Q(U))
        s.push()
        s.add(bad)
        r = s.check()
        s.pop()
        # non-vacuity: some equilibrium exists at the midpoint with mid-box prices
        s.add(x == Q(F(lo + hi, 2)), Pa == Q(U / 3), Pb == Q(2 * U / 3))
        nv = s.check()
        ok = (r == z3.unsat) and (nv == z3.sat)
        results.append(((lo, hi), str(r), str(nv), ok))
        if verbose:
            print(f"  piece x in [{lo},{hi}]: violation {r}, existence {nv}")
    return all(o for *_, o in results), results


def size(g):
    return len(g["buyers"]) + len(g["goods"]) + 1  # buyers + private goods + input good


def bits(g):
    tot = 0
    vals = [g["cp"]] + list(g["goods"].values())
    for m, e in g["buyers"]:
        vals.append(m)
        for (a, b) in e.values():
            vals += [a, b]
    for v in vals:
        v = F(v)
        tot += abs(v.numerator).bit_length() + v.denominator.bit_length()
    return tot
