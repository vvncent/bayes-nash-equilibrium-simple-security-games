"""Exact equilibrium-price/flow transplantation and continuous-path regressions.

Requires z3-solver. These are finite-instance checks of the general argument
in m1-equilibrium-space.md, including universal assertions over all real
market equilibria and one ordered price path with a full tie fiber.
"""

from fractions import Fraction as F
from random import Random

import z3

from wardrop.check_wardrop import add, expect, market, q, rule_out


def constraints(goods, buyers, prices, flow, best):
    tests = []
    for i, (mass, offers) in buyers.items():
        used = add(*(flow[i, j] for j in offers))
        tests.extend((best[i] >= 0, used <= q(mass), z3.Or(used == q(mass), best[i] == 0)))
        for j, (a, b) in offers.items():
            utility = q(a) - q(b) * prices[j]
            tests.extend((flow[i, j] >= 0, best[i] >= utility, z3.Or(flow[i, j] == 0, best[i] == utility)))
    for j, cap in goods.items():
        load = add(*(flow[i, k] for i, k in flow if k == j))
        tests.extend((prices[j] >= 0, load <= q(cap), z3.Or(prices[j] == 0, load == q(cap))))
    return z3.And(*tests)


def check_transplant(goods, buyers, tag):
    solver = z3.SolverFor("QF_LRA")
    p, f, _ = market(solver, tag + "1", goods, buyers)
    r, g, best = market(solver, tag + "2", goods, buyers)
    # An unchanged price keeps f's whole column. Every changed column keeps
    # g's, which is full in both equilibria by the demand comparison.
    h = {(i, j): z3.If(p[j] == r[j], val, g[i, j]) for (i, j), val in f.items()}
    claims = [constraints(goods, buyers, r, h, best)]
    for i, (_, opts) in buyers.items():
        claims.append(add(*(h[i, j] for j in opts)) == add(*(f[i, j] for j in opts)))
    for j in goods:
        claims.append(add(*(h[i, k] for i, k in h if k == j)) == add(*(f[i, k] for i, k in f if k == j)))
    expect(solver, z3.sat, f"{tag} exists")
    rule_out(solver, z3.Not(z3.And(*claims)), f"{tag} fails full simultaneous boundary transplantation")


def switch_test():
    goods = {"A": 1, "B": 1, "C": 3, "D": 2}
    buyers = {
        "U": (1, {"A": (4, 2), "B": (F(5, 2), 1), "C": (-1, 1)}),
        "V": (1, {"A": (3, 1), "B": (F(9, 2), 2)}),
        "W": (2, {"C": (0, 1), "D": (0, 1), "A": (-1, 1)}),
    }
    check_transplant(goods, buyers, "switch")
    solver = z3.SolverFor("QF_LRA")
    p, f, _ = market(solver, "all", goods, buyers)
    rule_out(solver, z3.Or(p["C"] != 0, p["D"] != 0), "named zero-price subarray is globally invariant")
    t, a, y, z = z3.Reals("diagonal_price matched_fraction load_C load_D")
    half = q(F(3, 2))
    regions = ((t >= 1, t < half, a == 1),
               (t == half, a >= 0, a <= 1),
               (t > half, t <= 2, a == 0))
    scalar = z3.SolverFor("QF_LRA")
    for region in regions:
        for test in (solver, scalar):
            test.push()
            test.add(*region, y >= 0, z >= 0, y+z <= 2)
        # Converse: no other core assignment can arise anywhere on this price class.
        solver.add(p["A"] == t, p["B"] == t, f["U", "A"] == a,
                   f["W", "C"] == y, f["W", "D"] == z)
        expect(solver, z3.sat, "nonempty piece of the joint path")
        rule_out(solver, z3.Or(f["V", "B"] != a, f["U", "B"] != 1-a,
                               f["V", "A"] != 1-a, f["W", "A"] != 0,
                               f["U", "C"] != 0), "extra path assignment")
        # Forward: verify explicit feasible allocations throughout each continuum.
        prices = {"A": t, "B": t, "C": q(0), "D": q(0)}
        flow = {("U","A"): a, ("U","B"): 1-a, ("U","C"): q(0),
                ("V","A"): 1-a, ("V","B"): a, ("W","A"): q(0),
                ("W","C"): y, ("W","D"): z}
        best = {"U": z3.If(t <= half, 4-2*t, q(F(5, 2))-t),
                "V": z3.If(t <= half, q(F(9, 2))-2*t, 3-t), "W": q(0)}
        rule_out(scalar, z3.Not(constraints(goods, buyers, prices, flow, best)),
                 "explicit all-real path or boundary-fiber witness failed")
        solver.pop()
        scalar.pop()
    # A separate reverse implication tests the excluded, incompatible diagonal
    # assignments without first assuming a is the expected value.
    solver.add(p["A"] == t, p["B"] == t, 1 <= t, t <= 2)
    rule_out(solver, z3.Or(z3.And(t < half, f["U", "A"] != 1),
                           z3.And(t > half, f["U", "A"] != 0)),
             "the two strict endpoint matchings should be forced")
    # Enumerate attainable masks by price class, including the support
    # strictly containing the two distinct endpoint singletons.
    for name, price, masks in (
        ("low", 1, {(True, False)}),
        ("tie", half, {(True, False), (False, True), (True, True)}),
        ("high", 2, {(False, True)}),
    ):
        for pos_a in (False, True):
            for pos_b in (False, True):
                solver.push()
                solver.add(t == price, (f["U", "A"] > 0) == pos_a,
                           (f["U", "B"] > 0) == pos_b)
                expected = z3.sat if (pos_a, pos_b) in masks else z3.unsat
                expect(solver, expected, f"{name} trade mask {(pos_a, pos_b)}")
                solver.pop()


def no_common_support():
    goods = dict.fromkeys("ABC", 1)
    buyers = {
        1: (1, {"A": (20, 2), "B": (16, 1), "C": (18, 2)}),
        2: (1, {"B": (20, 2), "C": (18, 1)}),
        3: (1, {"A": (18, 1), "C": (20, 3)}),
    }
    solver = z3.SolverFor("QF_LRA")
    p, f, _ = market(solver, "no_union", goods, buyers)
    matchings = (("A", "B", "C"), ("B", "C", "A"))
    for price, targets in zip((F(1, 2), F(9, 2)), matchings):
        solver.push()
        solver.add(*(t == q(price) for t in p.values()))
        expect(solver, z3.sat, "strict matching price clears")
        rule_out(solver, z3.Or(*(f[i, j] != 1 for i, j in enumerate(targets, 1))),
                 "strict matching endpoints are forced")
        solver.pop()
    rule_out(solver, z3.And(*(f[i, j] > 0 for targets in matchings
                              for i, j in enumerate(targets, 1))),
             "the two supports have an attainable common upper bound")
    a, b, c = (F(n, 11) for n in (32, 20, 18))
    assert 2*a == b+4 and 2*b == c+2 and 3*c == a+2
    assert (18-2*c) - (20-2*a) == F(6, 11)


def main():
    switch_test()
    no_common_support()
    rng = Random(1703)
    for k in range(32):
        capacities = {j: F(rng.randrange(1, 6), 2) for j in range(3)}
        buyers = {i: (F(rng.randrange(1, 6), 2),
                      {j: (rng.randrange(-1, 5), rng.randrange(1, 4)) for j in capacities})
                  for i in range(3)}
        check_transplant(capacities, buyers, f"rng{k}")
    print("Universal two-equilibrium transplantation passed on 32 seeded markets and one switching market.")
    print("Three continuous path pieces include every tied matching mixture and all outside/vacancy readouts on the triangular (C,D) subarray.")
    print("12 exact price-class/support cases confirmed the two endpoint singletons and their positive two-edge bridge.")
    print("A separate 3-by-3 market has two strict supports with no attainable upper bound; the obstructing payoff gap is 6/11.")


if __name__ == "__main__":
    main()
