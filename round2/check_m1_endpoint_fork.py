"""Check the optimal Boolean load-copy construction against the full M1 port conditions.

Run python3 -B round2/check_m1_endpoint_fork.py with z3-solver installed.
Terminal prices are variables, terminals have no capacity constraint and
unlisted buyer options are unavailable.
"""

from fractions import Fraction
from itertools import product

import z3


def rat(value):
    value = Fraction(value)
    return z3.Q(value.numerator, value.denominator)


def market(capacities, terminal_names, buyers):
    """An equilibrium of the private goods with arbitrary terminal prices in [0,1]."""
    solver = z3.SolverFor("QF_LRA")
    goods = tuple(capacities) + tuple(terminal_names)
    assert len(set(goods)) == len(goods)
    prices = {name: z3.Real(f"p_{name}") for name in goods}
    solver.add(*(price >= 0 for price in prices.values()))
    solver.add(*(prices[name] <= 1 for name in terminal_names))
    loads = {name: [] for name in goods}
    for index, (mass, offers) in enumerate(buyers):
        assert mass > 0
        utility = z3.Real(f"u_{index}")
        solver.add(utility >= 0)
        row = []
        for name, (intercept, slope) in offers.items():
            assert slope > 0
            allocation = z3.Real(f"f_{index}_{name}")
            payoff = rat(intercept) - rat(slope)*prices[name]
            solver.add(allocation >= 0, utility >= payoff, z3.Or(allocation == 0, utility == payoff))
            row.append(allocation)
            loads[name].append(allocation)
        total = z3.Sum(row)
        solver.add(total <= rat(mass), z3.Or(utility == 0, total == rat(mass)))
    total_load = {name: z3.Sum(terms) if terms else rat(0) for name, terms in loads.items()}
    for name, capacity in capacities.items():
        solver.add(total_load[name] <= rat(capacity),
                   z3.Or(prices[name] == 0, total_load[name] == rat(capacity)))
    return solver, prices, total_load


def require(solver, expected):
    result = solver.check()
    if result != expected:
        details = solver.model() if result == z3.sat else solver.reason_unknown()
        raise AssertionError(f"Expected {expected}, obtained {result}: {details}")


def check_fork(copies, scale, bit):
    error = scale * Fraction(copies - 1, 2 * copies)
    capacities, expected, buyers = {}, {}, []
    for rail, high in (("p", bit), ("n", 1-bit)):
        capacities[rail] = scale * (1-high)
        for k in range(copies):
            terminal = f"{rail}_{k}"
            buyers.append((scale/copies, {rail: (4+2*k, 1), terminal: (3, 1)}))
            if error:
                buyers.append((error, {terminal: (3, 1)}))
            expected[terminal] = error + high*scale/copies
    solver, prices, loads = market(capacities, expected, buyers)
    # Feasibility with mixed terminal prices, including both ends of the allowed interval.
    solver.push()
    for i, terminal in enumerate(expected):
        solver.add(prices[terminal] == rat(Fraction(i, len(expected)-1)))
    require(solver, z3.sat)
    solver.pop()
    # The four/all terminals may take arbitrary prices when we seek any wrong amount.
    solver.add(z3.Or(*(loads[name] != rat(value) for name, value in expected.items())))
    require(solver, z3.unsat)
    assert max(abs(value - (scale*bit if name.startswith("p") else scale*(1-bit)))
               for name, value in expected.items()) == error
    return error


def transplant_control():
    """One price strictly falls and one rises while an entire continuum of terminal splits survives."""
    capacities = {"falling": 1, "rising": 1, "equal": Fraction(1, 2)}
    buyers = [
        (1, {"falling": (5, 1), "x": (1, 1)}),
        (1, {"rising": (5, 1), "y": (1, 1)}),
        (1, {"equal": (4, 1), "x": (3, 1), "y": (3, 1),
             "falling": (1, 2), "rising": (1, 3)}),
    ]
    for p, q in ((3, 1), (1, 3)):
        solver, prices, loads = market(capacities, ("x", "y"), buyers)
        solver.add(prices["falling"] == p, prices["rising"] == q, prices["equal"] == 1,
                   prices["x"] == 0, prices["y"] == 0)
        for fraction in (0, Fraction(1, 6), Fraction(7, 20), Fraction(1, 2)):
            solver.push()
            solver.add(loads["x"] == rat(fraction), loads["y"] == rat(Fraction(1, 2)-fraction))
            require(solver, z3.sat)
            solver.pop()
        solver.add(loads["x"] + loads["y"] != rat(Fraction(1, 2)))
        require(solver, z3.unsat)
    # The two endpoint splits are feasible. At fixed prices convexity of the
    # supported flow polytope gives every split along the interval between them.


if __name__ == "__main__":
    for copies, scale in product((1, 2, 3, 5), (Fraction(1), Fraction(5, 3))):
        errors = [check_fork(copies, scale, bit) for bit in (0, 1)]
        assert errors[0] == errors[1]
        label = "copy" if copies == 1 else "copies"
        print(f"{copies} {label} at scale {scale}: exact endpoint error {errors[0]}")
    transplant_control()
    print("All 16 endpoint markets passed. Both price vectors support the same terminal-split control.")
