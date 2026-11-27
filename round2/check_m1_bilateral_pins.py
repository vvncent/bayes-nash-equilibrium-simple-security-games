"""Check bilateral payoff pinning using independent full and residual M1 constraints.

Run python3 -B round2/check_m1_bilateral_pins.py with z3-solver installed.
"""

from dataclasses import dataclass
from fractions import Fraction
from itertools import product
from random import Random

import z3


def rat(value):
    value = Fraction(value)
    return z3.Q(value.numerator, value.denominator)


def read(model, variable):
    return Fraction(model.eval(variable, model_completion=True).as_fraction())


@dataclass
class Market:
    masses: dict
    capacities: dict
    offers: dict
    outside: dict
    reserves: dict


@dataclass
class Conditions:
    solver: object
    utilities: dict
    prices: dict
    flows: dict


def conditions(market, tag, buyer_pins=None, seller_pins=None, edge_pins=None):
    """Literal M1 equations with all original edge, outside and capacity conditions."""
    solver = z3.SolverFor("QF_LRA")
    utilities = {i: z3.Real(f"{tag}_u_{i}") for i in market.masses}
    prices = {j: z3.Real(f"{tag}_p_{j}") for j in market.capacities}
    flows = {e: z3.Real(f"{tag}_f_{e[0]}_{e[1]}") for e in market.offers}
    for i, mass in market.masses.items():
        payoff = utilities[i]
        load = sum((f for (ii, _), f in flows.items() if ii == i), rat(0))
        solver.add(payoff >= rat(market.outside[i]), load <= rat(mass),
                   z3.Or(payoff == rat(market.outside[i]), load == rat(mass)))
    for j, capacity in market.capacities.items():
        price = prices[j]
        load = sum((f for (_, jj), f in flows.items() if jj == j), rat(0))
        solver.add(price >= rat(market.reserves[j]), load <= rat(capacity),
                   z3.Or(price == rat(market.reserves[j]), load == rat(capacity)))
    for (i, j), (intercept, slope) in market.offers.items():
        gap = utilities[i] + rat(slope)*prices[j] - rat(intercept)
        solver.add(gap >= 0, flows[i, j] >= 0, z3.Or(flows[i, j] == 0, gap == 0))
    for pins, variables in ((buyer_pins, utilities), (seller_pins, prices), (edge_pins, flows)):
        if pins:
            solver.add(*(variables[key] == rat(value) for key, value in pins.items()))
    return Conditions(solver, utilities, prices, flows)


def residual(market, buyer_pins, seller_pins):
    buyers = {i: mu for i, mu in market.masses.items() if i not in buyer_pins}
    goods = {j: cap for j, cap in market.capacities.items() if j not in seller_pins}
    offers = {e: ob for e, ob in market.offers.items() if e[0] in buyers and e[1] in goods}
    outside = {i: Fraction(market.outside[i]) for i in buyers}
    reserves = {j: Fraction(market.reserves[j]) for j in goods}
    for (i, j), (a, b) in market.offers.items():
        if i in buyers and j in seller_pins:
            outside[i] = max(outside[i], a - b*seller_pins[j])
        elif i in buyer_pins and j in goods:
            reserves[j] = max(reserves[j], Fraction(a - buyer_pins[i])/b)
    return Market(buyers, goods, offers, outside, reserves)


def zero_reserves(masses, capacities, offers):
    return Market(masses, capacities, offers, {i: 0 for i in masses},
                  {j: 0 for j in capacities})


def boundary_witness(full, market, buyer_pins, seller_pins):
    return {e: read(full.solver.model(), full.flows[e]) for e in market.offers
            if e[0] in buyer_pins or e[1] in seller_pins}


def extension_at(market, buyer_pins, seller_pins, reduced, boundary):
    state = reduced.solver.model()
    u = {i: read(state, var) for i, var in reduced.utilities.items()}
    p = {j: read(state, var) for j, var in reduced.prices.items()}
    return conditions(market, "extension", buyer_pins | u, seller_pins | p, boundary)


def random_pins():
    rng = Random(484)
    numbers = (Fraction(0), Fraction(1, 3), Fraction(1), Fraction(4, 3), Fraction(2))
    yes = no = 0
    for _ in range(45):
        n = rng.choice((2, 3))
        offers = {(i, j): (rng.randint(0, 4), rng.randint(1, 3))
                  for i, j in product(range(n), repeat=2)}
        full_market = zero_reserves(dict.fromkeys(range(n), 1), dict.fromkeys(range(n), 1), offers)
        bp, sp = {0: rng.choice(numbers)}, {0: rng.choice(numbers)}
        full = conditions(full_market, "full", bp, sp)
        expected = full.solver.check()
        assert expected in (z3.sat, z3.unsat)
        boundary = boundary_witness(full, full_market, bp, sp) if expected == z3.sat else {}
        small = residual(full_market, bp, sp)
        for trial_u, trial_p in product(numbers, repeat=2):
            test = conditions(small, "residual", {1: trial_u}, {1: trial_p})
            if test.solver.check() == z3.unsat:
                continue
            extended = extension_at(full_market, bp, sp, test, boundary)
            assert extended.solver.check() == expected
            if expected == z3.sat:
                yes += 1
            else:
                no += 1
    return yes, no


def targeted():
    # Split a boundary buyer and fill a boundary good from two interior buyers.
    # The other two buyers/goods form a changing-price block requiring rematching.
    masses = {0: 1, 1: Fraction(1, 2), 2: Fraction(1, 2), 3: 1, 4: 1}
    caps = {0: 1, 1: Fraction(1, 2), 2: Fraction(1, 2), 3: 1, 4: 1}
    offers = {(0, 1): (1, 1), (0, 2): (1, 1), (1, 0): (2, 1), (2, 0): (2, 1)}
    offers.update({(i, j): (2, 2 if i == j else 1) for i, j in product((3, 4), repeat=2)})
    market = zero_reserves(masses, caps, offers)
    bp, sp = {0: Fraction(1)}, {0: Fraction(1)}
    boundary = {e: Fraction(1, 2) for e in offers if e[0] == 0 or e[1] == 0}
    assert conditions(market, "old", bp, sp | {3: 0, 4: 0},
                      boundary | {(3, 3): 1, (4, 4): 1}).solver.check() == z3.sat
    assert conditions(market, "changed", bp, sp | {3: 1, 4: 1},
                      boundary | {(3, 3): 1, (4, 4): 1}).solver.check() == z3.unsat
    small = residual(market, bp, sp)
    changed = conditions(small, "res", seller_pins={3: 1, 4: 1})
    assert changed.solver.check() == z3.sat
    extension = extension_at(market, bp, sp, changed, boundary)
    assert extension.solver.check() == z3.sat
    assert all(read(extension.solver.model(), extension.flows[e]) == 1 for e in ((3, 4), (4, 3)))

    # A positive nonzero old reserve can dominate a proposed boundary contract.
    sparse = Market({10: 1, 11: 1}, {20: 1, 21: 1},
                    {(10, 21): (1, 2), (11, 20): (1, 3)},
                    {10: Fraction(1, 2), 11: Fraction(2)}, {20: Fraction(1), 21: Fraction(3)})
    bp, sp = {10: Fraction(1, 2)}, {20: Fraction(1)}
    small = residual(sparse, bp, sp)
    assert small.outside == {11: 2} and small.reserves == {21: 3}
    trial = conditions(small, "sparse")
    assert trial.solver.check() == z3.sat
    assert extension_at(sparse, bp, sp, trial, {(10, 21): 0, (11, 20): 0}).solver.check() == z3.sat

    # One or both sides may be entirely pinned; the remaining side then trades no interior mass.
    singleton = zero_reserves({0: 1}, {0: 1}, {(0, 0): (1, 1)})
    for bp, sp in (({0: Fraction(1, 2)}, {}), ({}, {0: Fraction(1, 2)}),
                   ({0: Fraction(1, 2)}, {0: Fraction(1, 2)})):
        small = residual(singleton, bp, sp)
        trial = conditions(small, "empty")
        assert trial.solver.check() == z3.sat
        assert extension_at(singleton, bp, sp, trial, {(0, 0): 1}).solver.check() == z3.sat


if __name__ == "__main__":
    yes, no = random_pins()
    print(f"{yes+no} residual payoff selections on 45 seeded markets: "
          f"{yes} extended with previous boundary flows, {no} failed along with the full pin system.")
    targeted()
    print("Fractional boundary preservation, required interior rematching, nonzero reserves, "
          "missing edges and empty interior sides passed.")
