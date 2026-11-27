"""Certify cycling of first-violated-offer insertion, including after M1 isolation.

Requires z3-solver. Run with Python 3.10+ from any working directory.
"""

from itertools import combinations
from random import Random

import z3

from m1_isolation import isolate_market
from wardrop.check_wardrop import exact, expect, market, q


CORE_EDGES = (("A", "X"), ("B", "X"), ("B", "Y"), ("B", "Z"),
              ("C", "X"), ("C", "Y"), ("C", "Z"))
ENTERING_ORDER = (1, 0, 2, 3, 5, 6, 4)
CORE_TRAJECTORY = (
    (), (1,), (0,), (0, 2), (0, 2, 3), (0, 2, 3, 5), (0, 2, 6),
    (2, 4, 6), (2, 3, 4, 6), (2, 3, 4, 5), (1, 2, 3, 5), (0, 2, 3, 5),
)


def core_market():
    goods = {"X": 3, "Y": 6, "Z": 3}
    buyers = {
        "A": (4, {"X": (3, 1)}),
        "B": (7, {"X": (11, 4), "Y": (6, 1), "Z": (7, 4)}),
        "C": (4, {"X": (6, 1), "Y": (5, 1), "Z": (2, 1)}),
    }
    return goods, buyers


def restricted_answer(goods, buyers, menu):
    restricted = {
        i: (mass, {j: bid for j, bid in options.items() if (i, j) in menu})
        for i, (mass, options) in buyers.items()
    }
    solver = z3.SolverFor("QF_LRA")
    variables = market(solver, "restricted", goods, restricted)
    expect(solver, z3.sat, "restricted equilibrium exists")
    model = solver.model()
    prices, flows, values = point = tuple(
        {key: exact(model, variable) for key, variable in part.items()}
        for part in variables
    )
    solver.add(z3.Or(*(variable != q(part_point[key])
                       for part, part_point in zip(variables, point)
                       for key, variable in part.items())))
    expect(solver, z3.unsat, "second equilibrium at this menu")
    basis = frozenset(edge for edge, amount in flows.items() if amount > 0)
    conflicts = frozenset((i, j) for i, (_, options) in buyers.items()
                          for j, (intercept, slope) in options.items()
                          if intercept > values[i] + slope * prices[j])
    return basis, conflicts


def check_all_core_menus():
    goods, buyers = core_market()
    ground = frozenset(CORE_EDGES)
    powerset = [frozenset(s) for k in range(len(ground) + 1)
                for s in combinations(CORE_EDGES, k)]
    answers = {menu: restricted_answer(goods, buyers, menu) for menu in powerset}
    for menu, (basis, conflicts) in answers.items():
        assert basis <= menu and not (conflicts & menu)
        for other, (other_basis, other_conflicts) in answers.items():
            assert (other_basis == basis) == (basis <= other <= ground - conflicts)
            if menu <= other and not (conflicts & other):
                assert other_conflicts == conflicts
    assert len({basis for basis, _ in answers.values()}) == 41
    for here, there in zip(CORE_TRAJECTORY, CORE_TRAJECTORY[1:]):
        current = frozenset(CORE_EDGES[k] for k in here)
        best, conflicts = answers[current]
        assert best == current
        entering = next(CORE_EDGES[k] for k in ENTERING_ORDER if CORE_EDGES[k] in conflicts)
        assert answers[current | {entering}][0] == frozenset(CORE_EDGES[k] for k in there)
    assert answers[ground][0] == frozenset(CORE_EDGES[k] for k in (0, 2, 3, 4, 5))
    print("All 128 compact menus have unique equilibria. Their 41 support intervals "
          "satisfy the violator axioms, and the first-violation rule cycles.")


def check_weighted_sampling():
    """Run Clarkson's Basis2 on a dimension-one market with 80 distinct bids."""
    rng = Random(17)
    total = 80
    goods = {"J": 1}
    buyers = {i: (2, {"J": (i + 1, 1)}) for i in range(total)}
    ground = [(i, "J") for i in range(total)]
    weights = [1] * total
    sample_size = 6
    for iteration in range(1, 1001):
        # Sampling positions without replacement avoids expanding a multiset.
        population = sum(weights)
        sample = []
        removed = [0] * total
        for t in range(sample_size):
            draw = rng.randrange(population - t)
            for index, weight in enumerate(weights):
                available = weight - removed[index]
                if draw < available:
                    removed[index] += 1
                    sample.append(ground[index])
                    break
                draw -= available
        basis, conflicts = restricted_answer(goods, buyers, frozenset(sample))
        assert len(basis) == 1
        if not conflicts:
            assert basis == frozenset({(total - 1, "J")})
            print(f"Clarkson's weighted sampler found the unique full-market edge "
                  f"among {total} offers in {iteration} rounds (dimension one).")
            return
        bad_indices = [i for i, _ in conflicts]
        if 3 * sum(weights[i] for i in bad_indices) <= population:
            for i in bad_indices:
                weights[i] *= 2
    raise AssertionError("seeded weighted sampling regression did not finish")


def rectangle_market():
    goods, buyers = core_market()
    buyers["B"] = (7, {"X2": (15, 2), "Y": (6, 1), "Z2": (11, 2)})
    auxiliary_priority = []
    for dest in ("X", "Z"):
        first, second = dest + "1", dest + "2"
        left, right, guard = "L" + dest, "R" + dest, "G" + dest
        goods[dest] += 1
        goods[first] = goods[second] = 10
        buyers[right] = (10, {second: (100, 1), first: (99, 1)})
        buyers[left] = (10, {first: (100, 1), dest: (99, 2)})
        buyers[guard] = (1, {second: (101, 1)})
        auxiliary_priority.extend(((guard, second), (right, second), (right, first),
                                   (left, first), (left, dest)))
    group = {"B", "LX", "LZ"}
    exceptional_goods = {"X", "Z", "X2", "Z2"}
    for i, (_, options) in buyers.items():
        for j, (_, slope) in options.items():
            assert slope == 1 + int(i in group and j in exceptional_goods)
    return goods, buyers, tuple(auxiliary_priority)


def check_rectangle():
    goods, buyers, prefix = rectangle_market()
    query = isolate_market(goods, buyers)
    core_edges = tuple((i, j + "2") if i == "B" and j in ("X", "Z") else (i, j)
                       for i, j in CORE_EDGES)
    priority = prefix + tuple(core_edges[e] for e in ENTERING_ORDER)
    complete = frozenset(priority)
    assert len(query.buyers) == 9 and len(query.goods) == 7 and len(complete) == 17
    for i, (_, offers) in buyers.items():
        for j, (_, slope) in offers.items():
            assert query.buyers[i][1][j][1] == slope
    observed = []
    menu = frozenset()
    for step in range(24):
        basis, conflicts = restricted_answer(query.goods, query.buyers, menu)
        if step >= 12:
            assert set(prefix) <= basis
            observed.append(tuple(e for e, edge in enumerate(core_edges) if edge in basis))
        if step == 23:
            break
        entering = next(edge for edge in priority if edge in conflicts)
        menu = basis | {entering}
    assert tuple(observed) == CORE_TRAJECTORY
    assert len(set(observed[5:-1])) == 6
    full, conflicts = restricted_answer(query.goods, query.buyers, complete)
    assert not conflicts
    assert full == frozenset(prefix) | frozenset(core_edges[k] for k in (0, 2, 3, 4, 5))
    print(f"Globally isolated single-rectangle instance: {len(buyers)} buyers, "
          f"{len(goods)} goods, {len(priority)} listed offers, "
          f"delta=2^-{query.delta.denominator.bit_length() - 1}. "
          "The exact six-cycle is reached from the empty menu.")


if __name__ == "__main__":
    check_all_core_menus()
    check_weighted_sampling()
    check_rectangle()
