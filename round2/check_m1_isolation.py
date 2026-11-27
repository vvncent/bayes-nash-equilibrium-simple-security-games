"""Exact tests of deterministic isolation and original-market support repair.

Run ``python3 -B round2/check_m1_isolation.py`` with z3-solver installed.
The full market oracle uses disjunctive real constraints independently of
the isolation compiler. The repair test quantifies over the entire original
linear system selected by the perturbed support.
"""

from collections import Counter
from fractions import Fraction as F
from itertools import product
from random import Random

import z3

from m1_isolation import decode_equilibrium, isolate_market
from wardrop.check_wardrop import exact, market, q


def check(solver, expected, message):
    result = solver.check()
    if result != expected:
        detail = solver.model() if result == z3.sat else solver.reason_unknown()
        raise AssertionError(f"{message}: expected {expected}, got {result}: {detail}")


def solve(goods, buyers, tag):
    solver = z3.SolverFor("QF_LRA")
    variables = market(solver, tag, goods, buyers)
    check(solver, z3.sat, tag)
    model = solver.model()
    point = tuple({key: exact(model, v) for key, v in group.items()} for group in variables)
    return solver, variables, point


def pins(variables, point):
    return z3.And(*(symbol == q(point[part][key]) for part, group in enumerate(variables)
                    for key, symbol in group.items()))


def has_another(solver, variables, point):
    solver.push()
    solver.add(z3.Not(pins(variables, point)))
    result = solver.check()
    if result == z3.unknown:
        raise AssertionError(solver.reason_unknown())
    solver.pop()
    return result == z3.sat


def test_pattern(goods, buyers, perturbed, repaired, label):
    """Require independent LP feasibility and exclude any invalid feasible point."""
    reference = z3.SolverFor("QF_LRA")
    p, f, u = market(reference, "repair", goods, buyers)
    prices, flows, utilities = perturbed
    pattern = z3.SolverFor("QF_LRA")
    for i, (mass, offers) in buyers.items():
        spent = sum((f[i, j] for j in offers), q(0))
        pattern.add(u[i] >= 0, spent <= q(mass))
        pattern.add(u[i] == 0 if utilities[i] == 0 else spent == q(mass))
        for j, (intercept, slope) in offers.items():
            gap = u[i] + q(slope) * p[j] - q(intercept)
            pattern.add(gap >= 0, f[i, j] >= 0)
            pattern.add(f[i, j] == 0 if flows[i, j] == 0 else gap == 0)
    for j, capacity in goods.items():
        load = sum((f[i, j] for i, (_, offers) in buyers.items() if j in offers), q(0))
        pattern.add(p[j] >= 0, load <= q(capacity))
        pattern.add(p[j] == 0 if prices[j] == 0 else load == q(capacity))

    for i, group in enumerate((p, f, u)):
        assert set(group) == set(repaired[i]), label
        assert all(isinstance(v, F) for v in repaired[i].values()), label
    pattern.push()
    pattern.add(pins((p, f, u), repaired))
    check(pattern, z3.sat, label + " decoded point in original pattern")
    pattern.pop()
    pattern.add(z3.Not(z3.And(*reference.assertions())))
    check(pattern, z3.unsat, label + " invalid original equilibrium in the repair polyhedron")


def validate_forest(goods, buyers, point):
    """All tight edges count, including unused ties."""
    prices, _, utilities = point
    graph = {(0, i): set() for i in buyers} | {(1, j): set() for j in goods}
    anchors = {(0, i) for i in buyers if utilities[i] == 0}
    anchors.update((1, j) for j in goods if prices[j] == 0)
    for i, (_, offers) in buyers.items():
        for j, (a, b) in offers.items():
            if utilities[i] + b * prices[j] == a:
                graph[0, i].add((1, j))
                graph[1, j].add((0, i))
    remaining = set(graph)
    while remaining:
        first = remaining.pop()
        component = {first}
        queue = [first]
        while queue:
            for neighbor in graph[queue.pop()]:
                if neighbor in remaining:
                    remaining.remove(neighbor)
                    component.add(neighbor)
                    queue.append(neighbor)
        assert len(anchors & component) == 1, (component, anchors)
        assert sum(len(graph[node]) for node in component) == 2 * (len(component) - 1)


def check_case(label, goods, buyers, counts, original_unique=None, first_offers=()):
    original, original_vars, original_point = solve(goods, buyers, "original")
    multiple = has_another(original, original_vars, original_point)
    if original_unique is not None:
        assert original_unique != multiple, label
    counts["multiple original" if multiple else "unique original"] += 1

    isolated = isolate_market(goods, buyers, first_offers=first_offers)
    assert isolated.goods == goods, label
    assert set(isolated.buyers) == set(buyers) and isolated.delta > 0, label
    for i, (mass, offers) in buyers.items():
        new_mass, new_offers = isolated.buyers[i]
        assert new_mass == mass + isolated.delta and set(offers) == set(new_offers), label
        for j, (a, b) in offers.items():
            assert new_offers[j][1] == b and new_offers[j][0] > a, label
    for exponent, (i, j) in enumerate(first_offers, 1):
        assert isolated.buyers[i][1][j][0] - buyers[i][1][j][0] == isolated.delta ** exponent

    solver, variables, perturbed = solve(isolated.goods, isolated.buyers, "isolated")
    assert not has_another(solver, variables, perturbed), label + " has a second isolated-market point"
    validate_forest(isolated.goods, isolated.buyers, perturbed)
    repaired = decode_equilibrium(goods, buyers, *perturbed)
    test_pattern(goods, buyers, perturbed, repaired, label)
    return isolated, repaired


def case_witness(goods, buyers, price_constraints=(), equal_flows=(), status=z3.sat):
    solver = z3.SolverFor("QF_LRA")
    prices, flows, _ = market(solver, "witness", goods, buyers)
    for j, value in price_constraints:
        solver.add(prices[j] == q(value))
    for edge, value in equal_flows:
        solver.add(flows[edge] == q(value))
    check(solver, status, "prescribed original-market witness")


def targeted(counts):
    # Intercepts alone cannot select a price in a balanced singleton.
    good = {"A": 1}
    balanced = {"one": (1, {"A": (2, F(2, 3))})}
    isolated, _ = check_case("balanced rational singleton", good, balanced, counts, False)
    intercept_only = {"one": (1, isolated.buyers["one"][1])}
    solver, variables, point = solve(good, intercept_only, "intercept_only")
    assert has_another(solver, (variables[0],), (point[0],))

    # Masses alone do not remove a tight transportation cycle, even though
    # its price is already uniquely zero and every buyer spends fully.
    roomy = {"A": 3, "B": 3}
    same = {i: (1, {"A": (1, 1), "B": (1, 1)}) for i in ("one", "two")}
    isolated, _ = check_case("mass changes cannot break edge ties", roomy, same, counts,
                             False, (("two", "B"), ("one", "A")))
    mass_only = {i: (isolated.buyers[i][0], offers) for i, (_, offers) in same.items()}
    solver, variables, point = solve(roomy, mass_only, "mass_only")
    assert not has_another(solver, (variables[0],), (point[0],))
    assert has_another(solver, (variables[1],), (point[1],))

    # A tight cycle with unequal products of slopes is consistent at (1,1).
    goods = {"A": 1, "B": 1}
    skew = {"one": (1, {"A": (2, 1), "B": (3, 2)}),
            "two": (1, {"A": (4, 3), "B": (2, 1)})}
    all_half = tuple((edge, F(1, 2)) for edge in product(skew, goods))
    case_witness(goods, skew, (("A", 1), ("B", 1)), all_half)
    check_case("positive unbalanced-slope cycle", goods, skew, counts, False)

    # The only original market price and utility are zero, but the buyer
    # may leave any fraction outside and the seller need not fill.
    at_zero = {"one": (F(1, 3), {"A": (0, F(2, 5))})}
    for allocation in (0, F(1, 6), F(1, 3)):
        case_witness(good, at_zero, (("A", 0),), ((("one", "A"), allocation),))
    check_case("zero reservation boundaries", good, at_zero, counts, False)

    # Both endpoint prices clear, but their straight midpoint forces a and b
    # onto good A and cannot clear.
    offers = {"a": (1, {"A": (2, 1), "B": (3, 6)}),
              "b": (1, {"A": (3, 4), "B": (2, 1)})}
    for value in (F(1, 8), F(3, 8)):
        case_witness(goods, offers, (("A", value), ("B", value)))
    case_witness(goods, offers, (("A", F(1, 4)), ("B", F(1, 4))), status=z3.unsat)
    check_case("nonconvex price set", goods, offers, counts, False)

    sparse = {"a": (F(2, 5), {"A": (F(-4, 3), F(3, 7))}),
              "b": (F(5, 7), {"B": (F(7, 8), F(9, 11))}),
              "c": (F(7, 11), {"A": (F(-1, 9), F(5, 13)), "B": (F(-4, 5), 2)})}
    check_case("sparse, no-trade buyer and isolated good", {"A": F(2, 3), "B": 1, "C": 4},
               sparse, counts, True)
    check_case("empty option list and no listed trades", {"A": 1}, {"one": (1, {})},
               counts, True)
    check_case("empty market", {}, {}, counts, True)


def generated(counts):
    # Enumerate all binary intercept tables on the same balanced K₂,₂.
    for table in product((0, 1), repeat=4):
        offers = {i: (1, {j: (table[2 * i + j], 1) for j in range(2)}) for i in range(2)}
        check_case("two by two " + str(table), {0: 1, 1: 1}, offers, counts)

    rng = Random(12034917)
    for trial in range(12):
        n = 2 + trial % 2
        goods = {j: F(rng.randint(1, 5), rng.randint(1, 4)) for j in range(n)}
        buyers = {}
        for i in range(n):
            row = {}
            for j in range(n):
                if i == j or rng.randrange(4) != 0:
                    row[j] = (F(rng.randint(-2, 7), rng.randint(1, 4)),
                              F(rng.randint(1, 5), rng.randint(1, 5)))
            buyers[i] = (F(rng.randint(1, 5), rng.randint(1, 5)), row)
        check_case("seeded sparse rational " + str(trial), goods, buyers, counts)


if __name__ == "__main__":
    counts = Counter()
    targeted(counts)
    generated(counts)
    print(f"{sum(counts.values())} markets: {counts['unique original']} uniquely solved before isolation, "
          f"{counts['multiple original']} originally nonunique.")
    print("Every perturbed market had exactly one real full equilibrium and one anchor per tight tree. "
          "Every decoded point satisfied its original support LP, and every point of that LP was an "
          "original equilibrium.")
    print("Intercept-only price ambiguity and mass-only allocation ambiguity both reproduced.")
