"""Compare the support-edge reconstruction and the literal M1 conditions.

Run ``python3 -B round2/check_m1_support_reconstruction.py`` with z3-solver.
"""

from dataclasses import dataclass
from fractions import Fraction
from itertools import combinations, product
from random import Random

import z3


@dataclass
class Market:
    masses: tuple
    capacities: tuple
    offers: dict


def rational(value):
    if hasattr(value, 'numerator_as_long'):
        return Fraction(value.numerator_as_long(), value.denominator_as_long())
    return Fraction(value)


def read(model, variables):
    return tuple(rational(model.eval(x, model_completion=True)) for x in variables)


def components(market, support):
    n, m = len(market.masses), len(market.capacities)
    neighbors = {k: [] for k in range(n + m)}
    for i, j in support:
        neighbors[i].append(n + j)
        neighbors[n + j].append(i)
    visited = set()
    for start in neighbors:
        if start in visited:
            continue
        pending = [start]
        visited.add(start)
        buyers, sellers = [], []
        while pending:
            node = pending.pop()
            if node < n:
                buyers.append(node)
            else:
                sellers.append(node - n)
            for dest in neighbors[node]:
                if dest not in visited:
                    pending.append(dest)
                    visited.add(dest)
        yield tuple(buyers), tuple(sellers)


def lp_endpoint(rows, objective, maximize):
    solver = z3.Optimize()
    solver.add(*rows)
    if maximize:
        solver.maximize(objective)
    else:
        solver.minimize(objective)
    result = solver.check()
    if result == z3.unsat:
        return None
    assert result == z3.sat
    return rational(solver.model().eval(objective, model_completion=True))


def reconstruction(market, support, maximize=False, require_exact=False):
    n, m = len(market.masses), len(market.capacities)
    u = [z3.Real(f'u_{i}') for i in range(n)]
    p = [z3.Real(f'p_{j}') for j in range(m)]
    payoffs = [x >= 0 for x in u + p]
    for (i, j), (a, b) in market.offers.items():
        payoffs.append(u[i] + b * p[j] >= a)
        if (i, j) in support:
            payoffs.append(u[i] + b * p[j] == a)
    full_buyers, full_sellers = set(), set()
    for buyers, sellers in components(market, support):
        if not buyers:
            payoffs.append(p[sellers[0]] == 0)
            continue
        if not sellers:
            payoffs.append(u[buyers[0]] == 0)
            continue
        local = [u[i] >= 0 for i in buyers] + [p[j] >= 0 for j in sellers]
        for i, j in support:
            if i in buyers:
                a, b = market.offers[i, j]
                local.append(u[i] + b * p[j] == a)
        reference = u[buyers[0]]
        low = lp_endpoint(local, reference, False)
        if low is None:
            return None
        high = lp_endpoint(local, reference, True)
        assert high is not None and high >= low
        difference = sum(market.masses[i] for i in buyers) - sum(
            market.capacities[j] for j in sellers
        )
        if difference > 0 or high == low:
            payoffs.append(reference == low)
        elif difference < 0:
            payoffs.append(reference == high)
        else:
            full_buyers.update(buyers)
            full_sellers.update(sellers)

    solver = z3.Optimize()
    solver.add(*payoffs)
    if maximize:
        solver.maximize(sum(u))
    else:
        solver.minimize(sum(u))
    result = solver.check()
    if result == z3.unsat:
        return None
    assert result == z3.sat
    model = solver.model()
    utilities, prices = read(model, u), read(model, p)

    flows = {edge: z3.Real(f'f_{edge[0]}_{edge[1]}') for edge in support}
    transport = z3.SolverFor('QF_LRA')
    transport.add(*(f > 0 if require_exact else f >= 0 for f in flows.values()))
    for i, mass in enumerate(market.masses):
        load = sum((f for (a, _), f in flows.items() if a == i), z3.RealVal(0))
        transport.add(load <= mass)
        if i in full_buyers or utilities[i] > 0:
            transport.add(load == mass)
    for j, capacity in enumerate(market.capacities):
        load = sum((f for (_, b), f in flows.items() if b == j), z3.RealVal(0))
        transport.add(load <= capacity)
        if j in full_sellers or prices[j] > 0:
            transport.add(load == capacity)
    result = transport.check()
    if result == z3.unsat:
        return None
    assert result == z3.sat
    model = transport.model()
    allocation = {e: read(model, (var,))[0] for e, var in flows.items()}
    return utilities, prices, allocation


def literal_feasibility(market, support, require_exact=False):
    """Direct feasibility without identifying components, extrema, or required fill vertices."""
    u = [z3.Real(f'original_u_{i}') for i in range(len(market.masses))]
    p = [z3.Real(f'original_p_{j}') for j in range(len(market.capacities))]
    f = {edge: z3.Real(f'original_f_{edge[0]}_{edge[1]}') for edge in market.offers}
    solver = z3.SolverFor('QF_LRA')
    solver.add(*(x >= 0 for x in u + p + list(f.values())))
    for (i, j), (a, b) in market.offers.items():
        gap = u[i] + b * p[j] - a
        solver.add(gap >= 0, z3.Implies(f[i, j] > 0, gap == 0))
        if (i, j) in support:
            solver.add(gap == 0)
            if require_exact:
                solver.add(f[i, j] > 0)
        else:
            solver.add(f[i, j] == 0)
    for i, mass in enumerate(market.masses):
        amount = sum(value for (buyer, _), value in f.items() if i == buyer)
        solver.add(amount <= mass, z3.Implies(u[i] > 0, amount == mass))
    for j, cap in enumerate(market.capacities):
        amount = sum(value for (_, good), value in f.items() if j == good)
        solver.add(amount <= cap, z3.Implies(p[j] > 0, amount == cap))
    result = solver.check()
    assert result in (z3.sat, z3.unsat)
    return result == z3.sat


def verify(market, support, solution):
    u, p, f = solution
    assert min(u + p) >= 0
    assert set(f) <= support
    for (i, j), (a, b) in market.offers.items():
        amount = f.get((i, j), 0)
        gap = u[i] + b * p[j] - a
        assert amount >= 0 and gap >= 0
        assert ((i, j) not in support and amount == 0) or gap == 0
    for i, mass in enumerate(market.masses):
        amount = sum(x for (buyer, _), x in f.items() if i == buyer)
        assert amount <= mass and (u[i] == 0 or amount == mass)
    for j, cap in enumerate(market.capacities):
        amount = sum(x for (_, good), x in f.items() if j == good)
        assert amount <= cap and (p[j] == 0 or amount == cap)
    # Either entire payoff vector determines the other, also at isolated vertices.
    for i in range(len(u)):
        assert u[i] == max(
            [0] + [a - b * p[j] for (r, j), (a, b) in market.offers.items() if i == r]
        )
    for j in range(len(p)):
        assert p[j] == max(
            [0] + [(a - u[i]) / b for (i, k), (a, b) in market.offers.items() if j == k]
        )


def cases():
    def complete(a, b):
        return {(i, j): (a[i][j], b[i][j]) for i, j in product(range(2), repeat=2)}

    return [
        Market((1, 1), (2,), {}),
        Market((1, 1), (2, 1), {(0, 1): (-1, 2)}),
        Market((2,), (1,), {(0, 0): (2, 3)}),
        Market((1,), (2,), {(0, 0): (2, 3)}),
        Market((1,), (1,), {(0, 0): (3, 2)}),
        # A rigid balanced component admits zero flow or full flow.
        Market((1,), (1,), {(0, 0): (0, 1)}),
        # Rigid cycle at utilities (2,3), prices (1,2).
        Market((1, 1), (1, 1), complete(((3, 4), (4, 7)), ((1, 1), (1, 2)))),
        # Factorable cycle with an interval and optional unused ties.
        Market((1, 1), (1, 1), complete(((2, 2), (2, 2)), ((1, 1), (1, 1)))),
        # Two balanced singleton-edge components constrained by cross edges.
        Market((1, 1), (1, 1), complete(((3, 4), (1, 3)), ((1, 1), (1, 1)))),
        # Positive flow of mass one has slack on both sides at nonisolated zero-payoff vertices.
        Market((2, 1), (1, 2), {(0, 0): (1, 1), (1, 0): (2, 1), (1, 1): (1, 1)}),
        # Connecting unused tie between two previously separate components.
        Market((2, 1), (1, 2), {(0, 0): (1, 1), (1, 1): (1, 1), (0, 1): (0, 2)}),
    ]


def main():
    markets = cases()
    rng = Random(731)
    for _ in range(12):
        edges = {
            (i, j): (Fraction(rng.randrange(-2, 7), rng.choice((1, 2))), rng.randrange(1, 4))
            for i, j in product(range(2), repeat=2)
            if rng.random() < 0.8
        }
        markets.append(
            Market(
                tuple(rng.randrange(1, 4) for _ in range(2)),
                tuple(rng.randrange(1, 4) for _ in range(2)),
                edges,
            )
        )

    total = feasible = exact_support = price_variation = 0
    canceled = 0
    for market in markets:
        edges = list(market.offers)
        found_forest = False
        for size in range(len(edges) + 1):
            for subset in combinations(edges, size):
                support = set(subset)
                expected = literal_feasibility(market, support)
                a = reconstruction(market, support)
                b = reconstruction(market, support, maximize=True)
                assert (a is not None) == expected == (b is not None)
                exact = reconstruction(market, support, require_exact=True)
                assert (exact is not None) == literal_feasibility(
                    market, support, require_exact=True
                )
                if exact is not None:
                    verify(market, support, exact)
                    assert {e for e, value in exact[2].items() if value > 0} == support
                    exact_support += 1
                    # Our fixtures are at most 2 x 2. A positive four-edge support
                    # has exactly the square cycle; every proper subset is a forest.
                    if len(support) == 4:
                        u, p, allocation = exact
                        amount = min(allocation[0, 0], allocation[1, 1])
                        allocation = {
                            (i, j): v + (-amount if i == j else amount)
                            for (i, j), v in allocation.items()
                        }
                        forest = {edge for edge, v in allocation.items() if v > 0}
                        reduced = (u, p, {edge: allocation[edge] for edge in forest})
                        assert len(forest) < 4
                        verify(market, forest, reduced)
                        assert reconstruction(market, forest, require_exact=True) is not None
                        canceled += 1
                    found_forest = True
                if a is not None:
                    verify(market, support, a)
                    verify(market, support, b)
                    verify(market, support, (a[0], a[1], b[2]))
                    verify(market, support, (b[0], b[1], a[2]))
                    feasible += 1
                    price_variation += a[1] != b[1]
                total += 1
        assert found_forest
    assert 0 < exact_support < feasible < total and price_variation > 0
    assert canceled > 0
    print(
        f'{len(markets)} markets, {total} supplied edge sets, {feasible} feasible, '
        f'{exact_support} realizable as exact positive supports, '
        f'{price_variation} with two distinct returned price vectors, '
        f'{canceled} positive cycles sparsified to forests. All exact checks passed.'
    )


if __name__ == '__main__':
    if not __debug__:
        raise RuntimeError('Run with Python assertions enabled.')
    main()
