"""Check the supplied-support hardness construction directly against rational BNE equations.

Run ``python3 -B round2/check_security_flat_support_hardness.py`` with z3-solver.
"""

from dataclasses import dataclass
from fractions import Fraction as Q
from itertools import combinations, product

import z3


@dataclass
class Game:
    n: int
    sets: tuple
    copies: int
    anchor: int
    resources: int
    theta: Q
    total_weight: Q
    priors: tuple
    payoffs: tuple
    support: set


def encode(n, sets, k):
    sets = tuple(tuple(sorted(s)) for s in sets)
    assert n > 0 and sets and all(s for s in sets) and 0 <= k <= n
    assert all(0 <= j < n for s in sets for j in s)
    copies = max(2, len(sets))
    anchor = n * copies
    theta = Q(1, 8) if all(len(s) == 2 for s in sets) else Q(1, 4 * (n + 1))
    weights, payoff_rows, support = [], [], set()

    def add(weight, overrides, edges):
        buyer = len(weights)
        weights.append(weight)
        payoff_rows.append(tuple(overrides.get(j, (-1, 1)) for j in range(anchor + 1)))
        support.update((buyer, j) for j in edges)

    occurrences = set()
    for i, s in enumerate(sets):
        allowed = [j * copies + i for j in s]
        occurrences.update(allowed)
        offers = {j: (1, 0) for j in allowed}
        offers[anchor] = (2, 1)
        add(1, offers, allowed)
    for j, pos in product(range(n), range(copies)):
        v = j * copies + pos
        following = j * copies + (pos + 1) % copies
        add(theta / 4 if v in occurrences else theta, {v: (1, 1), following: (1, 1)}, (v,))
    add(theta, {anchor: (1, 1)}, (anchor,))
    total = sum(weights)
    game = Game(
        n,
        sets,
        copies,
        anchor,
        k * copies + 1,
        theta,
        total,
        tuple(w / total for w in weights),
        tuple(payoff_rows),
        support,
    )
    assert all(p > 0 for p in game.priors) and sum(game.priors) == 1
    assert {a for row in game.payoffs for a, _ in row} <= {-1, 1, 2}
    assert {b for row in game.payoffs for _, b in row} <= {0, 1}
    return game


def forest_shape(game):
    vertices = len(game.priors) + game.anchor + 1
    adjacency = [set() for _ in range(vertices)]
    shift = len(game.priors)
    for i, j in game.support:
        adjacency[i].add(shift + j)
        adjacency[shift + j].add(i)
    seen = set()
    shapes = []
    for v in range(vertices):
        if v in seen:
            continue
        seen.add(v)
        pending = [v]
        degrees = []
        while pending:
            a = pending.pop()
            degrees.append(len(adjacency[a]))
            for b in adjacency[a]:
                if b not in seen:
                    seen.add(b)
                    pending.append(b)
        assert sum(degrees) == 2 * (len(degrees) - 1)
        shapes.append(tuple(sorted(degrees)))
    if all(len(s) == 2 for s in game.sets):
        assert {p * game.total_weight for p in game.priors} <= {1, Q(1, 8), Q(1, 32)}
        assert set(shapes) <= {(1, 1), (1, 1, 2, 2, 2)}
        assert all(sum(b == 0 for _, b in row) <= 2 for row in game.payoffs)


def bne_solver(game, mode):
    x = [z3.Real(f'x{j}') for j in range(game.anchor + 1)]
    u = [z3.Real(f'u{i}') for i in range(len(game.priors))]
    lam = z3.Real('lambda')
    edges = sorted(game.support)
    f = {edge: z3.Real(f'flow_{edge[0]}_{edge[1]}') for edge in edges}
    solver = z3.SolverFor('QF_LRA')
    solver.add(sum(x) == game.resources, lam >= 0, lam <= 1)
    for value in x:
        solver.add(value >= 0, value <= 1)
    for i, row in enumerate(game.payoffs):
        solver.add(sum(value for (r, _), value in f.items() if r == i) == game.priors[i])
        for j, (a, b) in enumerate(row):
            val = a - b * x[j]
            solver.add(u[i] >= val)
            if (i, j) in f:
                amount = f[i, j]
                solver.add(amount >= 0, z3.Implies(amount > 0, u[i] == val))
                if mode in ('tight', 'exact'):
                    solver.add(u[i] == val)
                if mode == 'exact':
                    solver.add(amount > 0)
    for j, price in enumerate(x):
        score = sum(value for (_, v), value in f.items() if v == j)
        solver.add(z3.Implies(price > 0, score >= lam), z3.Implies(price < 1, score <= lam))
    status = solver.check()
    assert status in (z3.sat, z3.unsat)
    return status == z3.sat


def verify_witness(game, hitting):
    x = tuple(int(j // game.copies in hitting) for j in range(game.anchor)) + (1,)
    assert sum(x) == game.resources
    flow = {}
    for i, s in enumerate(game.sets):
        selected = [j * game.copies + i for j in s if j in hitting]
        assert selected
        for j in s:
            v = j * game.copies + i
            flow[i, v] = 2 * game.theta if j in hitting else game.theta / 4
        allocated = sum(flow[i, j * game.copies + i] for j in s)
        assert allocated < 1
        flow[i, selected[0]] += 1 - allocated
    for i in range(len(game.sets), len(game.priors)):
        (j,) = (v for r, v in game.support if r == i)
        flow[i, j] = game.priors[i] * game.total_weight
    flow = {edge: w / game.total_weight for edge, w in flow.items()}
    assert set(flow) == game.support and min(flow.values()) > 0
    verify_equilibrium(game, x, flow, game.theta / game.total_weight)


def verify_equilibrium(game, x, flow, lam):
    assert len(x) == game.anchor + 1 and sum(x) == game.resources
    assert all(0 <= v <= 1 for v in x) and 0 <= lam <= 1
    assert all(w >= 0 for w in flow.values())
    for i, row in enumerate(game.payoffs):
        payoffs = tuple(a - b * x[j] for j, (a, b) in enumerate(row))
        assert sum(v for (r, _), v in flow.items() if r == i) == game.priors[i]
        assert all(payoffs[j] == max(payoffs) for (r, j), f in flow.items() if r == i and f > 0)
    for j, coverage in enumerate(x):
        load = sum(v for (_, t), v in flow.items() if t == j)
        assert (coverage == 0 or load >= lam) and (coverage == 1 or load <= lam)


def escape_witness(game):
    """Solve only the clone LP and its dual, then test the assembled equilibrium."""
    n = game.anchor
    budget = game.resources - 1
    x = [z3.Real(f'escape_x_{j}') for j in range(n)]
    gamma = z3.Real('escape_gamma')
    sigma = [z3.Real(f'escape_sigma_{j}') for j in range(n)]
    loads = [[] for _ in range(n)]
    flows, objective_terms = {}, []
    solver = z3.SolverFor('QF_LRA')
    solver.add(sum(x) == budget, gamma >= 0, gamma <= 2 * game.theta)
    for value, price in zip(x, sigma):
        solver.add(value >= 0, value <= 1, price >= 0)
    for j in range(n):
        i = len(game.sets) + j
        start = j - (j % game.copies)
        successor = start + (j - start + 1) % game.copies
        v = z3.Real(f'escape_v_{i}')
        row = []
        for t in (j, successor):
            g = z3.Real(f'escape_flow_{i}_{t}')
            flows[i, t] = g
            row.append(g)
            loads[t].append(g)
            solver.add(v <= x[t], g >= 0)
        m = game.priors[i] * game.total_weight
        objective_terms.append(m * v)
        solver.add(sum(row) == m)
    for j in range(n):
        solver.add(gamma + sigma[j] >= sum(loads[j]))
    solver.add(sum(objective_terms) == budget * gamma + sum(sigma))
    assert solver.check() == z3.sat
    model = solver.model()

    def rational(v):
        value = model.eval(v, model_completion=True)
        return Q(value.numerator_as_long(), value.denominator_as_long())

    joint = {edge: rational(v) / game.total_weight for edge, v in flows.items()}
    for i in (*range(len(game.sets)), len(game.priors) - 1):
        joint[i, game.anchor] = game.priors[i]
    coverage = tuple(rational(v) for v in x) + (1,)
    cutoff = rational(gamma) / game.total_weight
    verify_equilibrium(game, coverage, joint, cutoff)
    assert all((i, game.anchor) not in game.support for i in range(len(game.sets)))


def budgets(n, sets):
    for k in range(n + 1):
        yield n, sets, k


def cases():
    # Every nonempty simple graph on three labeled vertices and every budget.
    edges = tuple(combinations(range(3), 2))
    for count in range(1, len(edges) + 1):
        for subset in combinations(edges, count):
            yield from budgets(3, subset)
    # Every nonempty family of nonempty subsets on two labeled elements.
    subsets = ((0,), (1,), (0, 1))
    for count in range(1, len(subsets) + 1):
        for family in combinations(subsets, count):
            yield from budgets(2, family)
    # Repetitions, singleton supports, and a four-set family.
    yield from budgets(1, ((0,), (0,)))
    yield from budgets(4, ((0, 1), (1, 2), (2, 3), (3, 0)))
    yield from budgets(3, ((0, 1, 2), (0,), (0, 1, 2)))


def main():
    total = yes = witnesses = 0
    for n, sets, k in cases():
        game = encode(n, sets, k)
        forest_shape(game)
        hits = [h for h in combinations(range(n), k) if all(set(h).intersection(s) for s in sets)]
        answers = [bne_solver(game, mode) for mode in ('allowed', 'tight', 'exact')]
        assert answers == [bool(hits)] * 3, (n, sets, k, answers)
        escape_witness(game)
        for h in hits:
            verify_witness(game, set(h))
        witnesses += len(hits)
        total += 1
        yes += bool(hits)
        if sets == ((0, 1), (0, 2), (1, 2)):
            assert bool(hits) == (k >= 2)
    print(
        f'{total} games ({yes} yes, {total - yes} no), {3 * total} exact real feasibility checks, '
        f'{witnesses} explicit supported rational equilibria, '
        f'{total} unrestricted equilibria returned by the clone LP. All checks passed.'
    )


if __name__ == '__main__':
    if not __debug__:
        raise RuntimeError('Run with Python assertions enabled.')
    main()
