"""Check support-constrained and unrestricted equilibria in the one-flat Vertex Cover games.

Run ``python3 -B round2/check_security_one_flat_support.py`` with z3-solver.
"""

from dataclasses import dataclass
from fractions import Fraction as Q
from itertools import combinations, product

import z3


@dataclass
class Game:
    vertices: int
    pairs: tuple
    k: int
    anchor: int
    hubs: tuple
    resources: int
    theta: Q
    raw_masses: tuple
    payoffs: tuple
    support: set

    @property
    def weight(self):
        return sum(self.raw_masses)

    @property
    def copies(self):
        return len(self.pairs)

    def occurrence(self, j, pos):
        return j * self.copies + pos

    def successor(self, clone):
        j, pos = divmod(clone, self.copies)
        return self.occurrence(j, (pos + 1) % self.copies)

    def private_type(self, clone):
        return 2 * len(self.pairs) + clone


def encode(n, edges, k):
    assert n >= 2 and edges and 0 <= k <= n
    assert all(0 <= a < b < n for a, b in edges)
    pairs = tuple(edges) * 2
    m = len(pairs)
    theta = Q(1, 8)
    anchor = n * m
    hubs = tuple(range(anchor + 1, anchor + 1 + m))
    num_goods = anchor + 1 + m
    weights, rows, support = [], [], set()

    def add(weight, offers, allowed):
        i = len(rows)
        weights.append(weight)
        rows.append(tuple(offers.get(j, (-1, 1)) for j in range(num_goods)))
        support.update((i, j) for j in allowed)

    active = set()
    for s, pair in enumerate(pairs):
        for j in pair:
            occurrence, h = j * m + s, hubs[s]
            active.add(occurrence)
            add(
                3 * theta / 2,
                {occurrence: (1, 0), h: (Q(3, 2), 1), anchor: (2, 1)},
                (occurrence, h),
            )
    for j, s in product(range(n), range(m)):
        v = j * m + s
        nxt = j * m + (s + 1) % m
        add(theta / 4 if v in active else theta, {v: (1, 1), nxt: (1, 1)}, (v,))
    add(theta, {anchor: (1, 1)}, (anchor,))
    return Game(
        n, pairs, k, anchor, hubs, k * m + m // 2 + 1, theta, tuple(weights), tuple(rows), support
    )


def check_structure(game):
    assert game.copies >= 2 and game.copies % 2 == 0
    assert all(sum(slope == 0 for _, slope in row) <= 1 for row in game.payoffs)
    assert {a for row in game.payoffs for a, _ in row} <= {-1, 1, Q(3, 2), 2}
    assert {b for row in game.payoffs for _, b in row} == {0, 1}
    assert set(game.raw_masses) <= {Q(1, 32), Q(1, 8), Q(3, 16)}
    num_types, num_goods = len(game.raw_masses), len(game.payoffs[0])
    graph = [set() for _ in range(num_types + num_goods)]
    for i, j in game.support:
        graph[i].add(num_types + j)
        graph[num_types + j].add(i)
    seen = set()
    paths = singles = 0
    for start in range(len(graph)):
        if start in seen:
            continue
        stack = [start]
        seen.add(start)
        degrees = []
        while stack:
            x = stack.pop()
            degrees.append(len(graph[x]))
            for y in graph[x] - seen:
                stack.append(y)
                seen.add(y)
        if sorted(degrees) == [1, 1]:
            singles += 1
        else:
            assert sorted(degrees) == [1, 1, 2, 2, 2, 2, 2]
            paths += 1
    assert paths == game.copies and singles == game.anchor - 2 * game.copies + 1


def verify_profile(game, x, flow, cutoff, exact_support=False):
    assert len(x) == len(game.payoffs[0])
    assert all(0 <= v <= 1 for v in x) and sum(x) == game.resources
    assert 0 <= cutoff <= 1 and all(v > 0 for v in flow.values())
    if exact_support:
        assert set(flow) == game.support
    for i, row in enumerate(game.payoffs):
        assert sum(v for (r, _), v in flow.items() if r == i) == game.raw_masses[i] / game.weight
        values = tuple(a - b * x[j] for j, (a, b) in enumerate(row))
        assert all(values[j] == max(values) for r, j in flow if r == i)
    for j, value in enumerate(x):
        load = sum(f for (_, dest), f in flow.items() if dest == j)
        assert value == 0 or load >= cutoff
        assert value == 1 or load <= cutoff


def literal_test(game, mode, prescribed):
    n = len(game.payoffs[0])
    x = [z3.Real(f'x_{j}') for j in range(n)]
    u = [z3.Real(f'u_{i}') for i in range(len(game.payoffs))]
    f = {e: z3.Real(f'f_{e[0]}_{e[1]}') for e in game.support}
    cutoff = z3.Real('cutoff')
    solver = z3.SolverFor('QF_LRA')
    solver.add(sum(x) == game.resources, cutoff >= 0, cutoff <= 1)
    if prescribed:
        solver.add(cutoff == game.theta / game.weight)
    for val in x:
        solver.add(val >= 0, val <= 1)
    for i, row in enumerate(game.payoffs):
        solver.add(sum(v for (r, _), v in f.items() if r == i) == game.raw_masses[i] / game.weight)
        for j, (a, b) in enumerate(row):
            val = a - b * x[j]
            solver.add(u[i] >= val)
            if (i, j) in f:
                solver.add(f[i, j] >= 0, z3.Implies(f[i, j] > 0, u[i] == val))
                if mode != 'allowed':
                    solver.add(u[i] == val)
                if mode == 'exact':
                    solver.add(f[i, j] > 0)
    for j in range(n):
        load = sum(v for (_, t), v in f.items() if t == j)
        solver.add(z3.Implies(x[j] > 0, load >= cutoff), z3.Implies(x[j] < 1, load <= cutoff))
    result = solver.check()
    assert result in (z3.sat, z3.unsat)
    return result == z3.sat


def supported_witness(game, cover):
    theta = game.theta
    x = [Q(int(v // game.copies in cover)) for v in range(game.anchor)]
    x += [Q(1)] + [Q(1, 2)] * game.copies
    raw = {}
    for s, pair in enumerate(game.pairs):
        both = all(j in cover for j in pair)
        assert both or any(j in cover for j in pair)
        for t, j in enumerate(pair):
            amount = theta if both else (4 * theta / 3 if j in cover else 2 * theta / 3)
            i = 2 * s + t
            raw[i, game.occurrence(j, s)] = amount
            raw[i, game.hubs[s]] = game.raw_masses[i] - amount
    for v in range(game.anchor):
        raw[game.private_type(v), v] = game.raw_masses[game.private_type(v)]
    raw[len(game.raw_masses) - 1, game.anchor] = theta
    flow = {e: f / game.weight for e, f in raw.items()}
    verify_profile(game, x, flow, theta / game.weight, exact_support=True)


def fraction(model, expr):
    value = model.eval(expr, model_completion=True)
    return Q(value.numerator_as_long(), value.denominator_as_long())


def unrestricted_witness(game):
    """One polynomial-size LP for primal and dual optima of the clone-only zero-sum game."""
    m = game.anchor
    B = game.k * game.copies
    cp = [z3.Real(f'c_{t}') for t in range(m)]
    y = [z3.Real(f'y_{t}') for t in range(m)]
    alpha = [z3.Real(f'a_{t}') for t in range(m)]
    beta = [z3.Real(f'b_{t}') for t in range(m)]
    slack = [z3.Real(f's_{t}') for t in range(m)]
    cutoff = z3.Real('private_cutoff')
    solver = z3.SolverFor('QF_LRA')
    solver.add(sum(cp) == B, cutoff >= 0, cutoff <= 2 * game.theta)
    for t in range(m):
        following = game.successor(t)
        before = game.occurrence(t // game.copies, (t % game.copies - 1) % game.copies)
        q = game.raw_masses[game.private_type(t)]
        solver.add(cp[t] >= 0, cp[t] <= 1, y[t] <= cp[t], y[t] <= cp[following])
        solver.add(alpha[t] >= 0, beta[t] >= 0, alpha[t] + beta[t] == q)
        solver.add(slack[t] >= 0, slack[t] >= alpha[t] + beta[before] - cutoff)
    primal = sum(game.raw_masses[game.private_type(t)] * y[t] for t in range(m))
    solver.add(primal == sum(slack) + B * cutoff)
    assert solver.check() == z3.sat
    model = solver.model()
    lam = fraction(model, cutoff)
    raw = {}
    for t in range(m):
        i = game.private_type(t)
        raw[i, t] = fraction(model, alpha[t])
        raw[i, game.successor(t)] = fraction(model, beta[t])
    for s in range(game.copies):
        for i in (2 * s, 2 * s + 1):
            raw[i, game.hubs[s]] = lam / 2
            raw[i, game.anchor] = game.raw_masses[i] - lam / 2
    raw[len(game.raw_masses) - 1, game.anchor] = game.theta
    x = [fraction(model, c) for c in cp] + [Q(1)] + [Q(1, 2)] * game.copies
    flow = {e: f / game.weight for e, f in raw.items() if f > 0}
    verify_profile(game, x, flow, lam / game.weight)
    assert any(e not in game.support for e in flow)


def main():
    k3 = tuple(combinations(range(3), 2))
    graphs = [(3, edges) for count in range(1, 4) for edges in combinations(k3, count)]
    graphs.append((4, ((0, 1), (1, 2), (2, 3), (0, 3))))
    games = checks = yes = supported = 0
    for n, edges in graphs:
        for k in range(n + 1):
            game = encode(n, edges, k)
            check_structure(game)
            covers = [
                set(h)
                for h in combinations(range(n), k)
                if all(set(h).intersection(e) for e in edges)
            ]
            for mode, prescribed in product(('allowed', 'tight', 'exact'), (False, True)):
                assert literal_test(game, mode, prescribed) == bool(covers)
                checks += 1
            for cover in covers:
                supported_witness(game, cover)
            unrestricted_witness(game)
            games += 1
            yes += bool(covers)
            supported += len(covers)
            if edges == k3:
                assert bool(covers) == (k >= 2)
    print(
        f'{games} games ({yes} yes, {games-yes} no), {checks} exact support/cutoff queries, '
        f'{supported} exact-support profiles and {games} unrestricted BNE verified.'
    )


if __name__ == '__main__':
    if not __debug__:
        raise RuntimeError('Run with Python assertions enabled.')
    main()
