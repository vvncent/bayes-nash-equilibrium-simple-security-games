"""Check eligible graphs, scalable components, elimination distances and sample equilibria.

Run with Python and z3-solver. The feasibility systems in eligible_graph use
every original offer and the exact original coverage budget.
"""

from collections import Counter
from fractions import Fraction as F
from functools import lru_cache
from itertools import combinations

import z3

from check_security_support_reconstruction import make_game


def rat(value):
    return z3.RealVal(str(value))


def example(copies, hub):
    n = 3 * copies + int(hub)
    m = 2 * copies
    intercepts = [[-2] * n for _ in range(m)]
    slopes = [[1] * n for _ in range(m)]
    expected = set()
    for block in range(copies):
        first, second = 2 * block, 2 * block + 1
        p, s, t = 3 * block, 3 * block + 1, 3 * block + 2
        for i in (first, second):
            for j in (p, s, t):
                intercepts[i][j] = 1
                expected.add((i, j))
        intercepts[second][t] = F(17, 16)
        slopes[second][s] = 2
        if hub:
            expected.add((first, n - 1))
            intercepts[first][n - 1] = 1
    game = make_game([F(1, m)] * m, [1] * n, intercepts, slopes, 1)
    return game, expected


def eligible_graph(game):
    n = len(game.gains)
    x = [z3.Real(f"coverage_{j}") for j in range(n)]
    solver = z3.SolverFor("QF_LRA")
    solver.add(z3.Sum(x) == game.resources, *[z3.And(v >= 0, v <= 1) for v in x])
    result = {}
    for i in range(len(game.masses)):
        utility = [rat(game.offers[i, j][0]) - rat(game.offers[i, j][1]) * x[j] for j in range(n)]
        for j in range(n):
            solver.push()
            solver.add(*[utility[j] >= other for other in utility])
            status = solver.check()
            assert status in (z3.sat, z3.unsat), status
            if status == z3.sat:
                result[i, j] = game.offers[i, j][1]
            solver.pop()
    return result


class LabelledGraph:
    """Row vertices are 0,...,m-1, and target vertices are m,...,m+n-1."""

    def __init__(self, m, n, slopes):
        self.vertices = frozenset(range(m + n))
        self.adjacency = {v: {} for v in self.vertices}
        for (i, j), slope in slopes.items():
            self.adjacency[i][m + j] = 1 / slope
            self.adjacency[m + j][i] = slope

    @lru_cache(maxsize=None)
    def components_and_scalability(self, remaining):
        unseen = set(remaining)
        result = []
        while unseen:
            start = min(unseen)
            unseen.remove(start)
            scale = {start: F(1)}
            stack = [start]
            consistent = True
            while stack:
                v = stack.pop()
                for u, ratio in self.adjacency[v].items():
                    if u not in remaining:
                        continue
                    expected = scale[v] * ratio
                    if u in scale:
                        consistent &= scale[u] == expected
                    else:
                        scale[u] = expected
                        unseen.remove(u)
                        stack.append(u)
            result.append((frozenset(scale), consistent))
        return tuple(result)

    @lru_cache(maxsize=None)
    def depth_at_most(self, remaining, depth):
        for component, scalable in self.components_and_scalability(remaining):
            if scalable:
                continue
            if depth == 0:
                return False
            if not any(self.depth_at_most(component - {v}, depth - 1) for v in component):
                return False
        return True

    def static_deletion(self):
        for size in range(len(self.vertices) + 1):
            for removed in combinations(sorted(self.vertices), size):
                if self.depth_at_most(self.vertices.difference(removed), 0):
                    return size
        raise AssertionError("Deleting all vertices must suffice")


def check_equilibrium(game, coverage, flows):
    assert sum(coverage) == game.resources and all(0 <= x <= 1 for x in coverage)
    for i, row in enumerate(flows):
        assert all(f >= 0 for f in row) and sum(row) == game.masses[i]
        payoffs = [game.offers[i, j][0] - game.offers[i, j][1] * coverage[j]
                   for j in range(len(coverage))]
        assert all(f == 0 or payoff == max(payoffs) for f, payoff in zip(row, payoffs))
    scores = [d * sum(row[j] for row in flows) for j, d in enumerate(game.gains)]
    best_value = sum(sorted(scores, reverse=True)[:game.resources])
    assert sum(x * value for x, value in zip(coverage, scores)) == best_value


def planar_hierarchy_control(repetitions):
    """Lift a separator hierarchy from a ten-vertex planar core to an unequal bipartite graph."""
    small = set(range(8))
    # Draw the small side on a line. The two three-neighbor stars lie above
    # disjoint intervals, and the repeated length-two paths can lie below.
    neighbors = [(0, 1, 2), (4, 5, 6)]
    for _ in range(repetitions):
        neighbors.extend((j, j + 1) for j in range(7))
        neighbors.extend(((0,), (6,), ()))
    larger = set(range(8, 8 + len(neighbors)))
    original = {v: set() for v in small | larger}
    for v, adjacent in enumerate(neighbors, 8):
        original[v].update(adjacent)
        for u in adjacent:
            original[u].add(v)

    core_vertices = small | {v for v in larger if len(original[v]) >= 3}
    core = {v: original[v] & core_vertices for v in core_vertices}
    removed = larger - core_vertices
    for v in removed:
        if len(original[v]) == 2:
            a, b = original[v]
            core[a].add(b)
            core[b].add(a)

    def components(vertices):
        remaining = set(vertices)
        parts = []
        while remaining:
            stack = [min(remaining)]
            part = set(stack)
            remaining.difference_update(stack)
            while stack:
                adjacent = core[stack.pop()] & remaining
                part.update(adjacent)
                remaining.difference_update(adjacent)
                stack.extend(adjacent)
            parts.append(part)
        return parts

    location = {}

    def decompose(vertices, path):
        # Enumerate small separators only for this fixed ten-vertex fixture.
        for k in range(1, len(vertices) + 1):
            for separator in combinations(sorted(vertices), k):
                children = components(vertices.difference(separator))
                if all(3 * len(part) <= 2 * len(vertices) for part in children):
                    location.update((v, path) for v in separator)
                    for part in children:
                        decompose(part, path + (min(part),))
                    return
        raise AssertionError("The whole vertex set is always a separator")

    def parameters():
        sizes = Counter(location.values())
        height = max(map(len, sizes))
        path_size = max(sum(sizes[path[:i]] for i in range(1, len(path) + 1)) for path in sizes)
        return height, path_size

    for part in components(core_vertices):
        decompose(part, (min(part),))
    core_height, core_size = parameters()
    for v in removed:
        neighbors = original[v]
        parent = max((location[u] for u in neighbors), key=len, default=())
        location[v] = parent + (v,)
    assert set(location) == set(original)
    for v in original:
        for u in original[v]:
            first, second = sorted((location[v], location[u]), key=len)
            assert first == second[:len(first)]
    height, path_size = parameters()
    assert height <= core_height + 1 and path_size <= core_size + 1
    return len(larger), height, path_size


def main():
    game, _ = example(1, False)
    check_equilibrium(game, (F(5, 16), F(5, 16), F(3, 8)),
                      ((F(1, 6), F(1, 3), F(0)), (F(1, 6), F(0), F(1, 3))))
    # Changing the middle slope of the second row makes all six edges scalable.
    base = eligible_graph(game)
    base[1, 1] = F(1)
    scalable_graph = LabelledGraph(2, 3, base)
    assert scalable_graph.depth_at_most(scalable_graph.vertices, 0)

    tests = 0
    for copies, hub in ((1, False), (2, True), (3, True), (4, True)):
        game, expected = example(copies, hub)
        slopes = eligible_graph(game)
        assert set(slopes) == expected
        tests += len(game.offers)
        graph = LabelledGraph(len(game.masses), len(game.gains), slopes)
        assert len(graph.components_and_scalability(graph.vertices)) == 1
        depth = 2 if hub else 1
        assert graph.depth_at_most(graph.vertices, depth)
        assert not graph.depth_at_most(graph.vertices, depth - 1)
        assert graph.static_deletion() == copies
        print(f"{copies} block(s), {len(slopes)} eligible edges, depth {depth}, deletion size {copies}")

    # At budget one, offers 1 and 2 cannot both receive 3/4 coverage.
    # Offer 0 becomes best at the off-budget (0,1,1).
    changed = make_game([1], [1, 1, 1], [[1, F(7, 4), F(7, 4)]], [[1, 1, 1]], 1)
    assert set(eligible_graph(changed)) == {(0, 1), (0, 2)}
    assert all(changed.offers[0, 0][0] > changed.offers[0, j][0] - changed.offers[0, j][1]
               for j in (1, 2))
    print(f"Verified {tests + len(changed.offers)} original pair-feasibility tests, "
          "the two-row equilibrium, an exactly scalable control and an off-budget control.")
    planar = [planar_hierarchy_control(r) for r in (1, 100)]
    assert planar[0][1:] == planar[1][1:]
    print(f"Planar 8-by-{planar[0][0]} and 8-by-{planar[1][0]} lifts both have "
          f"height {planar[0][1]} and maximum path sum {planar[0][2]}.")


if __name__ == "__main__":
    main()
