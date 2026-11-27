"""Arithmetic decoding of an unrooted tight-edge forest in a one-resource game.

equilibrium_from_forest(game, edges) takes a normalized rational Game and
zero-based (attacker type, target) pairs. It returns the certified Profile or
None. On outputs of unique_one_resource exactly one edge set is accepted, by
the perturbation's distinct ratios and generic tight equations. For other
positive games acceptance still certifies a BNE; rejection decides only the
supplied candidate. Finding the forest is a separate search problem.

The decoder uses exact rational arithmetic and makes no solver calls.
"""

from collections import deque
from dataclasses import dataclass
from fractions import Fraction as F
from operator import index

from security_equilibrium_uniqueness import Game, Profile


@dataclass
class _Tree:
    reference: int
    targets: tuple
    total_mass: F
    ratio: F
    lower: F
    upper: F
    order: list
    parent: dict


def _components(game, adjacency):
    m = len(game.priors)
    n = len(game.gains)
    # Target j is vertex j; type i is vertex n+i. In each component the
    # reference is a target, and affine[v] gives its payoff or its coverage.
    affine = {}
    trees = []
    for reference in range(n):
        if reference in affine:
            continue
        affine[reference] = (F(0), F(1))
        parent = {reference: None}
        order = []
        queue = deque([reference])
        while queue:
            v = queue.popleft()
            order.append(v)
            offset, slope = affine[v]
            for w in adjacency[v]:
                if parent[v] == w:
                    continue
                if w in affine:
                    return None  # A second route to w closes a cycle.
                if v < n:
                    a, b = game.intercepts[w-n][v], game.slopes[w-n][v]
                    affine[w] = (a-b*offset, -b*slope)
                else:
                    a, b = game.intercepts[v-n][w], game.slopes[v-n][w]
                    affine[w] = ((a-offset)/b, -slope/b)
                parent[w] = v
                queue.append(w)
        targets = tuple(v for v in order if v < n)
        lower = max(-affine[j][0]/affine[j][1] for j in targets)
        upper = min((1-affine[j][0])/affine[j][1] for j in targets)
        if lower > upper:
            return None
        total = sum(game.priors[v-n] for v in order if v >= n)
        ratio = total/sum(1/game.gains[j] for j in targets)
        trees.append(_Tree(reference, targets, total, ratio, lower, upper, order, parent))
    if len(affine) != n+m:
        return None
    return trees, affine


def equilibrium_from_forest(game: Game, edges):
    """Return an exact full one-resource Profile for a valid forest, else None."""
    if (not isinstance(game, Game) or game.resources != 1 or min(game.priors) <= 0
            or min(game.gains) <= 0 or any(b <= 0 for row in game.slopes for b in row)):
        return None
    n, m = len(game.gains), len(game.priors)
    adjacency = [[] for _ in range(n+m)]
    listed = set()
    try:
        for edge in edges:
            raw_i, raw_j = edge
            if isinstance(raw_i, bool) or isinstance(raw_j, bool):
                return None
            i, j = index(raw_i), index(raw_j)
            if not (0 <= i < m and 0 <= j < n) or (i, j) in listed:
                return None
            listed.add((i, j))
            adjacency[n+i].append(j)
            adjacency[j].append(n+i)
    except (TypeError, ValueError):
        return None
    if any(not row for row in adjacency):
        return None
    result = _components(game, adjacency)
    if result is None:
        return None
    trees, affine = result
    peak = max(tree.ratio for tree in trees)
    maxima = [tree for tree in trees if tree.ratio == peak]
    if len(maxima) != 1:
        return None
    main = maxima[0]

    x = [F(0)]*n
    column_margins = [peak/d for d in game.gains]
    for tree in trees:
        if tree is main:
            continue
        for j in tree.targets:
            offset, slope = affine[j]
            x[j] = offset+slope*tree.lower
        zero = [j for j in tree.targets if x[j] == 0]
        if len(zero) != 1 or any(x[j] >= 1 for j in tree.targets):
            return None
        anchor = zero[0]
        column_margins[anchor] = tree.total_mass-sum(column_margins[j] for j in tree.targets if j != anchor)
        if column_margins[anchor] <= 0:
            return None
    offset_total = sum(affine[j][0] for j in main.targets)
    slope_total = sum(affine[j][1] for j in main.targets)
    parameter = (1-sum(x)-offset_total)/slope_total
    if not main.lower <= parameter <= main.upper:
        return None
    for j in main.targets:
        offset, slope = affine[j]
        x[j] = offset+slope*parameter
    if sum(x) != 1 or any(not 0 <= v <= 1 for v in x) or any(x[j] <= 0 for j in main.targets):
        return None

    remaining = column_margins+list(game.priors)
    probability = [[F(0)]*n for _ in range(m)]
    for tree in trees:
        for v in reversed(tree.order[1:]):
            w = tree.parent[v]
            amount = remaining[v]
            if amount <= 0:
                return None
            i, j = (v-n, w) if v >= n else (w-n, v)
            probability[i][j] = amount/game.priors[i]
            remaining[w] -= amount
        if remaining[tree.reference] != 0:
            return None

    # Recheck both players' best responses on the actual dense game and
    # exclude every positive/tight edge mismatch, including unused ties.
    score = [F(0)]*n
    for i, row in enumerate(probability):
        if sum(row) != 1:
            return None
        utility = [a-b*v for a, b, v in zip(game.intercepts[i], game.slopes[i], x)]
        best = max(utility)
        for j, chance in enumerate(row):
            if (chance > 0) != (utility[j] == best) or (chance > 0) != ((i, j) in listed):
                return None
            score[j] += game.gains[j]*game.priors[i]*chance
    if max(score) != peak or any(value and score[j] != peak for j, value in enumerate(x)):
        return None
    return Profile(tuple(x), tuple(map(tuple, probability)))
