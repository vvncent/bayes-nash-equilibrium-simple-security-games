"""Construct and check a one-resource membership query for one attack edge.

Run ``python3 -B round2/check_security_forest_edge_decision.py`` with z3-solver.
Tests quantify over the full real equilibrium conditions of the emitted payoff
tables, including every added type's strategy and every defender probability.
"""

from dataclasses import dataclass
from fractions import Fraction as F

import z3

from check_security_one_resource import bne, check, prove, q, rational_bne, variables
from security_equilibrium_uniqueness import Game, Profile


@dataclass(frozen=True)
class Query:
    game: Game
    floor_mass: F
    baseline_score: F
    type_index: int
    target_index: int


def edge_query(game, type_index, target_index):
    """Test a conditional attack probability in a uniquely solvable input."""
    n, m = len(game.gains), len(game.priors)
    if game.resources != 1 or not (0 <= type_index < m and 0 <= target_index < n):
        raise ValueError("A valid type, target and one-resource game are required")
    if min(game.gains) <= 0 or min(game.priors) <= 0 or min(map(min, game.slopes)) <= 0:
        raise ValueError("The input gains, priors and slopes must be strictly positive")
    j = target_index
    max_gain = max(game.gains)
    floor_mass = (1 + max_gain) / game.gains[j]
    baseline = (1 + max_gain) * (1 + floor_mass)
    dummy_gain = min(game.gains) / (2 * n * (1 + floor_mass))
    gains = list(game.gains) + [2 * game.gains[j], dummy_gain]
    gains[j] *= 2
    masses = list(game.priors)
    intercepts, slopes = [], []
    for i, (old_a, old_b) in enumerate(zip(game.intercepts, game.slopes)):
        a, b = list(old_a), [2 * weight for weight in old_b]
        a[j] += old_b[j]
        b[j] *= 2
        low = min(c - weight for c, weight in zip(a, b)) - 1
        intercepts.append(a + [a[j] if i == type_index else low, low])
        slopes.append(b + [b[j] if i == type_index else 1, 1])

    # The floor buyer chooses between the first twin and the last (dummy) target.
    a, b = [-3] * (n + 2), [1] * (n + 2)
    a[j], b[j], a[-1] = F(1, 2), 2, 0
    intercepts.append(a)
    slopes.append(b)
    masses.append(floor_mass)

    # One type for each original target supplies the common baseline score.
    for k, gain in enumerate(game.gains):
        a = [-3] * (n + 2)
        if k == j:
            a[j] = a[n] = 0
        else:
            a[k] = 2
        intercepts.append(a)
        slopes.append([1] * (n + 2))
        masses.append(baseline / gain)
    total = sum(masses)
    query = Game(tuple(mass / total for mass in masses), gains, intercepts, slopes, 1)
    return Query(query, floor_mass, baseline, type_index, target_index)


def endpoints(game, source, query):
    """Independently lift the source point by sending none/all of its edge to twin B."""
    j, i = query.target_index, query.type_index
    n = len(game.gains)
    loads = [sum(p * row[t] for p, row in zip(game.priors, source.strategies)) for t in range(n)]
    cutoff = max(d * w for d, w in zip(game.gains, loads))
    floor_trade = cutoff / game.gains[j] - loads[j]
    x = [v / 2 for v in source.coverage]
    x[j] = (x[j] + F(1, 2)) / 2
    x.extend([x[j], F(0)])
    edge_amount = game.priors[i] * source.strategies[i][j]
    equalizer_mass = query.baseline_score / game.gains[j]
    answers = []
    for to_b in (F(0), edge_amount):
        conditional = [list(row) + [F(0), F(0)] for row in source.strategies]
        conditional[i][j] -= to_b / game.priors[i]
        conditional[i][n] = to_b / game.priors[i]
        floor_row = [F(0)] * (n + 2)
        floor_row[j] = floor_trade / query.floor_mass
        floor_row[-1] = 1 - floor_row[j]
        conditional.append(floor_row)
        for k in range(n):
            row = [F(0)] * (n + 2)
            if k == j:
                half_load = (equalizer_mass + loads[j] + floor_trade) / 2
                row[n] = (half_load - to_b) / equalizer_mass
                row[j] = 1 - row[n]
            else:
                row[k] = 1
            conditional.append(row)
        answers.append(Profile(tuple(x), conditional))
    return answers


def fill(profile, x, sigma):
    return z3.And(*(v == q(w) for v, w in zip(x, profile.coverage)),
                  *(v == q(w) for row, old in zip(sigma, profile.strategies)
                    for v, w in zip(row, old)))


def verify(game, source, name):
    rational_bne(game, source.coverage, source.strategies)
    v, rows = variables(game, name + "_source")
    prove(z3.Implies(bne(game, v, rows), fill(source, v, rows)), name + " unique input")
    points = segments = 0
    for i, row in enumerate(source.strategies):
        for j, conditional in enumerate(row):
            query = edge_query(game, i, j)
            e0, e1 = endpoints(game, source, query)
            rational_bne(query.game, e0.coverage, e0.strategies)
            rational_bne(query.game, e1.coverage, e1.strategies)
            y, tau = variables(query.game, f"{name}_{i}_{j}")
            feasible = bne(query.game, y, tau)
            check(feasible, z3.sat, name + " query exists")
            if not conditional:
                assert e0 == e1
                prove(z3.Implies(feasible, fill(e0, y, tau)), name + " excludes any other profile")
                points += 1
                continue
            assert e0 != e1
            # The chosen row's probability at twin B fixes the unique interpolation parameter.
            parameter = tau[i][len(game.gains)] / q(conditional)
            in_segment = [parameter >= 0, parameter <= 1,
                          *(v == q(w) for v, w in zip(y, e0.coverage))]
            t = z3.Real(f"{name}_interpolation")
            candidate = []
            for old, new, actual in zip(e0.strategies, e1.strategies, tau):
                delta = [q(b - a) for a, b in zip(old, new)]
                in_segment.extend(v == q(a) + k * parameter for a, k, v in zip(old, delta, actual))
                candidate.append([q(a) + k * t for a, k in zip(old, delta)])
            prove(z3.Implies(feasible, z3.And(*in_segment)), name + " no point outside segment")
            prove(z3.Implies(z3.And(t >= 0, t <= 1),
                             bne(query.game, list(map(q, e0.coverage)), candidate)),
                  name + " all real points on segment are equilibria")
            segments += 1
    return points, segments


def main():
    fixtures = [
        ("three_way", Game((1,), (1, 2, 3), ((1, 1, 1),), ((1, 2, 3),), 1),
         Profile((F(6, 11), F(3, 11), F(2, 11)), ((F(6, 11), F(3, 11), F(2, 11)),))),
        ("pure", Game((F(2, 3), F(1, 3)), (1, 1, 1), ((5, 1, 0), (0, 5, 0)),
                      ((1, 1, 1), (1, 1, 1)), 1),
         Profile((1, 0, 0), ((1, 0, 0), (0, 1, 0)))),
        ("uncovered_attack", Game((F(3, 4), F(1, 4)), (1, 1, 1),
                               ((1, 1, 0), (-1, -1, 2)), ((1, 1, 1), (1, 1, 1)), 1),
         Profile((F(1, 2), F(1, 2), 0), ((F(1, 2), F(1, 2), 0), (0, 0, 1)))),
        ("one_target", Game((1,), (F(3, 17),), ((F(-4, 5),),), ((F(2, 7),),), 1),
         Profile((1,), ((1,),))),
    ]
    total_points = total_segments = 0
    for name, game, source in fixtures:
        points, segments = verify(game, source, name)
        total_points += points
        total_segments += segments
        print(f"{name}: {points} singletons, {segments} segments")
    print(f"All {total_points + total_segments} query games passed: {total_points} singletons, "
          f"{total_segments} exact nondegenerate closed line segments.")


if __name__ == "__main__":
    main()
