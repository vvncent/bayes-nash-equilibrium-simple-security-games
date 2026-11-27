"""Exact checks for the unlabelled-root, one-resource forest decoder.

Run from the repository root with python3 -B round2/check_security_one_resource_forest.py.
The decoder itself has no solver calls. These tests independently recover
examples from the compiler with the direct BNE conditions or a separately
verified labelled forest, and enumerate all candidate edge lists on small games.
"""

from fractions import Fraction as F
from itertools import combinations
import sys

from check_security_one_resource import (
    certified_isolated, model_point, no_alternative_smt, rational_bne,
)
from security_equilibrium_uniqueness import Game, Profile
from security_one_resource import isolate_game, unique_one_resource
from security_one_resource_forest import equilibrium_from_forest


def positive_edges(profile):
    return tuple((i, j) for i, row in enumerate(profile.strategies)
                 for j, value in enumerate(row) if value > 0)


def check_reference(game, expected):
    rational_bne(game, expected.coverage, expected.strategies)
    support = positive_edges(expected)
    matches = []
    for i, row in enumerate(game.intercepts):
        utility = [a-b*x for a, b, x in zip(row, game.slopes[i], expected.coverage)]
        best = max(utility)
        matches.extend((i, j) for j, u in enumerate(utility) if u == best)
    assert tuple(matches) == support, "the promised target has a tight edge carrying zero flow"
    decoded = equilibrium_from_forest(game, reversed(support))
    assert decoded == expected
    return support


def exhaust_all(game, expected):
    graph = tuple((i, j) for i in range(len(game.priors)) for j in range(len(game.gains)))
    wanted = positive_edges(expected)
    accepted = []
    examined = 0
    for size in range(len(graph)+1):
        for candidate in combinations(graph, size):
            result = equilibrium_from_forest(game, candidate)
            if result is not None:
                assert result == expected
                accepted.append(candidate)
            examined += 1
    assert accepted == [wanted]
    return examined


def alterations(game, expected):
    support = set(positive_edges(expected))
    full = {(i, j) for i in range(len(game.priors)) for j in range(len(game.gains))}
    count = 0
    for edge in full:
        assert equilibrium_from_forest(game, support ^ {edge}) is None
        count += 1
    return count


def main():
    if hasattr(sys, "set_int_max_str_digits"):
        sys.set_int_max_str_digits(0)
    # Direct, nontrivial isolated 4x2 positive target. The reference is
    # obtained from unrestricted literal equilibrium constraints in Z3.
    original = Game((F(1, 2), F(1, 2)), (1, 1), ((1, 1),)*2, ((1, 1),)*2, 1)
    isolated, _ = isolate_game(original)
    exact = model_point(isolated, "unrooted_direct")
    no_alternative_smt(isolated, exact)
    support = check_reference(isolated, exact)
    total = exhaust_all(isolated, exact)
    assert total == 256

    malformed = (None, [(0,)], [(0, 0, 0)], [(F(1, 2), 0)], [("0", 1)],
                 [(-1, 0)], [(len(isolated.priors), 0)], [(0, len(isolated.gains))],
                 [(False, 0)], support+support[:1], [], [(0, 0), (0, 1), (1, 0), (1, 1)])
    for edges in malformed:
        assert equilibrium_from_forest(isolated, edges) is None
    invalid_games = (None, Game((1,), (1, 1), ((1, 1),), ((1, 1),), 0),
                     Game((1, 0), (1, 1), ((1, 1),)*2, ((1, 1),)*2, 1),
                     Game((1,), (0, 1), ((1, 1),), ((1, 1),), 1),
                     Game((1,), (1, 1), ((1, 1),), ((0, 1),), 1))
    for g in invalid_games:
        assert equilibrium_from_forest(g, support) is None

    # A physical pure-coverage forest with unequal target scores, in strict
    # interior-budget output from the isolated-game constructor.
    pure = Game((1,), (1, 2), ((4, 0),), ((1, 1),), 1)
    pure_target, _ = isolate_game(pure)
    pure_eq = model_point(pure_target, "pure_direct")
    assert pure_eq.coverage == (1, 0)
    check_reference(pure_target, pure_eq)
    total += exhaust_all(pure_target, pure_eq)
    assert total == 320

    # The two compiler endpoints map to the same fixed 1x1 game.
    for budget in (0, 3):
        endpoint = Game((1, 0), (1, 0, 1), ((1, 0, 0), (0, 3, 0)),
                        ((1, 0, 1), (0, 1, 1)), budget)
        reduction = unique_one_resource(endpoint)
        fixed = Profile((1,), ((1,),))
        check_reference(reduction.target, fixed)
        assert reduction.decode(equilibrium_from_forest(reduction.target, [(0, 0)])).defense == (
            (tuple(range(budget)), F(1)),)

    # Real compiler outputs, each with multiple tight components. Neither
    # the zero-coverage locations nor the peak-score component is passed in.
    composite = (
        (Game((1, 0), (1, 1, 1), ((1, 1, 1), (0, 3, -1)), ((1, 1, 1), (1, 1, 1)), 2), 8),
        (Game((1, 0), (1, 2, 0), ((3, 3, 0), (0, 3, 0)), ((0, 1, 0), (1, 0, 1)), 2), 64),
    )
    edits = 0
    counts = []
    for k, (source, trial_power) in enumerate(composite):
        reduction = unique_one_resource(source)
        ref, tree_count, _ = certified_isolated(reduction.capped, reduction.target,
                                                "unrooted_full"+str(k), trial_power=trial_power)
        edges = check_reference(reduction.target, ref)
        assert tree_count >= 2
        wrong = alterations(reduction.target, ref)
        edits += wrong
        decoded = reduction.decode(equilibrium_from_forest(reduction.target, reversed(edges)))
        marginal = decoded.marginal(source)
        rational_bne(source, marginal.coverage, marginal.strategies)
        counts.append((len(edges), tree_count))
    # A type's unused maximizing edge is illegal even when a proposed graph
    # realizes an ordinary BNE on non-promised data at the physical solution.
    tie = Game((F(3, 4), F(1, 4)), (1, 1), ((2, 1), (0, 4)), ((1, 1), (1, 1)), 1)
    assert equilibrium_from_forest(tie, [(0, 0), (1, 1)]) is None
    print(f"{total} candidate edge sets exhausted on 4×2 mixed-coverage and 3×2 pure-coverage "
          "isolated games; each accepted exactly one unrooted forest.")
    print(f"{len(malformed)} malformed edge lists and {len(invalid_games)} invalid domains rejected; "
          "both 1×1 compiler endpoints recovered.")
    print(f"Two 8×4 compiler targets recovered with (positive edges, components)={counts}; "
          f"all {edits} single-edge changes rejected, and both original equilibria decoded exactly.")


if __name__ == "__main__":
    main()
