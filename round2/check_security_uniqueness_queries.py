"""Exact finite tests of the nonadaptive nonuniqueness-query reduction.

An independent small-game oracle solves literal one-resource BNE conditions
over all real strategies, then asks whether a distinct profile exists. For
each nonunique game it verifies both inclusions between the full equilibrium
set and the straight segment joining the two pure-probe endpoint profiles.
It removes only options that provably lose everywhere on the coverage simplex.
"""

from collections import Counter
from fractions import Fraction as F
import sys

import z3

from check_security_one_resource import model_point, rational_bne
from security_equilibrium_uniqueness import Game, Profile
from security_one_resource import isolate_game, unique_one_resource
from security_uniqueness_queries import prepare_queries


def q(v):
    v = F(v)
    return z3.RealVal(f"{v.numerator}/{v.denominator}")


def check_segment(solver, variables, probe_first, probe_mass, certificates):
    # Keep the auxiliary best values/defender peak to witness that every
    # interpolated physical profile is also an equilibrium.
    constraints = z3.And(*solver.assertions())
    amounts = (q(0), q(probe_mass))
    endpoints = []
    endpoints_all = []
    for amount in amounts:
        solver.push()
        solver.add(probe_first == amount)
        assert solver.check() == z3.sat, "a pure-probe endpoint does not exist"
        model = solver.model()
        endpoints.append([model.eval(v, model_completion=True) for v in variables])
        endpoints_all.append([model.eval(v, model_completion=True) for v in certificates])
        solver.pop()

    weight = probe_first/q(probe_mass)
    segment = [a+(b-a)*weight for a, b in zip(*endpoints)]
    solver.push()
    solver.add(z3.Or(probe_first < 0, probe_first > q(probe_mass),
                     *(v != value for v, value in zip(variables, segment))))
    assert solver.check() == z3.unsat, "an unrestricted equilibrium lies outside the segment"
    solver.pop()

    # Converse, covering every real interpolation parameter, including
    # irrational ones. All expressions remain affine in the single parameter.
    t = z3.Real("query_segment_parameter")
    src, dst = endpoints[0]+endpoints_all[0], endpoints[1]+endpoints_all[1]
    same_line = [a+(b-a)*t for a, b in zip(src, dst)]
    plugged = z3.substitute(constraints, *zip(variables+certificates, same_line))
    all_splits = z3.SolverFor("QF_LRA")
    all_splits.add(t >= 0, t <= 1, z3.Not(plugged))
    assert all_splits.check() == z3.unsat, "a point on the proposed segment is not an equilibrium"


def decision(game, expected_x, first):
    n = len(game.gains)
    x = [z3.Real(f"query_reference_x{j}") for j in range(n)]
    solver = z3.SolverFor("QF_LRA")
    solver.add(z3.Sum(x) == 1, *(v >= 0 for v in x))
    variables = list(x)
    columns = [[] for _ in x]
    certificates = []
    probe_first = None
    for i, (a, b, mass) in enumerate(zip(game.intercepts, game.slopes, game.priors)):
        # On the simplex one listed target always yields max_k(a_k-b_k) or more.
        floor = max(alpha-beta for alpha, beta in zip(a, b))
        possible = [j for j, val in enumerate(a) if val >= floor]
        best = z3.Real(f"query_reference_best{i}")
        certificates.append(best)
        row = []
        for j in possible:
            attack = z3.Real(f"query_reference_mass{i}_{j}")
            payoff = q(a[j])-q(b[j])*x[j]
            solver.add(attack >= 0, best >= payoff, z3.Or(attack == 0, best == payoff))
            columns[j].append(attack)
            row.append(attack)
            if i == len(game.priors)-1 and j == first:
                probe_first = attack
        solver.add(z3.Sum(row) == q(mass))
        variables.extend(row)
    peak = z3.Real("query_reference_peak")
    certificates.append(peak)
    for j, v in enumerate(x):
        score = q(game.gains[j])*z3.Sum(columns[j])
        solver.add(score <= peak, z3.Or(v == 0, score == peak))
    assert solver.check() == z3.sat
    model = solver.model()
    solver.push()
    solver.add(z3.Or(*(v != q(u) for v, u in zip(x, expected_x))))
    assert solver.check() == z3.unsat
    solver.pop()
    # Exclude a complete profile. Indirect utilities and cutoff certificates
    # are not part of the strategy and are deliberately absent.
    solver.push()
    solver.add(z3.Or(*(v != model.eval(v, model_completion=True) for v in variables)))
    result = solver.check()
    assert result in (z3.sat, z3.unsat)
    solver.pop()
    if result == z3.sat:
        assert probe_first is not None
        check_segment(solver, variables, probe_first, game.priors[-1], certificates)
    return result == z3.sat


def expected_bit(game, profile, key):
    x = profile.coverage
    if key[0] == "bound":
        _, j, v = key
        return x[j] == v, False
    _, i, j, k = key
    offers = [a-b*t for a, b, t in zip(game.intercepts[i], game.slopes[i], x)]
    return offers[j] == offers[k], offers[j] == offers[k] < max(offers)


def flags_for(game, profile):
    plan = prepare_queries(game)
    n, m = len(game.gains), len(game.priors)
    assert len(plan.queries) == m*n*(n-1)//2+2*n
    assert tuple(item.key for item in plan.queries) == tuple(item.key for item in prepare_queries(game).queries)
    answers, counts = [], Counter()
    for entry in plan.queries:
        want, incidental = expected_bit(game, profile, entry.key)
        expected_x = profile.coverage+((F(0),) if entry.key[0] == "bound" else ())
        first = entry.key[2] if entry.key[0] == "tie" else entry.key[1]
        observed = decision(entry.game, expected_x, first)
        assert observed == want, (entry.key, observed, want)
        counts["real decisions"] += 1
        counts["nonunique" if observed else "unique"] += 1
        counts["incidental"] += int(incidental)
        answers.append(observed)
    assert plan.recover(iter(answers)) == profile
    # Omit all positive bounds/ties to make the budget underdetermined.
    try:
        plan.recover([False]*len(answers))
    except ValueError:
        pass
    else:
        raise AssertionError("All-false answer vector unexpectedly determines coverage")
    return counts, answers


def main():
    if hasattr(sys, "set_int_max_str_digits"):
        sys.set_int_max_str_digits(0)
    total = Counter()
    # A genuine mixed-coverage target with 4 original H rows and two targets.
    base = Game((F(1, 2), F(1, 2)), (1, 1), ((1, 1),)*2, ((1, 1),)*2, 1)
    mixed, _ = isolate_game(base)
    profile = model_point(mixed, "decision_mixed")
    assert all(0 < v < 1 for v in profile.coverage)
    counts, _ = flags_for(mixed, profile)
    total.update(counts)

    # A genuine compiled pure-coverage target, including both bound types.
    pure_base = Game((1,), (1, 2), ((4, 0),), ((1, 1),), 1)
    pure, _ = isolate_game(pure_base)
    profile = model_point(pure, "decision_pure")
    assert profile.coverage == (1, 0)
    counts, _ = flags_for(pure, profile)
    total.update(counts)

    # Exact canonical promises do not require nonmaximal offers to be
    # distinct. This simple anchored example has a deliberately equal
    # losing pair in row 0. The equality probe must detect it.
    example = Game((F(8, 11), F(1, 11), F(2, 11)), (1, 1, 1),
                   ((4, -2, -2), (-3, 4, -2), (-3, -2, 4)), ((1, 1, 1),)*3, 1)
    expected = Profile((1, 0, 0), ((1, 0, 0), (0, 1, 0), (0, 0, 1)))
    rational_bne(example, expected.coverage, expected.strategies)
    counts, _ = flags_for(example, expected)
    assert counts["incidental"] >= 1
    total.update(counts)

    # Full original r=2 source, compiled to one resource and a unique target.
    # Probe answers may be tested entirely through QF_LRA on this small target.
    source = Game((1, 0), (1, 1, 1), ((1, 1, 1), (0, 3, -1)), ((1, 1, 1), (1, 1, 1)), 2)
    reduction = unique_one_resource(source)
    from check_security_one_resource import certified_isolated
    unique, _, _ = certified_isolated(reduction.capped, reduction.target, "decision_composite")
    counts, answers = flags_for(reduction.target, unique)
    total.update(counts)
    decoded = reduction.decode(prepare_queries(reduction.target).recover(answers))
    original = decoded.marginal(source)
    rational_bne(source, original.coverage, original.strategies)
    assert original.coverage == (F(2, 3),)*3
    assert dict(decoded.defense) == {(0, 1): F(1, 3), (0, 2): F(1, 3), (1, 2): F(1, 3)}

    # Forced-budgets in the compiler have the same fixed one-target game.
    end = unique_one_resource(Game((1,), (1, 1), ((1, 3),), ((1, 1),), 0))
    plan = prepare_queries(end.target)
    assert not plan.queries
    direct = end.decode(plan.recover(()))
    assert direct.defense == (((), F(1)),)
    print(f"Four games: all {total['real decisions']} oracle decisions checked over all real equilibria "
          f"({total['unique']} unique, {total['nonunique']} nonunique), including "
          f"{total['incidental']} nonmaximal equality. All 56 decisions for the composite 8×4 "
          "target recovered the original full equilibrium. The one-target endpoint used zero queries.")
    print(f"All {total['nonunique']} nonunique queries have exactly one closed segment of full "
          f"equilibria: verified both pure-probe endpoints, excluded every equilibrium off their "
          "line, and certified every real interpolation on the segment.")


if __name__ == "__main__":
    main()
