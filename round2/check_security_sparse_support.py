"""Exact weak-game support reconstruction and bounded-ambiguity BNE search.

Run with Python and z3-solver. Exact support means every named edge carries
positive mass. Both attacker slopes and defender gains may be zero.
"""

from dataclasses import dataclass
from fractions import Fraction as F
from itertools import combinations, product
from math import ceil, lcm

import z3

from check_security_support_reconstruction import (
    Game, Profile, check_profile, components, expect, instance_conditions, literal,
    lp_endpoint, q, read_fraction, realize_coverage, solve_linear_cells, symbols,
)


@dataclass
class Component:
    targets: tuple
    lower: dict
    upper: dict
    min_load: F
    max_load: F


def partition(game, support, var):
    x, u, _, _ = var
    if any(not any(a == i for a, _ in support) for i in range(len(u))):
        return None
    pos = {e for e in support if game.offers[e][1] > 0}
    all_parts = [(types, targets) for types, targets in components(game, pos) if targets]
    location = {j: c for c, (_, targets) in enumerate(all_parts) for j in targets}
    destinations = [{location[j] for i, j in support if i == h} for h in range(len(u))]
    result = []
    for c, (types, targets) in enumerate(all_parts):
        local = [z3.And(x[j] >= 0, x[j] <= 1) for j in targets]
        for i, j in support:
            if i in types:
                a, b = game.offers[i, j]
                local.append(u[i] == q(a) if b == 0 else u[i] + q(b) * x[j] == q(a))
        lower, upper = {}, {}
        for j in targets:
            lower[j] = lp_endpoint(local, x[j], False)
            if lower[j] is None:
                return None
            upper[j] = lp_endpoint(local, x[j], True)
        low = sum((p for i, p in enumerate(game.masses) if destinations[i] == {c}), F(0))
        high = sum((p for i, p in enumerate(game.masses) if c in destinations[i]), F(0))
        result.append(Component(targets, lower, upper, low, high))
    return result


def cutoff_cells(breaks, lam):
    points = sorted(breaks | {F(0)})
    for i, value in enumerate(points):
        if value > 0:
            yield value, [lam == q(value)]
        if i + 1 < len(points):
            end = points[i + 1]
            yield (value + end) / 2, [lam > q(value), lam < q(end)]
    yield points[-1] + 1, [lam > q(points[-1])]


def formulas(game, support, var):
    """Pure linear cases in their variables; branch only on overlapping variable-load intervals."""
    x, _, _, lam = var
    base, scores = instance_conditions(game, support, True, var)
    parts = partition(game, support, var)
    if parts is None:
        return base, [], 0

    def at_endpoint(part, high):
        cond = []
        for j, value in (part.upper if high else part.lower).items():
            cond.append(x[j] == q(value))
            if value > 0:
                cond.append(scores[j] >= lam)
            if value < 1:
                cond.append(scores[j] <= lam)
        return cond

    cuts, bounds = set(), {}
    for c, part in enumerate(parts):
        if part.lower != part.upper and all(game.gains[j] > 0 for j in part.targets):
            B = sum(1 / game.gains[j] for j in part.targets)
            bounds[c] = part.min_load / B, part.max_load / B
            cuts.update(bounds[c])
    zero = [lam == 0]
    zero.extend(x[j] == 1 for j in {j for _, j in support} if game.gains[j] > 0)
    cases, max_overlap = [z3.And(*zero)], 0
    for t, cell in cutoff_cells(cuts, lam):
        unsure = []
        for c, part in enumerate(parts):
            quota = [scores[j] == lam for j in part.targets]
            if c not in bounds:
                # A rigid part uses its only point. A flexible part containing
                # a zero-gain target must achieve x_j=0 at the lower endpoint.
                cell.extend(at_endpoint(part, False))
                continue
            lb, ub = bounds[c]
            if lb < t < ub:
                unsure.append((at_endpoint(part, False), quota, at_endpoint(part, True)))
            elif lb == ub == t:
                cell.extend(quota)
            else:
                cell.extend(at_endpoint(part, t <= lb))
        max_overlap = max(max_overlap, len(unsure))
        for labels in product(*unsure):
            cases.append(z3.And(*(cell + [clause for group in labels for clause in group])))
    return base, cases, max_overlap


def recover(game, support, verify=False):
    var = symbols(game)
    base, cases, overlap = formulas(game, support, var)
    if verify:
        solver = z3.SolverFor("QF_LRA")
        candidate = z3.And(*(base + [z3.Or(*cases)]))
        solver.add(z3.Xor(candidate, literal(game, support, True, var)))
        expect(solver, z3.unsat, "the complete profile sets differ")
    solver = z3.SolverFor("QF_LRA")
    solver.add(*base)
    for case in cases:
        solver.push()
        solver.add(case)
        outcome = solver.check()
        assert outcome in (z3.sat, z3.unsat)
        if outcome == z3.sat:
            x, u, f, lam = var
            model = solver.model()
            cov = tuple(read_fraction(model, v) for v in x)
            util = tuple(read_fraction(model, v) for v in u)
            mass = {e: read_fraction(model, v) for e, v in f.items()}
            prob = tuple(tuple(mass[i, j] / p for j in range(len(x))) for i, p in enumerate(game.masses))
            profile = Profile(cov, util, mass, read_fraction(model, lam), realize_coverage(cov, game.resources), prob)
            check_profile(game, support, True, profile)
            return profile, overlap
        solver.pop()
    return None, overlap


def options(game):
    """Remove inferior/duplicate flats and impossible actions; pin an always-best choice if possible."""
    x = [z3.Real(f"coverage{j}") for j in range(len(game.gains))]
    cube = [z3.Sum(x) == game.resources, *[z3.And(v >= 0, v <= 1) for v in x]]
    choices = []
    for i in range(len(game.masses)):
        payoff = [q(game.offers[i, j][0]) - q(game.offers[i, j][1]) * x[j] for j in range(len(x))]
        flat = [j for j in range(len(x)) if game.offers[i, j][1] == 0]
        retained_flat = max(flat, key=lambda j: game.offers[i, j][0]) if flat else None
        possible = []
        for j, val in enumerate(payoff):
            if j in flat and j != retained_flat:
                continue
            worst = [lp_endpoint(cube, val - other, False) for other in payoff]
            if min(worst) >= 0:
                possible = [j]
                break
            sat = z3.SolverFor("QF_LRA")
            sat.add(*(cube + [val >= other for other in payoff]))
            if sat.check() == z3.sat:
                possible.append(j)
        assert possible
        choices.append(tuple(possible))
    return tuple(choices)


def supports(choices):
    support_rows = [[s for k in range(1, len(targets) + 1) for s in combinations(targets, k)]
                    for targets in choices]
    for selected in product(*support_rows):
        yield {(i, j) for i, targets in enumerate(selected) for j in targets}


def equilibrium(game):
    choices = options(game)
    for support in supports(choices):
        profile, _ = recover(game, support)
        if profile is not None:
            return profile, choices
    raise AssertionError("A reduced finite game has an equilibrium")


def perturb(game, choices):
    """Implement the uniform Cramer-gap perturbation in the manuscript's degenerate-data lemma."""
    m, n = len(game.masses), len(game.gains)
    table = {}
    for i, targets in enumerate(choices):
        minimum = min(game.offers[i, j][0] - game.offers[i, j][1] for j in targets)
        for j in range(n):
            table[i, j] = game.offers[i, j] if j in targets else (minimum - 2, F(1))
    scalars = (*game.masses, *game.gains, F(game.resources), *(v for ab in table.values() for v in ab))
    denominator = lcm(*(v.denominator for v in scalars))
    height = denominator * (2 * ceil(max(abs(v) for v in scalars)) + 2)
    dimension = n + m * n + 2
    eps = F(1, 8 * (dimension * height) ** dimension)
    positive = {(i, j): (a, b + eps) for (i, j), (a, b) in table.items()}
    return Game(game.masses, tuple(d + eps for d in game.gains), positive, game.resources)


def repair(game, witness):
    """Re-solve the perturbed witness's allowed attack edges and coverage labels on original payoffs."""
    support = {e for e, mass in witness.attack_masses.items() if mass > 0}
    var = symbols(game)
    x, u, f, lam = var
    base, scores = instance_conditions(game, support, False, var)
    solver = z3.SolverFor("QF_LRA")
    solver.add(*base)
    for j, value in enumerate(witness.coverage):
        if value == 0:
            solver.add(x[j] == 0, scores[j] <= lam)
        elif value == 1:
            solver.add(x[j] == 1, scores[j] >= lam)
        else:
            solver.add(scores[j] == lam)
    expect(solver, z3.sat, "perturbed BNE's original pattern")
    model = solver.model()
    cov = tuple(read_fraction(model, v) for v in x)
    util = tuple(read_fraction(model, v) for v in u)
    mass = {e: read_fraction(model, v) for e, v in f.items()}
    prob = tuple(tuple(mass[i, j] / p for j in range(len(x))) for i, p in enumerate(game.masses))
    result = Profile(cov, util, mass, read_fraction(model, lam), realize_coverage(cov, game.resources), prob)
    check_profile(game, support, False, result)
    return result


def perturbed_search(game, choices):
    if game.resources in (0, len(game.gains)):
        return equilibrium(game)[0]
    positive = perturb(game, choices)
    for support in supports(choices):
        witness = solve_linear_cells(positive, support, exact=True)
        if witness is not None:
            return repair(game, witness)
    raise AssertionError("No perturbed support found among the original retained edges")


def example(masses, gains, a, b, r):
    return Game(tuple(map(F, masses)), tuple(map(F, gains)),
                {(i, j): (F(a[i][j]), F(b[i][j])) for i in range(len(masses)) for j in range(len(gains))}, r)


def fixtures():
    half = F(1, 2)
    return [
        example((half, half), (1, 1), ((1, 1), (1, 1)), ((0, 0), (0, 0)), 1),
        example((F(3, 4), F(1, 4)), (1, 1), ((F(3, 2), 1), (0, F(3, 2))), ((1, 0), (1, 1)), 1),
        example((half, half), (0, 1), ((2, 2), (0, 2)), ((0, 0), (1, 1)), 1),
        example((half, half), (0, 2), ((0, 0), (1, 1)), ((1, 1), (1, 1)), 1),
        example((1,), (1, 0, 0), ((3, 3, -1),), ((0, 0, 1),), 2),
        example((half, half), (0, 0), ((2, 1), (1, 2)), ((0, 0), (1, 1)), 0),
        example((half, half), (1, 0), ((0, 1), (1, 1)), ((0, 1), (1, 0)), 2),
        example((1,), (1, 1, 1), ((1, 1, F(3, 2)),), ((0, 0, 1),), 1),
    ]


def disjoint_windows(pairs):
    n = pairs * 2
    mass = F(1, 3 * pairs)
    support = {(i, j) for i in range(pairs) for j in (2 * i, 2 * i + 1)}
    support.update((pairs + j, j) for j in range(n))
    a = [[-2] * n for _ in range(3 * pairs)]
    b = [[1] * n for _ in range(3 * pairs)]
    for i, j in support:
        a[i][j], b[i][j] = (0, 0) if i < pairs else (2, 1)
    game = example([mass] * (3 * pairs), [3 ** j for j in range(n)], a, b, pairs)
    return game, support


def main():
    count = feasible = positive_overlap = largest_overlap = 0
    games = fixtures()
    for game in games:
        edges = tuple(game.offers)
        for flags in product((False, True), repeat=len(edges)):
            support = {e for e, present in zip(edges, flags) if present}
            profile, width = recover(game, support, verify=True)
            count += 1
            feasible += profile is not None
            positive_overlap += width > 0
            largest_overlap = max(largest_overlap, width)
        _, choices = equilibrium(game)
        perturbed_search(game, choices)
    assert options(games[0]) == ((0,), (0,))  # All targets tied for both flat types.
    assert recover(games[0], set(games[0].offers))[1] == 2
    assert options(games[1]) == ((0, 1), (1,))
    assert options(games[-1]) == ((0, 2),)   # Two interchangeable flats can tie with a sloping option.
    wide_game, wide_support = disjoint_windows(3)
    profile, overlap = recover(wide_game, wide_support, verify=True)
    assert profile and overlap == 1
    parts = partition(wide_game, wide_support, symbols(wide_game))
    assert sum(part.min_load < part.max_load for part in parts) == 6
    print(f"{count} exact-support full-profile equivalence checks on {len(games)} weak games; {feasible} feasible supports.")
    print(f"{positive_overlap} supports had positive overlap width; greatest tested overlap {largest_overlap}.")
    print("Direct search and restricted-game perturbation/repair returned an exact BNE on every original input.")
    print("Additional 9-type, 6-target exact-support profile check: 6 uncertain components, overlap width 1.")


if __name__ == "__main__":
    main()
