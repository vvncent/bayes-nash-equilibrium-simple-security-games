"""Exact checker for reconstruction from attack-support edges on the original security game.

Requires z3-solver. Type masses, defender gains and support-edge attacker slopes
are positive. A zero attacker slope is allowed off the supplied support.
The support may contain unused tight edges. Set exact=True to require positive flow
on every proposed edge. Coverage, attack probabilities and cutoff are returned.
"""

from collections import Counter
from dataclasses import dataclass
from fractions import Fraction as F
from itertools import combinations, product
from pathlib import Path
from random import Random
from typing import NamedTuple
import sys

import z3

sys.path.insert(0, str(Path(__file__).resolve().parent / "wardrop"))
from check_wardrop import exact as read_fraction, expect, q
from check_m1_support_reconstruction import components, lp_endpoint


@dataclass(frozen=True)
class Game:
    masses: tuple
    gains: tuple
    offers: dict
    resources: int

    @property
    def capacities(self):
        # The shared bipartite-components routine uses only the number of goods.
        return self.gains


class Profile(NamedTuple):
    coverage: tuple
    utilities: tuple
    attack_masses: dict
    cutoff: F
    defense_mix: dict
    attack_probabilities: tuple


def make_game(masses, gains, a, b, resources):
    masses, gains = tuple(map(F, masses)), tuple(map(F, gains))
    assert sum(masses) == 1 and all(p > 0 for p in masses) and all(d > 0 for d in gains)
    assert isinstance(resources, int) and 0 <= resources <= len(gains)
    offers = {(i, j): (F(a[i][j]), F(b[i][j]))
              for i in range(len(masses)) for j in range(len(gains))}
    assert all(slope >= 0 for _, slope in offers.values())
    return Game(masses, gains, offers, resources)


def symbols(game):
    x = tuple(z3.Real(f"x{j}") for j in range(len(game.gains)))
    u = tuple(z3.Real(f"u{i}") for i in range(len(game.masses)))
    f = {e: z3.Real(f"f{e[0]}_{e[1]}") for e in game.offers}
    return x, u, f, z3.Real("cutoff")


def instance_conditions(game, support, exact, var):
    x, u, f, lam = var
    rows = [lam >= 0, z3.Sum(x) == game.resources]
    rows.extend(z3.And(v >= 0, v <= 1) for v in x)
    for i, p in enumerate(game.masses):
        rows.append(z3.Sum([f[i, j] for j in range(len(x))]) == q(p))
    for (i, j), (a, b) in game.offers.items():
        rows.append(u[i] >= q(a) - q(b) * x[j])
        if (i, j) in support:
            rows.extend((u[i] == q(a) - q(b) * x[j], f[i, j] > 0 if exact else f[i, j] >= 0))
        else:
            rows.append(f[i, j] == 0)
    score = [q(d) * z3.Sum([f[i, j] for i in range(len(u))]) for j, d in enumerate(game.gains)]
    return rows, score


def literal(game, support, exact, var):
    """Direct best-response conditions, independent of any support-component reasoning."""
    x, u, f, lam = var
    rows, score = instance_conditions(game, support, exact, var)
    for (i, j), (a, b) in game.offers.items():
        rows.append(z3.Implies(f[i, j] > 0, u[i] == q(a) - q(b) * x[j]))
    for j, s in enumerate(score):
        rows.extend((z3.Implies(x[j] > 0, s >= lam), z3.Implies(x[j] < 1, s <= lam)))
    return z3.And(*rows)


@dataclass
class Segment:
    targets: tuple
    lower: dict
    upper: dict
    ratio: F


def prepare(game, support, var):
    """Compute each coverage coordinate's local extremal values without the global dominance rows."""
    if any(game.offers[e][1] <= 0 for e in support):
        raise ValueError("All supplied support-edge slopes must be positive")
    x, u, _, _ = var
    intervals, isolated = [], []
    for types, targets in components(game, support):
        if not targets:
            return None  # A positive-mass row cannot be empty.
        if not types:
            isolated.extend(targets)
            continue
        local = [z3.And(x[j] >= 0, x[j] <= 1) for j in targets]
        for i, j in support:
            if i in types:
                a, b = game.offers[i, j]
                local.append(u[i] == q(a) - q(b) * x[j])
        lower, upper = {}, {}
        for j in targets:
            lower[j] = lp_endpoint(local, x[j], False)
            if lower[j] is None:
                return None
            upper[j] = lp_endpoint(local, x[j], True)
        ratio = sum(game.masses[i] for i in types) / sum(1 / game.gains[j] for j in targets)
        intervals.append(Segment(targets, lower, upper, ratio))
    return intervals, isolated


def cutoff_cells(ratios, lam):
    breaks = sorted(set(ratios) | {F(0)})
    for i, a in enumerate(breaks):
        yield a, [lam == q(a)]
        if i + 1 < len(breaks):
            b = breaks[i + 1]
            yield (a + b) / 2, [lam > q(a), lam < q(b)]
    yield breaks[-1] + 1, [lam > q(breaks[-1])]


def reconstructed(game, support, exact, var):
    x, _, _, lam = var
    rows, score = instance_conditions(game, support, exact, var)
    data = prepare(game, support, var)
    if data is None:
        return z3.BoolVal(False), ()
    segments, isolated = data
    cases = []
    for t, constraints in cutoff_cells((part.ratio for part in segments), lam):
        if t > 0:
            constraints.extend(x[j] == 0 for j in isolated)
        for part in segments:
            if t == part.ratio and part.lower != part.upper:
                constraints.extend(score[j] == lam for j in part.targets)
                continue
            endpoint = part.upper if t < part.ratio else part.lower
            for j in part.targets:
                v = endpoint[j]
                constraints.append(x[j] == q(v))
                if v != 0:
                    constraints.append(score[j] >= lam)
                if v != 1:
                    constraints.append(score[j] <= lam)
        cases.append(z3.And(*constraints))
    return z3.And(*rows, z3.Or(*cases)), tuple(cases)


def solve_linear_cells(game, support, exact=False):
    """Solve each cutoff cell as its own pure linear system, preserving strict branches."""
    var = symbols(game)
    rows, _ = instance_conditions(game, support, exact, var)
    _, cases = reconstructed(game, support, exact, var)
    solver = z3.SolverFor("QF_LRA")
    solver.add(*rows)
    for cell in cases:
        solver.push()
        solver.add(cell)
        result = solver.check()
        assert result in (z3.sat, z3.unsat)
        if result == z3.sat:
            model = solver.model()
            x, u, f, lam = var
            coverage = tuple(read_fraction(model, a) for a in x)
            utilities = tuple(read_fraction(model, a) for a in u)
            masses = {ij: read_fraction(model, amount) for ij, amount in f.items()}
            attacks = tuple(tuple(masses[i, j] / p for j in range(len(x))) for i, p in enumerate(game.masses))
            return Profile(coverage, utilities, masses, read_fraction(model, lam),
                           realize_coverage(coverage, game.resources), attacks)
        solver.pop()
    return None


def realize_coverage(coverage, resources):
    """Translate a coverage into a sparse distribution over legal pure r-subsets."""
    cumulative = [F(0)]
    for v in coverage:
        cumulative.append(cumulative[-1] + v)
    breaks = sorted({F(1)} | {z % 1 for z in cumulative})
    mix = {}
    for left, right in zip(breaks, breaks[1:]):
        offset = (left + right) / 2
        chosen = tuple(j for j in range(len(coverage))
                       if any(cumulative[j] <= offset + k < cumulative[j + 1] for k in range(resources)))
        mix[chosen] = mix.get(chosen, F(0)) + right - left
    return mix


def check_profile(game, support, exact, result):
    x, u, f, lam, defense, attacks = result
    assert all(0 <= v <= 1 for v in x) and sum(x) == game.resources and lam >= 0
    scores = [d * sum(f[i, j] for i in range(len(u))) for j, d in enumerate(game.gains)]
    for (i, j), (a, b) in game.offers.items():
        assert f[i, j] >= 0 and u[i] >= a - b * x[j]
        if (i, j) in support:
            assert u[i] == a - b * x[j] and (not exact or f[i, j] > 0)
        else:
            assert f[i, j] == 0
    for i, p in enumerate(game.masses):
        assert sum(f[i, j] for j in range(len(x))) == p
        assert sum(attacks[i]) == 1 and all(p * prob == f[i, j] for j, prob in enumerate(attacks[i]))
        assert u[i] == max(game.offers[i, j][0] - game.offers[i, j][1] * x[j] for j in range(len(x)))
    # Check the defender against every pure choice, independently of the cutoff argument.
    assert sum(s * v for s, v in zip(scores, x)) == max(
        sum(scores[j] for j in selection) for selection in combinations(range(len(x)), game.resources))
    assert len(defense) <= len(x) and sum(defense.values()) == 1
    assert all(m > 0 and len(s) == len(set(s)) == game.resources for s, m in defense.items())
    assert all(sum(m for s, m in defense.items() if j in s) == x[j] for j in range(len(x)))


def compare(game, support, exact):
    var = symbols(game)
    truth = literal(game, support, exact, var)
    candidate, _ = reconstructed(game, support, exact, var)
    solver = z3.SolverFor("QF_LRA")
    solver.add(z3.Xor(truth, candidate))
    expect(solver, z3.unsat, "literal cutoff and linear-cell unions differ on a real profile")
    result = solve_linear_cells(game, support, exact)
    direct = z3.SolverFor("QF_LRA")
    direct.add(truth)
    expect(direct, z3.sat if result is not None else z3.unsat, "support decision")
    if result is not None:
        check_profile(game, support, exact, result)
    return result


def require_at(game, support, exact, pins):
    var = symbols(game)
    body, _ = reconstructed(game, support, exact, var)
    solver = z3.SolverFor("QF_LRA")
    solver.add(body, *pins(var))
    expect(solver, z3.sat, "targeted witness and cutoff")


def cancel_to_forest(masses):
    """Delete positive bipartite cycles, preserving every row and column load."""
    result = dict(masses)
    while True:
        tree = {}
        cycle = None
        for edge, value in sorted(result.items()):
            if not value:
                continue
            i, j = edge
            a, b = ("type", i), ("target", j)
            parent = {a: (None, None)}
            todo = [a]
            while todo and b not in parent:
                v = todo.pop()
                for w, e in tree.get(v, ()):
                    if w not in parent:
                        parent[w] = v, e
                        todo.append(w)
            if b in parent:
                cycle = [edge]
                v = b
                while v != a:
                    v, e = parent[v]
                    cycle.append(e)
                break
            tree.setdefault(a, []).append((b, edge))
            tree.setdefault(b, []).append((a, edge))
        if cycle is None:
            return result
        assert len(cycle) >= 4 and len(cycle) % 2 == 0
        delta = min(result[e] for e in cycle[::2])
        for k, e in enumerate(cycle):
            result[e] += delta if k % 2 else -delta


def forest_regression(flat):
    f = {e: F(1, 4) for e in flat.offers}
    x, lam = (F(1, 2), F(1, 2)), F(1, 2)
    u = tuple(flat.offers[i, 0][0] - flat.offers[i, 0][1] * x[0] for i in range(2))
    before = Profile(x, u, f, lam, realize_coverage(x, 1), ((F(1, 2), F(1, 2)),) * 2)
    check_profile(flat, set(f), True, before)
    new = cancel_to_forest(f)
    forest = {e for e, amount in new.items() if amount > 0}
    assert len(forest) == 2 and all(sum(new[i, j] for j in range(2)) == flat.masses[i] for i in range(2))
    assert all(sum(new[i, j] for i in range(2)) == F(1, 2) for j in range(2))
    attacks = tuple(tuple(new[i, j] / flat.masses[i] for j in range(2)) for i in range(2))
    check_profile(flat, forest, True, before._replace(attack_masses=new, attack_probabilities=attacks))
    rebuilt = solve_linear_cells(flat, forest, exact=True)
    assert rebuilt is not None
    check_profile(flat, forest, True, rebuilt)


def fixtures():
    one = [[1, 1], [1, 1]]
    flat = make_game((F(1, 2),) * 2, (1, 1), ((-3, -3), (-3, -3)), one, 1)
    rigid = make_game((F(1, 2),) * 2, (1, 2), ((0, 1), (0, 2)), ((1, 1), (1, 2)), 1)
    bad = make_game((F(1, 2),) * 2, (1, 2), ((0, 0), (1, 0)), one, 1)
    diag = make_game((F(1, 3), F(2, 3)), (1, 3), ((2, -2), (-2, 2)), one, 1)
    floor = make_game((1,), (1, 1), ((F(1, 2), 0),), ((1, 1),), 1)
    iso = make_game((1,), (1, 3, 5), ((3, -2, -2),), ((2, 3, 1),), 2)
    saturate = make_game((1,), (1, 2), ((0, 1),), ((1, 1),), 1)
    joined = make_game((F(1, 2),) * 2, (2, 1, 2),
                       ((1, 1, -3), (-3, -3, 2)), ((1, 2, 1), (1, 1, 1)), 1)
    return (flat, rigid, bad, diag, floor, iso, saturate, joined)


def targeted(cases):
    flat, rigid, bad, diag, floor, iso, saturate, _ = cases
    full = set(flat.offers)
    require_at(flat, full, True, lambda var: [var[0][0] == q(F(1, 2)), var[3] == q(F(1, 2))])
    require_at(rigid, full, True, lambda var: [var[0][0] == 0, var[0][1] == 1, var[3] == q(F(2, 3)),
                                             var[2][0, 0] == q(F(1, 12))])
    assert compare(bad, full, False) is None
    diagonal = {(0, 0), (1, 1)}
    for cutoff in (F(1, 3), F(7, 9), F(2)):
        require_at(diag, diagonal, True, lambda var: [var[3] == q(cutoff)])
    require_at(floor, set(floor.offers), True, lambda var: [var[0][0] == q(F(3, 4)), var[0][1] == q(F(1, 4))])
    require_at(iso, {(0, 0)}, True, lambda var: [var[0][1] == q(F(1, 3)), var[3] == 0])
    require_at(saturate, set(saturate.offers), False,
               lambda var: [var[0][0] == 0, var[0][1] == 1, var[2][0, 0] == 0])
    # The unused edge has zero slope and is globally dominant in the second game.
    for off_payoff, feasible in ((-1, True), (6, False)):
        zero_off = make_game((1,), (1, 1), ((3, off_payoff),), ((1, 0),), 1)
        assert (compare(zero_off, {(0, 0)}, True) is not None) == feasible
    for r, cutoff in ((0, F(13)), (2, F(0))):
        budget = Game(flat.masses, flat.gains, flat.offers, r)
        require_at(budget, full, True, lambda var: [var[3] == q(cutoff)])
        assert compare(budget, full, True) is not None


def edge_sets(game):
    edges = tuple(game.offers)
    for mask in range(1 << len(edges)):
        yield {e for bit, e in enumerate(edges) if mask >> bit & 1}


def main():
    cases = fixtures()
    targeted(cases)
    forest_regression(cases[0])
    totals = Counter()
    for game in cases:
        for support in edge_sets(game):
            totals["supports"] += 1
            for exact in (False, True):
                result = compare(game, support, exact)
                totals["modes"] += 1
                if result is not None:
                    totals["exact" if exact else "weak"] += 1
    rng = Random(1780)
    for _ in range(16):
        m, n = rng.randint(1, 3), rng.randint(2, 4)
        weights = [rng.randint(1, 6) for _ in range(m)]
        a = [[rng.randint(-3, 4) for _ in range(n)] for _ in range(m)]
        b = [[rng.randint(1, 5) for _ in range(n)] for _ in range(m)]
        game = make_game([F(w, sum(weights)) for w in weights], [rng.randint(1, 5) for _ in range(n)],
                         a, b, rng.randint(0, n))
        for _ in range(4):
            support = {(i, rng.randrange(n)) for i in range(m)}
            support.update(e for e in game.offers if rng.randrange(3) == 0)
            totals["supports"] += 1
            for exact in (False, True):
                result = compare(game, support, exact)
                totals["modes"] += 1
                if result is not None:
                    totals["exact" if exact else "weak"] += 1
    print(f"{totals['supports']} proposed supports, {totals['modes']} two-way full-profile equivalence checks.")
    print(f"{totals['weak']} weak support witnesses, {totals['exact']} exact-positive witnesses, all verified against pure defenses.")
    print("Targeted cutoff endpoints, rigid mixed bounds, interior ties, isolated targets, off-support zero slopes and both budget endpoints passed.")
    print("Dense 2x2 equilibrium reduced to a two-edge forest preserving x, utilities, cutoff and loads; reconstruction on the same game passed.")


if __name__ == "__main__":
    main()
