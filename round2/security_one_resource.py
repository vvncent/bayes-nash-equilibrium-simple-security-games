"""Reduce an explicitly listed security game to one uniquely solvable game.

Calling unique_one_resource builds the sole oracle input. Its decode method
accepts that game's equilibrium as a Profile and returns an exact sparse
FullProfile of the original game. No equilibrium search runs in the compiler.
"""

from dataclasses import dataclass
from fractions import Fraction as F
from math import lcm

import z3

from check_security_support_reconstruction import realize_coverage
from security_equilibrium_uniqueness import FullProfile, Game, Profile
from wardrop.check_wardrop import exact, q as _q


def cap_game(game):
    """Encode positive target gains and an interior budget with one resource."""
    n, r = len(game.gains), game.resources
    if not 0 < r < n or min(game.gains) <= 0:
        raise ValueError("Cap encoding needs positive gains and an interior budget")
    floor_score = 1 + max(game.gains)
    enforcers = tuple(floor_score / gain for gain in game.gains)
    population = 1 + sum(enforcers)
    dummy_penalty = 1 + max(abs(a) for row in game.intercepts for a in row)
    dummy_penalty += r * max(b for row in game.slopes for b in row)
    intercepts = [row + (-dummy_penalty,) for row in game.intercepts]
    slopes = [tuple(r * b for b in row) + (1,) for row in game.slopes]
    for j in range(n):
        intercepts.append(tuple(1 if k == j else -3 for k in range(n)) + (0,))
        slopes.append(tuple(r if k == j else 1 for k in range(n)) + (1,))
    return Game(tuple(mass / population for mass in game.priors + enforcers),
                game.gains + (floor_score / (2 * population),),
                intercepts, slopes, 1)


def _with_dedicated_types(game):
    n = len(game.gains)
    intercepts = tuple(tuple(2 if k == j else -2 for k in range(n)) for j in range(n))
    return Game(game.priors + (F(0),) * n, game.gains, game.intercepts + intercepts,
                game.slopes + ((F(1),) * n,) * n, game.resources)


def _denominator_and_height(values):
    values = list(values)
    denominator = lcm(*(z.denominator for z in values))
    height = max([denominator, 4] + [abs(int(z * denominator)) for z in values])
    return denominator, height


def isolate_game(game):
    """Return a strict game's uniquely solvable marginal perturbation and δ."""
    n = len(game.gains)
    if (not 0 < game.resources < n or min(game.gains) <= 0 or min(game.priors) <= 0
            or any(b <= 0 for row in game.slopes for b in row)):
        raise ValueError("Isolation needs strictly positive data and an interior budget")
    base = _with_dedicated_types(game)
    m, r = len(base.priors), game.resources
    numbers = list(base.priors + base.gains) + [1 / d for d in base.gains]
    for row in base.intercepts + base.slopes:
        numbers.extend(row)
    denominator, height = _denominator_and_height(numbers)
    height = max(height, 1 + r)
    dimension = m * n + m + n + 2
    determinant_bound = (dimension * height) ** (dimension + 2)
    coefficient_bound = 4 * dimension ** 2 * (r + 1) * height ** 2 * determinant_bound
    exponent = max(8, 4 * coefficient_bound, 4 * denominator * determinant_bound).bit_length()
    delta = F(1, 1 << exponent)
    masses = [mass + F(1, 1 << ((i + 1) * exponent)) for i, mass in enumerate(base.priors)]
    total = sum(masses)
    intercepts = [
        tuple(a + F(1, 1 << ((i * n + j + 1) * exponent)) for j, a in enumerate(row))
        for i, row in enumerate(base.intercepts)
    ]
    return Game(tuple(mass / total for mass in masses), base.gains, intercepts, base.slopes, r), delta


def _positive_effects(game):
    if min(game.gains) > 0 and all(b > 0 for row in game.slopes for b in row):
        return game
    numbers = list(game.priors + game.gains)
    for row in game.intercepts + game.slopes:
        numbers.extend(row)
    denominator, height = _denominator_and_height(numbers)
    # In chapter 3's pairwise pattern LP, row RHSs include a difference
    # between two intercepts or the cap 1+max d. The slack is unscaled
    # before multiplying each row by this common denominator.
    height = max(2 * height, denominator * (1 + game.resources))
    dimension = len(game.gains) * (len(game.priors) + 1) + 2
    epsilon = F(1, 8 * (dimension * height) ** dimension)
    return Game(game.priors, tuple(d + epsilon for d in game.gains), game.intercepts,
                tuple(tuple(b + epsilon for b in row) for row in game.slopes), game.resources)


def _repair_profile(game, pattern):
    """One rational LP with fixed allowed edges and coverage bound labels."""
    solver = z3.SolverFor("QF_LRA")
    r, n = game.resources, len(game.gains)
    x = [z3.FreshReal("coverage") for _ in range(n)]
    theta = z3.FreshReal("cutoff")
    solver.add(z3.Sum(x) == r, theta >= 0)
    columns = [[] for _ in x]
    rows = []
    for mass, intercepts, slopes, old in zip(game.priors, game.intercepts,
                                            game.slopes, pattern.strategies):
        best = z3.FreshReal("best")
        row = [z3.FreshReal("attack") for _ in x]
        solver.add(z3.Sum(row) == _q(mass))
        for j, (a, b) in enumerate(zip(intercepts, slopes)):
            offer = _q(a) - _q(b) * x[j]
            solver.add(row[j] >= 0, best >= offer)
            solver.add(best == offer if old[j] > 0 else row[j] == 0)
            columns[j].append(row[j])
        rows.append(row)
    for j, old in enumerate(pattern.coverage):
        score = _q(game.gains[j]) * z3.Sum(columns[j])
        solver.add(x[j] >= 0, x[j] <= 1)
        if old == 0:
            solver.add(x[j] == 0, score <= theta)
        elif old == 1:
            solver.add(x[j] == 1, score >= theta)
        else:
            solver.add(score == theta)
    result = solver.check()
    if result != z3.sat:
        raise ValueError(f"The proposed equilibrium's pattern could not be repaired ({result})")
    model = solver.model()
    coverage = tuple(exact(model, v) for v in x)
    # A zero-mass dedicated row in the base game carries no conditional
    # information. Give it a true best response to complete the profile.
    strategies = []
    for i, mass in enumerate(game.priors):
        if mass > 0:
            strategies.append(tuple(exact(model, v) / mass for v in rows[i]))
        else:
            strategies.append(_best_pure(game, i, coverage))
    return Profile(coverage, strategies)


def _best_pure(game, i, coverage):
    utility = [a - b * x for a, b, x in zip(game.intercepts[i], game.slopes[i], coverage)]
    j = utility.index(max(utility))
    return tuple(int(k == j) for k in range(len(coverage)))


@dataclass(frozen=True)
class Reduction:
    original: Game
    positive_rows: tuple
    retained: Game
    strict: Game
    capped: Game
    target: Game

    def decode(self, profile):
        n, r = len(self.original.gains), self.original.resources
        if r in (0, n):
            coverage = (F(int(r == n)),) * n
            strategies = [_best_pure(self.original, i, coverage) for i in range(len(self.original.priors))]
        else:
            before = _repair_profile(_with_dedicated_types(self.capped), profile)
            coverage = tuple(r * y for y in before.coverage[:n])
            decoded = Profile(coverage, [row[:n] for row in before.strategies[:len(self.strict.priors)]])
            if self.retained is not self.strict:
                decoded = _repair_profile(self.retained, decoded)
            coverage = decoded.coverage
            restored = dict(zip(self.positive_rows, decoded.strategies))
            strategies = [restored[i] if i in restored else _best_pure(self.original, i, coverage)
                          for i in range(len(self.original.priors))]
        return FullProfile(realize_coverage(coverage, r), strategies)


def unique_one_resource(game):
    """Build a one-resource, positive-effect game with exactly one full BNE."""
    n = len(game.gains)
    if game.resources in (0, n):
        fixed = Game((1,), (1,), ((1,),), ((1,),), 1)
        return Reduction(game, (), game, game, fixed, fixed)
    keep = tuple(i for i, p in enumerate(game.priors) if p > 0)
    retained = Game([game.priors[i] for i in keep], game.gains,
                    [game.intercepts[i] for i in keep], [game.slopes[i] for i in keep], game.resources)
    strict = _positive_effects(retained)
    capped = cap_game(strict)
    target, _ = isolate_game(capped)
    return Reduction(game, keep, retained, strict, capped, target)
