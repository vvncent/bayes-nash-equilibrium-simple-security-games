"""Exact uniqueness of a supplied security-game equilibrium.

Game(priors, gains, intercepts, slopes, resources) and
Profile(coverage, strategies) accept rationals convertible to Fraction.
The strategies are conditional attacker distributions, even for zero priors.
second_equilibrium(game, profile) returns another exact Profile or None when
the supplied marginal equilibrium is globally unique. For full strategies,
second_full_equilibrium(game, FullProfile(defense, strategies)) accepts
a sparse mapping or sequence of (r-subset, probability) pairs, using zero-based
target indices. It returns a sparse full equilibrium or None if it is unique.
Invalid input raises ValueError.

Each feasibility query uses only conjunctions of rational linear constraints.
At most 2*n*(1+m) queries suffice. The proof that the two fixed-opponent
sections detect every second equilibrium uses connectedness of the entire
equilibrium set and its finite union of products of polytopes.
"""

from dataclasses import dataclass
from fractions import Fraction as F
from itertools import combinations, islice
from operator import index
from typing import Optional

import z3

from check_security_support_reconstruction import realize_coverage
from wardrop.check_wardrop import exact, q as _q


def _rows(table):
    return tuple(tuple(F(v) for v in row) for row in table)


@dataclass(frozen=True)
class Game:
    priors: tuple
    gains: tuple
    intercepts: tuple
    slopes: tuple
    resources: int

    def __post_init__(self):
        p, d = tuple(map(F, self.priors)), tuple(map(F, self.gains))
        a, b = _rows(self.intercepts), _rows(self.slopes)
        m, n = len(p), len(d)
        if not m or sum(p) != 1 or min(p) < 0:
            raise ValueError("Attacker type priors must form a nonempty probability distribution")
        if not n or min(d) < 0:
            raise ValueError("The game needs at least one target and nonnegative defender gains")
        r = F(self.resources)
        if r.denominator != 1 or not 0 <= r <= n:
            raise ValueError("The resource budget must be an integer from zero to the target count")
        if len(a) != m or len(b) != m or any(len(row) != n for row in a+b):
            raise ValueError("Each payoff table must have one entry per type and target")
        if any(value < 0 for row in b for value in row):
            raise ValueError("Attacker coverage effects must be nonnegative")
        object.__setattr__(self, "priors", p)
        object.__setattr__(self, "gains", d)
        object.__setattr__(self, "intercepts", a)
        object.__setattr__(self, "slopes", b)
        object.__setattr__(self, "resources", int(r))


@dataclass(frozen=True)
class Profile:
    coverage: tuple
    strategies: tuple

    def __post_init__(self):
        object.__setattr__(self, "coverage", tuple(map(F, self.coverage)))
        object.__setattr__(self, "strategies", _rows(self.strategies))


def _scores(game, strategies):
    return tuple(gain*sum(p*row[j] for p, row in zip(game.priors, strategies))
                 for j, gain in enumerate(game.gains))


def _utilities(game, coverage):
    return tuple(tuple(a-b*x for a, b, x in zip(intercepts, slopes, coverage))
                 for intercepts, slopes in zip(game.intercepts, game.slopes))


def _check_profile(game, profile):
    x, sigma = profile.coverage, profile.strategies
    n = len(game.gains)
    if len(x) != n or sum(x) != game.resources or any(not 0 <= t <= 1 for t in x):
        raise ValueError("The supplied coverage violates the defense budget or a target bound")
    if len(sigma) != len(game.priors) or any(
            len(row) != n or sum(row) != 1 or min(row) < 0 for row in sigma):
        raise ValueError("Each type needs a conditional probability distribution on all targets")
    for row, utilities in zip(sigma, _utilities(game, x)):
        best = max(utilities)
        if any(p and u != best for p, u in zip(row, utilities)):
            raise ValueError("The supplied attacker strategy uses a suboptimal target")
    scores = _scores(game, sigma)
    if sum(s*v for s, v in zip(scores, x)) != sum(sorted(scores, reverse=True)[:game.resources]):
        raise ValueError("The supplied defender strategy is suboptimal")


def _other_point(solver, variables, known):
    for var, coordinate in zip(variables, known):
        current = _q(coordinate)
        for halfspace in (var < current, var > current):
            solver.push()
            solver.add(halfspace)
            result = solver.check()
            if result == z3.unknown:
                raise RuntimeError(f"Linear feasibility returned unknown: {solver.reason_unknown()}")
            if result == z3.sat:
                model = solver.model()
                answer = tuple(exact(model, v) for v in variables)
                solver.pop()
                return answer
            solver.pop()
    return None


def second_equilibrium(game: Game, profile: Profile) -> Optional[Profile]:
    """Return a second marginal equilibrium, or None to certify uniqueness."""
    _check_profile(game, profile)
    known_x, known_sigma = profile.coverage, profile.strategies
    n = len(known_x)

    # First fiber: vary coverage, preserving both players' optimality.
    x = [z3.Real(f"uniqueness_x{j}") for j in range(n)]
    fixed_attacks = z3.SolverFor("QF_LRA")
    fixed_attacks.add(z3.Sum(x) == game.resources, *(z3.And(v >= 0, v <= 1) for v in x))
    scores = _scores(game, known_sigma)
    optimum = sum(score*v for score, v in zip(scores, known_x))
    fixed_attacks.add(z3.Sum([_q(score)*v for score, v in zip(scores, x)]) == _q(optimum))
    for i, row in enumerate(known_sigma):
        offers = [_q(a)-_q(b)*v for a, b, v in zip(game.intercepts[i], game.slopes[i], x)]
        for j, probability in enumerate(row):
            if probability:
                fixed_attacks.add(*(offers[j] >= other for other in offers))
    other_x = _other_point(fixed_attacks, x, known_x)
    if other_x is not None:
        return Profile(other_x, known_sigma)

    # Second fiber: vary conditional attacks, keeping coverage optimal.
    variables = []
    column_terms = [[] for _ in range(n)]
    fixed_coverage = z3.SolverFor("QF_LRA")
    for i, utility in enumerate(_utilities(game, known_x)):
        row = [z3.Real(f"uniqueness_s{i}_{j}") for j in range(n)]
        best = max(utility)
        fixed_coverage.add(z3.Sum(row) == 1, *(v >= 0 for v in row))
        for j, v in enumerate(row):
            if utility[j] < best:
                fixed_coverage.add(v == 0)
            column_terms[j].append(_q(game.priors[i]*game.gains[j])*v)
        variables.extend(row)
    scores = [z3.Sum(terms) for terms in column_terms]
    for j in range(n):
        if known_x[j] > 0:
            fixed_coverage.add(*(scores[j] >= scores[k] for k in range(n) if known_x[k] < 1))
    flat = tuple(p for row in known_sigma for p in row)
    other_sigma = _other_point(fixed_coverage, variables, flat)
    if other_sigma is None:
        return None
    return Profile(known_x, tuple(other_sigma[j:j+n] for j in range(0, len(flat), n)))


@dataclass(frozen=True)
class FullProfile:
    defense: tuple
    strategies: tuple

    def __post_init__(self):
        entries = self.defense.items() if hasattr(self.defense, "items") else self.defense
        weights = {}
        for selection, weight in entries:
            try:
                subset = tuple(sorted(index(j) for j in selection))
            except TypeError as error:
                raise ValueError("Pure defenses must contain integer target indices") from error
            if len(set(subset)) != len(subset) or (subset and subset[0] < 0):
                raise ValueError("A pure defense must list distinct nonnegative target indices")
            weight = F(weight)
            if weight < 0:
                raise ValueError("Pure defense probabilities must be nonnegative")
            if weight:
                weights[subset] = weights.get(subset, F(0))+weight
        if sum(weights.values()) != 1:
            raise ValueError("The defender's strategy must have total probability one")
        object.__setattr__(self, "defense", tuple(sorted(weights.items())))
        object.__setattr__(self, "strategies", _rows(self.strategies))

    def marginal(self, game: Game) -> Profile:
        coverage = [F(0)]*len(game.gains)
        for subset, weight in self.defense:
            if len(subset) != game.resources or (subset and subset[-1] >= len(coverage)):
                raise ValueError("Each positive pure defense must be a legal subset of targets")
            for j in subset:
                coverage[j] += weight
        return Profile(tuple(coverage), self.strategies)


def _redistribute_support(mix, fractional):
    # Every incidence column has r' ones on these k coordinates. Thus the
    # first k+1 columns are linearly dependent and each dependence has sum 0.
    selected = list(islice(mix, len(fractional)+1))
    z = [z3.Real(f"uniqueness_direction{i}") for i in range(len(selected))]
    dependence = z3.SolverFor("QF_LRA")
    for j in fractional:
        dependence.add(z3.Sum([v for v, subset in zip(z, selected) if j in subset]) == 0)
    # Scaling a nonzero direction permits some coordinate to equal 1.
    for v in z:
        dependence.push()
        dependence.add(v == 1)
        status = dependence.check()
        if status == z3.unknown:
            raise RuntimeError(f"Linear dependence returned unknown: {dependence.reason_unknown()}")
        if status == z3.sat:
            model = dependence.model()
            direction = [exact(model, w) for w in z]
            dependence.pop()
            step = min(mix[subset]/(-coefficient) for subset, coefficient in zip(selected, direction)
                       if coefficient < 0)
            shifted = dict(mix)
            for subset, coefficient in zip(selected, direction):
                shifted[subset] += step*coefficient
            return shifted
        dependence.pop()
    raise ArithmeticError("More than k incidence columns on k fractional targets were independent")


def _other_realization(game, x, defense):
    ones = tuple(j for j, value in enumerate(x) if value == 1)
    fractional = tuple(j for j, value in enumerate(x) if 0 < value < 1)
    k, residual = len(fractional), game.resources-len(ones)
    if not k or residual == 1 or residual == k-1:
        return None

    mix = dict(defense)
    if len(mix) > k:
        return _redistribute_support(mix, fractional)

    # An interior rank 2..k-2 hypersimplex has more than k face vertices.
    # Only the first s+1 candidates need be generated when support size s<=k.
    candidates = islice(combinations(fractional, residual), len(mix)+1)
    for part in candidates:
        vertex = tuple(sorted(ones+part))
        if vertex not in mix:
            break
    else:
        raise ArithmeticError("No missing vertex in a nonsimplex minimal face")
    included = set(vertex)
    step = min(x[j] if j in included else 1-x[j] for j in fractional)
    remaining = tuple((value-step*int(j in included))/(1-step) for j, value in enumerate(x))
    shifted = {subset: (1-step)*mass for subset, mass in realize_coverage(remaining, game.resources).items()}
    shifted[vertex] = shifted.get(vertex, F(0))+step
    return shifted


def second_full_equilibrium(game: Game, profile: FullProfile) -> Optional[FullProfile]:
    """Return a second equilibrium over explicit defenses, using sparse supports only."""
    known = profile.marginal(game)
    _check_profile(game, known)
    other_defense = _other_realization(game, known.coverage, profile.defense)
    if other_defense is not None:
        return FullProfile(other_defense, known.strategies)
    other = second_equilibrium(game, known)
    if other is None:
        return None
    defense = (profile.defense if other.coverage == known.coverage
               else realize_coverage(other.coverage, game.resources))
    return FullProfile(defense, other.strategies)
