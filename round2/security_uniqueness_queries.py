"""Recover a security-game BNE with nonadaptive one-resource nonuniqueness queries.

For canonical strict one-resource H, prepare_queries(H) returns a plan. Each
entry of plan.queries has a .game; the Boolean answer is True iff that game
has more than one full equilibrium. plan.recover(answers) uses only rational
arithmetic and the unrooted forest decoder. For an arbitrary original game,
run unique_one_resource(original), prepare queries on .target, and call the
reduction's .decode on the recovered profile. This is an oracle reduction,
not an implementation of the decision oracle.
"""

from dataclasses import dataclass
from fractions import Fraction as F
from itertools import combinations
from math import lcm

from security_equilibrium_uniqueness import Game, Profile
from security_one_resource_forest import equilibrium_from_forest


def _solve(equations, n):
    """Unique solution of a possibly overdetermined rational affine system."""
    rows = [list(map(F, lhs))+[F(rhs)] for lhs, rhs in equations]
    used = 0
    for j in range(n):
        pivot = next((i for i in range(used, len(rows)) if rows[i][j]), None)
        if pivot is None:
            raise ValueError("The decision answers do not determine the coverage")
        rows[used], rows[pivot] = rows[pivot], rows[used]
        divisor = rows[used][j]
        rows[used] = [value/divisor for value in rows[used]]
        for i, row in enumerate(rows):
            scale = row[j]
            if i != used and scale:
                rows[i] = [a-scale*b for a, b in zip(row, rows[used])]
        used += 1
    if any(row[-1] for row in rows[used:]):
        raise ValueError("The decision answers are inconsistent")
    return tuple(row[-1] for row in rows[:n])


@dataclass(frozen=True)
class Query:
    key: tuple
    game: Game


@dataclass(frozen=True)
class QueryPlan:
    target: Game
    epsilon: F
    queries: tuple

    def recover(self, answers):
        """Return the certified original H equilibrium, with True = nonunique."""
        flags = tuple(answers)
        if len(flags) != len(self.queries) or any(type(v) is not bool for v in flags):
            raise ValueError("Expected one Boolean nonuniqueness answer per query")
        g = self.target
        n = len(g.gains)
        if n == 1:
            return Profile((1,), ((1,),)*len(g.priors))
        equations = [([F(1)]*n, F(1))]
        for item, active in zip(self.queries, flags):
            if not active:
                continue
            key, row = item.key, [F(0)]*n
            if key[0] == "tie":
                _, i, j, k = key
                row[j], row[k] = g.slopes[i][j], -g.slopes[i][k]
                value = g.intercepts[i][j]-g.intercepts[i][k]
            else:
                _, j, value = key
                row[j] = F(1)
            equations.append((row, value))
        x = _solve(equations, n)
        if any(v < 0 or v > 1 for v in x):
            raise ValueError("Decision answers yield out-of-bounds coverage")
        utilities = [tuple(a-b*v for a, b, v in zip(row, slopes, x))
                     for row, slopes in zip(g.intercepts, g.slopes)]
        for query, answer in zip(self.queries, flags):
            if query.key[0] == "tie":
                _, i, j, k = query.key
                correct = utilities[i][j] == utilities[i][k]
            else:
                _, j, value = query.key
                correct = x[j] == value
            if answer != correct:
                raise ValueError("A decision answer disagrees with the reconstructed coverage")
        tight = []
        for i, row in enumerate(utilities):
            best = max(row)
            tight.extend((i, j) for j, value in enumerate(row) if value == best)
        profile = equilibrium_from_forest(g, tight)
        if profile is None or profile.coverage != x:
            raise ValueError("Queries did not recover a verified canonical equilibrium")
        return profile


def _mass_scale(game):
    reciprocals = [1/d for d in game.gains]
    denominator = lcm(*(v.denominator for v in (*game.priors, *reciprocals)))
    return 1/(4*denominator**2*max(F(1), sum(reciprocals)))


def prepare_queries(game: Game) -> QueryPlan:
    """Build all queries before receiving any answer; input must have the isolation promise."""
    if (not isinstance(game, Game) or game.resources != 1 or min(game.priors) <= 0
            or min(game.gains) <= 0 or any(b <= 0 for row in game.slopes for b in row)):
        raise ValueError("Queries require the canonical positive one-resource target")
    n, m = len(game.gains), len(game.priors)
    if n == 1:
        return QueryPlan(game, F(0), ())
    if m < n:
        raise ValueError("Missing the final n dedicated types")
    for j in range(n):
        i = m-n+j
        if any(game.intercepts[i][j]-game.slopes[i][j] <= game.intercepts[i][k]
               for k in range(n) if k != j):
            raise ValueError("The last n types must be strictly dedicated in target order")
    epsilon = _mass_scale(game)
    priors = tuple(w/(1+epsilon) for w in (*game.priors, epsilon))
    queries = []
    for i in range(m):
        for j, k in combinations(range(n), 2):
            low = min(game.intercepts[i][j]-game.slopes[i][j],
                      game.intercepts[i][k]-game.slopes[i][k])-1
            a, b = [low]*n, [F(1)]*n
            for t in (j, k):
                a[t], b[t] = game.intercepts[i][t], game.slopes[i][t]
            probe = Game(priors, game.gains, game.intercepts+(tuple(a),), game.slopes+(tuple(b),), 1)
            queries.append(Query(("tie", i, j, k), probe))
    # Each original row can always obtain more than its appended dummy offer.
    dummy_a = tuple(row+(max(a-b for a, b in zip(row, slope))-1,)
                    for row, slope in zip(game.intercepts, game.slopes))
    dummy_b = tuple(row+(1,) for row in game.slopes)
    dummy_gain = min(game.gains)/(2*n)
    for j in range(n):
        for bound in (0, 1):
            a = tuple(bound if t == j else -2 for t in range(n))+(0,)
            b = (F(1),)*(n+1)
            probe = Game(priors, game.gains+(dummy_gain,), dummy_a+(a,), dummy_b+(b,), 1)
            queries.append(Query(("bound", j, bound), probe))
    return QueryPlan(game, epsilon, tuple(queries))
