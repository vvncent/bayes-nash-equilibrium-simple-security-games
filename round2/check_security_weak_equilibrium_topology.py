"""Exact finite tests of the conditional-strategy weak security-game LCP.

Run with Python 3 and z3-solver. The Z3 checks cover all real strategies
of each listed game. Independent integer arithmetic checks every principal
minor for three fixed small matrices. The tests do not prove contractibility.
"""

from collections import Counter
from dataclasses import dataclass
from fractions import Fraction as F
from itertools import combinations
from math import lcm
from random import Random

import z3


def q(value):
    value = F(value)
    return z3.RealVal(f"{value.numerator}/{value.denominator}")


def check(solver, expected, label):
    actual = solver.check()
    if actual != expected:
        evidence = solver.model() if actual == z3.sat else solver.reason_unknown()
        raise AssertionError(f"{label}: expected {expected}, got {actual}: {evidence}")


def example(formula, label):
    solver = z3.SolverFor("QF_LRA")
    solver.add(formula)
    check(solver, z3.sat, label)


def prove(formula, label):
    solver = z3.SolverFor("QF_LRA")
    solver.add(z3.Not(formula))
    check(solver, z3.unsat, label)


def largest(values):
    value = values[0]
    for other in values[1:]:
        value = z3.If(value >= other, value, other)
    return value


def positive(value):
    return z3.If(value >= 0, value, q(0))


def descending(values):
    ordered = []
    for value in values:
        carry = value
        for i, old in enumerate(ordered):
            ordered[i], carry = z3.If(old >= carry, old, carry), z3.If(old >= carry, carry, old)
        ordered.append(carry)
    return ordered


def vector_sum(items):
    return z3.Sum(list(items))


@dataclass(frozen=True)
class Game:
    name: str
    priors: tuple
    gains: tuple
    intercepts: tuple
    slopes: tuple
    resources: int


def scores_of(game, sigma):
    return [q(d)*vector_sum(q(p)*row[j] for p, row in zip(game.priors, sigma))
            for j, d in enumerate(game.gains)]


def exchange_optimal(x, scores):
    # An infinitesimal transfer from covered j to nonsaturated k cannot improve payoff.
    return z3.And(*(z3.Or(x[j] == 0, x[k] == 1, scores[j] >= scores[k])
                    for j in range(len(x)) for k in range(len(x)) if j != k))


def cut_valid(x, scores, cutoff):
    return z3.And(*(z3.And(z3.Or(value == 0, score >= cutoff),
                           z3.Or(value == 1, score <= cutoff))
                    for value, score in zip(x, scores)))


def direct(game, x, sigma, scores):
    conditions = [vector_sum(x) == game.resources, exchange_optimal(x, scores)]
    conditions.extend(z3.And(value >= 0, value <= 1) for value in x)
    for row, intercept, slope in zip(sigma, game.intercepts, game.slopes):
        utility = [q(a)-q(b)*value for a, b, value in zip(intercept, slope, x)]
        conditions.append(vector_sum(row) == 1)
        for j, probability in enumerate(row):
            conditions.extend((probability >= 0, z3.Or(probability == 0,
                               z3.And(*(utility[j] >= other for other in utility)))))
    return z3.And(*conditions)


def shifted(game, x):
    result = []
    for a, b in zip(game.intercepts, game.slopes):
        offset = 1 + max(slope-intercept for slope, intercept in zip(b, a))
        result.append([q(intercept+offset)-q(slope)*value
                       for intercept, slope, value in zip(a, b, x)])
    return result


def lcp(game, x, sigma, scores, offers, t, u, lam):
    pairs = [(lam, game.resources-vector_sum(x))]
    pairs.extend((cap, 1-value) for cap, value in zip(t, x))
    pairs.extend((value, lam-1+cap-score) for value, cap, score in zip(x, t, scores))
    for row, row_offers, best in zip(sigma, offers, u):
        pairs.append((best, 1-vector_sum(row)))
        pairs.extend((probability, best-offer) for probability, offer in zip(row, row_offers))
    return z3.And(*(z3.And(var >= 0, slack >= 0, z3.Or(var == 0, slack == 0))
                    for var, slack in pairs))


def check_game(game):
    m, n = len(game.priors), len(game.gains)
    assert sum(game.priors) == 1 and all(p >= 0 for p in game.priors)
    assert m == len(game.intercepts) == len(game.slopes) and 0 < game.resources < n
    assert all(len(row) == n for row in game.intercepts+game.slopes)
    assert all(d >= 0 for d in game.gains) and all(b >= 0 for row in game.slopes for b in row)
    x = [z3.Real(f"x{j}") for j in range(n)]
    sigma = [[z3.Real(f"s{i}_{j}") for j in range(n)] for i in range(m)]
    t = [z3.Real(f"t{j}") for j in range(n)]
    u = [z3.Real(f"u{i}") for i in range(m)]
    lam, test = z3.Reals("shifted_lambda independent_cutoff")
    scores = scores_of(game, sigma)
    offers = shifted(game, x)
    best = [largest(row) for row in offers]
    direct_bne = direct(game, x, sigma, scores)
    lifted = lcp(game, x, sigma, scores, offers, t, u, lam)
    ordered = descending(scores)
    low, high = ordered[game.resources], ordered[game.resources-1]
    cutoff = lam-1
    named_fiber = z3.And(direct_bne, low <= cutoff, cutoff <= high,
                         *(value == want for value, want in zip(u, best)),
                         *(cap == positive(score-cutoff) for cap, score in zip(t, scores)))
    example(lifted, f"{game.name} has an LCP solution")
    prove(lifted == named_fiber, f"{game.name} all direct BNE lifts and their only multipliers")
    prove(z3.Implies(direct_bne, cut_valid(x, scores, test) ==
                     z3.And(low <= test, test <= high)), f"{game.name} full cutoff interval")
    canonical_t = [positive(score-high) for score in scores]
    prove(direct_bne == lcp(game, x, sigma, scores, offers, canonical_t, best, 1+high),
          f"{game.name} canonical upper-order-statistic section")
    if game.name == "zero_prior_free":
        for first in (0, F(1, 2), 1):
            example(z3.And(lifted, x[0] == 1, sigma[0][0] == 1,
                           sigma[1][0] == q(first)),
                    f"free zero-prior row admits conditional probability {first}")
    if game.name == "zero_prior_strict":
        prove(z3.Implies(lifted, z3.And(sigma[0][0] == 1, sigma[1][1] == 1,
                         x[0] == 1, scores[0] == 1, scores[1] == 0)),
              "the zero-prior row responds strictly while contributing no score")


def generic_cutoff_checks():
    count = 0
    for n in range(2, 7):
        x = [z3.Real(f"generic_x{j}") for j in range(n)]
        scores = [z3.Real(f"generic_score{j}") for j in range(n)]
        value = z3.Real("candidate_cutoff")
        ordered = descending(scores)
        for r in range(1, n):
            optimal = z3.And(vector_sum(x) == r, exchange_optimal(x, scores),
                             *(z3.And(v >= 0, v <= 1) for v in x), *(s >= 0 for s in scores))
            low, high = ordered[r], ordered[r-1]
            prove(z3.Implies(optimal, cut_valid(x, scores, value) ==
                             z3.And(low <= value, value <= high)),
                  f"all optimal points and scores, n={n}, r={r}")
            count += 1
    return count


def conditional_matrix(game):
    """Derivatives of the displayed slack vector in (sigma,t,lambda,u,x) order."""
    labels = ([("s", i, j) for i in range(len(game.priors)) for j in range(len(game.gains))]
              + [("t", j) for j in range(len(game.gains))] + [("lambda",)]
              + [("u", i) for i in range(len(game.priors))]
              + [("x", j) for j in range(len(game.gains))])
    index = {label: k for k, label in enumerate(labels)}
    matrix = [[0]*len(labels) for _ in labels]
    for i, prior in enumerate(game.priors):
        u = index["u", i]
        for j, gain in enumerate(game.gains):
            s, x = index["s", i, j], index["x", j]
            matrix[s][u], matrix[s][x] = 1, game.slopes[i][j]
            matrix[u][s], matrix[x][s] = -1, -gain*prior
    lam = index[("lambda",)]
    for j in range(len(game.gains)):
        t, x = index["t", j], index["x", j]
        matrix[t][x], matrix[lam][x] = -1, -1
        matrix[x][t], matrix[x][lam] = 1, 1
    # Positive scaling of the whole matrix preserves the sign of every minor.
    scale = lcm(*(F(v).denominator for row in matrix for v in row))
    return [[int(v*scale) for v in row] for row in matrix]


def determinant(matrix):
    """Bareiss elimination with exact integer divisions and row pivoting."""
    n = len(matrix)
    if n == 0:
        return 1
    a = [row[:] for row in matrix]
    sign = previous = 1
    for k in range(n-1):
        pivot_row = next((i for i in range(k, n) if a[i][k]), None)
        if pivot_row is None:
            return 0
        if pivot_row != k:
            a[k], a[pivot_row] = a[pivot_row], a[k]
            sign = -sign
        pivot = a[k][k]
        for i in range(k+1, n):
            factor = a[i][k]
            for j in range(k+1, n):
                numerator = a[i][j]*pivot-factor*a[k][j]
                assert numerator % previous == 0
                a[i][j] = numerator // previous
            a[i][k] = 0
        previous = pivot
    return sign*a[-1][-1]


def all_minors(game):
    matrix = conditional_matrix(game)
    n = len(matrix)
    counts = Counter()
    for size in range(1, n+1):
        for cut in combinations(range(n), size):
            value = determinant([[matrix[i][j] for j in cut] for i in cut])
            assert value >= 0, (game.name, cut, value)
            counts["positive" if value else "zero"] += 1
    assert sum(counts.values()) == 2**n-1 and counts["positive"] and counts["zero"]
    return counts


def rank_one_normal_map():
    # M = [[1,1],[1,1]], q = (-1,-1). With z=y_+, the normal map
    # (M+eps I)z + (y-z) is evaluated at -q=(1,1).
    y = z3.Reals("normal_y0 normal_y1")
    z = [positive(v) for v in y]
    for eps in (0, 1, F(1, 2), F(1, 16)):
        normal_fiber = z3.And(*(vector_sum(z)+q(eps)*z[i]+y[i]-z[i] == 1
                                for i in range(2)))
        if eps == 0:
            expected = z3.And(y[0] >= 0, y[1] >= 0, vector_sum(y) == 1)
        else:
            point = q(1/F(2+eps))
            expected = z3.And(y[0] == point, y[1] == point)
        prove(normal_fiber == expected, f"rank-one normal-map fiber at epsilon={eps}")


def games():
    suite = [
        Game("flat_everywhere", (1,), (0, 0), ((-2, -2),), ((0, 0),), 1),
        Game("flat_attacker", (1,), (1, 1), ((2, 2),), ((0, 0),), 1),
        Game("flat_defender", (1,), (0, 0), ((1, 1),), ((1, 1),), 1),
        Game("zero_prior_free", (1, 0), (1, 1), ((5, 0), (2, 2)), ((1, 1), (0, 0)), 1),
        Game("zero_prior_strict", (1, 0), (1, 1), ((5, 0), (0, 3)), ((1, 1), (0, 1)), 1),
        Game("zero_prior_first", (0, 1), (2, 0), ((0, 0), (-2, -1)), ((3, 0), (0, 2)), 1),
        Game("fractional_data", (F(1, 4), F(3, 4)), (F(3, 2), 2),
             ((-2, 0), (3, -4)), ((F(1, 2), 2), (1, F(3, 2))), 1),
        Game("mixed_targets", (F(1, 3), 0, F(2, 3)), (0, 2, F(1, 3)),
             ((0, 0, 1), (0, 2, 3), (2, 1, 3)), ((1, 0, 2), (0, 2, 0), (0, 0, 3)), 2),
        Game("published_nonconvex", (F(1, 3),)*3, (1, 1, 1),
             ((2, 3, 0), (3, 2, 0), (0, 0, 2)), ((1, 6, 1), (4, 1, 1), (1, 1, 1)), 1),
    ]
    rng = Random(32711)
    for k in range(9):
        m, n = 2+k%2, 2+(k//2)%2
        p = [rng.randrange(1, 4) for _ in range(m)]
        if k%3 == 0:
            p[k%m] = 0
        priors = tuple(F(z, sum(p)) for z in p)
        a = tuple(tuple(rng.randrange(-3, 4) for _ in range(n)) for _ in range(m))
        b = tuple(tuple(rng.randrange(4) for _ in range(n)) for _ in range(m))
        suite.append(Game(f"seeded{k}", priors, tuple(rng.randrange(4) for _ in range(n)),
                          a, b, 1+k%(n-1)))
    return suite


if __name__ == "__main__":
    suite = games()
    for g in suite:
        check_game(g)
    print(f"{len(suite)} games: LCP existence, exact full fibers, canonical section, and cutoff intervals.")
    print(f"{generic_cutoff_checks()} target-count/budget pairs: exact cutoff intervals for all admissible real scores and optimal covers.")
    counts = Counter()
    for name in ("flat_everywhere", "zero_prior_first", "fractional_data"):
        counts.update(all_minors(next(g for g in suite if g.name == name)))
    print(f"{sum(counts.values())} nonempty principal minors on three normalized matrices: "
          f"{counts['positive']} positive, {counts['zero']} zero.")
    rank_one_normal_map()
    print("Rank-one P0 example: one complete unperturbed segment and three exact singleton regularized fibers.")
