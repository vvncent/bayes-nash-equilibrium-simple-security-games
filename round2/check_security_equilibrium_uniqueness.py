"""Compare the two-polytope uniqueness procedure to unrestricted BNE feasibility.

Run with Python 3 and z3-solver. The independent global model uses original
attacker maximizers and a defender cutoff, and permits both strategies to vary.
"""

from collections import Counter
from fractions import Fraction as F
from itertools import combinations

import z3

from check_security_weak_equilibrium_topology import games as topology_games
from security_equilibrium_uniqueness import (
    FullProfile, Game, Profile, second_equilibrium, second_full_equilibrium,
)


def q(value):
    value = F(value)
    return z3.RealVal(f"{value.numerator}/{value.denominator}")


def evaluate(model, variable):
    value = model.eval(variable, model_completion=True)
    return F(value.numerator_as_long(), value.denominator_as_long())


class GlobalEquilibria:
    def __init__(self, game):
        m, n = len(game.priors), len(game.gains)
        self.solver = z3.SolverFor("QF_LRA")
        self.x = [z3.Real(f"global_x{j}") for j in range(n)]
        self.sigma = [[z3.Real(f"global_s{i}_{j}") for j in range(n)] for i in range(m)]
        solver = self.solver
        solver.add(z3.Sum(self.x) == game.resources, *(z3.And(v >= 0, v <= 1) for v in self.x))
        for i, row in enumerate(self.sigma):
            best = z3.Real(f"global_best{i}")
            solver.add(z3.Sum(row) == 1)
            for j, p in enumerate(row):
                offer = q(game.intercepts[i][j]) - q(game.slopes[i][j])*self.x[j]
                solver.add(p >= 0, best >= offer, z3.Or(p == 0, best == offer))
        cutoff = z3.Real("global_cutoff")
        solver.add(cutoff >= 0, cutoff <= q(max(game.gains)))
        for j, defense in enumerate(self.x):
            score = q(game.gains[j])*z3.Sum([q(p)*s[j] for p, s in zip(game.priors, self.sigma)])
            solver.add(z3.Or(defense == 0, score >= cutoff), z3.Or(defense == 1, score <= cutoff))

    def pin(self, profile):
        return z3.And(*(v == q(x) for v, x in zip(self.x, profile.coverage)),
                      *(v == q(p) for row, old in zip(self.sigma, profile.strategies)
                        for v, p in zip(row, old)))

    def find(self, condition=True):
        self.solver.push()
        self.solver.add(condition)
        status = self.solver.check()
        if status == z3.unknown:
            raise AssertionError(self.solver.reason_unknown())
        profile = None
        if status == z3.sat:
            model = self.solver.model()
            profile = Profile(tuple(evaluate(model, v) for v in self.x),
                              tuple(tuple(evaluate(model, v) for v in row) for row in self.sigma))
        self.solver.pop()
        return profile


def check_seed(name, game, global_bne, supplied, counts):
    assert global_bne.find(global_bne.pin(supplied)) == supplied, (name, "invalid supplied equilibrium")
    alternate = second_equilibrium(game, supplied)
    unrestricted = global_bne.find(z3.Not(global_bne.pin(supplied)))
    assert (alternate is None) == (unrestricted is None), (name, supplied, alternate, unrestricted)
    if alternate is None:
        counts["unique"] += 1
    else:
        assert alternate != supplied and global_bne.find(global_bne.pin(alternate)) == alternate
        same_coverage = alternate.coverage == supplied.coverage
        same_attacks = alternate.strategies == supplied.strategies
        assert same_coverage != same_attacks
        counts["different conditional attacks" if same_coverage else "different coverage"] += 1
    return alternate, unrestricted


def check_case(name, game, counts, supplied=None):
    global_bne = GlobalEquilibria(game)
    if supplied is None:
        supplied = global_bne.find()
    assert supplied is not None
    result, other = check_seed(name, game, global_bne, supplied, counts)
    if other is not None:
        check_seed(name+" alternate seed", game, global_bne, other, counts)
    return result


def benchmark_profiles(counts):
    # Both opponent-only best-response sets equal the full simplex here, but
    # changing either player at the unique mixed profile destroys equilibrium.
    matching = Game((1,), (1, 1), ((1, 1),), ((1, 1),), 1)
    half = F(1, 2)
    mixed = Profile((half, half), ((half, half),))
    assert check_case("unique fully mixed", matching, counts, mixed) is None
    global_bne = GlobalEquilibria(matching)
    assert global_bne.find(global_bne.pin(Profile((1, 0), mixed.strategies))) is None
    assert global_bne.find(global_bne.pin(Profile(mixed.coverage, ((1, 0),)))) is None

    # The same flat attacker offers allow both opposite pure equilibria,
    # but both crossed profiles violate defender optimality.
    flats = Game((1,), (1, 1), ((1, 1),), ((0, 0),), 1)
    left, right = Profile((1, 0), ((1, 0),)), Profile((0, 1), ((0, 1),))
    global_bne = GlobalEquilibria(flats)
    for seed in (left, right):
        second, _ = check_seed("noninterchangeable flat game", flats, global_bne, seed, counts)
        assert second is not None and second.coverage == seed.coverage
    assert global_bne.find(global_bne.pin(Profile(left.coverage, right.strategies))) is None
    assert global_bne.find(global_bne.pin(Profile(right.coverage, left.strategies))) is None

    # A complete set of checkpoints on the path around the nonconvex coverage example.
    published = Game((F(1, 3),)*3, (1, 1, 1),
                     ((2, 3, 0), (3, 2, 0), (0, 0, 2)), ((1, 6, 1), (4, 1, 1), (1, 1, 1)), 1)
    global_bne = GlobalEquilibria(published)
    identity = ((1, 0, 0), (0, 1, 0), (0, 0, 1))
    swapped = ((0, 1, 0), (1, 0, 0), (0, 0, 1))
    mixture = ((half, half, 0), (half, half, 0), (0, 0, 1))
    p = tuple(F(v, 8) for v in (3, 3, 2))
    t = tuple(F(v, 23) for v in (7, 5, 11))
    r = tuple(F(v, 8) for v in (1, 1, 6))
    for x, s in ((p, identity), (t, identity), (t, mixture), (t, swapped), (r, swapped)):
        answer, _ = check_seed("published nonconvex", published, global_bne, Profile(x, s), counts)
        assert answer is not None
        if x == t and s == mixture:
            assert answer.coverage == t
    assert global_bne.find(global_bne.pin(Profile(p, swapped))) is None
    assert global_bne.find(global_bne.pin(Profile(r, identity))) is None

    # On the endpoint budgets, changes to tied zero-prior types still count.
    num_cases = 3
    for budget in (0, 2):
        x = (0, 0) if budget == 0 else (1, 1)
        for tied in (False, True):
            endpoint = Game((1, 0), (1, 2), ((3, 0), (0, 0) if tied else (0, 3)),
                            ((1, 1), (0, 0)), budget)
            supplied = Profile(x, ((1, 0), (0, 1)))
            alternate = check_case("endpoint, zero prior", endpoint, counts, supplied)
            assert (alternate is not None) == tied
            if alternate is not None:
                assert alternate.coverage == x and alternate.strategies[0] == (1, 0)
            num_cases += 1
    for budget in (0, 1):
        sole_target = Game((1,), (0,), ((0,),), ((0,),), budget)
        assert check_case("single target", sole_target, counts) is None
        num_cases += 1
    return num_cases


class PureEquilibria:
    """Test oracle listing every r-subset and comparing pure expected payoffs directly."""
    def __init__(self, game):
        n = len(game.gains)
        self.game = game
        self.subsets = tuple(combinations(range(n), game.resources))
        self.weights = [z3.Real(f"pure_weight{i}") for i in range(len(self.subsets))]
        self.sigma = [[z3.Real(f"pure_s{i}_{j}") for j in range(n)] for i in range(len(game.priors))]
        self.x = [z3.Sum([v for subset, v in zip(self.subsets, self.weights) if j in subset])
                  for j in range(n)]
        self.simplex = [z3.Sum(self.weights) == 1, *(v >= 0 for v in self.weights)]
        solver = self.solver = z3.SolverFor("QF_LRA")
        solver.add(*self.simplex)
        scores = [q(d)*z3.Sum([q(p)*s[j] for p, s in zip(game.priors, self.sigma)])
                  for j, d in enumerate(game.gains)]
        payoffs = [z3.Sum([scores[j] for j in subset]) for subset in self.subsets]
        for row, p in enumerate(self.weights):
            solver.add(z3.Or(p == 0, z3.And(*(payoffs[row] >= other for other in payoffs))))
        for i, probabilities in enumerate(self.sigma):
            utility = [q(game.intercepts[i][j])-q(game.slopes[i][j])*x for j, x in enumerate(self.x)]
            solver.add(z3.Sum(probabilities) == 1)
            for j, p in enumerate(probabilities):
                solver.add(p >= 0, z3.Or(p == 0, z3.And(*(utility[j] >= other for other in utility))))

    def pin(self, profile):
        mix = dict(profile.defense)
        return z3.And(*(v == q(mix.get(subset, 0)) for v, subset in zip(self.weights, self.subsets)),
                      *(v == q(p) for row, given in zip(self.sigma, profile.strategies)
                        for v, p in zip(row, given)))

    def exists(self, conditions):
        self.solver.push()
        self.solver.add(conditions)
        result = self.solver.check()
        self.solver.pop()
        assert result in (z3.sat, z3.unsat), result
        return result == z3.sat

    def other_realization_lp(self, profile):
        # Independent pure-strategy LP with fixed coverage and all vertex weights.
        lp = z3.SolverFor("QF_LRA")
        lp.add(*self.simplex)
        mix = dict(profile.defense)
        known_x = tuple(sum(p for subset, p in profile.defense if j in subset)
                        for j in range(len(self.game.gains)))
        lp.add(*(x == q(orig) for x, orig in zip(self.x, known_x)))
        for subset, weight in zip(self.subsets, self.weights):
            given = q(mix.get(subset, 0))
            for exclusion in (weight < given, weight > given):
                lp.push()
                lp.add(exclusion)
                result = lp.check()
                lp.pop()
                assert result in (z3.sat, z3.unsat), result
                if result == z3.sat:
                    return True
        return False


def full_check(name, game, full, counts):
    engine = PureEquilibria(game)
    assert engine.exists(engine.pin(full)), (name, "invalid seed")
    other = second_full_equilibrium(game, full)
    assert (other is not None) == engine.exists(z3.Not(engine.pin(full))), (name, "global")
    same_margin_possible = engine.other_realization_lp(full)
    if other is None:
        assert not same_margin_possible
        counts["unique"] += 1
        return None
    assert other != full and engine.exists(engine.pin(other)), (name, other)
    if other.marginal(game) == full.marginal(game):
        assert same_margin_possible
        counts["second realization"] += 1
    else:
        assert not same_margin_possible  # Solver tries the same-coverage witness first.
        counts["second marginal"] += 1
    return other


def full_strategy_tests():
    counts = Counter()
    def uniform_game(n, r):
        game = Game((1,), (1,)*n, ((1,)*n,), ((1,)*n,), r)
        return game, ((F(1, n),)*n,)

    game, attacks = uniform_game(4, 2)
    # Both decompositions have the same uniform (1/2,...,1/2) coverage.
    # Two complementary vertices are independent; all six vertices are dependent.
    pairs = tuple(combinations(range(4), 2))
    for subset_list in (((0, 1), (2, 3)), ((0, 1), (2, 3), (0, 2), (1, 3)), pairs):
        full = FullProfile({s: F(1, len(subset_list)) for s in subset_list}, attacks)
        out = full_check("Delta(4,2)", game, full, counts)
        assert out is not None and out.marginal(game) == full.marginal(game)
        if len(subset_list) > 4:
            assert len(out.defense) < len(full.defense)
        else:
            assert set(dict(out.defense)) - set(dict(full.defense))
    for n in (3, 4, 5):
        for r in (1, n-1):
            game, attacks = uniform_game(n, r)
            full = FullProfile({s: F(1, n) for s in combinations(range(n), r)}, attacks)
            assert full_check(f"Delta({n},{r})", game, full, counts) is None

    # A simplex minimal face in Delta(5,2): target 0 is always covered, and
    # the unique defender mix distributes the one remaining resource uniformly.
    face_game = Game((1,), (1,)*5, ((F(3, 4), 0, 0, 0, 0),), ((1,)*5,), 2)
    face_full = FullProfile({(0, j): F(1, 4) for j in range(1, 5)}, ((F(1, 5),)*5,))
    full_check("embedded simplex face", face_game, face_full, counts)

    for r in (0, 4):
        game = Game((1,), (1,)*4, ((7, 0, 0, 0),), ((1,)*4,), r)
        subset = tuple(range(r))
        assert full_check("forced pure endpoint", game, FullProfile({subset: 1}, ((1, 0, 0, 0),)), counts) is None
    pure = Game((F(2, 3), F(1, 3)), (1,)*4, ((5, 0, 0, 0), (0, 5, 0, 0)),
                ((1,)*4, (1,)*4), 2)
    seed = FullProfile({(0, 1): 1}, ((1, 0, 0, 0), (0, 1, 0, 0)))
    assert full_check("pure interior budget", pure, seed, counts) is None

    free = Game((1, 0), (1, 1), ((1, 1), (0, 0)), ((1, 1), (0, 0)), 1)
    full = FullProfile({(0,): F(1, 2), (1,): F(1, 2)}, ((F(1, 2), F(1, 2)), (1, 0)))
    other = full_check("free zero-prior row", free, full, counts)
    assert other and other.defense == full.defense and other.strategies != full.strategies
    sparse = Game((1,), (0, 0), ((1, 0),), ((0, 0),), 1)
    full = FullProfile({(0,): 1}, ((1, 0),))
    other = full_check("changing coverage", sparse, full, counts)
    assert other and other.defense != full.defense

    # A large hypersimplex needs no pure enumeration. Its two complementary
    # supported defenses meet every target at 1/2; the solver adds a missing one.
    game, attacks = uniform_game(40, 20)
    full = FullProfile({tuple(range(20)): F(1, 2), tuple(range(20, 40)): F(1, 2)}, attacks)
    other = second_full_equilibrium(game, full)
    assert other != full and other.marginal(game) == full.marginal(game)
    assert len(other.defense) <= 41
    return counts


def main():
    counts = Counter()
    suite = topology_games()
    for datum in suite:
        game = Game(datum.priors, datum.gains, datum.intercepts, datum.slopes, datum.resources)
        check_case(datum.name, game, counts)
    extra = benchmark_profiles(counts)
    print(f"{len(suite)+extra} game cases, {sum(counts.values())} supplied BNE checked against unrestricted exact search.")
    print(f"{counts['unique']} unique; alternate BNE changed coverage in {counts['different coverage']} cases "
          f"and conditional attacks in {counts['different conditional attacks']}.")
    print("Noninterchangeable endpoints, a unique fully mixed profile with broad best responses, "
          "five nonconvex-path checkpoints, zero priors, and endpoint budgets passed.")
    full = full_strategy_tests()
    print(f"{sum(full.values())} full-profile cases checked against enumerated pure strategies and direct "
          f"decomposition LPs: {full['unique']} unique, {full['second realization']} alternative pure "
          f"mixtures at fixed marginals, {full['second marginal']} alternative marginal profiles.")
    print("A separate Delta(40,20) sparse-support case produced a second realization without pure enumeration.")


if __name__ == "__main__":
    main()
