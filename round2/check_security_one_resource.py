"""Exact finite checks of the cap-enforcer reduction to a one-resource game.

The compiled game has a dense ordinary payoff table, normalized priors,
and a positive-gain dummy. The QF_LRA checks cover all real equilibria of
each fixed game and all real source equilibria for the canonical lift.
Requires Python 3 and z3-solver.
"""

from collections import Counter, defaultdict, deque
from dataclasses import dataclass
from fractions import Fraction as F
from itertools import combinations
import sys

import z3


def q(value):
    value = F(value)
    return z3.RealVal(f"{value.numerator}/{value.denominator}")


def check(formula, expected, context):
    solver = z3.SolverFor("QF_LRA")
    solver.add(formula)
    status = solver.check()
    if status != expected:
        evidence = solver.model() if status == z3.sat else solver.reason_unknown()
        raise AssertionError(f"{context}: expected {expected}, saw {status}: {evidence}")


def prove(formula, context):
    check(z3.Not(formula), z3.unsat, context)


@dataclass(frozen=True)
class Game:
    name: str
    priors: tuple
    gains: tuple
    intercepts: tuple
    slopes: tuple
    resources: int


def variables(game, prefix):
    x = [z3.Real(f"{prefix}_x{j}") for j in range(len(game.gains))]
    sigma = [[z3.Real(f"{prefix}_s{i}_{j}") for j in range(len(x))]
             for i in range(len(game.priors))]
    return x, sigma


def loads(priors, sigma):
    return [z3.Sum([q(p)*row[j] for p, row in zip(priors, sigma)])
            for j in range(len(sigma[0]))]


def bne(game, x, sigma):
    """Direct conditional best responses and pairwise budget-exchange constraints."""
    rows = [z3.Sum(x) == game.resources]
    rows.extend(z3.And(v >= 0, v <= 1) for v in x)
    for row, intercept, slope in zip(sigma, game.intercepts, game.slopes):
        utility = [q(a)-q(b)*v for a, b, v in zip(intercept, slope, x)]
        rows.append(z3.Sum(row) == 1)
        for j, chance in enumerate(row):
            rows.extend((chance >= 0, z3.Or(chance == 0,
                         z3.And(*(utility[j] >= u for u in utility)))))
    scores = [q(d)*w for d, w in zip(game.gains, loads(game.priors, sigma))]
    rows.extend(z3.Or(x[j] == 0, x[k] == 1, scores[j] >= scores[k])
                for j in range(len(x)) for k in range(len(x)) if j != k)
    return z3.And(*rows)


def order_stats(values):
    ordered = []
    for v in values:
        incoming = v
        for i, before in enumerate(ordered):
            ordered[i] = z3.If(before >= incoming, before, incoming)
            incoming = z3.If(before >= incoming, incoming, before)
        ordered.append(incoming)
    return ordered


def build_game(original):
    m, n, r = len(original.priors), len(original.gains), original.resources
    assert 1 <= r <= n and sum(original.priors) == 1 and min(original.priors) >= 0
    assert min(original.gains) > 0
    base = 1+max(original.gains)
    enforcer = [F(base)/d for d in original.gains]
    population = 1+sum(enforcer)
    dummy_gain = F(base)/(2*population)
    mass = tuple(F(w)/population for w in (*original.priors, *enforcer))
    intercepts, slopes = [], []
    for intercept, slope in zip(original.intercepts, original.slopes):
        floor = min(a-r*b for a, b in zip(intercept, slope))
        intercepts.append(tuple(intercept)+(floor-1,))
        slopes.append(tuple(r*b for b in slope)+(1,))
    for j in range(n):
        intercepts.append(tuple(1 if j == k else -3 for k in range(n))+(0,))
        slopes.append(tuple(r if j == k else 1 for k in range(n))+(1,))
    transformed = Game(original.name+" compiled", mass, (*original.gains, dummy_gain),
                       tuple(intercepts), tuple(slopes), 1)
    assert len(transformed.priors) == m+n and sum(mass) == 1
    assert dummy_gain*population < base
    return transformed, F(base), enforcer


def check_instance(source, counts):
    compiled, base, enforcer = build_game(source)
    m, n, r = len(source.priors), len(source.gains), source.resources
    y, tau = variables(compiled, source.name+"_market")
    actual = bne(compiled, y, tau)
    check(actual, z3.sat, source.name+" compiled equilibrium exists")
    decoded_x = [r*v for v in y[:n]]
    decoded_sigma = [row[:n] for row in tau[:m]]
    shape = [y[n] == 0, *(v <= 1 for v in decoded_x), *(row[n] == 0 for row in tau[:m])]
    for j in range(n):
        row = tau[m+j]
        shape.extend(row[k] == 0 for k in range(n) if k != j)
        shape.append(z3.Or(decoded_x[j] == 1, row[j] == 1))
    prove(z3.Implies(actual, z3.And(*shape)), source.name+" dummy, caps and enforcer shape")
    prove(z3.Implies(actual, bne(source, decoded_x, decoded_sigma)), source.name+" reverse projection")

    # Converse at an arbitrary, symbolic source equilibrium, independent of the decoder.
    x, sigma = variables(source, source.name+"_source")
    source_bne = bne(source, x, sigma)
    check(source_bne, z3.sat, source.name+" source equilibrium exists")
    source_scores = [q(d)*w for d, w in zip(source.gains, loads(source.priors, sigma))]
    theta = order_stats(source_scores)[r-1]
    exempted = []
    for j, d in enumerate(source.gains):
        partial = (q(base)+theta-source_scores[j])/q(d)
        exempted.append(z3.If(x[j] == 1, partial, q(enforcer[j])))
    lifted_y = [v/r for v in x]+[q(0)]
    lifted_tau = [list(row)+[q(0)] for row in sigma]
    for j, z in enumerate(exempted):
        own = z/q(enforcer[j])
        lifted_tau.append([own if k == j else q(0) for k in range(n)]+[1-own])
    prove(z3.Implies(source_bne, bne(compiled, lifted_y, lifted_tau)),
          source.name+" upper order statistic lifts every source equilibrium")

    # Independently characterize all enforcer choices at every supplied source
    # equilibrium. K is the largest real *unnormalized* compiled target score.
    # When all coordinates are saturated (r=n), K can fall below base.
    z = [z3.Real(f"{source.name}_own{j}") for j in range(n)]
    real = [source_scores[j]+q(source.gains[j])*z[j] for j in range(n)]
    peak = order_stats(real)[0]
    dummy_score = q(compiled.gains[-1])*z3.Sum([q(h)-v for h, v in zip(enforcer, z)])
    fibers = [dummy_score <= peak]
    rows = [list(row)+[q(0)] for row in sigma]
    for j in range(n):
        own = z[j]/q(enforcer[j])
        rows.append([own if j == k else q(0) for k in range(n)]+[1-own])
        fibers.extend((z[j] >= 0, z[j] <= q(enforcer[j]),
                       z3.Or(x[j] == 1, z[j] == q(enforcer[j])),
                       z3.Or(x[j] == 0, real[j] == peak)))
    prove(z3.Implies(source_bne, bne(compiled, lifted_y, rows) == z3.And(*fibers)),
          source.name+" full real enforcer-allocation fiber")
    counts["games"] += 1
    counts["profiles"] += 2
    counts["universal"] += 4
    return compiled, base, enforcer


def pinned(compiled, y, tau, y_values, sigma, own_amounts, masses):
    n = len(masses)
    cond = [y[j] == q(value) for j, value in enumerate(y_values)]
    cond.extend(tau[i][j] == q(p) for i, row in enumerate(sigma) for j, p in enumerate(row))
    cond.extend(q(masses[j])*tau[len(sigma)+j][j] == q(z) for j, z in enumerate(own_amounts))
    return z3.And(bne(compiled, y, tau), *cond)


def games():
    return [
        Game("interior_tie", (1,), (1, 1, 1), ((1, 1, 1),), ((1, 1, 1),), 2),
        Game("pure_gap", (F(3, 5), F(2, 5)), (1, 1, 1),
             ((5, 0, 0), (0, 5, 0)), ((1, 1, 1), (1, 1, 1)), 2),
        Game("both_saturated", (F(1, 2), F(1, 2)), (1, 1, 1),
             ((1, 0, 0), (0, 1, 0)), ((0, 0, 0), (0, 0, 0)), 2),
        Game("weak_negative", (F(1, 3), F(2, 3)), (F(1, 2), F(3, 2), 2, 3),
             ((-5, 1, -7, 0), (-3, -4, 1, -2)), ((0, 1, 0, 3), (4, 0, 2, 0)), 3),
        Game("zero_prior", (1, 0), (F(2, 3), 2, F(3, 2)),
             ((2, 0, 2), (-2, 1, -1)), ((1, 1, 1), (0, 1, 0)), 2),
        Game("full_budget", (F(2, 3), F(1, 3)), (1, 2, 1),
             ((2, 1, 0), (0, 2, 1)), ((2, 1, 0), (0, 0, 1)), 3),
        Game("single_resource", (1,), (1, 2), ((1, 1),), ((1, 1),), 1),
        Game("single_target", (1,), (2,), ((-5,),), ((0,),), 1),
    ]


def check_pinned(source, compiled, base, masses):
    y, tau = variables(compiled, source.name+"_pin")
    if source.name == "interior_tie":
        y_values = (F(1, 3),)*3+(0,)
        sigma = ((F(1, 3),)*3+(0,),)
        full = pinned(compiled, y, tau, y_values, sigma, masses, masses)
        check(full, z3.sat, "all interior targets fully enforced at unique source profile")
        return 1
    if source.name == "pure_gap":
        y_values = (F(1, 2), F(1, 2), 0, 0)
        sigma = ((1, 0, 0, 0), (0, 1, 0, 0))
        # Any q in the true cutoff range [0,2/5] gives a distinct full compiled
        # equilibrium over the same globally unique pure source profile.
        for theta in (0, F(1, 5), F(2, 5)):
            own = (base+theta-F(3, 5), base+theta-F(2, 5), base)
            check(pinned(compiled, y, tau, y_values, sigma, own, masses), z3.sat, "pure-gap fiber sample")
        source_x, source_s = variables(source, "pure_source_pin")
        same = z3.And(*(v == q(target) for v, target in zip(source_x, (1, 1, 0))),
                      *(v == q(target) for row, given in zip(source_s, sigma) for v, target in zip(row, given)))
        prove(z3.Implies(bne(source, source_x, source_s), same), "pure-gap source profile is globally unique")
        return 4
    if source.name == "full_budget":
        total = 1+sum(masses)
        scores = loads(compiled.priors, tau)
        max_score = order_stats([q(total*d)*s for d, s in zip(compiled.gains[:-1], scores[:-1])])[0]
        check(z3.And(bne(compiled, y, tau), max_score < q(base)), z3.sat,
              "r=n allows a fully saturated compiled equilibrium strictly below the base level")
        return 1
    return 0


def check_cap_cases():
    totals = Counter()
    pins = 0
    data = games()
    for game in data:
        built, C, weights = check_instance(game, totals)
        pins += check_pinned(game, built, C, weights)
    print(f"{totals['games']} games ({sum(g.resources > 1 for g in data)} with r>1): "
          f"{totals['profiles']} source/compiled existence checks and {totals['universal']} all-real "
          f"projection, lift, enforcer-shape, and full-fiber statements passed.")
    print(f"{pins} targeted checks cover a fully interior tie, a globally unique source with "
          f"three compiled lifts, and a saturated r=n game whose score peak can fall below C.")


def rational_bne(game, x, sigma):
    assert sum(x) == game.resources and all(0 <= v <= 1 for v in x)
    assert len(sigma) == len(game.priors)
    for i, row in enumerate(sigma):
        assert len(row) == len(x) and sum(row) == 1 and min(row) >= 0
        payoff = [a-b*v for a, b, v in zip(game.intercepts[i], game.slopes[i], x)]
        best = max(payoff)
        assert all(not p or u == best for p, u in zip(row, payoff))
    score = [d*sum(p*row[j] for p, row in zip(game.priors, sigma)) for j, d in enumerate(game.gains)]
    assert sum(s*v for s, v in zip(score, x)) == sum(sorted(score, reverse=True)[:game.resources])


def pattern(game, profile):
    """All maximizing edges, including ones carrying zero conditional attack."""
    tight = []
    for i, (a, b) in enumerate(zip(game.intercepts, game.slopes)):
        values = [u-v*w for u, v, w in zip(a, b, profile.coverage)]
        best = max(values)
        tight.extend((i, j) for j, v in enumerate(values) if v == best)
    fixed = {j: x for j, x in enumerate(profile.coverage) if x in (0, 1)}
    return tight, fixed


def trial_isolate(base, epsilon):
    """Work at a small trial scale to discover an exact forest; no certificate uses this scale."""
    from security_equilibrium_uniqueness import Game as ExactGame
    n = len(base.gains)
    a = list(base.intercepts)
    b = list(base.slopes)
    for j in range(n):
        a.append(tuple(2 if k == j else -2 for k in range(n)))
        b.append((F(1),)*n)
    p = [mass+epsilon**(i+1) for i, mass in enumerate((*base.priors, *((0,)*n)))]
    a = [tuple(value+epsilon**(1+i*n+j) for j, value in enumerate(row)) for i, row in enumerate(a)]
    return ExactGame(tuple(v/sum(p) for v in p), base.gains, tuple(a), tuple(b), base.resources)


def model_point(game, label):
    from security_equilibrium_uniqueness import Profile
    # Dedicated types have a pre-established strictly best target even at arbitrary
    # y. Prune each individually dominated edge by a coverage-box comparison.
    n = len(game.gains)
    x = [z3.Real(f"{label}_coverage{j}") for j in range(n)]
    s = z3.SolverFor("QF_LRA")
    s.add(z3.Sum(x) == game.resources, *(z3.And(v >= 0, v <= 1) for v in x))
    rows, cols = [], [[] for _ in x]
    for i, (a, b) in enumerate(zip(game.intercepts, game.slopes)):
        low = max(u-v for u, v in zip(a, b))
        viable = [j for j, value in enumerate(a) if value >= low]
        row = [None]*n
        best = z3.Real(f"{label}_best{i}")
        for j in viable:
            mass = z3.Real(f"{label}_mass{i}_{j}")
            value = q(a[j])-q(b[j])*x[j]
            s.add(mass >= 0, best >= value, z3.Or(mass == 0, best == value))
            row[j] = mass
            cols[j].append(mass)
        s.add(z3.Sum([row[j] for j in viable]) == q(game.priors[i]))
        rows.append(row)
    cutoff = z3.Real(f"{label}_cut")
    for j in range(n):
        score = q(game.gains[j])*z3.Sum(cols[j])
        s.add(z3.Or(x[j] == 0, score >= cutoff), z3.Or(x[j] == 1, score <= cutoff))
    assert s.check() == z3.sat, label
    mdl = s.model()
    def exact(v):
        amount = mdl.eval(v, model_completion=True)
        return F(amount.numerator_as_long(), amount.denominator_as_long())
    numeric = Profile(tuple(exact(v) for v in x),
                      tuple(tuple(exact(v)/mass if v is not None else F(0) for v in row)
                            for row, mass in zip(rows, game.priors)))
    rational_bne(game, numeric.coverage, numeric.strategies)
    return numeric


def forest_profile(game, trial):
    """Solve the full-precision equilibrium equalities by exact tree elimination."""
    from security_equilibrium_uniqueness import Profile
    tight, fixed = trial
    m, n = len(game.priors), len(game.gains)
    graph = defaultdict(list)
    for i, j in tight:
        graph["i", i].append(("j", j))
        graph["j", j].append(("i", i))
    unseen = {("i", i) for i in range(m)} | {("j", j) for j in range(n)}
    components = []
    # Within a tree store every payoff/coverage as constant+slope*root coverage.
    affine, parameter, free, trees = {}, {}, [], 0
    while unseen:
        first = min(unseen)
        members, pending = {first}, [first]
        while pending:
            v = pending.pop()
            for w in graph[v]:
                if w not in members:
                    pending.append(w)
                    members.add(w)
        unseen -= members
        bounds = [v for v in members if v[0] == "j" and v[1] in fixed]
        assert len(bounds) <= 1
        root = bounds[0] if bounds else min(v for v in members if v[0] == "j")
        affine[root] = (F(0), F(1))
        if bounds:
            parameter[root] = fixed[root[1]]
        else:
            free.append(root)
        order, parent, queue = [], {root: None}, deque([root])
        while queue:
            v = queue.popleft()
            order.append(v)
            p0, p1 = affine[v]
            for w in graph[v]:
                if w == parent[v]:
                    continue
                assert w not in parent, "tight component contains a cycle"
                parent[w] = v
                if v[0] == "i":
                    a, b = game.intercepts[v[1]][w[1]], game.slopes[v[1]][w[1]]
                    affine[w] = ((a-p0)/b, -p1/b)
                else:
                    a, b = game.intercepts[w[1]][v[1]], game.slopes[w[1]][v[1]]
                    affine[w] = (a-b*p0, -b*p1)
                queue.append(w)
        assert set(order) == members
        components.append((root, order, parent))
        trees += 1
    assert (len(free) == 1) if len(fixed) < n else (not free)
    if free:
        amount, coefficient = F(0), F(0)
        for root, order, _ in components:
            for v in order:
                if v[0] == "j":
                    c, b = affine[v]
                    amount += c
                    if root == free[0]:
                        coefficient += b
                    else:
                        amount += b*parameter[root]
        parameter[free[0]] = (game.resources-amount)/coefficient
    x = [None]*n
    for root, order, _ in components:
        for v in order:
            if v[0] == "j":
                a, b = affine[v]
                x[v[1]] = a+b*parameter[root]
    sig = [[F(0)]*n for _ in range(m)]
    if not free:
        for i in range(m):
            (j,) = [v[1] for v in graph["i", i]]
            sig[i][j] = F(1)
    else:
        verts = next(order for root, order, _ in components if root == free[0])
        theta = (sum(game.priors[k] for side, k in verts if side == "i") /
                 sum(1/game.gains[k] for side, k in verts if side == "j"))
        for _, order, parent in components:
            accumulated = defaultdict(F)
            for v in reversed(order[1:]):
                w = parent[v]
                i, j = (v[1], w[1]) if v[0] == "i" else (w[1], v[1])
                margin = game.priors[v[1]] if v[0] == "i" else theta/game.gains[v[1]]
                amount = margin-accumulated[v]
                sig[i][j] = amount/game.priors[i]
                accumulated[w] += amount
    answer = Profile(tuple(x), tuple(map(tuple, sig)))
    rational_bne(game, answer.coverage, answer.strategies)
    assert pattern(game, answer) == (tight, fixed)
    return answer, trees


def ratios_and_anchors(game, original_type_count):
    """Check exact disequality of every competing ratio, independent of the scale proof."""
    m, n = len(game.priors), len(game.gains)
    # Normalizing each subset ratio by their common mass/denominator factors keeps
    # directly enumerated integers small, even at the certified isolation precision.
    from math import lcm
    mass_den = lcm(*(p.denominator for p in game.priors))
    reciprocal = tuple(1/d for d in game.gains)
    gain_den = lcm(*(s.denominator for s in reciprocal))
    masses = [int(v*mass_den) for v in game.priors]
    weights = [int(v*gain_den) for v in reciprocal]
    denoms = {sum(weights[j] for j in targets) for size in range(1, n+1)
              for targets in combinations(range(n), size)}
    seen = defaultdict(list)
    for bits in range(1, 1 << m):
        numerator = sum(v for i, v in enumerate(masses) if bits & (1 << i))
        for denominator in denoms:
            value = F(numerator, denominator)
            assert not any(prior & bits == 0 for prior in seen[value])
            seen[value].append(bits)
    for j in range(n):
        i = original_type_count+j
        assert game.intercepts[i][j]-game.slopes[i][j] > max(
            game.intercepts[i][k] for k in range(n) if k != j)
    return len(denoms)*((1 << m)-1)


def no_alternative_smt(game, original):
    x, sigma = variables_fresh(len(game.priors), len(game.gains), "direct_generic")
    different = z3.Or(*(v != q(w) for v, w in zip(x, original.coverage)),
                      *(v != q(w) for row, ref in zip(sigma, original.strategies) for v, w in zip(row, ref)))
    prove(z3.Implies(bne(game, x, sigma), z3.Not(different)), "isolated BNE globally unique in direct QF_LRA")


def variables_fresh(m, n, name):
    return ([z3.Real(f"{name}_x{j}") for j in range(n)],
            [[z3.Real(f"{name}_s{i}_{j}") for j in range(n)] for i in range(m)])


def certified_isolated(base, target, label, trial_power=8):
    trial = trial_isolate(base, F(1, 1 << trial_power))
    guessed = model_point(trial, label+"_trial")
    witness, trees = forest_profile(target, pattern(trial, guessed))
    checks = ratios_and_anchors(target, len(base.priors))
    return witness, trees, checks


def isolation_suite():
    from security_equilibrium_uniqueness import Game as ExactGame, Profile
    from security_one_resource import cap_game, isolate_game, unique_one_resource
    direct = []
    for n, r in ((2, 1), (3, 2)):
        base = ExactGame((F(1, 2), F(1, 2)), (1,)*n, ((1,)*n,)*2, ((1,)*n,)*2, r)
        x = (F(r, n),)*n
        flat = (F(1, n),)*n
        sigma = [list(flat), list(flat)]
        shift = F(1, 2*n)
        for i in (0, 1):
            sigma[i][i] += shift
            sigma[i][1-i] -= shift
        rational_bne(base, x, [flat, flat])
        rational_bne(base, x, sigma)
        assert Profile(x, [flat, flat]) != Profile(x, sigma)
        target, delta = isolate_game(base)
        witness, trees, count = certified_isolated(base, target, f"direct{n}")
        no_alternative_smt(target, witness)
        direct.append((n, r, len(target.priors), F(delta).denominator.bit_length()-1, trees, count))
    # One positive-prior row and an independently optimal zero-prior type.
    # r=2,n=3 makes the cap compilation nontrivial.
    origin = ExactGame((1, 0), (1, 1, 1), ((1, 1, 1), (0, 3, -1)), ((1, 1, 1), (1, 1, 1)), 2)
    positive = ExactGame((1,), origin.gains, (origin.intercepts[0],), (origin.slopes[0],), 2)
    cap = cap_game(positive)
    reduction = unique_one_resource(origin)
    unique, trees, count = certified_isolated(cap, reduction.target, "end_to_end")
    assert reduction.target.resources == 1
    no_alternative_smt(reduction.target, unique)
    restored = reduction.decode(unique)
    decoded = restored.marginal(origin)
    rational_bne(origin, decoded.coverage, decoded.strategies)
    assert decoded.coverage == (F(2, 3),)*3
    assert decoded.strategies == ((F(1, 3),)*3, (0, 1, 0))
    assert dict(restored.defense) == {pair: F(1, 3) for pair in combinations(range(3), 2)}
    # This additional source exercises the positive-effects restoration LP:
    # both an original gain and several original slopes are exactly zero.
    weak = ExactGame((1, 0), (1, 2, 0), ((3, 3, 0), (0, 3, 0)), ((0, 1, 0), (1, 0, 1)), 2)
    weak_reduction = unique_one_resource(weak)
    assert weak_reduction.capped.resources == 1
    unique_weak, weak_trees, weak_ratios = certified_isolated(
        weak_reduction.capped, weak_reduction.target, "simultaneous_zeros", trial_power=64)
    weak_full = weak_reduction.decode(unique_weak)
    weak_profile = weak_full.marginal(weak)
    rational_bne(weak, weak_profile.coverage, weak_profile.strategies)
    assert weak_full.defense == (((0, 1), F(1)),)
    assert weak_profile.strategies == ((1, 0, 0), (0, 1, 0))
    highest = max(v.denominator.bit_length() for row in weak_reduction.target.intercepts for v in row)
    for budget in (0, 3):
        endpoint = ExactGame((1, 0), (0, 2, 1),
                             ((2, 0, 0), (0, 3, 0)), ((0, 1, 1), (1, 0, 1)), budget)
        fixed = unique_one_resource(endpoint)
        fixed_point = Profile((1,), ((1,),))
        rational_bne(fixed.target, fixed_point.coverage, fixed_point.strategies)
        no_alternative_smt(fixed.target, fixed_point)
        restored = fixed.decode(fixed_point)
        endpoint_point = restored.marginal(endpoint)
        rational_bne(endpoint, endpoint_point.coverage, endpoint_point.strategies)
        assert dict(restored.defense) == {tuple(range(budget)): F(1)}
        assert endpoint_point.strategies == ((1, 0, 0), (0, 1, 0))
    for n, r, m, power, tree_count, ratios in direct:
        print(f"Direct isolation n={n}, r={r}: nonunique source; unique {m}-type target, "
              f"delta=2^-{power}, {tree_count} exact tight trees, {ratios} subset-ratio cases.")
    print(f"Composite r=2 with a zero-prior original type: unique target "
          f"{len(reduction.target.priors)} types × {len(reduction.target.gains)} targets; "
          f"{trees} tight tree(s), {count} subset-ratio cases, recovered all three pure defenses "
          f"and both original conditional strategies.")
    print(f"Additional r=2 source with simultaneous zero gain, slope and prior: unique 8×4 target, "
          f"{weak_trees} exact tight tree(s), {weak_ratios} subset-ratio cases at full precision; "
          f"largest intercept denominator {highest} bits; exact original pure defense and both rows recovered.")
    print("Unrestricted all-real QF_LRA excluded a second equilibrium on both directly isolated "
          "targets and on the first composite 8×4 target; original budget endpoints 0 and n "
          "also decoded to their sole legal pure defense.")


if __name__ == "__main__":
    if hasattr(sys, "set_int_max_str_digits"):
        sys.set_int_max_str_digits(0)
    check_cap_cases()
    isolation_suite()
