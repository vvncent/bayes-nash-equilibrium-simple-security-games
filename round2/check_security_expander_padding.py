"""Exact finite checks for the small-prior expander padding and unchanged-coverage repair.

Run ``python3 -B round2/check_security_expander_padding.py`` with z3-solver.
"""

from collections import Counter
from fractions import Fraction as Q
from itertools import combinations, product
from math import isqrt

import z3


def square_graph(q):
    """Undirected Lee square graph, with parallel edges and loops discarded."""
    edges = set()
    for x, y in product(range(q), repeat=2):
        u = x * q + y
        for a, b in ((x + 1, y), (x, y + 1), (x + y, y), (x, y + x)):
            v = (a % q) * q + (b % q)
            if u != v:
                edges.add(tuple(sorted((u, v))))
    return edges


def quotient(n):
    q = isqrt(n - 1) + 1
    return {tuple(sorted((u % n, v % n))) for u, v in square_graph(q) if u % n != v % n}


def cut_checks():
    total = 0
    minimum = None
    for n in range(2, 13):
        q = isqrt(n - 1) + 1
        source = square_graph(q)
        target = quotient(n)
        degree = Counter(v for edge in target for v in edge)
        assert len(degree) == n and max(degree.values()) <= 32
        multiplicity = Counter(tuple(sorted((u % n, v % n))) for u, v in source if u % n != v % n)
        assert max(multiplicity.values()) <= 32
        for mask in range(1, 1 << n):
            A = {k for k in range(n) if mask & (1 << k)}
            if len(A) > n // 2:
                continue
            source_cut = sum((u % n in A) != (v % n in A) for u, v in source)
            quotient_cut = sum((u in A) != (v in A) for u, v in target)
            assert 0 < quotient_cut <= source_cut <= 32 * quotient_cut
            size = len({v for v in range(q * q) if v % n in A})
            assert min(size, q * q - size) >= len(A)
            ratio = Q(quotient_cut, len(A))
            minimum = ratio if minimum is None else min(minimum, ratio)
            total += 1
    return total, minimum


def subsets(values):
    return (s for k in range(1, len(values) + 1) for s in combinations(values, k))


def unit_gain_cutoff_checks():
    """Compare the two families of cut bounds with exact LP intervals, including empty ones."""
    count = 0
    types = (0, 1)
    for n in (2, 3):
        goods = tuple(range(n))
        flows = {(i, j): z3.Real(f'cut_flow_{i}_{j}') for i in types for j in goods}
        cutoff = z3.Real('cut_test_lambda')
        menus = tuple(subsets(goods))
        for neighbors in product(menus, repeat=len(types)):
            for masses in ((Q(1, 5), Q(4, 5)), (Q(2, 5), Q(3, 5))):
                rows = [sum(flows[i, j] for j in goods) == masses[i] for i in types]
                rows += [v >= 0 if j in neighbors[i] else v == 0 for (i, j), v in flows.items()]
                for labels in product(('zero', 'interior', 'one'), repeat=n):
                    covered = {j for j in goods if labels[j] != 'zero'}
                    unsaturated = {j for j in goods if labels[j] != 'one'}
                    lower, upper = Q(0), Q(1)
                    for buyers in subsets(types):
                        targets = set().union(*(neighbors[i] for i in buyers))
                        if targets <= unsaturated:
                            lower = max(lower, sum(masses[i] for i in buyers) / len(targets))
                    for targets in subsets(covered):
                        mass = sum((masses[i] for i in types if set(neighbors[i]).intersection(targets)), Q(0))
                        upper = min(upper, mass / len(targets))
                    solver = z3.SolverFor('QF_LRA')
                    solver.add(*rows, cutoff >= 0, cutoff <= 1)
                    loads = [sum(flows[i, j] for i in types) for j in goods]
                    score_constraints(solver, loads, cutoff, labels)
                    assert (solver.check() == z3.sat) == (lower <= upper)
                    if lower <= upper:
                        for endpoint in {lower, upper}:
                            assert solver.check(cutoff == endpoint) == z3.sat
                        assert solver.check(z3.Or(cutoff < lower, cutoff > upper)) == z3.unsat
                    else:
                        assert lower - upper >= Q(1, 5 * n * n)
                    count += 1
    return count


def mass_threshold(priors, gains):
    values = [Q(v) for v in priors + gains]
    K = max([1] + [max(abs(v.numerator), v.denominator) for v in values])
    N = len(priors) * len(gains) + 2
    return Q(1, 2 * (N * K) ** N) / max([1] + gains)


def as_fraction(model, expression):
    val = model.eval(expression, model_completion=True)
    return Q(val.numerator_as_long(), val.denominator_as_long())


def statuses(x):
    return tuple('zero' if v == 0 else 'one' if v == 1 else 'interior' for v in x)


def score_constraints(solver, scores, cutoff, labels):
    for val, label in zip(scores, labels):
        if label != 'zero':
            solver.add(val >= cutoff)
        if label != 'one':
            solver.add(val <= cutoff)


def check_game(priors, payoffs, gains, r):
    n = len(gains)
    m = len(priors)
    eta = mass_threshold(priors, gains)
    graph = sorted(quotient(n))
    augmented = payoffs + [tuple((0, 1) if j in e else (-2, 1) for j in range(n)) for e in graph]
    raw = priors + [eta / len(graph)] * len(graph)
    total = 1 + eta
    assert sum(raw) == total

    def feasible_choices(row):
        p = [z3.Real(f'c_{j}') for j in range(n)]
        util = [a - b * v for (a, b), v in zip(row, p)]
        found = set()
        for k in range(n):
            s = z3.SolverFor('QF_LRA')
            s.add(sum(p) == r, *(v >= 0 for v in p), *(v <= 1 for v in p))
            s.add(*(util[k] >= w for w in util))
            if s.check() == z3.sat:
                found.add(k)
        return found

    old_choices = [feasible_choices(row) for row in payoffs]
    all_choices = [feasible_choices(row) for row in augmented]
    assert old_choices == all_choices[:m] and all(len(js) <= 2 for js in old_choices)
    assert all(js == set(e) for js, e in zip(all_choices[m:], graph))

    x = [z3.Real(f'x_{j}') for j in range(n)]
    cutoff = z3.Real('cutoff')
    a_flow = {(i, j): z3.Real(f'aug_f_{i}_{j}') for i, js in enumerate(all_choices) for j in js}
    solver = z3.SolverFor('QF_LRA')
    solver.add(sum(x) == r, *(v >= 0 for v in x), *(v <= 1 for v in x))
    solver.add(cutoff >= 0, cutoff <= max(gains))
    for i, row in enumerate(augmented):
        solver.add(sum(a_flow[i, j] for j in all_choices[i]) == raw[i] / total)
        utility = [a - b * x[j] for j, (a, b) in enumerate(row)]
        for j in all_choices[i]:
            f = a_flow[i, j]
            solver.add(f >= 0, *(z3.Implies(f > 0, utility[j] >= v) for v in utility))
    for j, d in enumerate(gains):
        score = d * sum(f for (i, k), f in a_flow.items() if k == j)
        solver.add(z3.Implies(x[j] > 0, score >= cutoff), z3.Implies(x[j] < 1, score <= cutoff))

    count = changed = 0
    while solver.check() == z3.sat:
        model = solver.model()
        observed = tuple(as_fraction(model, v) for v in x)
        labels = statuses(observed)
        retained = {e for e, var in a_flow.items() if e[0] < m and as_fraction(model, var) > 0}
        # Every seen pattern represents all real coverages with its attained row labels.
        # Freeze the pattern. Never change or optimize an original coverage coordinate.
        repair = z3.SolverFor('QF_LRA')
        f = {e: z3.Real(f'fixed_{e[0]}_{e[1]}') for e in retained}
        lam = z3.Real('fixed_cutoff')
        repair.add(lam >= 0, lam <= max(gains), *(v >= 0 for v in f.values()))
        for i in range(m):
            repair.add(sum(v for (h, j), v in f.items() if h == i) == priors[i])
        score_constraints(
            repair,
            [d * sum(v for (i, h), v in f.items() if h == j) for j, d in enumerate(gains)],
            lam,
            labels,
        )
        assert repair.check() == z3.sat
        answer = repair.model()
        fixed = {e: as_fraction(answer, v) for e, v in f.items()}
        target = as_fraction(answer, lam)
        old_raw = {e: as_fraction(model, v) * total for e, v in a_flow.items() if e[0] < m}
        for i in range(m):
            assert sum(v for (h, j), v in fixed.items() if h == i) == priors[i]
            vals = [a - b * observed[j] for j, (a, b) in enumerate(payoffs[i])]
            assert all(vals[j] == max(vals) for (h, j), v in fixed.items() if h == i and v > 0)
        for j, d in enumerate(gains):
            w = sum(v for (i, h), v in fixed.items() if h == j)
            assert observed[j] == 0 or d * w >= target
            assert observed[j] == 1 or d * w <= target
        # Detect examples for which simply dropping the new mass and rescaling
        # cannot retain the displayed defender choice at *any* old cutoff.
        w = [d * sum(v for (i, h), v in old_raw.items() if h == j) for j, d in enumerate(gains)]
        upper = min((w[j] for j in range(n) if observed[j] > 0), default=max(gains))
        lower = max((w[j] for j in range(n) if observed[j] < 1), default=0)
        changed += lower > upper
        count += 1
        key = [var > 0 if e in retained else var == 0 for e, var in a_flow.items() if e[0] < m]
        key.extend(
            v == 0 if label == 'zero' else v == 1 if label == 'one' else z3.And(v > 0, v < 1)
            for label, v in zip(labels, x)
        )
        solver.add(z3.Not(z3.And(*key)))
    assert count > 0
    return count, changed


def main():
    cuts, min_expansion = cut_checks()
    intervals = unit_gain_cutoff_checks()
    controls = [
        ([Q(1)], [((1, 1), (1, 1), (-3, 1))], [Q(1), Q(2), Q(1)], 1),
        (
            [Q(1, 3), Q(2, 3)],
            [((1, 2), (0, 0), (-3, 1)), ((-2, 1), (1, 1), (1, 2))],
            [Q(2, 3), Q(1, 2), Q(2)],
            2,
        ),
        (
            [Q(1, 2), Q(1, 2)],
            [((0, 0), (0, 0), (-2, 1)), ((-2, 1), (1, 1), (1, 1))],
            [Q(0), Q(1), Q(0)],
            1,
        ),
        ([Q(1)], [((0, 0), (0, 0))], [Q(0), Q(0)], 1),
    ]
    patterns = repairs = 0
    for case in controls:
        size, changed = check_game(*case)
        patterns += size
        repairs += changed
    assert repairs > 0
    print(
        f'{cuts} graph cuts for n=2…12, smallest observed expansion {min_expansion}. '
        f'{patterns} realizable old support/coverage patterns across {len(controls)} augmented '
        f'games had exact same-coverage repairs; {repairs} sampled allocations needed a repair. '
        f'{intervals} unit-gain cutoff intervals and separation bounds checked by exact LP.'
    )


if __name__ == '__main__':
    if not __debug__:
        raise RuntimeError('Run with Python assertions enabled.')
    main()
