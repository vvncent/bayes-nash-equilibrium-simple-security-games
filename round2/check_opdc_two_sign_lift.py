"""Exhaustive slice and answer checks for the two-threshold ordered lift.

Points are tuples in increasing coordinate order. The pair for source bit i
is (p_i, q_i), with q_i the original bit. Answers use zero-based OV2 axes
and OV1 prefix lengths. This file tests the semantic lift independently of
the compiler that realizes it as a NOR digraph.
"""

from collections import Counter, defaultdict
from itertools import combinations, product
from random import Random


def lift_point(q):
    return tuple(value for bit in q for value in (1 - bit, bit))


def lift_targets(point, source):
    d = len(point) // 2
    weight = sum(point)
    if weight != d:
        return (int(weight < d),) * (2 * d)

    p, q = point[::2], point[1::2]
    source_target = source[q]
    rows = [0] * (2 * d)
    higher_valid = True
    for i in reversed(range(d)):
        if higher_valid:
            rows[2 * i] = 1 - q[i]
            rows[2 * i + 1] = source_target[i]
        else:
            for j in (2 * i, 2 * i + 1):
                rows[j] = int(all(point[:j + 1]))
        higher_valid = higher_valid and p[i] != q[i]
    return tuple(rows)


def stationary_slices(targets):
    """Enumerate all stationary prefixes directly from the target equations."""
    result = defaultdict(list)
    for point, targets_at_point in targets.items():
        r = 0
        result[(r, point)].append(point)
        for bit, target in zip(point, targets_at_point):
            if bit != target:
                break
            r += 1
            result[(r, point[r:])].append(point)
    return result


def ov1(r, a, b):
    return ("OV1", r, min(a, b), max(a, b))


def ordered_answers(targets, slices):
    n = len(next(iter(targets)))
    result = {("root", x) for x in slices.get((n, ()), ())}
    for (r, suffix), roots in slices.items():
        for a, b in combinations(roots, 2):
            result.add(ov1(r, a, b))
        if not suffix or suffix[0] != 0:
            continue
        upper = slices.get((r, (1,) + suffix[1:]), ())
        for lo in roots:
            if targets[lo][r] == 1:
                for hi in upper:
                    if targets[hi][r] == 0:
                        result.add(("OV2", r, lo, hi))
    return result


def project_answer(answer):
    if answer[0] == "root":
        return ("root", answer[1][1::2])
    kind, index, a, b = answer
    if kind == "OV1":
        return ov1(index // 2, a[1::2], b[1::2])
    assert index % 2 == 1, ("spurious crossing on p", answer)
    return ("OV2", index // 2, a[1::2], b[1::2])


def predicted_slice(d, r, suffix, source_slices):
    """Classify lifts before inspecting the enumerated stationary set."""
    # At an odd boundary q_i is pinned alone. All higher pairs are complete.
    complete = suffix[r % 2:]
    defect = any(p == q for p, q in zip(complete[::2], complete[1::2]))
    if defect:
        k = min(r, max(0, d - sum(suffix)))
        return "defective", {(1,) * k + (0,) * (r - k) + suffix}
    source_suffix = suffix[1 - r % 2::2]
    response = source_slices.get((r // 2, source_suffix), ())
    return "clean", {lift_point(q) for q in response}


def check(source, points, counters):
    d = len(next(iter(source)))
    lifted = {x: lift_targets(x, source) for x in points}
    low_slices = stationary_slices(source)
    high_slices = stationary_slices(lifted)
    for r in range(2 * d + 1):
        for suffix in product((0, 1), repeat=2 * d - r):
            kind, predicted = predicted_slice(d, r, suffix, low_slices)
            actual = set(high_slices.get((r, suffix), ()))
            assert actual == predicted, (r, suffix, predicted, actual)
            counters[kind + " slices"] += 1
    expected = ordered_answers(source, low_slices)
    produced = ordered_answers(lifted, high_slices)
    projected = {project_answer(answer) for answer in produced}
    assert projected == expected, (expected - projected, projected - expected)
    counters["input maps"] += 1
    counters["source answers"] += len(expected)
    counters["lifted answers"] += len(produced)
    counters["OV1 at half-pair"] += sum(
        answer[0] == "OV1" and answer[1] % 2 == 1 for answer in produced
    )


def main():
    rng = Random(302146)
    counters = Counter()
    for d in range(1, 7):
        inputs = tuple(product((0, 1), repeat=d))
        points = tuple(product((0, 1), repeat=2 * d))
        if d <= 2:
            # Every possible tuple of d Boolean target truth tables.
            for outputs in product(inputs, repeat=len(inputs)):
                check(dict(zip(inputs, outputs)), points, counters)
        else:
            for _ in range({3: 128, 4: 32, 5: 8, 6: 2}[d]):
                targets = {q: rng.choice(inputs) for q in inputs}
                check(targets, points, counters)
            # Many simultaneous roots expose half-pair OV1s. A bitwise
            # complement supplies crossings. A constant map tests a promise.
            for transform in (lambda q: q, lambda q: tuple(1 - v for v in q),
                              lambda q: (1,) * d):
                check({q: transform(q) for q in inputs}, points, counters)
    assert counters["OV1 at half-pair"] > 0
    print(", ".join(f"{count:,} {field}" for field, count in counters.items()))


if __name__ == "__main__":
    main()
