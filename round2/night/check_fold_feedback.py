"""Exact arithmetic checks of the feedback construction at the rotor-law level.

The test uses only Python's standard library. It checks both extremal closed
solutions in four coarse-precision examples and checks exact recovery at the
theorem's precision from an interval enclosing every closed solution.
"""

from fractions import Fraction as F
from itertools import combinations, product
from math import lcm
from operator import ge, le
from random import Random


def clip(value):
    return max(F(1, 4), min(F(3, 4), value))


def switch(load, quantum):
    assert 0 <= load <= 2
    periods, remainder = divmod(load, 2 * quantum)
    first = periods * quantum + min(quantum, remainder)
    second = load - first
    assert 0 <= first - load / 2 <= quantum / 2 and 0 <= second <= 1
    return first, second


def split_third(load, quantum):
    """Pick a solution of the two-switch loop and check its local equations."""
    assert 0 <= load <= 1
    # For total=(4j+r)δ, R1(R1(total))=jδ+(r−3)_+δ.
    # Given load=(3j+s)δ with 0≤s<3, choose r=s.
    periods, remainder = divmod(load, 3 * quantum)
    total = 4 * periods * quantum + remainder
    second = switch(total, quantum)[1]
    output, feedback = switch(second, quantum)
    assert total == load + feedback and 0 <= output <= load
    assert abs(output - load / 3) <= quantum / 3
    return output


def damp(load, quantum, depth):
    remainder = load
    for _ in range(depth):
        remainder = switch(remainder, quantum)[1]
    alpha = F(1, 2**depth)
    result = load - remainder + alpha / 2
    assert abs(result - ((1 - alpha) * load + alpha / 2)) <= quantum
    return result


def fold(first_input, second_input, threshold, quantum):
    positive, negative = map(clip, (first_input, second_input))
    low_positive = min(positive, threshold)
    low_negative = min(negative, 1 - threshold)
    assert low_negative >= threshold / 3
    first = threshold + positive - low_positive
    first += split_third(negative - low_negative, quantum)
    second = low_negative - threshold / 3
    second += split_third(low_positive, quantum)
    exact_fold = max(positive, threshold + (threshold - positive) / 3)
    error = abs(first_input + second_input - 1)
    assert abs(first + second - 1) <= error + 4 * quantum
    assert abs(first - exact_fold) <= error / 3 + 2 * quantum
    assert 0 <= first <= F(4, 3) and 0 <= second <= F(4, 3)
    return first, second


def independent_support_solver(b):
    """Enumerate exact complementary bases using rational row elimination."""
    n = len(b)
    matrix = [[F(1 if i == j else 2 if i > j else -2) for j in range(n)]
              for i in range(n)]
    for size in range(n + 1):
        for rows in combinations(range(n), size):
            system = [[matrix[i][j] for j in rows] + [-F(b[i])] for i in rows]
            for j in range(size):
                pivot = system[j][j]
                assert pivot != 0
                system[j] = [x / pivot for x in system[j]]
                for i in range(size):
                    if i != j:
                        scale = system[i][j]
                        system[i] = [x - scale * y for x, y in zip(system[i], system[j])]
            z = [F(0)] * n
            for i, equation in zip(rows, system):
                z[i] = equation[-1]
            w = [v + sum(c * x for c, x in zip(row, z)) for row, v in zip(matrix, b)]
            if min(z) >= 0 and min(w) >= 0:
                assert all(x * y == 0 for x, y in zip(z, w))
                return z
    raise AssertionError("No complementary basis")


def replay(u, b):
    result = []
    for value in b:
        new = max(u, -(u + value) / 3)
        result.append(new - u)
        u = new
    return result


def circuit(b, quantum, depth):
    scale = max(1, *map(abs, b))
    thresholds = [F(1, 2) - F(value, 32 * scale) for value in b]

    def step(point):
        first, second = point
        for threshold in thresholds:
            first, second = fold(first, second, threshold, quantum)
        return damp(second, quantum, depth), damp(first, quantum, depth)

    return step


def coarse_closed_solutions():
    # The two-switch divider has a unique output even when its internal
    # feedback can vary. In quantum units, h1(h1(t)) increases only on
    # t∈[4j+3,4j+4], where h0(h1(t)) is constant. Thus all solutions of
    # t-h1(h1(t))=v have the same output. This also proves the divider's
    # output is monotone in v. Every external rail operation is monotone.
    for b in [(3, -1, -5), (-3, -2, 2), (0, 0, 0), (4, -6, 2)]:
        step = circuit(b, F(1, 512), 3)
        extremes = []
        for origin in (F(0), F(5, 3)):
            ordered = le if origin == 0 else ge
            point = (origin, origin)
            for _ in range(1000):
                new = step(point)
                assert all(ordered(a, b) for a, b in zip(point, new))
                if new == point:
                    break
                point = new
            else:
                raise AssertionError("Failed to reach the extremal fixed point")
            extremes.append(point)
        assert all(a <= b for a, b in zip(*extremes))
    print("Four closed circuits reached both extremal routing solutions at coarse precision")


def full_precision(q):
    """Check the all-equilibria error certificate and test the worst-case endpoints."""
    Q = lcm(*(x.denominator for x in q))
    b = [int(Q * x) for x in q]
    n = len(b)
    B = max(1, *map(abs, b))
    U = 3**n + 1
    depth = (256 * B * U**2 - 1).bit_length()
    alpha = F(1, 2**depth)
    k = (100 * (n + 1)**2 * 2**(2 * depth) - 1).bit_length()
    quantum = F(1, 2**k)
    assert alpha <= F(1, 256 * B * U**2)
    assert quantum <= alpha**2 / (100 * (n + 1)**2)
    z = independent_support_solver(b)
    true_u = -sum(z) / 2
    # These exact-component calculations check the certificate without
    # requiring an outer iteration whose rate can approach 1-alpha.
    max_imbalance = (4 * n + 2) * quantum / alpha + 4 * n * quantum
    prefix_error = n * (max_imbalance / 3 + 2 * quantum)
    normalized_residual = max_imbalance + prefix_error + alpha + quantum
    radius = 8 * B * F(3, 2) * normalized_residual
    assert true_u.denominator <= U and radius < F(1, 2 * U**2)
    for endpoint in (true_u - radius, true_u + radius):
        recovered = endpoint.limit_denominator(U)
        assert recovered == true_u and replay(recovered, b) == z
    assert min(z) >= 0


def full_precision_fixed_points():
    """Decode actual least routing fixed points at the construction's precision."""
    for b in [(-3,), (3, -1, -5)]:
        n = len(b)
        B = max(map(abs, b))
        U = 3**n + 1
        depth = (256 * B * U**2 - 1).bit_length()
        k = (100 * (n + 1)**2 * 2**(2 * depth) - 1).bit_length()
        quantum = F(1, 2**k)
        step = circuit(b, quantum, depth)
        point = (F(0), F(0))
        for _ in range(300):
            new = step(point)
            if new == point:
                break
            point = new
        else:
            raise AssertionError("Failed to reach the full-precision fixed point")
        estimated = 8 * B * (clip(point[0]) - F(1, 2))
        z = replay(estimated.limit_denominator(U), b)
        assert z == independent_support_solver(b)
    print("Two actual full-precision closed routing solutions decoded exactly")


def priority_cases():
    quotas = [F(1, 4), F(1, 2), F(1, 4)]
    anchor = F(3)
    capacity = sum(quotas) + anchor
    count = 0
    for prices in product((F(0), F(1, 2), F(1)), repeat=3):
        bids = [F(j, 8) + price / 16 for j, price in enumerate(prices, 1)]
        endpoints = [F(0), *bids, F(1), F(2)]
        samples = endpoints + [(x+y)/2 for x, y in zip(endpoints, endpoints[1:])]
        for load in (F(0), F(1, 8), F(1, 4), F(1, 2), F(3, 4), F(1), F(2)):
            found = False
            for price in samples:
                # Feasible home loads on each row from the actual bid comparison,
                # treating the singleton with bid 1 as the fourth row.
                lower = [quota if price < bid else F(0)
                         for quota, bid in zip([*quotas, anchor], [*bids, F(1)])]
                upper = [quota if price <= bid else F(0)
                         for quota, bid in zip([*quotas, anchor], [*bids, F(1)])]
                target = capacity - load
                if target < sum(lower) or (price > 0 and target > sum(upper)):
                    continue
                found = True
                preceding = F(0)
                for i, quota in enumerate(quotas):
                    lo, hi = lower[i], min(upper[i], target - sum(lower) + lower[i])
                    if price > 0:
                        lo = max(lo, target - sum(upper) + upper[i])
                    output = min(quota, max(F(0), load - preceding))
                    assert quota - lo == quota - hi == output
                    preceding += quota
            assert found
            count += 1
    print(f"{count} priority-market checks covered every feasible price region and tie")


def local_cases():
    rng = Random(90714)
    for _ in range(750):
        quantum = F(1, 2**rng.randint(2, 64))
        first, second = (F(rng.randint(0, 768), 512) for _ in range(2))
        threshold = F(1, 2) + F(rng.randint(-20, 20), 640)
        fold(first, second, threshold, quantum)
        damp(first, quantum, rng.randint(1, 45))
    # Check all plateau endpoints, interior feedback choices, and both
    # switch exits on a rational mesh in a small saturated gadget.
    quantum = F(1, 16)
    for tick in range(193):
        total = F(tick, 128)
        first_stage = switch(total, quantum)[1]
        output, feedback = switch(first_stage, quantum)
        load = total - feedback
        if 0 <= load <= 1:
            assert output == split_third(load, quantum)
            assert abs(output - load / 3) <= quantum / 3
    print("750 rational component tests and a direct sweep of feedback values passed")


if __name__ == "__main__":
    priority_cases()
    local_cases()
    coarse_closed_solutions()
    full_precision_fixed_points()
    for v in product(range(-2, 3), repeat=3):
        full_precision(tuple(map(F, v)))
    for v in [(F(3, 2), F(-1, 2), F(-5, 2)),
              (F(-1, 17), F(3, 19), F(-7, 23), F(2, 31)),
              (F(0),), (F(-8, 15),)]:
        full_precision(v)
    print("129 full-precision error bounds and exact rational decodings passed")
