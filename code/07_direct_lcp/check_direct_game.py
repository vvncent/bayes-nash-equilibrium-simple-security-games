"""Exact checks for the one-call direct-game P-LCP reduction."""
from fractions import Fraction as Q
from itertools import combinations
from math import ceil, lcm

import z3


def determinant(matrix):
    work = [list(row) for row in matrix]
    size = len(work)
    sign = 1
    value = Q(1)
    for k in range(size):
        pivot = next((row for row in range(k, size) if work[row][k]), None)
        if pivot is None:
            return Q(0)
        if pivot != k:
            work[k], work[pivot] = work[pivot], work[k]
            sign = -sign
        leading = work[k][k]
        value *= leading
        for row in range(k + 1, size):
            if work[row][k]:
                factor = Q(work[row][k], leading)
                for col in range(k + 1, size):
                    work[row][col] -= factor * work[k][col]
    return sign * value


def matrices(b, d):
    buyers, goods = len(b), len(d)
    attack_count = buyers * goods
    cols = attack_count + goods + 1
    vertices = buyers + goods
    a_mat = [[Q(0)] * cols for _ in range(vertices)]
    d_mat = [[Q(0)] * cols for _ in range(vertices)]
    for i in range(buyers):
        for j in range(goods):
            e = i * goods + j
            a_mat[i][e] = d_mat[i][e] = 1
            a_mat[buyers + j][e] = d[j]
            d_mat[buyers + j][e] = b[i][j]
    for j in range(goods):
        for mat in (a_mat, d_mat):
            mat[buyers + j][attack_count + j] = -1
            mat[buyers + j][-1] = -1
    matrix = [[Q(0)] * cols + list(row) for row in zip(*d_mat)]
    matrix += [[-coef for coef in row] + [Q(0)] * vertices for row in a_mat]
    return a_mat, d_mat, matrix


def restricted_det(matrix, rows, cols):
    return determinant([[matrix[i][j] for j in cols] for i in rows])


def check_minors():
    instances = [
        ([[1, 1, 1], [1, 2, 2]], [2, 3, 5]),
        ([[0, Q(13, 17), Q(3, 4)], [Q(4, 9), 0, Q(19, 23)]], [0, Q(17, 12), Q(2, 29)]),
    ]
    for b, d in instances:
        a_mat, d_mat, _ = matrices(b, d)
        row_count, col_count = len(a_mat), len(a_mat[0])
        zero = positive = dense = 0
        for k in range(min(row_count, col_count) + 1):
            for rows in combinations(range(row_count), k):
                for cols in combinations(range(col_count), k):
                    a_det = restricted_det(a_mat, rows, cols)
                    d_det = restricted_det(d_mat, rows, cols)
                    product = a_det * d_det
                    assert product >= 0, (b, d, rows, cols, a_det, d_det)
                    zero += product == 0
                    positive += product > 0
                    dense += product > 0 and col_count - 1 in cols
        print(f"2 by 3 game with gains {d}: {zero} zero, {positive} positive, "
              f"{dense} positive with budget column")


def scalar(value):
    value = Q(value)
    return z3.Q(value.numerator, value.denominator)


def rational(expr):
    return Q(expr.numerator_as_long(), expr.denominator_as_long())


def row_as_ints(row):
    row = [Q(v) for v in row]
    common = lcm(*(v.denominator for v in row))
    return [v.numerator * (common // v.denominator) for v in row]


def pattern_precision(matrix, constant, bound):
    entries = [1, bound]
    for row, rhs in zip(matrix, constant):
        entries.extend(abs(v) for v in row_as_ints([*row, rhs, 1]))
    variables = len(matrix) + 1
    q_bound = (variables * max(entries)) ** variables
    return Q(1, 2 * bound * q_bound)


def slacks(matrix, constant, z):
    return [scalar(rhs) + sum(scalar(c) * v for c, v in zip(row, z) if c)
            for rhs, row in zip(constant, matrix)]


def verify_game(a, b, d, p, budget, z):
    m, n = len(a), len(d)
    f = [z[i * n:(i + 1) * n] for i in range(m)]
    x = z[-n:]
    scores = [d[j] * sum(row[j] for row in f) for j in range(n)]
    assert all(0 <= v <= 1 for v in x) and sum(x) == budget
    for i in range(m):
        assert sum(f[i]) == p[i] and min(f[i]) >= 0
        utility = [a[i][j] - b[i][j] * x[j] for j in range(n)]
        assert all(not f[i][j] or utility[j] == max(utility) for j in range(n))
    for j in range(n):
        for k in range(n):
            if x[j] > 0 and x[k] < 1:
                assert scores[j] >= scores[k]
    return f, x, scores


def pure_defenses(x, budget):
    left = [Q(0)]
    for v in x:
        left.append(left[-1] + v)
    cuts = sorted({Q(0), Q(1), *(v % 1 for v in left)})
    schedule = {}
    for lo, hi in zip(cuts, cuts[1:]):
        sample = (lo + hi) / 2
        pure = tuple(j for j in range(len(x)) if any(
            left[j] <= sample + k < left[j + 1] for k in range(budget)
        ))
        assert len(pure) == budget
        schedule[pure] = schedule.get(pure, Q(0)) + hi - lo
    assert len(schedule) <= len(x) and sum(schedule.values()) == 1
    for j, value in enumerate(x):
        assert sum(weight for pure, weight in schedule.items() if j in pure) == value
    return schedule


def check_game(a, b, d, p, budget):
    m, n = len(a), len(d)
    shifts = [1 + max(0, *(b[i][j] - a[i][j] for j in range(n))) for i in range(m)]
    shifted = [[a[i][j] + shifts[i] for j in range(n)] for i in range(m)]
    umax = max(max(row) for row in shifted)
    wmax = 1 + m * umax
    smax = 1 + max(d) * wmax
    bound = ceil(max(1, umax, wmax, 1 + smax))
    _, _, matrix = matrices(b, d)
    constant = [-v for row in shifted for v in row] + [1] * n + [budget] + list(p) + [-1] * n
    epsilon = pattern_precision(matrix, constant, bound)
    z = [z3.Real(f"z{k}") for k in range(len(matrix))]
    affine = slacks(matrix, constant, z)
    oracle = z3.Solver()
    for v, base in zip(z, affine):
        slack = base + scalar(epsilon) * v
        oracle.add(v >= 0, slack >= 0, z3.Or(v == 0, slack == 0))
    assert oracle.check() == z3.sat
    z_star = [rational(oracle.model().eval(v)) for v in z]
    assert all(0 <= v <= bound for v in z_star)
    for k, (row, rhs) in enumerate(zip(matrix, constant)):
        unshifted = rhs + sum(c * v for c, v in zip(row, z_star))
        assert unshifted >= -epsilon * bound
        if z_star[k] > 0:
            assert unshifted == -epsilon * z_star[k]
    repair = z3.Solver()
    for v, base, chosen in zip(z, affine, z_star):
        repair.add(v >= 0, v <= bound, base >= 0, v == 0 if chosen == 0 else base == 0)
    assert repair.check() == z3.sat
    equilibrium = [rational(repair.model().eval(v)) for v in z]
    f, x, scores = verify_game(a, b, d, p, budget, equilibrium)
    schedule = pure_defenses(x, budget)
    print(f"1/epsilon uses {epsilon.denominator.bit_length()} bits; exact coverages "
          f"{[str(v) for v in x]}, scores {[str(v) for v in scores]}, "
          f"{len(schedule)} pure defenses and {sum(v > 0 for row in f for v in row)} used attacks")
    return equilibrium


def main():
    check_minors()
    # Attacker necessarily splits over two defender-tied targets at interior coverages.
    equilibrium = check_game(
        [[0, 0]], [[1, 2]], [1, 1], [Q(1)], 1
    )
    assert equilibrium[:2] == [Q(1, 2), Q(1, 2)]
    assert equilibrium[-2:] == [Q(2, 3), Q(1, 3)]
    # Gains and all attack slopes can vanish, including tied attacks and cutoff zero.
    check_game([[0, 0, -1], [0, 0, 0]], [[0] * 3, [0] * 3],
               [0, 0, 0], [Q(2, 7), Q(5, 7)], 2)
    # Long binary data and a zero gain. The exact first coverage is strictly interior.
    long = Q(1, (1 << 73) + 7)
    check_game([[1 + long, 1, -5]], [[1, 1, 0]], [Q(2, 3), Q(3, 2), 0], [1], 1)
    # The exposed budget/target coordinates must include a cap and a lower bound.
    fixture = check_game([[10, -5, -5], [-3, 8, -3]],
                         [[2, 1, 0], [0, 2, 1]], [2, 2, 0],
                         [Q(9, 10), Q(1, 10)], 1)
    assert fixture[-3:] == [1, 0, 0]
    print("All direct-game checks passed.")


if __name__ == "__main__":
    main()
