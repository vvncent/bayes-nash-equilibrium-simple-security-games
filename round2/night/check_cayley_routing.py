"""Exact Cayley feedback checks on the four-row example.

The closed circuit uses the proved switch transfer law. Its parameters and
fixed-point search do not use a known LCP solution. An independent enumeration
checks the answer afterwards. The test does not expand the switches into buyers.
"""

from bisect import bisect_right
from fractions import Fraction as F
from itertools import combinations, product
from math import lcm

from check_fold_feedback import switch


C = ((1, 1, 1, 1), (-1, 1, 1, 2), (-1, -1, 1, 1), (-1, -2, -1, 1))
R = [[F(x, 9) for x in row] for row in
     ((1, -4, -2, 0), (0, -1, -4, -4), (2, 0, 1, -4), (4, 4, 0, -1))]
G = [[abs(x) for x in row] for row in R]
BASE = (F(4, 5), F(1), F(4, 5), F(1))
N = len(C)


def apply(matrix, vector):
    return [sum(a * x for a, x in zip(row, vector)) for row in matrix]


def solve(matrix, rhs):
    """Rational Gaussian elimination, also for the empty active set."""
    rows = [list(map(F, row)) + [F(x)] for row, x in zip(matrix, rhs)]
    for j in range(len(rows)):
        k = next(i for i in range(j, len(rows)) if rows[i][j])
        rows[j], rows[k] = rows[k], rows[j]
        pivot = rows[j][j]
        rows[j] = [item / pivot for item in rows[j]]
        for i in range(len(rows)):
            if i != j:
                multiplier = rows[i][j]
                rows[i] = [a - multiplier * b for a, b in zip(rows[i], rows[j])]
    return [row[-1] for row in rows]


def support_solution(q):
    answers = set()
    for size in range(N + 1):
        for support in combinations(range(N), size):
            z = [F(0)] * N
            block = [[C[i][j] for j in support] for i in support]
            positive = solve(block, [-q[i] for i in support])
            for i, value in zip(support, positive):
                z[i] = value
            w = [a + b for a, b in zip(apply(C, z), q)]
            if all(x >= 0 and y >= 0 and x*y == 0 for x, y in zip(z, w)):
                answers.add((tuple(z), tuple(w)))
    assert len(answers) == 1
    return answers.pop()


def certificates():
    plus = [[2 * int(i == j) + C[i][j] for j in range(N)] for i in range(N)]
    minus = [[2 * int(i == j) - C[i][j] for j in range(N)] for i in range(N)]
    for j in range(N):
        assert apply(plus, [row[j] for row in R]) == [row[j] for row in minus]
    assert [sum(row[j] for row in G) for j in range(N)] == [F(7,9), 1, F(7,9), 1]
    received = apply(G, BASE)
    assert [b-g for b, g in zip(BASE, received)] == [F(4,45)] * N
    assert max(g/b for b,g in zip(BASE, received)) == F(41,45)
    inverse_row_sums = solve([[int(i == j) - G[i][j] for j in range(N)]
                              for i in range(N)], [1] * N)
    assert inverse_row_sums == [F(9), F(45,4), F(9), F(45,4)]
    return plus, max(inverse_row_sums)


def ceiling_log2(value):
    exponent = max(0, value.numerator.bit_length() - value.denominator.bit_length())
    return exponent + int(2**exponent < value)


class Distributor:
    """Evaluate a compressed binary tree using bit reversal of rotor unit indices."""

    def __init__(self, coefficients, k):
        self.k = k
        self.coefficients = list(coefficients)
        self.boundaries = []
        current = 0
        for weight in coefficients:
            current += int((1 << k) * weight)
            self.boundaries.append(current)
        assert current <= 1 << k
        self.boundaries.append(1 << k)
        # A leaf prefix reached by left/right choices corresponds to stream
        # unit indices with these successive low-order bits. This lets the
        # exact tests evaluate long trees without materializing their buyers.
        self.pieces = []
        self.splits = 0

        def visit(lo, width, residue, stride):
            destination = bisect_right(self.boundaries, lo)
            if lo + width <= self.boundaries[destination]:
                self.pieces.append((destination, residue, stride))
                return
            self.splits += 1
            half = width // 2
            visit(lo, half, residue, stride * 2)
            visit(lo + half, half, residue + stride, stride * 2)

        visit(0, 1 << k, 0, 1)
        assert self.splits <= len(coefficients) * k
        for i in range(len(coefficients) + 1):
            assert sum(dest == i for dest, _, _ in self.pieces) <= 2*k+1

    def route_units(self, load, unit):
        """Input and output are whole ticks; one rotor quantum has `unit` ticks."""
        count, tail = divmod(load, unit)
        result = [0] * len(self.boundaries)
        for dest, residue, stride in self.pieces:
            number = (count + stride - 1 - residue) // stride
            result[dest] += number * unit
            if count % stride == residue:
                result[dest] += tail
        assert sum(result) == load
        return result

    def explicit(self, load, quantum):
        """Independent slow evaluation, recursively invoking the manuscript law."""
        result = [F(0)] * len(self.boundaries)

        def route(lo, width, t):
            dest = bisect_right(self.boundaries, lo)
            if lo + width <= self.boundaries[dest]:
                result[dest] += t
                return
            left, right = switch(t, quantum)
            half = width // 2
            route(lo, half, left)
            route(lo+half, half, right)

        route(0, 1 << self.k, load)
        return result


def folded(positive, negative, base):
    """Compute the two integer-tick outputs of the physical abs router."""
    assert base % 2 == 0
    half = base // 2
    p, n = min(positive, base), min(negative, base)
    a = half + max(0, p-half) + max(0, n-half)
    b = max(0, min(p, half) + min(n, half) - half)
    return a, b


def test_components():
    assert all(folded(30+i, 30-i, 60) == (30+abs(i), 30-abs(i))
               for i in range(-30, 31))
    for p, n, u, v in product(range(0, 121, 10), repeat=4):
        left, right = folded(p, n, 60), folded(u, v, 60)
        assert sum(abs(x-y) for x, y in zip(left, right)) <= abs(p-u) + abs(n-v)
    cases = [(0, F(1,9), F(5,11), 0), (F(1,4), F(1,2), F(1,4), 0),
             (0, 0, 0, 0), (F(2,17), 0, F(9,16), F(1,19))]
    for k, weights in product((3, 7, 23), cases):
        router = Distributor(weights, k)
        quantum = F(1, 1 << (k+3))
        error = F(3, 2**(k+1)) + (2*k+1)*quantum
        for value in [F(0), F(3,2), 17*quantum/7, F(75,128), F(1), F(6,7)]:
            ticks = lcm(value.denominator, quantum.denominator)
            actual = [F(v,ticks) for v in router.route_units(int(value*ticks), int(quantum*ticks))]
            assert actual == router.explicit(value, quantum)
            assert all(abs(v-weight*value) <= error for v,weight in zip(actual, weights))
    print("Clipped absolute rails and 72 compressed distributors agreed with direct switch evaluation")


def closed_case(q, shifted, gamma_norm):
    q = tuple(map(F, q))
    bias = solve(shifted, [-2*v for v in q])
    sigma = min(F(1,45)/(1+abs(v)) for v in bias)
    constant = [[F(2,45) + sign*sigma*v for sign in (1,-1)] for v in bias]
    common_denominator = lcm(*(v.denominator for v in q))
    largest_integer = max([2*common_denominator, *(abs(int(common_denominator*v)) for v in q)])
    limit = 2*common_denominator * (N*largest_integer)**N
    k = max(2, ceiling_log2(32*N*gamma_norm*limit**2/sigma))
    quantum_exponent = k + ceiling_log2(F(2*k+1))
    quantum = F(1, 1 << quantum_exponent)
    epsilon = F(3, 2**(k+1)) + (2*k+1)*quantum
    assert 2*N*gamma_norm*epsilon/sigma < F(1, 2*limit**2)
    distributors = [Distributor([row[j] for row in G], k) for j in range(N)]
    assert 2*sum(tree.splits for tree in distributors) <= 2*N*N*k
    ticks = lcm(quantum.denominator, *(b.denominator*2 for b in BASE),
                *(c.denominator for pair in constant for c in pair))
    unit = int(ticks*quantum)
    bases = [int(ticks*b) for b in BASE]
    sources = [[int(ticks*c) for c in pair] for pair in constant]

    def step(point):
        new = [pair.copy() for pair in sources]
        for j, (positive, negative) in enumerate(point):
            a, b = folded(positive, negative, bases[j])
            assert max(a, b) <= 3*ticks//2
            for side, value in enumerate((a, b)):
                deliveries = distributors[j].route_units(value, unit)
                for i, amount in enumerate(deliveries[:-1]):
                    target = side if R[i][j] >= 0 else 1-side
                    new[i][target] += amount
        return new

    # The rail operators are nondecreasing. The zero seed computes a closed
    # solution independently of the complementary-basis oracle below.
    point = [[0, 0] for _ in range(N)]
    for iteration in range(1, 4001):
        new = step(point)
        assert all(a <= b for row, nxt in zip(point, new) for a, b in zip(row, nxt))
        if new == point:
            break
        point = new
    else:
        raise AssertionError("Exact closed routing did not stabilize within 4000 iterations")
    assert step(point) == point
    real = [[F(value, ticks) for value in row] for row in point]
    x = [((pair[0] - base/2)/sigma).limit_denominator(limit) for pair,base in zip(real,BASE)]
    decoded = tuple(max(v, 0) for v in x), tuple(2*max(-v, 0) for v in x)
    truth = support_solution(q)
    assert decoded == truth
    true_x = [z-w/2 for z,w in zip(*truth)]
    error = []
    for (p,n), t, base in zip(real, true_x, BASE):
        assert abs(sigma*t) <= base/4 and t.denominator <= limit
        error.append(abs(p-base/2-sigma*t) + abs(n-base/2+sigma*t))
    assert all(e <= c + 2*N*epsilon for e,c in zip(error, apply(G,error)))
    assert all(e <= 2*N*gamma_norm*epsilon for e in error)
    print(f"q={tuple(map(str,q))}: k={k}, rotor precision={quantum_exponent} bits, "
          f"switches={2*sum(t.splits for t in distributors)}, closed after {iteration} steps")
    return truth


if __name__ == "__main__":
    plus, gamma = certificates()
    test_components()
    assert closed_case([0,0,0,0], plus, gamma) == ((0,)*4, (0,)*4)
    closed_case([-2,1,-1,F(3,2)], plus, gamma)
    # The original complementarity solution is z=(1,0,1/2,0),
    # w=(0,0,0,2), with a genuine z_i=w_i=0 tie in row 2.
    z, w = closed_case([F(-3,2), F(1,2), F(1,2), F(7,2)], plus, gamma)
    assert z == (1,0,F(1,2),0) and w == (0,0,0,2)
