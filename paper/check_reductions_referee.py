"""Exact examples for the switching-flow decoder and the Cayley subclass.

Run with Python 3 and SymPy. The finite checks complement the written proofs.
"""

from itertools import combinations, product
from random import Random

from sympy import Matrix, Rational, diag, eye, factor, ones, symbols


def check_switching_flows():
    # Use integer numerators throughout, on the grid {0, 1/4, ..., 4}.
    unit = 4
    pairs = points = fractional = different = 0
    for n in (1, 2):
        for exits in product(range(n + 2), repeat=2 * n):
            live = {n, n + 1}
            for _ in range(n):
                live.update(v for v in range(n) if any(h in live for h in exits[2*v:2*v+2]))
            if len(live) < n + 2:
                continue
            for origin in range(n):
                pairs += 1
                walk = [0] * (2 * n)
                vertex = origin
                while vertex < n:
                    first = 2 * vertex
                    edge = first + (walk[first] + walk[first + 1]) % 2
                    walk[edge] += 1
                    vertex = exits[edge]
                for x in product(range(4 * unit + 1), repeat=n):
                    incoming = [0] * (n + 2)
                    rounded_in = [0] * (n + 2)
                    incoming[origin], rounded_in[origin] = unit, 1
                    rounded_out = []
                    for v, mass in enumerate(x):
                        k, rem = divmod(mass, 2 * unit)
                        flows = (k * unit + min(rem, unit), k * unit + max(rem - unit, 0))
                        for head, flow in zip(exits[2*v:2*v+2], flows):
                            incoming[head] += flow
                            rounded_in[head] += flow // unit
                            rounded_out.append(flow // unit)
                    if tuple(incoming[:n]) != x:
                        continue
                    for v, mass in enumerate(x):
                        total = mass // unit
                        assert rounded_in[v] == total
                        assert rounded_out[2*v:2*v+2] == [(total + 1) // 2, total // 2]
                    assert sum(rounded_in[n:]) == rounded_in[vertex] == 1
                    assert all(incoming[t] == unit * rounded_in[t] for t in (n, n + 1))
                    points += 1
                    fractional += any(mass % unit for mass in x)
                    different += rounded_out != walk
    assert (pairs, points, fractional, different) == (440, 2440, 1620, 728)
    print(f"{pairs} graph/origin pairs, {points} fixed points, {fractional} fractional, "
          f"{different} switching flows different from the run profile.")


def check_cayley_scope():
    rng = Random(20261126)
    cases = []
    for n in range(1, 5):
        for rep in range(15):
            raw = Matrix(n, n, lambda i, j: rng.randint(-3, 3))
            bound = 1 + max(sum(abs(raw[i, j]) for j in range(n)) for i in range(n))
            scale = diag(*(2**i for i in range(n)))
            cases.append((scale * raw * scale.inv() / bound, Rational(rep + 1, 5)))
    cases.append((Matrix([[0, 2], [0, 0]]), Rational(1)))
    offsets = 0
    for R, step in cases:
        n = R.rows
        I = eye(n)
        A = (I + R).inv() * (I - R) / step
        B = R.applyfunc(abs)
        t = (I - B).inv() * ones(n, 1)
        v = (I - B.T).inv() * ones(n, 1)
        assert all(a >= 1 for a in t) and all(a >= 1 for a in v)
        D = diag(*(v[i] / t[i] for i in range(n)))
        residual = D - R.T * D * R
        hessian = D * A + A.T * D
        S = I + step * A
        assert S.T * residual * S == 2 * step * hessian
        for k in range(1, n + 1):
            assert residual[:k, :k].det() > 0 and hessian[:k, :k].det() > 0
        for _ in range(7):
            q = Matrix([rng.randint(-4, 4) for _ in range(n)])
            answers = set()
            for k in range(n + 1):
                for active in combinations(range(n), k):
                    z = Matrix.zeros(n, 1)
                    if active:
                        values = -A.extract(active, active).inv() * q.extract(active, [0])
                        for j, value in zip(active, values):
                            z[j] = value
                    w = A * z + q
                    if all(value >= 0 for value in (*z, *w)):
                        assert (z.T * D * w)[0] == 0
                        answers.add(tuple(z))
            assert len(answers) == 1
            offsets += 1
    A = eye(3) + 2 * Matrix([[0, 1, 0], [0, 0, 1], [1, 0, 0]])
    x = symbols("x")
    assert factor(A.charpoly(x).as_expr()) == (x - 3) * (x*x + 3)
    assert A.det() == 9
    for k in (1, 2):
        for indices in combinations(range(3), k):
            assert A.extract(indices, indices).det() == 1
    print(f"{len(cases)} promised matrices, {offsets} offsets, and the excluded P-matrix verified.")


if __name__ == "__main__":
    check_switching_flows()
    check_cayley_scope()
