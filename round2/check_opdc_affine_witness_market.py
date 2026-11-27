"""Verify priority Gaussian elimination and its ordinary matching market."""

from itertools import product
from random import Random

from check_opdc_feedback_market import check_all_equilibria
from opdc_affine_witness_market import compile_market, solve
from opdc_width_witness_market import Instance
from check_opdc_width_witness_market import check_actual_graph


def targets(matrix, rhs, point):
    return tuple((sum(a * x for a, x in zip(row, point)) + b) % 2
                 for row, b in zip(matrix, rhs))


def verify(matrix, rhs, answer, exhaustive):
    if answer[0] == "root":
        assert targets(matrix, rhs, answer[1]) == answer[1]
        return
    _, j, a, b = answer
    fa, fb = targets(matrix, rhs, a), targets(matrix, rhs, b)
    assert a[j] == 0 and b[j] == 1 and a[j + 1:] == b[j + 1:]
    assert a[:j] == fa[:j] and b[:j] == fb[:j] and fa[j] == 1 and fb[j] == 0
    if exhaustive:
        assert not any(targets(matrix, rhs, x) == x for x in product((0, 1), repeat=len(rhs)))


def physical_test(matrix, rhs):
    emitted = compile_market(matrix, rhs)
    prices = emitted.circuit_prices()
    ok, root, flags, low, high = emitted.ports
    expected = {g: prices[g] for pair in (ok, *root, *flags, *low, *high) for g in pair}
    physical = check_all_equilibria(emitted.capacities, emitted.buyers, expected)
    answer = emitted.decode(physical)
    verify(matrix, rhs, answer, True)
    assert solve(matrix, rhs) == answer
    return len(emitted.capacities), len(emitted.buyers), answer


def torus(m, order):
    """A sparse torus with invertible, overlapping row additions."""
    n = m * m
    place = {old: new for new, old in enumerate(order)}
    directed = []
    for a in range(m):
        for b in range(m):
            east = m * a + (b + 1) % m
            north = m * ((a + 1) % m) + b
            directed.append({east, north})
    matrix, rhs = [], []
    for v in order:
        _, b = divmod(v, m)
        stationary = directed[v]
        if b % 2:
            stationary = stationary ^ directed[v - 1]
        readers = {place[w] for w in stationary ^ {v}}
        matrix.append(tuple(int(j in readers) for j in range(n)))
        rhs.append(int(v == 0) ^ int(b % 2 == 1 and v - 1 == 0))
    return tuple(matrix), tuple(rhs)


def main():
    count, roots = 0, 0
    for n in (1, 2, 3):
        for values in product((0, 1), repeat=n * (n + 1)):
            matrix = tuple(values[n * i:n * i + n] for i in range(n))
            rhs = values[n * n:]
            answer = solve(matrix, rhs)
            verify(matrix, rhs, answer, True)
            roots += int(answer[0] == "root")
            count += 1
    print(f"{count:,} affine systems exhaustively checked, {roots:,} root cases.", flush=True)
    # Earliest late pivot is the first row, but it is globally consistent.
    matrix = ((1, 1), (0, 0))
    assert solve(matrix, (1, 1)) == ("root", (0, 1))
    assert solve(matrix, (1, 0)) == ("OV2", 0, (0, 0), (1, 0))
    # An invertible exchange matrix still needs a late first pivot.
    assert solve(((1, 1), (1, 1)), (0, 0))[0] == "root"
    xor_ring = ((0, 1, 1), (1, 0, 1), (1, 1, 0))
    for coefficients, rhs in ((matrix, (1, 1)), (matrix, (1, 0)),
                              (xor_ring, (1, 0, 0))):
        ng, nb, answer = physical_test(coefficients, rhs)
        print(f"all-equilibria check: {ng:,} goods, {nb:,} buyers, {answer}", flush=True)

    scopes = ((1, 2), (0, 2), (0, 1))
    tables = ((1, 0, 0, 1), (0, 1, 1, 0), (0, 1, 1, 0))
    instance = Instance(scopes, tables, ((0, 1, 2),), (-1,))
    graph_size = check_actual_graph(instance, solve(xor_ring, (1, 0, 0)))
    rng = Random(981445)
    torus_count = 0
    axes = set()
    for m in (2, 3, 4, 5, 6):
        n = m * m
        for trial in range(7):
            order = list(range(n))
            rng.shuffle(order)
            if trial == 0:
                warm = [i for i in order if i % m % 2 == 1]
                order = warm + [i for i in order if i % m % 2 == 0]
            matrix, rhs = torus(m, order)
            assert all(sum(row) == 3 for row in matrix)
            answer = solve(matrix, rhs)
            assert answer[0] == "OV2"
            verify(matrix, rhs, answer, False)
            axes.add(answer[1])
            torus_count += 1
    print(f"{torus_count} permuted sparse tori through 36 bits, crossing axes {sorted(axes)}; "
          f"actual two-first-exception NOR lift with {graph_size:,} vertices checked.")


if __name__ == "__main__":
    main()
