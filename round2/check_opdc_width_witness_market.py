"""Check bounded-width search, physical price pairs, and both NOR lifts."""

from fractions import Fraction
from itertools import product
from random import Random

from check_opdc_feedback_market import check_all_equilibria
from opdc_two_sign_kernel import compile_two_sign_kernel
from opdc_width_witness_market import Instance, compile_market


def verify_answer(source, answer):
    if answer[0] == "root":
        return source.targets(answer[1]) == answer[1]
    _, j, a, b = answer
    ta, tb = source.targets(a), source.targets(b)
    return (a[j] == 0 and b[j] == 1 and a[j + 1:] == b[j + 1:]
            and a[:j] == ta[:j] and b[:j] == tb[:j] and ta[j] == 1 and tb[j] == 0)


class NAND:
    def __init__(self, n):
        self.n = n
        self.gates = []
        self.cache = {}
        self.one = self.nand(0, self.neg(0))
        self.zero = self.neg(self.one)

    def nand(self, a, b):
        key = tuple(sorted((a, b)))
        if key not in self.cache:
            self.cache[key] = self.n + len(self.gates)
            self.gates.append(key)
        return self.cache[key]

    def neg(self, a):
        return self.nand(a, a)

    def meet(self, a, b):
        return self.neg(self.nand(a, b))

    def join(self, a, b):
        return self.nand(self.neg(a), self.neg(b))

    def all(self, terms):
        acc = self.one
        for term in terms:
            acc = self.meet(acc, term)
        return acc

    def any(self, terms):
        acc = self.zero
        for term in terms:
            acc = self.join(acc, term)
        return acc

    def eq(self, a, b):
        return self.join(self.meet(a, b), self.meet(self.neg(a), self.neg(b)))

    def target(self, source, j, point):
        ones = []
        for args, result in zip(product((0, 1), repeat=len(source.readers[j])), source.tables[j]):
            if result:
                ones.append(self.all(point[v] if bit else self.neg(point[v])
                                     for v, bit in zip(source.readers[j], args)))
        return self.any(ones)

    def evaluate(self, bits, wire):
        trace = list(bits)
        for a, b in self.gates:
            trace.append(1 - trace[a] * trace[b])
        return trace[wire]


def witness_guard(source):
    """Build V for the actual fixed output layout and g'=V OR (NOT g)."""
    n = len(source.readers)
    d = 3 * n + 2
    c = NAND(d)
    flags = tuple(range(n + 1))
    lo = tuple(range(n + 1, 2 * n + 1))
    hi = tuple(range(2 * n + 1, 3 * n + 1))
    target_lo = tuple(c.target(source, j, lo) for j in range(n))
    target_hi = tuple(c.target(source, j, hi) for j in range(n))
    lo_ok = tuple(c.eq(a, b) for a, b in zip(lo, target_lo))
    hi_ok = tuple(c.eq(a, b) for a, b in zip(hi, target_hi))
    agree = tuple(c.eq(a, b) for a, b in zip(lo, hi))
    valid = [c.all((flags[0], *lo_ok, *agree))]
    for j in range(n):
        valid.append(c.all((flags[n - j], c.neg(lo[j]), hi[j], target_lo[j], c.neg(target_hi[j]),
                            *lo_ok[:j], *hi_ok[:j], *agree[j + 1:])))
    exclusive = c.all(c.nand(a, b) for i, a in enumerate(flags) for b in flags[:i])
    accepts = c.meet(c.any(valid), exclusive)
    return c, accepts, tuple(range(d - 1)) + (c.join(accepts, c.neg(d - 1)),)


def check_actual_graph(source, answer):
    n = len(source.readers)
    c = NAND(n)
    outputs = tuple(c.target(source, j, tuple(range(n))) for j in range(n))
    graph = compile_two_sign_kernel(n, c.gates, outputs)
    bad_heads = {w for v, row in enumerate(graph.rows) for w in row if graph.colors[v] == graph.colors[w]}
    assert bad_heads == {0, 1}
    cut = len(graph.evaluation_order)

    def lift(point):
        return graph.lift_rails(tuple(x for bit in point for x in (1 - bit, bit)))

    def raw_targets(x):
        return tuple(int(not any(x[w] for w in row)) for row in graph.rows)

    if answer[0] == "root":
        p = lift(answer[1])
        assert raw_targets(p) == p
    else:
        _, j, lo, hi = answer
        a, b = lift(lo), lift(hi)
        k = cut + 2 * j + 1
        f, h = raw_targets(a), raw_targets(b)
        assert a[:k] == f[:k] and b[:k] == h[:k]
        assert a[k] == h[k] == 0 and b[k] == f[k] == 1 and a[k + 1:] == b[k + 1:]
        assert graph.decode(("OV2", k, a, b)) == answer
    return len(graph.rows)


def check_pinned_cofactor(source, compiled, prices):
    c, accepts, outputs = witness_guard(source)
    z = tuple(prices[g] for pair in compiled.quarter_ports for g in pair)
    bits = tuple(int(v > Fraction(1, 2)) for v in z[1::2])
    assert bits[-1] == 1 and c.evaluate(bits, accepts) == 1
    assert sum(z) == c.n and sum(z) + z[-1] == c.n + Fraction(3, 4)
    assert all(a + b == 1 for a, b in zip(z[::2], z[1::2]))
    graph = compile_two_sign_kernel(c.n, c.gates, outputs, balance_cofactor=True)
    assert graph.middle_cofactor(z) == z
    return len(graph.rows)


def ring(n):
    readers = tuple(((j + 1) % n, (j + 2) % n) for j in range(n))
    tables = tuple((0, 1, 1, 0) if j else (1, 0, 0, 1) for j in range(n))
    bags = (tuple(range(n)),) if n <= 5 else tuple((0, 1, i, i + 1, i + 2)
                                                    for i in range(2, n - 2))
    return Instance(readers, tables, bags, tuple(range(-1, len(bags) - 1)))


def verify_one(source):
    compiled = compile_market(source)
    answer = compiled.decode(compiled.circuit_prices())
    roots = [x for x in product((0, 1), repeat=len(source.readers)) if source.targets(x) == x]
    assert (answer[0] == "root") == bool(roots) and verify_answer(source, answer)


def main():
    rng = Random(772471)
    count = 0
    for n in (1, 2, 3, 4):
        bag = (tuple(range(n)),)
        for _ in range(24):
            scopes = tuple(tuple(rng.sample(range(n), rng.randint(0, min(3, n)))) for _ in range(n))
            tables = tuple(tuple(rng.randrange(2) for _ in range(2 ** len(s))) for s in scopes)
            source = Instance(scopes, tables, bag, (-1,))
            verify_one(source)
            count += 1
    scopes = ((0, 1, 2), (0, 1), (0, 2), (0, 1, 3), (0, 2, 4))
    for _ in range(24):
        tables = tuple(tuple(rng.randrange(2) for _ in range(2 ** len(s))) for s in scopes)
        verify_one(Instance(scopes, tables, ((0, 1, 2), (0, 1, 3), (0, 2, 4)), (-1, 0, 0)))
        count += 1
    print(f"{count} seeded maps agree with unrestricted root enumeration and direct crossing checks.")

    for n in (3, 4, 6, 9):
        source = ring(n)
        compiled = compile_market(source)
        prices = compiled.circuit_prices()
        answer = compiled.decode(prices)
        assert (answer[0] == "OV2") == (n % 3 == 0) and verify_answer(source, answer)
        graph_size = check_actual_graph(source, answer)
        if n in (3, 4):
            expected = {g: prices[g] for pair in compiled.quarter_ports for g in pair}
            expected.update({g: prices[g] for pair in compiled.bits for g in pair})
            physical = check_all_equilibria(compiled.capacities, compiled.buyers, expected)
            assert compiled.decode(physical) == answer
            guard_size = check_pinned_cofactor(source, compiled, physical)
            verification = f"all-equilibria price check, guarded circuit {guard_size:,} vertices"
        else:
            verification = "open-circuit price check"
        print(f"n={n}, {len(compiled.capacities):,} goods, {len(compiled.buyers):,} buyers, "
              f"source lift {graph_size:,} vertices, {answer[0]}, {verification}.", flush=True)


if __name__ == "__main__":
    main()
