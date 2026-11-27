"""One elimination circuit for ordered affine Boolean targets F(x)=C x+b.

All matrix entries and right-hand sides are named, complementary input prices.
At every equilibrium the output prices give a full fixed point if one exists,
or an ordered crossing at the first nontrivial row escaping its own prefix.
"""

from dataclasses import dataclass
from functools import reduce
from operator import xor

from opdc_feedback_market import _MarketBuilder
from opdc_width_witness_market import _Circuit


class _Boolean:
    constants = (0, 1)

    @staticmethod
    def boolean(op, a, b=None):
        if op == "not":
            return 1 ^ a
        if op == "and":
            return a & b
        if op == "or":
            return a | b
        if op == "xor":
            return a ^ b
        raise ValueError(op)

    @staticmethod
    def fold(op, terms):
        if op == "xor":
            return reduce(xor, terms, 0)
        return int((all if op == "and" else any)(terms))


def _validate(matrix, rhs):
    n = len(rhs)
    if (not n or len(matrix) != n or any(len(row) != n for row in matrix)
            or any(bit not in (0, 1) for row in matrix for bit in row)
            or any(bit not in (0, 1) for bit in rhs)):
        raise ValueError("Expected a nonempty square Boolean coefficient matrix and right-hand side")


def _network(C, b, logic):
    n = len(b)
    false, true = logic.constants

    def both(a, b):
        return logic.boolean("and", a, b)

    def either(a, b):
        return logic.boolean("or", a, b)

    def add(a, b):
        return logic.boolean("xor", a, b)

    def negate(a):
        return logic.boolean("not", a)

    def dot(a, b):
        return logic.fold("xor", (both(x, y) for x, y in zip(a, b)))

    basis = []
    flags = []
    # A crossing may have a single one in its common higher suffix.
    suffix = [false] * n
    seen, inconsistent = false, false
    active_before = []
    for i in range(n):
        row = [negate(v) if j == i else v for j, v in enumerate(C[i])]
        rhs = b[i]
        for old, old_rhs, old_pivot in basis:
            subtract = dot(row, old_pivot)
            row = [add(val, both(subtract, x)) for val, x in zip(row, old)]
            rhs = add(rhs, both(subtract, old_rhs))
        pivot = []
        nonzero = false
        for v in row:
            pivot.append(both(v, negate(nonzero)))
            nonzero = either(nonzero, v)
        contradiction = both(negate(nonzero), rhs)
        inconsistent = either(inconsistent, contradiction)
        late = either(contradiction, logic.fold("or", pivot[i + 1:]))
        first = both(negate(seen), late)
        flags.append(first)
        seen = either(seen, late)
        active_before.append(negate(seen))
        pick_one = both(first, negate(rhs))
        suffix = [either(x, both(pick_one, p)) for x, p in zip(suffix, pivot)]
        basis.append((tuple(row), rhs, tuple(pivot)))

    def backsolve(initial, enabled):
        x = list(initial)
        for (row, rhs, pivot), use in reversed(tuple(zip(basis, enabled))):
            error = both(use, add(rhs, dot(row, x)))
            x = [add(a, both(error, p)) for a, p in zip(x, pivot)]
        return tuple(x)

    root = backsolve([false] * n, [true] * n)
    low = backsolve(suffix, active_before)
    high = backsolve([either(p, s) for p, s in zip(flags, suffix)], active_before)
    return negate(inconsistent), root, tuple(flags), low, high


def _answer(ports, read):
    feasible, root, flags, low, high = ports
    if read(feasible):
        return "root", tuple(map(read, root))
    return ("OV2", next(i for i, flag in enumerate(flags) if read(flag)),
            tuple(map(read, low)), tuple(map(read, high)))


def solve(matrix, rhs):
    """Evaluate the same network on bits using O(n^3) operations."""
    _validate(matrix, rhs)
    return _answer(_network(matrix, rhs, _Boolean()), int)


class _Logic(_Circuit):
    def fold(self, op, terms):
        if op != "xor":
            return super().fold(op, terms)
        return reduce(lambda a, b: self.boolean("xor", a, b), terms, self.constants[0])


@dataclass
class Market:
    capacities: dict
    buyers: dict
    ports: tuple
    pins: dict
    gates: tuple

    def decode(self, prices):
        def bit(pair):
            values = tuple(prices[g] for g in pair)
            if values not in ((1, 0), (0, 1)):
                raise ValueError("Expected an integral complementary output port")
            return int(values[1])
        return _answer(self.ports, bit)

    def circuit_prices(self):
        prices = {**self.pins, "source/zero": 0, "source/one": 1}
        for out, op, a, b in self.gates:
            prices[out] = (min if op == "min" else max)(prices[a], prices[b])
        return prices


def compile_market(matrix, rhs):
    _validate(matrix, rhs)
    n = len(rhs)
    logic = _Logic()
    pins = {}

    def pin(name, bit):
        pair = (name + "/zero", name + "/one")
        pins[pair[0]], pins[pair[1]] = 1 - bit, bit
        return pair

    coefficients = [[pin(f"matrix/{i}/{j}", matrix[i][j]) for j in range(n)] for i in range(n)]
    constants = [pin(f"rhs/{i}", rhs[i]) for i in range(n)]
    ports = _network(coefficients, constants, logic)
    builder = _MarketBuilder()
    logic.install(builder)
    for name, bit in {**pins, "source/zero": 0, "source/one": 1}.items():
        builder.source(name, bit)
    return Market(builder.capacities, builder.buyers, ports, pins, tuple(logic.gates))
