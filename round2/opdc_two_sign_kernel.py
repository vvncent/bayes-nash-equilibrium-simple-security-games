"""Compile a Boolean OPDC target circuit to a colored, ordered NOR graph.

Input wires 0 through d-1 represent source bits. Each two-input NAND gate
appends a wire, and outputs names one target wire per source bit. The graph's
last 2d coordinates are p0,q0,p1,q1,... . Its first two coordinates are the
only vertices read across a same-color arc. Open-circuit evaluation order
and OPDC coordinate order may differ.
"""

from dataclasses import dataclass
from graphlib import TopologicalSorter


@dataclass
class TwoSignKernel:
    rows: tuple
    colors: tuple
    dimension: int
    evaluation_order: tuple

    def middle_cofactor(self, rails, meet=min, join=max):
        """Evaluate signed gates with the two negated threshold reads set to 0 and 1."""
        if len(rails) != 2 * self.dimension:
            raise ValueError("Expected one rail pair per source coordinate")
        cut = len(self.evaluation_order)
        signed = [None] * cut + list(rails)
        pins = {0: 0, 1: 1}

        def row(v):
            args = [pins[w] if self.colors[w] == self.colors[v] else signed[w]
                    for w in self.rows[v]]
            if len(args) == 1:
                return args[0]
            return (join if self.colors[v] else meet)(*args)

        for v in self.evaluation_order:
            signed[v] = row(v)
        return tuple(row(v) for v in range(cut, len(self.rows)))

    def lift_rails(self, rails):
        """Return the unique assignment to the open circuit at fixed p,q rails."""
        if len(rails) != 2 * self.dimension or any(bit not in (0, 1) for bit in rails):
            raise ValueError("Expected one pair of Boolean rails per source coordinate")
        values = [0] * len(self.evaluation_order) + list(rails)
        for v in self.evaluation_order:
            values[v] = int(not any(values[w] for w in self.rows[v]))
        return tuple(values)

    def decode(self, answer, original_directions=None):
        """Decode a certified ('root'/'OV1'/'OV2', zero-based axis, *points).

        Roots carry the full dimension as their axis. Passing the original
        signed direction circuit permits returning an outward (OV3) witness.
        """
        kind, axis, *points = answer
        cut = len(self.evaluation_order)
        projected = [tuple(x[cut + 1::2]) for x in points]
        if kind == "root":
            return kind, self.dimension, projected[0]
        if kind not in ("OV1", "OV2") or axis < cut:
            raise ValueError("Unexpected violation in the gate block or at the boundary")
        rail_axis = axis - cut
        if kind == "OV1":
            return kind, (rail_axis + 1) // 2 - 1, *sorted(projected)
        if rail_axis % 2 != 1:
            raise ValueError("Unexpected crossing on the complementary rail")
        i = rail_axis // 2
        if original_directions is not None:
            for q in projected:
                if (q[i], original_directions(q)[i]) in ((0, -1), (1, 1)):
                    return "OV3", i, q
        return kind, i, *projected


class SignedCircuit:
    """Physical NOR gates with signed value at v equal to x[v] XOR color[v]."""

    def __init__(self, primary_count):
        self.rows = [()] * primary_count
        self.colors = [0] * primary_count
        self.adapters = {}
        self.gates = {}
        self.heads = []
        self.one = self.nor(0, ())
        self.zero = self.nor(1, ())

    def nor(self, color, wires):
        self.rows.append(tuple(wires))
        self.colors.append(color)
        return len(self.rows) - 1

    def positive_read(self, source, reader_color):
        if self.colors[source] != reader_color:
            return source
        if source not in self.adapters:
            self.adapters[source] = self.nor(1 - reader_color, (source,))
        return self.adapters[source]

    def binary(self, color, a, b):
        """Signed AND (color zero) or OR (color one)."""
        if a == b:
            return a
        key = color, min(a, b), max(a, b)
        if key not in self.gates:
            self.gates[key] = self.nor(color, (self.positive_read(a, color),
                                               self.positive_read(b, color)))
        return self.gates[key]

    def both(self, a, b):
        if self.zero in (a, b):
            return self.zero
        if self.one in (a, b):
            return b if a == self.one else a
        return self.binary(0, a, b)

    def either(self, a, b):
        if self.one in (a, b):
            return self.one
        if self.zero in (a, b):
            return b if a == self.zero else a
        return self.binary(1, a, b)

    def threshold(self, wires, level):
        """Monotone dynamic program for 'at least level', with fan-in two."""
        counts = [self.one] + [self.zero] * level
        for i, wire in enumerate(wires):
            for t in range(min(level, i + 1), 0, -1):
                counts[t] = self.either(counts[t], self.both(wire, counts[t - 1]))
        return counts[level]

    def threshold_complement(self, source):
        # Give this exceptional read its own head, which has a single reader.
        head = self.nor(1 - self.colors[source], (source,))
        self.heads.append(head)
        return self.nor(self.colors[head], (head,))

    def keep_dependencies(self, primary_count):
        """Remove unused gates, including the cardinality program's initial constants."""
        live = set(range(primary_count))
        stack = list(live)
        while stack:
            for w in self.rows[stack.pop()]:
                if w not in live:
                    live.add(w)
                    stack.append(w)
        order = sorted(live)
        index = {v: i for i, v in enumerate(order)}
        self.rows = [tuple(index[w] for w in self.rows[v]) for v in order]
        self.colors = [self.colors[v] for v in order]
        self.heads = [index[v] for v in self.heads]

    def bound_degree(self):
        readers = [[] for _ in self.rows]
        for v, wires in enumerate(self.rows):
            for i, w in enumerate(wires):
                readers[w].append((v, i))

        def copies(w, count):
            if count == 1:
                return [w]
            middle = self.nor(1 - self.colors[w], (w,))
            left = self.nor(self.colors[w], (middle,))
            right = self.nor(self.colors[w], (middle,))
            return copies(left, count // 2) + copies(right, count - count // 2)

        for w, uses in enumerate(readers):
            if len(uses) > 1:
                for (v, i), leaf in zip(uses, copies(w, len(uses))):
                    row = list(self.rows[v])
                    row[i] = leaf
                    self.rows[v] = tuple(row)

    def subdivide(self, girth):
        length = max(1, (girth + 2) // 3)
        if length % 2 == 0:
            length += 1
        if length == 1:
            return
        for v, wires in enumerate(tuple(self.rows)):
            delayed = []
            for w in wires:
                for i in range(length - 1):
                    # Alternate from the reader end. The first new gate reads
                    # w with the old sign, retaining the actual exceptional head.
                    w = self.nor(self.colors[v] ^ (i % 2), (w,))
                delayed.append(w)
            self.rows[v] = tuple(delayed)

    def finish(self, dimension, girth):
        primaries = 2 * dimension
        self.keep_dependencies(primaries)
        self.bound_degree()
        self.subdivide(girth)
        dependencies = {v: tuple(w for w in self.rows[v] if w >= primaries)
                        for v in range(primaries, len(self.rows))}
        topo = tuple(TopologicalSorter(dependencies).static_order())
        heads = set(self.heads)
        order = self.heads + [v for v in topo if v not in heads] + list(range(primaries))
        index = {v: i for i, v in enumerate(order)}
        return TwoSignKernel(tuple(tuple(index[w] for w in self.rows[v]) for v in order),
                             tuple(self.colors[v] for v in order), dimension,
                             tuple(index[v] for v in topo))


def compile_two_sign_kernel(dimension, nand_gates, outputs, girth=3, balance_cofactor=False):
    """Return an ordered NOR graph. Balancing improves its continuous middle cofactor."""
    if dimension < 1 or len(outputs) != dimension or girth < 1:
        raise ValueError("Expected positive dimension/girth and one target per bit")
    if any(len(g) != 2 or any(w < 0 or w >= dimension + i for w in g)
           for i, g in enumerate(nand_gates)):
        raise ValueError("Each NAND operand must be an earlier wire")
    if any(w < 0 or w >= dimension + len(nand_gates) for w in outputs):
        raise ValueError("Unknown output wire")
    rails = list(range(2 * dimension))
    c = SignedCircuit(len(rails))

    lower_threshold = c.threshold(rails, dimension)
    upper_threshold = c.threshold(rails, dimension + 1)
    below = c.threshold_complement(lower_threshold)
    at_most = c.threshold_complement(upper_threshold)
    # On the central layer W=d, this is exactly the complement of rail v.
    opposite = [c.threshold(rails[:v] + rails[v + 1:], dimension) for v in rails]
    target_wires = [(q, opposite[q]) for q in rails[1::2]]
    for a, b in nand_gates:
        pos_a, neg_a = target_wires[a]
        pos_b, neg_b = target_wires[b]
        target_wires.append((c.either(neg_a, neg_b), c.both(pos_a, pos_b)))

    prefixes = []
    acc = c.one
    for v in rails:
        acc = c.both(acc, v)
        prefixes.append(acc)
    higher_valid, higher_invalid = c.one, c.zero
    for i in reversed(range(dimension)):
        p, q = 2 * i, 2 * i + 1
        for v, original in ((p, opposite[q]), (q, target_wires[outputs[i]][0])):
            core = c.either(c.both(higher_invalid, prefixes[v]), c.both(higher_valid, original))
            if balance_cofactor:
                core = c.either(upper_threshold, c.both(lower_threshold, core))
            # Keep both threshold reads on every return. Since source gates
            # use only the two literal rails, a syntactic constant in the
            # source still has a nonconstant monotone expression off-layer.
            bounded = c.binary(0, at_most, core)
            result = c.binary(1, below, bounded)
            c.rows[v] = (c.positive_read(result, c.colors[v]),)
        if i:
            valid = c.either(c.both(p, opposite[q]), c.both(opposite[p], q))
            invalid = c.either(c.both(p, q), c.both(opposite[p], opposite[q]))
            higher_valid = c.both(higher_valid, valid)
            higher_invalid = c.either(higher_invalid, invalid)

    return c.finish(dimension, girth)
