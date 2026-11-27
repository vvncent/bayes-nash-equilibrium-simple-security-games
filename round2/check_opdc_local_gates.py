"""Finite checks for the local Boolean OPDC reduction. Run with python3."""

from collections import Counter
from itertools import product


def certificates(points, direction, dimension):
    """All OPDC answers, with the zero endpoint first in an OV2 pair."""
    for point in points:
        if all(value == 0 for value in direction(point)):
            yield ("root", dimension, point)
    for axis in range(dimension):
        slices = {}
        for point in points:
            signs = direction(point)
            if any(signs[:axis]):
                continue
            slices.setdefault(point[axis + 1 :], []).append((point, signs[axis]))
        for endpoints in slices.values():
            zeros = [point for point, sign in endpoints if sign == 0]
            for offset, point in enumerate(zeros):
                for other in zeros[offset + 1 :]:
                    yield ("OV1", axis, point, other)
            lower = [point for point, sign in endpoints if point[axis] == 0 and sign == 1]
            upper = [point for point, sign in endpoints if point[axis] == 1 and sign == -1]
            for point in lower:
                for other in upper:
                    yield ("OV2", axis, point, other)
            for point, sign in endpoints:
                if (point[axis], sign) in ((0, -1), (1, 1)):
                    yield ("OV3", axis, point)


def decode(answer, gate_count, original):
    tag, axis, *points = answer
    if axis < gate_count or tag == "OV3":
        raise AssertionError("A violation occurred inside the gate block or at the boundary")
    axis -= gate_count
    points = [point[gate_count:] for point in points]
    if tag == "OV2":
        for point in points:
            if (point[axis], original(point)[axis]) in ((0, -1), (1, 1)):
                return ("OV3", axis, point)
    if tag == "OV1":
        points.sort()
    return (tag, axis, *points)


def check_normalization():
    """Every two-bit direction table, including all outward boundary directions."""
    points = list(product(range(2), repeat=2))
    count = 0
    outputs = Counter()
    for table in product((-1, 0, 1), repeat=8):
        raw = dict(zip(points, zip(table[::2], table[1::2])))
        normalized = {
            point: tuple(0 if sign == 0 else 1 - 2 * bit for sign, bit in zip(raw[point], point))
            for point in points
        }
        valid = set(certificates(points, raw.__getitem__, 2))
        for answer in certificates(points, normalized.__getitem__, 2):
            projected = decode(answer, 0, raw.__getitem__)
            assert projected in valid, (raw, answer, projected)
            outputs[projected[0]] += 1
        count += 1
    assert set(outputs) == {"root", "OV1", "OV2", "OV3"}
    return count


def gate_value(gate, point):
    operation, *inputs = gate
    if operation == "copy":
        return point[inputs[0]]
    if operation == "nand":
        return 1 - point[inputs[0]] * point[inputs[1]]
    if operation == "zero":
        return 0
    if operation == "one":
        return 1
    raise ValueError(operation)


def check_network(gates, outputs):
    """Expand all free gate assignments, including inconsistent ones, before projection."""
    size = len(gates)
    dimension = len(outputs)
    readers = Counter(wire for gate in gates for wire in gate[1:])
    readers.update(outputs)
    assert max(readers.values(), default=0) <= 2
    assert all(wire >= size or wire < index for index, gate in enumerate(gates) for wire in gate[1:])

    points = list(product(range(2), repeat=dimension))
    original = {}
    for x in points:
        point = [0] * size + list(x)
        for index, gate in enumerate(gates):
            point[index] = gate_value(gate, point)
        original[x] = tuple(point[wire] - bit for wire, bit in zip(outputs, x))
    valid = set(certificates(points, original.__getitem__, dimension))

    lifted = {}
    for point in product(range(2), repeat=size + dimension):
        targets = [gate_value(gate, point) for gate in gates] + [point[wire] for wire in outputs]
        lifted[point] = tuple(target - bit for target, bit in zip(targets, point))
    projected = {decode(answer, size, original.__getitem__)
                 for answer in certificates(lifted, lifted.__getitem__, size + dimension)}
    assert projected == valid, (gates, outputs, projected, valid)
    return valid


def check_gate_lifts():
    # Signals 0 and 1 are gate outputs, signals 2 and 3 are the two feedback bits.
    gate_lists = []
    for sources in ((2, 3), (0, 2, 3)):
        gate_lists.append(
            [("zero",), ("one",)]
            + [("copy", wire) for wire in sources]
            + [("nand", left, right) for left in sources for right in sources]
        )
    count = 0
    for gates in product(*gate_lists):
        outputs = (0, 1)
        readers = Counter(wire for gate in gates for wire in gate[1:])
        readers.update(outputs)
        if max(readers.values()) <= 2:
            check_network(gates, outputs)
            count += 1

    # A branching copy tree supplies four input positions to three NAND gates.
    tree = (("copy", 6), ("copy", 0), ("copy", 0),
            ("nand", 1, 2), ("nand", 1, 3), ("nand", 2, 3))
    check_network(tree, (4, 5))
    # With F_a=b and F_b=NOT a, the full slice has exactly one crossing witness.
    crossing = check_network((("copy", 3), ("nand", 2, 2)), (0, 1))
    assert crossing == {("OV2", 1, (0, 0), (1, 1))}
    # Both affine extensions admit (1/2, 1/2), with disjoint Boolean answers.
    copies = check_network((("copy", 3), ("copy", 2)), (0, 1))
    negations = check_network((("nand", 3, 3), ("nand", 2, 2)), (0, 1))
    assert copies.isdisjoint(negations)
    return count


if __name__ == "__main__":
    tables = check_normalization()
    networks = check_gate_lifts()
    print(f"Checked all {tables} two-bit direction tables, {networks} bounded-use two-gate circuits,")
    print("a branching copy tree, a forced crossing, and two loops with disjoint answer sets.")
