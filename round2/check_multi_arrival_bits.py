"""Small exhaustive and large binary construction checks for multi_arrival_bits."""

from itertools import product
from random import Random

from multi_arrival_bits import split_terminal_dispatches, terminal_bit


def reachable(graph):
    n = len(graph)
    found = {n, n + 1}
    for _ in graph:
        found.update(v for v, pair in enumerate(graph) if any(w in found for w in pair))
    return all(v in found for v in range(n))


def route(graph, supplies, reverse):
    n = len(graph)
    rotor = [0] * n
    totals = [0] * (len(supplies) - n)
    starts = range(len(supplies) - 1, -1, -1) if reverse else range(len(supplies))
    for origin in starts:
        for _ in range(supplies[origin]):
            v = origin
            while v < n:
                option = rotor[v]
                rotor[v] ^= 1
                v = graph[v][option]
            totals[v - n] += 1
    return totals


def check(graph, supplies):
    n = len(graph)
    totals = route(graph, supplies, reverse=False)
    assert totals == route(graph, supplies, reverse=True)
    examined = 0
    for terminal, quantity in enumerate(totals, n):
        for bit in range(sum(supplies).bit_length() + 1):
            one_chip = terminal_bit(graph, len(totals), supplies, terminal, bit)
            assert one_chip.simulate() == bool((quantity >> bit) & 1)
            examined += 1
    return examined


def main():
    tested = instances = 0
    for pair in product(range(3), repeat=2):
        graph = (pair,)
        if reachable(graph):
            for supplies in product(range(3), repeat=3):
                tested += check(graph, supplies)
                instances += 1
    rng = Random(32004)
    for _ in range(150):
        n = rng.randrange(2, 6)
        graph = tuple((rng.randrange(n + 2), rng.randrange(n + 2)) for _ in range(n))
        if reachable(graph):
            supplies = tuple(rng.randrange(5) for _ in range(n + 2))
            tested += check(graph, supplies)
            instances += 1

    # Both arcs of one initial terminal can reach the same vertex, and another
    # initially active terminal can receive a chip that has already dispatched.
    supplies = split_terminal_dispatches(3, [((0, 0), 5), ((2, 0), 7), ((), 0)])
    assert supplies == (8, 0, 4)
    tested += check(((1, 2),), supplies)
    assert terminal_bit((), 2, (3, 5), 1, 2).simulate()

    # Construction itself must scale with binary length, without running chips.
    huge = (1 << 4096) + (1 << 2027) + 19
    compiled = terminal_bit(((1, 2),), 2, (huge, 7, 3), 1, 2023)
    assert len(compiled.successors) < 35_000
    assert not terminal_bit((), 2, (5, 7), 1, 10**6).simulate()
    print(f"{tested} single-chip bit answers checked on {instances + 1} multi-chip inputs.")
    print(f"A 4097-bit supply produced {len(compiled.successors)} ordinary switches.")


if __name__ == "__main__":
    main()
