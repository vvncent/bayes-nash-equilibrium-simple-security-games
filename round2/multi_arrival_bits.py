"""Compile a binary multi-token terminal-count bit to a one-token ARRIVAL graph.

Vertices 0..len(successors)-1 are nonterminal switches. The next `terminals`
vertices are absorbing. `supplies[v]` is a binary nonnegative number of chips
originally placed at v. Original terminal dispatches can be split beforehand
using split_terminal_dispatches. The output uses -1 for YES and -2 for NO.
The reduction never follows a chip. `simulate` is only for small tests.
"""

from bisect import bisect_right
from dataclasses import dataclass
from operator import index


YES, NO = -1, -2


@dataclass(frozen=True)
class Arrival:
    successors: tuple
    origin: int

    def simulate(self, limit=1_000_000):
        rotors = [0] * len(self.successors)
        vertex = self.origin
        for _ in range(limit):
            if vertex < 0:
                return vertex == YES
            position = rotors[vertex]
            rotors[vertex] ^= 1
            vertex = self.successors[vertex][position]
        raise RuntimeError("Test simulation exceeded its step bound")


def split_terminal_dispatches(vertex_count, dispatches):
    """Translate (out-neighbor tuple, binary starting count) terminal records."""
    supplies = [0] * vertex_count
    for neighbors, quantity in dispatches:
        if quantity < 0 or len(neighbors) not in (0, 1, 2):
            raise ValueError("A terminal needs zero to two successors and nonnegative supply")
        if quantity and not neighbors:
            raise ValueError("A positive dispatch needs an outgoing arc")
        if len(neighbors) == 1:
            supplies[neighbors[0]] += quantity
        if len(neighbors) == 2:
            supplies[neighbors[0]] += (quantity + 1) // 2
            supplies[neighbors[1]] += quantity // 2
    return tuple(supplies)


def terminal_bit(successors, terminals, supplies, target, bit):
    """Return one ordinary ARRIVAL instance deciding this terminal-count bit."""
    successors = tuple(tuple(map(index, row)) for row in successors)
    quantities = tuple(map(index, supplies))
    terminals, target, bit = map(index, (terminals, target, bit))
    n = len(successors)
    if (terminals <= 0 or not n <= target < n + terminals or bit < 0
            or len(quantities) != n + terminals or any(v < 0 for v in quantities)
            or any(len(row) != 2 or min(row) < 0 or max(row) >= n + terminals
                   for row in successors)):
        raise ValueError("Invalid multi-token instance or bit")
    total = sum(quantities)
    if bit >= total.bit_length():
        return Arrival(((NO, NO),), 0)

    modulus = 1 << (bit + 1)
    quotient, remainder = divmod(total, modulus)
    yes_offset = modulus // 2
    other_offset = modulus - 1 - remainder
    visits = total + yes_offset + other_offset

    # Reserve a root whose two equal successors dispatch successive excursions.
    root = n
    graph = [None] * (n + 1)

    def node(first, second):
        graph.append((first, second))
        return len(graph) - 1

    def counter(threshold, success):
        bits = (threshold - 1).bit_length()
        initial = (1 << bits) - threshold
        carry = success
        for j in reversed(range(bits)):
            carry = (node(carry, root) if initial & (1 << j)
                     else node(root, carry))
        return carry

    monitor = counter(quotient + 1, YES)
    discarded = counter(visits - quotient, NO)

    def divide():
        output = monitor
        for _ in range(bit + 1):
            output = node(discarded, output)
        return output

    yes_filter, other_filter = divide(), divide()

    def destination(vertex):
        if vertex < n:
            return vertex
        return yes_filter if vertex == target else other_filter

    for v, (first, second) in enumerate(successors):
        graph[v] = (destination(first), destination(second))

    destinations, ends = [], []
    count = 0
    for label, amount in ([(destination(v), weight) for v, weight in enumerate(quantities)]
                          + [(yes_filter, yes_offset), (other_filter, other_offset)]):
        if amount:
            count += amount
            destinations.append(label)
            ends.append(count)
    depth = (visits - 1).bit_length()
    period = 1 << depth
    if visits < period:
        destinations.append(root)
        ends.append(period)

    # Only dyadic intervals containing a label boundary need an actual switch.
    # Bottom-up construction avoids recursion on very long binary counts.
    unbuilt = [(0, period, False)]
    built = {}
    while unbuilt:
        lo, hi, expanded = unbuilt.pop()
        label = bisect_right(ends, lo)
        if hi <= ends[label]:
            built[lo, hi] = destinations[label]
        else:
            mid = (lo + hi) // 2
            if expanded:
                built[lo, hi] = node(built.pop((lo, mid)), built.pop((mid, hi)))
            else:
                unbuilt.append((lo, hi, True))
                unbuilt.append((mid, hi, False))
                unbuilt.append((lo, mid, False))
    start = built[0, period]
    graph[root] = (start, start)
    return Arrival(tuple(graph), root)
