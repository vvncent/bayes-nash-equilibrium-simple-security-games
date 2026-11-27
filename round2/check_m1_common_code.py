"""Check the terminal-load metric, pair routing and four-bit inequalities.

Run python3 -B round2/check_m1_common_code.py with z3-solver installed.
"""

from fractions import Fraction
from itertools import product

import z3

from check_m1_endpoint_fork import market, rat, require


def tau(delta):
    positive = sum(max(value, 0) for value in delta)
    negative = sum(max(-value, 0) for value in delta)
    return max(positive, negative)


def support_values(buyers, external):
    """Optimize each subset total directly over all real clearing outcomes."""
    private = ("a", "b")
    terminals = ("x", "y")
    capacities = {good: 1 - load for good, load in zip(private, external)}
    solver, prices, loads = market(capacities, terminals, buyers)
    solver.add(prices["x"] == 0, prices["y"] == 0)
    require(solver, z3.sat)
    result = {}
    for weights in ((1, 0), (0, 1), (1, 1), (2, -1)):
        objective = sum(w * loads[name] for w, name in zip(weights, terminals))
        optimizer = z3.Optimize()
        optimizer.add(*solver.assertions())
        optimum = optimizer.maximize(objective)
        assert optimizer.check() == z3.sat
        value = optimum.value()
        bound = (Fraction(value.as_long()) if z3.is_int_value(value) else
                 Fraction(value.numerator_as_long(), value.denominator_as_long()))
        # Check both attainment and global maximality with a separate QF_LRA solver.
        solver.push()
        solver.add(objective == rat(bound))
        require(solver, z3.sat)
        solver.pop()
        solver.push()
        solver.add(objective > rat(bound))
        require(solver, z3.unsat)
        solver.pop()
        result[weights] = bound
    return result


def check_terminal_supports():
    inputs = {
        (Fraction(a, 2), Fraction(b, 2))
        for a, b in product(range(3), repeat=2)
    }
    examples = (
        [(1, {"a": (5, 1), "x": (3, 1), "y": (3, 1)}),
         (1, {"b": (4, 1), "x": (2, 1), "y": (2, 1)})],
        [(Fraction(3, 2), {"a": (4, 2), "b": (3, 1),
                           "x": (1, 1), "y": (1, 1)}),
         (1, {"a": (3, 1), "b": (5, 3), "y": (2, 1)})],
        [(1, {"a": (3, 1), "b": (4, 2), "x": (0, 1)}),
         (Fraction(1, 2), {"b": (4, 3), "a": (1, 2), "y": (1, 1)}),
         (Fraction(1, 2), {"a": (2, 1), "y": (2, 1)})],
    )
    checked = 0
    for i, buyers in enumerate(examples):
        values = {u: support_values(buyers, u) for u in sorted(inputs)}
        for u in inputs:
            for v in inputs:
                if u == v:
                    continue
                budget = tau(tuple(t - s for s, t in zip(u, v)))
                for weights, before in values[u].items():
                    oscillation = max(0, *weights) - min(0, *weights)
                    assert abs(values[v][weights] - before) <= budget * oscillation
                    checked += 1
        if i == 0:
            # At (1,1) both tied terminal-split extrema exist, with different subsets.
            assert values[1, 1][1, 0] == values[1, 1][0, 1] == 2
            assert values[1, 1][1, 1] == 2
    return checked


def update(state, kind, size):
    if kind == "increment":
        return (state + 1) % size
    if kind == "swap":
        return 1 - state if state < 2 else state
    raise ValueError(kind)


def check_one_hot(size):
    for kind in ("increment", "swap"):
        for state in range(size):
            private = tuple(f"i{i}" for i in range(size))
            terminal = tuple(f"t{i}" for i in range(size))
            buyers = [(1, {private[i]: (2, 1), terminal[update(i, kind, size)]: (1, 1)})
                      for i in range(size)]
            capacities = {name: int(i != state) for i, name in enumerate(private)}
            solver, prices, loads = market(capacities, terminal, buyers)
            solver.add(*(prices[name] == 0 for name in terminal))
            require(solver, z3.sat)
            dest = update(state, kind, size)
            solver.add(z3.Or(*(loads[name] != int(i == dest)
                               for i, name in enumerate(terminal))))
            require(solver, z3.unsat)
    return 2 * size


def pair_word(size, start, end):
    x, y = start
    u, v = end
    gap = (y - x) % size
    target_gap = (v - u) % size
    if gap > target_gap:
        x, u = y, v
        gap, target_gap = size - gap, size - target_gap
    return ("increment",) * ((-x) % size) + (
        "increment", "swap") * (target_gap - gap) + ("increment",) * u


def check_pair_routing():
    total = 0
    maximum = {}
    for size in range(2, 13):
        pairs = [(x, y) for x in range(size) for y in range(size) if x != y]
        longest = 0
        for start in pairs:
            for end in pairs:
                word = pair_word(size, start, end)
                x, y = start
                for step in word:
                    x = update(x, step, size)
                    y = update(y, step, size)
                assert (x, y) == end
                assert len(word) <= 4 * size - 6
                longest = max(longest, len(word))
                total += 1
        maximum[size] = longest
    return total, maximum


def four_bit_step(bits):
    a, b, c, d = bits
    return (int(not (b and c)), int(not (c and d)), a, b)


def four_bit_weight_test():
    states = tuple(product((0, 1), repeat=4))
    events = set()
    simultaneous = []
    for state in states:
        for i in range(4):
            neighbor = list(state)
            neighbor[i] ^= 1
            moving = tuple(j for j, (u, v) in enumerate(
                zip(four_bit_step(state), four_bit_step(neighbor))) if u != v)
            events.add((i, moving))
            if state == (1, 1, 1, 1):
                simultaneous.append(moving)
    assert simultaneous == [(2,), (0, 3), (0, 1), (1,)]
    scale = [z3.Real(f"w_{i}") for i in range(4)]
    for error, expected in ((0, z3.unsat), (Fraction(16447, 100000), z3.unsat),
                            (Fraction(16448, 100000), z3.sat)):
        solver = z3.SolverFor("QF_LRA")
        solver.add(*(w > 0 for w in scale), z3.Sum(scale) == 1)
        for i, changed in events:
            solver.add(rat(1 - 2 * error) * sum(scale[j] for j in changed) <= scale[i])
        require(solver, expected)
    return len(events)


def direct_metric_test():
    sizes = []
    for dim in range(1, 6):
        vectors = list(product(range(-2, 3), repeat=dim))
        for delta in vectors:
            subset_norm = max(abs(sum(x for x, use in zip(delta, mask) if use))
                              for mask in product((0, 1), repeat=dim))
            assert tau(delta) == subset_norm
            assert 2 * tau(delta) == sum(abs(x) for x in delta) + abs(sum(delta))
        sizes.append(len(vectors))
    return sum(sizes)


if __name__ == "__main__":
    print(f"Subset and augmented l1 metrics agree on {direct_metric_test()} signed differences.")
    print(f"General terminal support bound passed {check_terminal_supports()} exact comparisons.")
    print(f"One-hot controls passed in {sum(check_one_hot(n) for n in (2, 4, 8))} full markets.")
    count, lengths = check_pair_routing()
    print(f"All {count} ordered-pair routes passed through N=12; longest at N=12 was {lengths[12]}.")
    print(f"Four-bit test: {four_bit_weight_test()} distinct coordinate-flip conditions; "
          "0.16447 infeasible and 0.16448 feasible for the weighted inequalities.")
