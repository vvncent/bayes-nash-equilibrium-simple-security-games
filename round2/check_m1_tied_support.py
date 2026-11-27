"""Exact tests for positive terminal loads and individual tight-edge support in M1."""

from itertools import product

import z3

from wardrop.check_wardrop import add, expect, market, q, rule_out


def totals_at(goods, buyers, quotes, tag):
    solver = z3.SolverFor("QF_LRA")
    p, f, _ = market(solver, tag, goods, buyers)
    solver.add(*(p[j] == q(value) for j, value in quotes.items()))
    amounts = {j: add(*(value for (_, k), value in f.items() if j == k)) for j in goods}
    result = set()
    for bits in product((0, 1), repeat=len(goods)):
        solver.push()
        solver.add(*(amount > 0 if bit else amount == 0 for amount, bit in zip(amounts.values(), bits)))
        if solver.check() == z3.sat:
            result.add(frozenset(j for j, bit in zip(goods, bits) if bit))
        solver.pop()
    assert result
    union = frozenset().union(*result)
    for support in result:
        for extra in union - support:
            assert support | {extra} in result
    return result


def circulation(arcs):
    vertices = sorted(set(v for endpoints in arcs for v in endpoints))
    goods = {v: sum(a == v for a, _ in arcs) for v in vertices}
    assert all(goods.values()) and all(a != b for a, b in arcs)
    rows = {k: (1, {v: (2, 1) for v in arc}) for k, arc in enumerate(arcs)}
    return goods, rows


def check_circulation(arcs, tag):
    goods, buyers = circulation(arcs)
    solver = z3.SolverFor("QF_LRA")
    p, f, _ = market(solver, tag, goods, buyers)
    signal = [f[e, b] for e, (_, b) in enumerate(arcs)]
    expect(solver, z3.sat, "circulation market clears")
    bad = [p[v] > 2 for v in goods]
    bad.extend(f[e, a] + f[e, b] != 1 for e, (a, b) in enumerate(arcs))
    for v, c in goods.items():
        bad.append(add(*(value for (_, target), value in f.items() if target == v)) != c)
        bad.append(add(*(t for t, (a, _) in zip(signal, arcs) if a == v)) !=
                   add(*(t for t, (_, b) in zip(signal, arcs) if b == v)))
    rule_out(solver, z3.Or(*bad), "margins or circulation at an arbitrary clearing price")
    return solver, p, signal


def main():
    capacities = {j: 1 for j in range(3)}
    complete = {i: (1, {j: (2, 1) for j in capacities}) for i in range(2)}
    free = {j: 0 for j in capacities}
    masks = totals_at(capacities, complete, free, "complete")
    assert len(masks) == 4 and all(len(mask) >= 2 for mask in masks)
    # At price one good 0 must fill. Buyer 1 may use either of its tied
    # zero-utility goods or its outside; good 3 is below all best offers.
    other = {0: (1, {0: (2, 1), 1: (1, 1)}),
             1: (1, {0: (1, 1), 2: (0, 1), 3: (-1, 1)})}
    locked = totals_at({j: 1 for j in range(4)}, other, {0: 1, 1: 0, 2: 0, 3: 0}, "locked")
    assert locked == {frozenset({0}), frozenset({0, 2}), frozenset({0, 1}), frozenset({0, 1, 2})}
    checked = 0
    for flags in product((0, 1), repeat=6):
        rows = {i: (1, {j: (2 if flags[3*i+j] else -1, 1) for j in capacities}) for i in range(2)}
        s = z3.SolverFor("QF_LRA")
        p, _, _ = market(s, "eligible", capacities, rows)
        s.add(*(v == 0 for v in p.values()))
        if s.check() == z3.sat:
            totals_at(capacities, rows, free, "small")
            checked += 1

    merge = [(0, 1), (1, 2), (2, 0), (1, 3), (3, 0)]
    solver, prices, (z, x, copy_x, y, copy_y) = check_circulation(merge, "merge")
    rule_out(solver, z3.Or(z != x+y, x != copy_x, y != copy_y), "two input supports merge")
    choices = 0
    for a, b, c in product((0, 1), repeat=3):
        solver.push()
        solver.add(*(p == 0 for p in prices.values()))
        solver.add(*[(v > 0 if flag else v == 0) for v, flag in zip((x, y, z), (a, b, c))])
        expect(solver, z3.sat if c == (a | b) else z3.unsat, "OR on three individual allocations")
        solver.pop()
        choices += 1
    copies = 0
    for n in (2, 3, 5, 15):
        directed = [(i, (i+1) % n) for i in range(n)]
        s, p, v = check_circulation(directed, f"ring{n}")
        rule_out(s, z3.Or(*(t != v[0] for t in v)), "edge-to-edge endogenous copies")
        for numerator in range(4):
            s.push()
            s.add(*(t == 0 for t in p.values()), v[0] == z3.Q(numerator, 3))
            expect(s, z3.sat, "four interior/endpoint circulation values")
            s.pop()
            copies += 1
    print(f"{checked} small market price fibers and two named fibers satisfy support augmentation.")
    print(f"Five-buyer, four-good cyclic merge implements exactly the {choices} tested OR truth assignments.")
    print(f"Four closed-wire rings through 15 goods: all-equilibria equality and {copies} exact rational lifts.")


if __name__ == "__main__":
    main()
