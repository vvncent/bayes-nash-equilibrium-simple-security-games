"""Verify the two-literal slice descent and its emitted Boolean certificate circuit.

Exhaustive small-instance tests compare implication-graph results with direct
enumeration, including assignments held fixed by an OPDC prefix slice.
"""
from collections import Counter
from itertools import product
from random import Random

from check_opdc_feedback_market import assignment_index, check_certificate, table_circuit, truth_table


def relation_tables(circuits, parents, last):
    """Truth relations on (own,parent) independently read from the original target circuit."""
    k = len(circuits)
    relations = []
    for i, p in enumerate(parents):
        table = truth_table(circuits[i])
        mask = 0
        for own, other in product((0, 1), repeat=2):
            point = [0] * k
            point[-1] = last
            if p is not None:
                point[p] = other
            point[i] = own
            val = table[assignment_index(point)]
            if val == own:
                mask |= 1 << (2 * own + other)
        relations.append(mask)
    return tuple(relations)


def brute_models(parents, masks, free, suffix):
    """All witness assignments for the desired rows, up to the prefix boundary."""
    def holds(x, i):
        other = x[parents[i]] if parents[i] is not None else 0
        return bool(masks[i] & (1 << (2 * x[i] + other)))
    models = []
    for prefix in product((0, 1), repeat=free):
        x = prefix + suffix
        if all(holds(x, i) for i in range(free)):
            models.append(x)
    return models


def implication_instance(parents, relations, free, suffix):
    n = len(parents)
    assert len(relations) == n and free + len(suffix) == n
    arcs = set()
    for i, mask in enumerate(relations[:free]):
        p = parents[i]
        for own, other in product((0, 1), repeat=2):
            if mask & (1 << (2 * own + other)):
                continue
            a = 2 * i + own
            if p is None:
                if other == 0:
                    arcs.add((a, a ^ 1))
                continue
            b = 2 * p + other
            arcs.update(((a, b ^ 1), (b, a ^ 1)))
    for i, bit in enumerate(suffix, free):
        d = 2 * i + bit
        arcs.add((d ^ 1, d))
    assert all((b ^ 1, a ^ 1) in arcs for a, b in arcs)
    returns = []
    for origin in range(2 * n):
        found = {origin}
        work = [origin]
        while work:
            a = work.pop()
            for u, v in arcs:
                if u == a and v not in found:
                    work.append(v)
                    found.add(v)
        returns.append(found)
    return returns


def greedy_model(parents, masks, free, suffix):
    reach = implication_instance(parents, masks, free, suffix)
    if any(a ^ 1 in r and a in reach[a ^ 1] for a, r in enumerate(reach)):
        return None
    forced = set()
    for i in range(len(parents)):
        low = 2 * i
        lit = low + int(low ^ 1 in reach[low] or low ^ 1 in forced)
        forced.update(reach[lit])
        assert all(a ^ 1 not in forced for a in forced)
    return tuple(int(2 * i + 1 in forced) for i in range(len(parents)))


def target_from_relation(mask):
    """Stationarity for the chosen raw Boolean function is exactly the 4-bit mask."""
    raw = 0
    for own, other, b in product((0, 1), repeat=3):
        valid = (mask >> (2 * own + other)) & 1
        raw |= (own if valid else 1 - own) << (4 * own + 2 * other + b)
    return raw


def all_binary_relations():
    from opdc_feedback_market import Circuit

    parents = (1, 0)
    points = tuple(product((0, 1), repeat=3))
    rows = [[table_circuit(3, (i, p, 2), target_from_relation(mask)) for mask in range(16)]
            for i, p in enumerate(parents)]
    count = sat = 0
    for masks in product(range(16), repeat=2):
        targets = (rows[0][masks[0]], rows[1][masks[1]], Circuit(3, (), 2))
        for last in (0, 1):
            assert relation_tables(targets, parents, last) == masks
            for i in range(2):
                raw = truth_table(targets[i])
                assert all((raw[assignment_index(x)] == x[i]) == bool(
                    masks[i] & 1 << (2 * x[i] + x[parents[i]])) for x in points)
        for free in range(3):
            for suffix in product((0, 1), repeat=2 - free):
                models = brute_models(parents, masks, free, suffix)
                found = greedy_model(parents, masks, free, suffix)
                assert found == (models[0] if models else None), (parents, masks, free, suffix, found, models)
                count += 1
                sat += bool(models)
    assert count == 256 * 7
    return count, sat


def check_random_closures(seed=1418, count=150):
    rng = Random(seed)
    checks = 0
    for _ in range(count):
        n = rng.randrange(1, 7)
        parents = tuple(rng.choice((None,) + tuple(range(n))) for _ in range(n))
        masks = tuple(rng.randrange(16) for i in parents)
        free = rng.randrange(n + 1)
        suffix = tuple(rng.randrange(2) for i in range(n - free))
        models = brute_models(parents, masks, free, suffix)
        got = greedy_model(parents, masks, free, suffix)
        assert got == (models[0] if models else None)
        checks += 1
    return checks


def reference_certificate(tables, parents, masks0, masks1):
    """Recover the specified ordered certificate via exhaustive Boolean feasibility."""
    n = len(parents)
    branches = []
    for last, masks in enumerate((masks0, masks1)):
        full = brute_models(parents, masks, n, ())
        if full:
            branches.append(full[0] + (last,))
            continue
        suffix = ()
        for axis in reversed(range(n)):
            lower = brute_models(parents, masks, axis, (0,) + suffix)
            higher = brute_models(parents, masks, axis, (1,) + suffix)
            if lower and higher:
                return 'OV2', axis, lower[0] + (last,), higher[0] + (last,)
            suffix = (int(bool(lower)),) + suffix
        raise AssertionError('An empty set of prefix constraints cannot be infeasible')
    low, high = branches
    a, b = tables[-1][assignment_index(low)], tables[-1][assignment_index(high)]
    if not a:
        return 'root', low
    if b:
        return 'root', high
    return 'OV2', n, low, high


def real_decision_test(circuits, parents):
    from opdc_binary_constraints_market import decision_circuit

    d = decision_circuit(circuits, parents)
    values = d.evaluate()
    tables = tuple(truth_table(c) for c in circuits)
    masks = tuple(relation_tables(circuits, parents, b) for b in (0, 1))
    for (last, i, own, pv), rail in d.flags.items():
        good = (masks[last][i] >> (2 * own + pv)) & 1
        actual = tuple(values[p] for p in rail)
        assert actual == (good, 1 - good), (last, i, own, pv, actual)
    expected = reference_certificate(tables, parents, *masks)
    actual = d.decode(values)
    assert actual == expected, (parents, masks, expected, actual)
    return check_certificate(actual, tables), len(d.gates), values, actual, d


def exhaustive_decision_instances():
    from opdc_binary_constraints_market import Circuit

    parents = (1, 0)
    operators = [Circuit(3, (), 2), Circuit(3, (('not', 2),), 3),
                 Circuit(3, (('xor', 0, 1), ('nand', 3, 2)), 4)]
    counts = Counter()
    for m, n in product(range(16), repeat=2):
        lower = m, n
        # Each branch separately exhausts all pairs of independent binary relations.
        # Distinct involutions in the two rows make the sibling genuinely different.
        upper = m ^ 3, n ^ 11
        prefix = []
        for i, p in enumerate(parents):
            mask = 0
            for own, other, last in product((0, 1), repeat=3):
                accepted = ((upper if last else lower)[i] >> (2 * own + other)) & 1
                mask |= (own if accepted else 1 - own) << (4 * own + 2 * other + last)
            prefix.append(table_circuit(3, (i, p, 2), mask))
        for out in operators:
            circuits = tuple(prefix) + (out,)
            key, _, _, _, _ = real_decision_test(circuits, parents)
            counts[key] += 1
    assert sum(counts.values()) == 768
    return counts


def all_three_bit_prefix_sources_fixed_sibling():
    """Try every arbitrary three-bit truth table separately for each prefix role."""
    from opdc_binary_constraints_market import Circuit

    parents = (1, 0)
    counts = Counter()
    controls = [Circuit(3, (('nand', 1, 2),), 3), Circuit(3, (('nand', 0, 1),), 3)]
    for varied in (0, 1):
        for mask in range(256):
            cc = list(controls)
            cc[varied] = table_circuit(3, (0, 1, 2), mask)
            # A nontrivial final target shared across the sweeps.
            out = Circuit(3, (('xor', 0, 1), ('or', 3, 2)), 4)
            kind, _, _, _, _ = real_decision_test(tuple(cc) + (out,), parents)
            counts[kind] += 1
    for mask in range(256):
        out = table_circuit(3, (0, 1, 2), mask)
        kind, _, _, _, _ = real_decision_test(tuple(controls) + (out,), parents)
        counts[kind] += 1
    assert sum(counts.values()) == 768
    return counts


def random_outer_circuit(k, rng):
    from opdc_binary_constraints_market import Circuit

    # All input variables occur, through a tree with shared later references.
    order = list(range(k))
    rng.shuffle(order)
    gates = []
    w = order[0]
    for v in order[1:]:
        gates.append((rng.choice(('and', 'nand', 'xor', 'or')), w, v))
        w = k + len(gates) - 1
    for _ in range(4):
        a = rng.randrange(k + len(gates))
        gates.append((rng.choice(('and', 'or', 'xor')), a, w))
        w = k + len(gates) - 1
    return Circuit(k, tuple(gates), w)


def larger_decision_tests():
    rng = Random(20261123)
    counts, largest = Counter(), 0
    for k in (4, 5, 6, 7, 8):
        for iteration in range(8):
            if iteration == 0:
                parents = tuple((i + 1) % (k - 1) for i in range(k - 1))
            elif iteration == 1:
                parents = (0,) * (k - 1)
            else:
                parents = tuple(rng.choice((None,) + tuple(range(k - 1))) for _ in range(k - 1))
            rows = []
            for i, p in enumerate(parents):
                inputs = (i, k - 1) if p is None or p == i else (i, p, k - 1)
                mask = rng.randrange(1 << (1 << len(inputs)))
                rows.append(table_circuit(k, inputs, mask))
            circuits = tuple(rows) + (random_outer_circuit(k, rng),)
            kind, gate_count, _, _, _ = real_decision_test(circuits, parents)
            counts[kind] += 1
            largest = max(largest, gate_count)
    return counts, largest


def full_market_cases():
    from opdc_binary_constraints_market import Circuit, compile_market
    from check_opdc_feedback_market import check_all_equilibria

    cases = [
        ((Circuit(1, (('not', 0),), 1),), (), ('OV2', 0, (0,), (1,))),
        ((Circuit(2, (('or', 0, 1),), 2), Circuit(2, (('nand', 1, 0),), 2)), (None,),
         ('OV2', 1, (0, 0), (1, 1))),
        ((Circuit(2, (('or', 0, 1),), 2), Circuit(2, (('or', 1, 0),), 2)), (0,),
         ('root', (0, 0))),
        ((Circuit(3, (('nand', 1, 2),), 3), Circuit(3, (('nand', 0, 1),), 3), Circuit(3, (), 0)),
         (1, 0), ('OV2', 1, (1, 0, 0), (1, 1, 0))),
        ((Circuit(3, (('not', 1), ('and', 3, 2)), 4),
          Circuit(3, (('or', 0, 2), ('not', 3)), 4),
          Circuit(3, (('not', 0), ('and', 3, 1), ('or', 3, 1), ('and', 2, 5), ('or', 4, 6)), 7)),
         (1, 0), ('OV2', 2, (0, 1, 0), (1, 0, 1))),
    ]
    sizes = []
    for circuits, parents, expected_answer in cases:
        _, _, predicted, decision, dag = real_decision_test(circuits, parents)
        assert decision == expected_answer
        m = compile_market(circuits, parents)
        assert m.decision.gates == dag.gates
        rails = list(m.flags.values()) + [m.ports.is_root] + list(m.ports.axes) + list(m.ports.low) + list(m.ports.high)
        observed = {name: predicted[name] for rail in rails for name in rail}
        witness = check_all_equilibria(m.capacities, m.buyers, observed)
        assert m.decode(witness) == expected_answer
        sizes.append((len(m.capacities), len(m.buyers), len(observed)))
    return sizes


def check_four_bit_benchmark():
    """Enumerate every OPDC answer for the first example outside the binary-row compiler."""
    from check_opdc_local_gates import certificates

    points = tuple(product((0, 1), repeat=4))

    def direction(point):
        a, b, c, d = point
        targets = (1 - (b & c), 1 - (c & d), a, b)
        return tuple(target - current for target, current in zip(targets, point))

    answers = list(certificates(points, direction, 4))
    assert answers == [('OV2', 2, (1, 1, 0, 0), (0, 1, 1, 0))]


def main():
    if not __debug__:
        raise RuntimeError('Run the verifier with Python assertions enabled.')
    tested, feasible = all_binary_relations()
    print(f'All 256 relation pairs and {tested} prefix/suffix cases: {feasible} feasible; '
          'all closure witnesses equal the least brute-force model.', flush=True)
    print(f'{check_random_closures()} additional implication instances, including absent and repeated parents.', flush=True)
    for description, function in [('two related branch tables per row', exhaustive_decision_instances),
                                  ('all truth tables separately on each original coordinate', all_three_bit_prefix_sources_fixed_sibling)]:
        tally = function()
        print(f'{sum(tally.values())} emitted decision circuits for {description}: {dict(sorted(tally.items()))}.', flush=True)
    tallies, size = larger_decision_tests()
    print(f'{sum(tallies.values())} emitted circuits on 4 through 8 coordinates; largest {size} '
          f'price gates. Certified outputs {dict(sorted(tallies.items()))}.', flush=True)
    print('Full M1 benchmarks with SAT and wrong-price UNSAT (goods, buyers, distinct checked prices): '
          f'{full_market_cases()}.')
    check_four_bit_benchmark()
    print('The four-bit benchmark has exactly one admissible OPDC answer across all prefix slices.')


if __name__ == '__main__':
    main()
