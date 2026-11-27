"""Verify ordered OPDC certificates and the ordinary-market encoding.

Run ``python3 check_opdc_feedback_market.py`` in an environment with z3-solver.
The exhaustive Boolean checks and the all-equilibria market tests are separate.
"""

from collections import Counter
from fractions import Fraction as F
from itertools import product
from time import monotonic


def rational(z3, x):
    x = F(x)
    return z3.RealVal(f'{x.numerator}/{x.denominator}')


def equilibrium_solver(capacities, buyers, reader_bounds=None):
    """Encode the rational affine market including its zero-valued outside option."""
    import z3

    reader_bounds = reader_bounds or {}
    solver = z3.SolverFor('QF_LRA')
    prices = {j: z3.Real(f'p_{i}') for i, j in enumerate(capacities)}
    loads = {j: [] for j in capacities}
    for j, bound in reader_bounds.items():
        extra = z3.Real(f'optional_reader_{j}')
        solver.add(0 <= extra, extra < rational(z3, bound))
        loads[j].append(extra)
    for i, (mass, offers) in enumerate(buyers.values()):
        assert mass > 0 and all(j in prices and slope > 0 for j, (_, slope) in offers.items())
        utility = z3.Real(f'u_{i}')
        solver.add(utility >= 0)
        row = []
        for h, (j, (intercept, slope)) in enumerate(offers.items()):
            f = z3.Real(f'f_{i}_{h}')
            payoff = rational(z3, intercept) - rational(z3, slope) * prices[j]
            solver.add(f >= 0, utility >= payoff, z3.Or(f == 0, utility == payoff))
            loads[j].append(f)
            row.append(f)
        total = z3.Sum(row) if row else rational(z3, 0)
        solver.add(total <= rational(z3, mass), z3.Or(total == rational(z3, mass), utility == 0))
    for j, capacity in capacities.items():
        assert capacity > 0
        total = z3.Sum(loads[j]) if loads[j] else rational(z3, 0)
        solver.add(prices[j] >= 0, total <= rational(z3, capacity),
                   z3.Or(prices[j] == 0, total == rational(z3, capacity)))
    return solver, prices


def require_status(solver, expected, verb):
    actual = solver.check()
    if actual != expected:
        import z3
        extra = solver.model() if actual == z3.sat else solver.reason_unknown()
        raise AssertionError(f'{verb}: expected {expected}, got {actual}: {extra}')


def check_all_equilibria(capacities, buyers, expected, reader_bounds=None, realised_readers=None):
    import z3

    solver, prices = equilibrium_solver(capacities, buyers, reader_bounds)
    require_status(solver, z3.sat, 'market feasibility')
    model = solver.model()
    witness = {}
    for j, price in prices.items():
        number = model.eval(price, model_completion=True)
        witness[j] = F(number.numerator_as_long(), number.denominator_as_long())
    if realised_readers:
        solver.push()
        for j, load in realised_readers.items():
            solver.add(z3.Real(f'optional_reader_{j}') == rational(z3, load))
        require_status(solver, z3.sat, 'prescribed nonuniform positive reader loads')
        solver.pop()
    solver.add(z3.Or([prices[j] != rational(z3, value) for j, value in expected.items()]))
    require_status(solver, z3.unsat, 'exclude every wrong terminal/literal price')
    return witness


def selected_component(vertices, active, source):
    adjacent = {v: [] for v in vertices}
    for u, v in active:
        adjacent[u].append(v)
        adjacent[v].append(u)
    seen = {source}
    work = [source]
    while work:
        v = work.pop()
        for w in adjacent[v]:
            if w not in seen:
                seen.add(w)
                work.append(w)
    return seen


def selected_edge_tests():
    """Quantify over external loads at all vertices and all real equilibria."""
    cases = [
        (('T',), (('T', 'T'),)),
        (('T', 'u'), (('u', 'u'), ('T', 'u'), ('u', 'T'))),
        (('T', 'u', 'v'), (('u', 'v'), ('u', 'v'), ('u', 'u'))),
        (('T', 'u', 'v'), (('T', 'u'), ('u', 'v'), ('v', 'T'))),
        (('T', 'u', 'v', 'w'), (('T', 'v'), ('u', 'w'), ('u', 'v'), ('w', 'w'))),
        (('T', 'u', 'v'), ()),
    ]
    checked = 0
    for vertices, edges in cases:
        degree = Counter(x for edge in edges for x in edge)
        eps = F(1, 4 * len(vertices) + 4)
        for mask in product((0, 1), repeat=len(edges)):
            capacities = {v: 1 + degree[v] + eps for v in vertices}
            buyers = {f'base_{v}': (F(1), {v: (F(2), F(1))}) for v in vertices}
            buyers['terminal'] = (F(1), {'T': (F(1), F(1))})
            active = []
            expected = {}
            for e, ((a, b), bit) in enumerate(zip(edges, mask)):
                on, off = f'on_{e}', f'off_{e}'
                for rail, value in ((on, bit), (off, 1 - bit)):
                    capacities[rail] = F(5)
                    buyers[f'pin_{rail}'] = (F(6), {rail: (F(value), F(1))})
                    expected[rail] = value
                buyers[f'edge_{e}'] = (F(2), {a: (F(2), F(1)), b: (F(2), F(1)), on: (F(3), F(3))})
                for h, v in enumerate((a, b)):
                    buyers[f'home_{e}_{h}'] = (F(1), {v: (F(2), F(1)), off: (F(3), F(3))})
                if bit:
                    active.append((a, b))
            reached = selected_component(vertices, active, 'T')
            expected.update((v, int(v in reached)) for v in vertices)
            load_sample = {v: eps * F(i + 1, len(vertices) + 1) for i, v in enumerate(vertices)}
            check_all_equilibria(capacities, buyers, expected, {v: eps for v in vertices}, load_sample)
            checked += 1
    return checked


def truth_table(circuit):
    """Original Boolean target table. This evaluator does not use compiler semantics."""
    table = []
    for assignment in product((0, 1), repeat=circuit.inputs):
        values = list(assignment)
        for op, *args in circuit.gates:
            if op == 'const': value = args[0]
            elif op == 'copy': value = values[args[0]]
            elif op == 'not': value = 1 - values[args[0]]
            else:
                a, b = (values[w] for w in args)
                if op == 'and': value = a & b
                elif op == 'or': value = a | b
                elif op == 'xor': value = a ^ b
                elif op == 'nand': value = 1 - (a & b)
                else: raise ValueError(op)
            values.append(value)
        table.append(values[circuit.output])
    return tuple(table)


def assignment_index(x):
    index = 0
    for bit in x:
        assert bit in (0, 1)
        index = 2 * index + bit
    return index


def check_certificate(certificate, tables):
    """Definition 14 on inward Boolean inputs, including the equality of suffixes."""
    n = len(tables)
    if certificate[0] == 'root':
        _, x = certificate
        assert len(x) == n
        idx = assignment_index(x)
        assert all(tab[idx] == bit for tab, bit in zip(tables, x)), (certificate, tables)
        return 'root'
    tag, axis, low, high = certificate
    assert tag == 'OV2' and 0 <= axis < n and len(low) == len(high) == n
    assert low[axis] == 0 and high[axis] == 1 and low[axis + 1:] == high[axis + 1:]
    p, q = assignment_index(low), assignment_index(high)
    assert all(tables[i][p] == low[i] and tables[i][q] == high[i] for i in range(axis))
    assert tables[axis][p] == 1 and tables[axis][q] == 0
    return f'OV2[{axis}]'


def table_circuit(k, variables, mask):
    """Generate an ordinary circuit from a supplied small Boolean table, by its ANF."""
    from opdc_feedback_market import Circuit

    gates = []

    def gate(*spec):
        wire = k + len(gates)
        gates.append(spec)
        return wire

    terms = []
    for subset in range(1 << len(variables)):
        coefficient = sum((mask >> s) & 1 for s in range(subset + 1) if s & subset == s) & 1
        if not coefficient:
            continue
        literals = [v for j, v in enumerate(variables) if subset & (1 << (len(variables) - j - 1))]
        term = literals[0] if literals else gate('const', 1)
        for v in literals[1:]:
            term = gate('and', term, v)
        terms.append(term)
    result = terms[0] if terms else gate('const', 0)
    for term in terms[1:]:
        result = gate('xor', result, term)
    return Circuit(k, tuple(gates), result)


def independent_slice(parents, masks, last_bit):
    """Build literal edges from the directly tabulated normalized Boolean target.

    Constant targets go to their required literal. A nonconstant unary relation
    joins each child literal to its satisfying parent literal. Each all-active
    cycle is seeded at the maximum coordinate's zero literal.
    """
    prefix = len(parents)
    terminal = 2 * prefix
    vertices = range(terminal + 1)
    edges = []
    coefficients = []
    for i, (parent, mask) in enumerate(zip(parents, masks)):
        value_at_zero = (mask >> last_bit) & 1
        value_at_one = (mask >> (2 + last_bit)) & 1
        coefficients.append((value_at_zero, value_at_zero ^ value_at_one))
        if value_at_zero == value_at_one:
            edges.append((terminal, 2 * i + value_at_zero))
        else:
            assert parent is not None
            for p in (0, 1):
                child = (mask >> (2 * p + last_bit)) & 1
                edges.append((2 * i + child, 2 * parent + p))
    # Follow only live parent relations and deduplicate cycles by their vertex sets.
    cycles = set()
    for start in range(prefix):
        path = []
        v = start
        while v is not None and v not in path and coefficients[v][1]:
            path.append(v)
            v = parents[v]
        if v is not None and v in path:
            cycles.add(frozenset(path[path.index(v):]))
    for cycle in cycles:
        edges.append((terminal, 2 * max(cycle)))
    reached = selected_component(vertices, edges, terminal)
    rails = tuple((int(2 * i in reached), int(2 * i + 1 in reached)) for i in range(prefix))
    odd = tuple(sorted(max(c) for c in cycles if sum(coefficients[v][0] for v in c) % 2))
    return rails, tuple(coefficients), odd


def outer_component(low, high):
    """Read final zero/one literal reachability in its own independently built graph."""
    edges = [('T', 1)] if low and high else [('T', 0)]
    if low and not high:
        edges.append((0, 1))
    reached = selected_component(('T', 0, 1), edges, 'T')
    return int(0 in reached), int(1 in reached)


def exhaustive_marked_component_tests(k):
    from opdc_feedback_market import decode_feedback

    points = tuple(product((0, 1), repeat=k))
    prefix = k - 1
    output_count = 1 << (1 << k)
    outer = [table_circuit(k, tuple(range(k)), mask) for mask in range(output_count)]
    outer_tables = [truth_table(circ) for circ in outer]
    assert all(t == tuple((m >> i) & 1 for i in range(len(points))) for m, t in enumerate(outer_tables))
    literals = [[table_circuit(k, (parent, prefix), mask) for mask in range(16)]
                for parent in range(prefix)]
    prefix_tables = [[truth_table(circ) for circ in row] for row in literals]
    for parent in range(prefix):
        for mask in range(16):
            assert prefix_tables[parent][mask] == tuple(
                (mask >> (2 * x[parent] + x[-1])) & 1 for x in points)
    finals = {(u, v): outer_component(u, v) for u, v in product((0, 1), repeat=2)}
    outcomes = Counter()
    multi_odd = 0
    for parents in product(range(prefix), repeat=prefix):
        for masks in product(range(16), repeat=prefix):
            info = tuple(independent_slice(parents, masks, b) for b in (0, 1))
            inner = tuple(data[0] for data in info)
            coefficients = tuple(data[1] for data in info)
            odd_branch = next((b for b in (0, 1) if info[b][2]), None)
            input_circuits = tuple(literals[p][m] for p, m in zip(parents, masks))
            input_tables = tuple(prefix_tables[p][m] for p, m in zip(parents, masks))
            if odd_branch is None:
                assert all(sum(pair) == 1 for b in inner for pair in b)
                locations = tuple(assignment_index(tuple(x[1] for x in inner[t]) + (t,)) for t in (0, 1))
            for mask, (circ, target_table) in enumerate(zip(outer, outer_tables)):
                if odd_branch is None:
                    final = finals[target_table[locations[0]], target_table[locations[1]]]
                else:
                    # The inner OV2 must be recovered before any final output price is used.
                    final = None
                ts = input_circuits + (circ,)
                decision = decode_feedback(ts, parents, inner, final, coefficients)
                key = check_certificate(decision, input_tables + (target_table,))
                outcomes[key] += 1
                if odd_branch is not None:
                    assert decision[0] == 'OV2' and decision[1] == min(info[odd_branch][2])
                    assert decision[2][-1] == decision[3][-1] == odd_branch
                    multi_odd += int(len(info[odd_branch][2]) > 1)
    expected = (prefix ** prefix) * (16 ** prefix) * output_count
    assert sum(outcomes.values()) == expected
    if k == 3:
        assert multi_odd > 0
    return outcomes, multi_odd


def compiled_market_benchmarks():
    from opdc_feedback_market import Circuit, compile_market

    # The unique admissible OPDC answer here uses two genuinely different points.
    cases = [((Circuit(2, (), 1), Circuit(2, (('not', 0),), 2)), (0,),
              (((1, 0),), ((0, 1),)), (1, 1), ('OV2', 1, (0, 0), (1, 1))),
             # No prefix bits for a unary final negation. Both final terminals must be marked.
             ((Circuit(1, (('not', 0),), 1),), (), ((), ()), (1, 1),
              ('OV2', 0, (0,), (1,))),
             # Two separate negative self-cycles share an odd branch. Its lowest maximum is zero.
             ((Circuit(3, (('not', 0),), 3), Circuit(3, (('not', 1),), 3), Circuit(3, (), 2)),
              (0, 1), (((1, 1), (1, 1)), ((1, 1), (1, 1))), None,
              ('OV2', 0, (0, 0, 0), (1, 0, 0))),
             # One negative two-cycle forces an OV2 with different earlier-coordinate witnesses.
             ((Circuit(3, (('not', 1),), 3), Circuit(3, (), 0), Circuit(3, (), 2)),
              (1, 0), (((1, 1), (1, 1)), ((1, 1), (1, 1))), None,
              ('OV2', 1, (1, 0, 0), (0, 1, 0))),
             # A syntactically parent-free prefix target and a constant outer target tested together.
             ((Circuit(2, (), 1), Circuit(2, (('const', 1),), 2)), (None,),
              (((1, 0),), ((0, 1),)), (0, 1), ('root', (1, 1))),
             # With a=OR(a,b), b=NAND(a,b), both children are consistent and the last crosses.
             ((Circuit(2, (('or', 0, 1),), 2), Circuit(2, (('nand', 0, 1),), 2)), (0,),
              (((1, 0),), ((0, 1),)), (1, 1), ('OV2', 1, (0, 0), (1, 1))),
             # Changing the outer NAND to OR forces a root after the nonconstant inner selection.
             ((Circuit(2, (('or', 0, 1),), 2), Circuit(2, (('or', 0, 1),), 2)), (0,),
              (((1, 0),), ((0, 1),)), (1, 0), ('root', (0, 0))),
             # NAND in both targets has an odd slice when b=1 and a forced earlier crossing there.
             ((Circuit(2, (('nand', 0, 1),), 2), Circuit(2, (('nand', 0, 1),), 2)), (0,),
              (((0, 1),), ((1, 1),)), None, ('OV2', 0, (0, 1), (1, 1))),
             # F0=(not x1) AND b, F1=NOR(x0,b), F2=majority(not x0,x1,b).
             # Both inner relations are nonlinear and switch their signed dependence on the other
             # prefix bit; the unrestricted outer target has all three inputs essential.
             ((Circuit(3, (('not', 1), ('and', 3, 2)), 4),
               Circuit(3, (('or', 0, 2), ('not', 3)), 4),
               Circuit(3, (('not', 0), ('and', 3, 1), ('or', 3, 1),
                           ('and', 2, 5), ('or', 4, 6)), 7)), (1, 0),
              (((1, 0), (0, 1)), ((0, 1), (1, 0))), (1, 1),
              ('OV2', 2, (0, 1, 0), (1, 0, 1)))]
    sizes = []
    for targets, parents, inner_expected, outer_expected, answer in cases:
        compiled = compile_market(targets, parents)
        expected = {}
        for branch, bits in zip(compiled.inner_ports, inner_expected):
            for rails, vals in zip(branch, bits):
                expected.update(zip(rails, vals))
        if outer_expected is not None:
            expected.update(zip(compiled.outer_ports, outer_expected))
        # Independently derive each physical cofactor label from the supplied target table.
        for last_bit, branch in enumerate(compiled.coefficients):
            for i, (uu, vv) in enumerate(branch):
                point = [0] * len(parents) + [last_bit]
                u = truth_table(targets[i])[assignment_index(point)]
                if parents[i] is not None:
                    point[parents[i]] = 1
                v = u ^ truth_table(targets[i])[assignment_index(point)]
                expected.update(zip(uu, (1 - u, u)))
                expected.update(zip(vv, (1 - v, v)))
        witness = check_all_equilibria(compiled.capacities, compiled.buyers, expected)
        assert compiled.decode(witness) == answer
        check_certificate(answer, tuple(truth_table(c) for c in targets))
        sizes.append((len(compiled.capacities), len(compiled.buyers)))
    return sizes


def main():
    if not __debug__:
        raise RuntimeError('Run this verifier with Python assertions enabled.')
    for k in (2, 3):
        started = monotonic()
        outcomes, odd = exhaustive_marked_component_tests(k)
        print(f'{k}-bit graph/decoder semantics: {sum(outcomes.values())} inputs, '
              f'{dict(sorted(outcomes.items()))}; {odd} inputs with multiple selected odd components '
              f'({monotonic()-started:.2f}s).', flush=True)
    graphs = selected_edge_tests()
    print(f'{graphs} controlled-graph markets: an equilibrium exists, and every equilibrium has '
          'the predicted vertex prices for all admissible symbolic reader loads.', flush=True)
    sizes = compiled_market_benchmarks()
    print(f'Full compiled-market tests (goods, buyers): {sizes}. All designated prices and '
          'decoded answers are forced; allocation uniqueness was not tested.')


if __name__ == '__main__':
    main()
