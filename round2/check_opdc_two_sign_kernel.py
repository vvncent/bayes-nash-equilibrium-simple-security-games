"""Check the physical two-exception NOR reduction using NetworkX and Z3."""

from collections import Counter
from itertools import product
from random import Random

import networkx as nx
import z3

from check_opdc_local_gates import certificates
from check_opdc_two_sign_lift import lift_targets
from opdc_two_sign_kernel import compile_two_sign_kernel


def source_table(d, gates, outputs):
    table = {}
    for q in product((0, 1), repeat=d):
        wires = list(q)
        for a, b in gates:
            wires.append(1 - wires[a] * wires[b])
        table[q] = tuple(wires[v] for v in outputs)
    return table


def check_graph(d, gates, outputs, girth=3):
    compiled = compile_two_sign_kernel(d, gates, outputs, girth)
    rows, colors = compiled.rows, compiled.colors
    cut = len(rows) - 2 * d
    graph = nx.DiGraph()
    graph.add_nodes_from(range(len(rows)))
    graph.add_edges_from((v, w) for v, row in enumerate(rows) for w in row)
    assert all(1 <= len(row) == len(set(row)) <= 2 for row in rows)
    assert nx.number_of_selfloops(graph) == 0
    assert len(graph.to_undirected().edges) == len(graph.edges)
    assert max(dict(graph.in_degree()).values()) <= 2
    assert max(dict(graph.to_undirected().degree()).values()) <= 3
    if girth > 3:
        assert nx.girth(graph.to_undirected()) >= girth

    exceptional = [(v, w) for v, w in graph.edges if colors[v] == colors[w]]
    assert len(exceptional) == 2 and {w for v, w in exceptional} == {0, 1}
    residual = graph.copy()
    residual.remove_edges_from(exceptional)
    assert nx.is_bipartite(residual.to_undirected())
    assert nx.is_strongly_connected(graph)
    assert nx.is_directed_acyclic_graph(graph.subgraph(range(cut)))
    assert colors[cut:] == (0,) * (2 * d)
    # Natural continuous extension in physical coordinates is 1 - max(inputs).
    # Check the public midpoint even after degree reduction and subdivision.
    midpoint = (0.5,) * len(rows)
    assert tuple(1 - max(midpoint[w] for w in row) for row in rows) == midpoint

    source = source_table(d, gates, outputs)
    directions = {}
    for rails in product((0, 1), repeat=2 * d):
        x = compiled.lift_rails(rails)
        target = tuple(int(not any(x[w] for w in row)) for row in rows)
        assert x[:cut] == target[:cut]
        assert target[cut:] == lift_targets(rails, source)
        directions[rails] = tuple(a - b for a, b in zip(target[cut:], rails))
    lifted_answers = set()
    for kind, axis, *points in certificates(tuple(directions), directions.__getitem__, 2 * d):
        raw = (kind, cut + axis, *[compiled.lift_rails(x) for x in points])
        if kind == "OV2":
            assert axis % 2
        q = [x[1::2] for x in points]
        if kind == "OV1":
            q.sort()
            axis = (axis + 1) // 2 - 1
        else:
            axis //= 2
        answer = (kind, axis, *q)
        assert compiled.decode(raw) == answer
        lifted_answers.add(answer)
    def source_direction(point):
        return tuple(a - b for a, b in zip(source[point], point))
    assert lifted_answers == set(certificates(tuple(source), source_direction, d))
    return compiled, lifted_answers


def verify_raw_violations(compiled, expected):
    """Search directly over both full physical vectors with free inconsistent helpers."""
    rows = compiled.rows
    size = len(rows)
    cut = size - 2 * compiled.dimension
    a = [z3.Bool(f"a{i}") for i in range(size)]
    b = [z3.Bool(f"b{i}") for i in range(size)]

    def targets(x):
        return [z3.Not(z3.Or([x[w] for w in row])) for row in rows]

    ta, tb = targets(a), targets(b)
    sat_count = Counter()
    for axis in range(size):
        solver = z3.Solver()
        solver.add([a[i] == b[i] for i in range(axis + 1, size)])
        for i in range(axis):
            solver.add(a[i] == ta[i], b[i] == tb[i])
        for kind in ("OV1", "OV2"):
            solver.push()
            if kind == "OV1":
                solver.add(a[axis] == ta[axis], b[axis] == tb[axis],
                           z3.Or([a[i] != b[i] for i in range(axis + 1)]))
            else:
                solver.add(z3.Not(a[axis]), b[axis], ta[axis], z3.Not(tb[axis]))
            while True:
                result = solver.check()
                if result == z3.unsat:
                    break
                assert result == z3.sat and axis >= cut
                model = solver.model()
                project = lambda xs: tuple(int(z3.is_true(model.eval(v, model_completion=True)))
                                           for v in xs[cut + 1::2])
                qa, qb = project(a), project(b)
                rail_axis = axis - cut
                if kind == "OV1":
                    qa, qb = sorted((qa, qb))
                    orig_axis = (rail_axis + 1) // 2 - 1
                else:
                    assert rail_axis % 2
                    orig_axis = rail_axis // 2
                assert (kind, orig_axis, qa, qb) in expected
                sat_count[kind] += 1
                # Block this ordered physical primary pair. All its helpers
                # are uniquely fixed whenever the crossing axis is a primary.
                solver.add(z3.Or([v != model.eval(v, model_completion=True)
                                  for v in a[cut:] + b[cut:]]))
            solver.pop()
    return sat_count


def main():
    rng = Random(190617)
    cases = [
        (1, (), (0,)),                       # two full roots and OV1
        (1, ((0, 0),), (1,)),                # one crossing
        (2, ((0, 0),), (1, 2)),              # crossing at the original upper axis
        (2, ((0, 0), (0, 2)), (3, 3)),       # constant one, unique promised root
        (4, ((1, 2), (2, 3)), (4, 5, 0, 1)),
    ]
    measured = []
    raw = Counter()
    for i, (d, gates, outputs) in enumerate(cases):
        g, expected = check_graph(d, gates, outputs)
        measured.append(len(g.rows))
        if i < 4:
            raw.update(verify_raw_violations(g, expected))
    g, _ = check_graph(1, ((0, 0),), (1,), girth=17)
    for lower, upper, result in [(-1, -1, ("OV3", 0, (0,))),
                                 (1, 1, ("OV3", 0, (1,)))]:
        crossing = ("OV2", len(g.rows) - 1,
                    g.lift_rails((1, 0)), g.lift_rails((0, 1)))
        assert g.decode(crossing, lambda q: ((lower, upper)[q[0]],)) == result
    for trial in range(40):
        d = 1 + trial % 4
        gates = tuple((rng.randrange(d + j), rng.randrange(d + j)) for j in range(trial % 8))
        outputs = tuple(rng.randrange(d + len(gates)) for _ in range(d))
        measured.append(len(check_graph(d, gates, outputs)[0].rows))
    print(f"{len(measured)} strongly connected physical graphs, {min(measured)}–{max(measured)} "
          "vertices, all primary-rail states, two exceptional arcs with heads in positions 0 and 1.")
    print(f"Girth-17 graph passed with {len(g.rows)} vertices. Raw all-helper SMT on four "
          f"graphs allowed {raw['OV1']} ordered OV1 pairs and {raw['OV2']} OV2 pairs; "
          "all projected to source answers.")


if __name__ == "__main__":
    main()
