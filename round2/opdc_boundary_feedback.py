"""Compile ordered circuit blocks with two trailing feedback coordinates into one M1 market.

Each block is a contiguous range of 0-based coordinates ending in u,v.
Removing the two rows for u,v must leave its interior dependency graph
acyclic. Rows may also read earlier blocks. No row may read a later block.
The decoder returns ("root", point) or ("OV2", axis, lower, upper).
"""

from dataclasses import dataclass
from heapq import heapify, heappop, heappush

from opdc_feedback_market import Circuit, _Gates, _Graph, _MarketBuilder, _crossing


class _Logic(_Gates):
    """Fold fixed Boolean pins while retaining the active dependency graph as market goods."""

    def boolean(self, op, x, y=None):
        if op in ("copy", "not"):
            return super().boolean(op, x, y)
        if op == "nand":
            return self.boolean("and", x, y)[::-1]
        zero, one = self.constants
        if op == "xor":
            if x == zero or y == zero:
                return y if x == zero else x
            if x == one or y == one:
                return (y if x == one else x)[::-1]
            if x == y:
                return zero
            if x == y[::-1]:
                return one
        elif op in ("and", "or"):
            absorbing, neutral = (zero, one) if op == "and" else (one, zero)
            if x == absorbing or y == absorbing or x == y[::-1]:
                return absorbing
            if x == neutral or x == y:
                return y
            if y == neutral:
                return x
        return super().boolean(op, x, y)


def interior_order(targets, start, end):
    u = end - 2
    incoming = {i: 0 for i in range(start, u)}
    out = {i: [] for i in incoming}
    for i in range(start, end):
        live, _ = targets[i].dependencies()
        if any(j >= end for j in live):
            raise ValueError("A block cannot read a later block")
        if i < u:
            for j in live:
                if j in incoming:
                    incoming[i] += 1
                    out[j].append(i)
    ready = [i for i in incoming if not incoming[i]]
    heapify(ready)
    order = []
    while ready:
        i = heappop(ready)
        order.append(i)
        for j in out[i]:
            incoming[j] -= 1
            if not incoming[j]:
                heappush(ready, j)
    if len(order) != len(incoming):
        raise ValueError("Removing the two boundary rows must break every interior cycle")
    return tuple(order)


@dataclass
class Layer:
    start: int
    end: int
    inner: tuple
    outer: object
    interior_ports: tuple
    outputs: dict


@dataclass
class Compiled:
    targets: tuple
    capacities: dict
    buyers: dict
    layers: tuple

    def decode(self, prices):
        def rail(port):
            pair = tuple(prices[g] for g in port)
            if pair not in ((0, 1), (1, 0), (1, 1)):
                raise ValueError(f"Expected Boolean literal prices, received {pair}")
            return pair

        def bit(port):
            pair = rail(port)
            if pair == (1, 1):
                raise ValueError("A selected root needs complementary literals")
            return int(pair[1])

        prefix = ()
        n = len(self.targets)
        for layer in self.layers:
            start, end = layer.start, layer.end
            u, v = end - 2, end - 1
            suffix = (0,) * (n - end)
            for t in (0, 1):
                if rail(layer.inner[t].ports[u - start]) == (1, 1):
                    pts = []
                    for s in (0, 1):
                        body = tuple(bit(layer.interior_ports[t][s][i]) for i in range(start, u))
                        pts.append(prefix + body + (s, t) + suffix)
                    return _crossing(self.targets, u, *pts)
            if rail(layer.outer.ports[0]) == (1, 1):
                pts = []
                for t in (0, 1):
                    body = tuple(bit(p) for p in layer.inner[t].ports)
                    pts.append(prefix + body + (t,) + suffix)
                return _crossing(self.targets, v, *pts)
            prefix += tuple(bit(layer.outputs[i]) for i in range(start, end))
        if any(row.evaluate(prefix) != prefix[i] for i, row in enumerate(self.targets)):
            raise ValueError("The market's selected coordinates do not give a Boolean root")
        return "root", prefix


def compile_market(targets, block_ends, fold_pins=True):
    """block_ends lists the exclusive endpoints of the consecutive two-boundary blocks."""
    targets, ends = tuple(targets), tuple(block_ends)
    if not targets or not ends or ends[-1] != len(targets):
        raise ValueError("Blocks must partition all coordinates")
    if any(not isinstance(row, Circuit) or row.inputs != len(targets) for row in targets):
        raise ValueError("All target circuits must use the same full coordinate set")
    physical = _MarketBuilder()
    pins = ("boundaries/zero", "boundaries/one")
    constants = (pins[::-1], pins)
    logic = _Logic if fold_pins else _Gates
    earlier, schedule, layers = {}, [], []
    start = 0
    for end in ends:
        if type(end) is not int or end - start < 2:
            raise ValueError("Each block needs two trailing boundary coordinates")
        u, v = end - 2, end - 1
        order = interior_order(targets, start, end)
        front = logic(f"b{start}/conditional", constants)
        schedule.append(front)
        graphs, saved = [], []
        for t in (0, 1):
            graph = _Graph(f"b{start}/inner{t}", u - start + 1)
            graphs.append(graph)
            z = []
            h = []
            for s in (0, 1):
                wires = dict(earlier)
                wires[u], wires[v] = constants[s], constants[t]
                for i in order:
                    wires[i] = front.compile(targets[i], wires)
                z.append({i: wires[i] for i in range(start, u + 1)})
                h.append(front.compile(targets[u], wires))
            saved.append(tuple(z))
            target = {i: (z[0][i], z[1][i]) for i in order}
            target[u] = h
            varying = {i: front.boolean("xor", pair[0], pair[1]) for i, pair in target.items()}
            for i in range(start, u + 1):
                p = graph.ports[i - start]
                for out_bit in (0, 1):
                    at_zero = target[i][0] if out_bit else target[i][0][::-1]
                    if i != u:
                        at_zero = front.boolean("and", at_zero, varying[i][::-1])
                    graph.edge(graph.source, p[out_bit], at_zero)
                for j in targets[i].dependencies()[0]:
                    if not start <= j <= u:
                        continue
                    pred = graph.ports[j - start]
                    active = varying[i] if j == u else front.boolean("and", varying[i], varying[j])
                    parity = front.boolean("xor", z[0][j], target[i][0])
                    for sign in (0, 1):
                        on = front.boolean("and", active, parity if sign else parity[::-1])
                        for b in (0, 1):
                            graph.edge(pred[b], p[b ^ sign], on)
            schedule.append(graph)
        outer_gates = logic(f"b{start}/outer-control", constants)
        y = []
        for t in (0, 1):
            inputs = dict(earlier)
            inputs.update(zip(range(start, u + 1), graphs[t].ports))
            inputs[v] = constants[t]
            y.append(outer_gates.compile(targets[v], inputs))
        outer = _Graph(f"b{start}/outer", 1)
        is11 = outer_gates.boolean("and", *y)
        is10 = outer_gates.boolean("and", y[0], y[1][::-1])
        outer.edge(outer.source, outer.ports[0][0], is11[::-1])
        outer.edge(outer.source, outer.ports[0][1], is11)
        outer.edge(outer.ports[0][0], outer.ports[0][1], is10)
        mux = logic(f"b{start}/output", constants)
        selected = outer.ports[0]
        outputs = {v: selected}
        for i in range(start, u + 1):
            when0 = mux.boolean("and", selected[::-1], graphs[0].ports[i - start])
            when1 = mux.boolean("and", selected, graphs[1].ports[i - start])
            outputs[i] = mux.boolean("or", when0, when1)
        schedule.extend((outer_gates, outer, mux))
        layers.append(Layer(start, end, tuple(graphs), outer, tuple(saved), outputs))
        earlier.update(outputs)
        start = end
    for stage in reversed(schedule):
        stage.install(physical)
    for value, name in enumerate(pins):
        physical.source(name, value)
    return Compiled(targets, physical.capacities, physical.buyers, tuple(layers))
