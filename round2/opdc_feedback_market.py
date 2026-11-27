"""Compile a conditional signed-unary OPDC prefix and one arbitrary last bit to an M1 market.

`Circuit(k, gates, output)` numbers its k inputs first and then its gates in
topological order. A gate is ("const", 0/1), ("copy"/"not", wire), or
("and"/"or"/"xor"/"nand", wire, wire).

`compile_market(targets, parents)` accepts one circuit per bit. Prefix target
i may read the final bit and parents[i], which is either another prefix index
(including i) or None. The final target can read any input. The condition is
checked on gates reachable from each target output. All two-bit circuits
qualify with parents=(0,). Good and buyer names are stable strings.

For (mass, offers) in the returned buyers table, offers[g]=(a,b) means
utility a-b*price[g]. Unlisted alternatives are unavailable (equivalently,
intercept -1 and slope 1); all outside utilities and price floors are zero.
The numbers in the table are fractions.Fraction. The decoder needs only
prices. It returns ("root", point) or ("OV2", zero_based_axis, lower, upper).
"""

from dataclasses import dataclass
from fractions import Fraction
from typing import Dict, Optional, Sequence, Tuple


Offer = Tuple[Fraction, Fraction]
Offers = Dict[str, Offer]
Buyers = Dict[str, Tuple[Fraction, Offers]]
Rail = Tuple[str, str]  # The price of rail[q] is the indicator of bit value q.
Gate = Tuple
Point = Tuple[int, ...]


_ARITY = {"copy": 1, "not": 1, "and": 2, "or": 2, "xor": 2, "nand": 2}


@dataclass(frozen=True)
class Circuit:
    inputs: int
    gates: Tuple[Gate, ...]
    output: int

    def __post_init__(self):
        object.__setattr__(self, "gates", tuple(tuple(g) for g in self.gates))
        if not isinstance(self.inputs, int) or self.inputs < 0:
            raise ValueError("Circuit input count must be a nonnegative integer")
        for index, gate in enumerate(self.gates, self.inputs):
            if not gate:
                raise ValueError("Every circuit gate must have an operation")
            if gate[0] == "const":
                if len(gate) != 2 or gate[1] not in (0, 1):
                    raise ValueError("A constant gate needs one Boolean value")
                continue
            if gate[0] not in _ARITY or len(gate) != _ARITY[gate[0]] + 1:
                raise ValueError(f"Unknown or malformed gate {gate!r}")
            if any(not isinstance(w, int) or not 0 <= w < index for w in gate[1:]):
                raise ValueError(f"Forward or invalid input in gate {gate!r}")
        if not isinstance(self.output, int) or not 0 <= self.output < self.inputs + len(self.gates):
            raise ValueError("Circuit output is not a wire")

    def dependencies(self):
        """The live original inputs and live computed wires, both in topological order."""
        live = {self.output}
        for wire in range(self.inputs + len(self.gates) - 1, self.inputs - 1, -1):
            if wire in live:
                gate = self.gates[wire - self.inputs]
                if gate[0] != "const":
                    live.update(gate[1:])
        return (tuple(i for i in range(self.inputs) if i in live),
                tuple(i for i in range(self.inputs, self.inputs + len(self.gates)) if i in live))

    def evaluate(self, point: Sequence[int]) -> int:
        if len(point) != self.inputs or any(bit not in (0, 1) for bit in point):
            raise ValueError("Circuit evaluation needs one Boolean value per input")
        values = list(point)
        for op, *args in self.gates:
            if op == "const":
                value = int(args[0])
            else:
                x = values[args[0]]
                if op == "copy":
                    value = x
                elif op == "not":
                    value = 1 - x
                else:
                    y = values[args[1]]
                    if op == "and":
                        value = x & y
                    elif op == "or":
                        value = x | y
                    elif op == "xor":
                        value = x ^ y
                    else:
                        value = 1 - (x & y)
            values.append(value)
        return values[self.output]


def _cycles(parents: Tuple[Optional[int], ...]):
    """All directed cycles of the base parent map, before any edges are switched off."""
    finished = set()
    result = []
    for start in range(len(parents)):
        path, position = [], {}
        v = start
        while v is not None and v not in finished and v not in position:
            position[v] = len(path)
            path.append(v)
            v = parents[v]
        if v in position:
            result.append(tuple(path[position[v]:]))
        finished.update(path)
    return tuple(result)


@dataclass
class CompiledMarket:
    capacities: Dict[str, Fraction]
    buyers: Buyers
    targets: Tuple[Circuit, ...]
    parents: Tuple[Optional[int], ...]
    inner_ports: Tuple[Tuple[Rail, ...], ...]
    outer_ports: Rail
    coefficients: Tuple[Tuple[Tuple[Rail, Rail], ...], ...]  # Per branch and variable: (u,v).

    def decode(self, prices) -> Tuple:
        """Decode any exact equilibrium prices. Several equilibrium allocations are allowed."""
        inner = tuple(tuple((prices[p0], prices[p1]) for p0, p1 in ports) for ports in self.inner_ports)
        outer = tuple(prices[g] for g in self.outer_ports)
        coefs = tuple(tuple((prices[u[1]], prices[v[1]]) for u, v in block)
                      for block in self.coefficients)
        return decode_feedback(self.targets, self.parents, inner, outer, coefs)


def _bit(val):
    if val not in (0, 1):
        raise ValueError(f"Expected a Boolean equilibrium price, got {val}")
    return int(val)


def _crossing(targets, axis: int, lo: Point, hi: Point):
    if (lo[axis], hi[axis]) != (0, 1) or lo[axis + 1:] != hi[axis + 1:]:
        raise ValueError("The proposed crossing does not have common suffix and adjacent endpoints")
    for point in (lo, hi):
        if targets[axis].evaluate(point) == point[axis]:
            raise ValueError("The proposed crossing is stationary at its crossing coordinate")
        if any(targets[i].evaluate(point) != point[i] for i in range(axis)):
            raise ValueError("The proposed crossing fails a lower-coordinate target")
    return "OV2", axis, lo, hi


def _branch_coefficients(targets, parents, last):
    pairs = []
    for i, parent in enumerate(parents):
        point = [0] * len(parents) + [last]
        u = targets[i].evaluate(point)
        if parent is not None:
            point[parent] = 1
        v = u ^ targets[i].evaluate(point)
        pairs.append((u, v))
    return pairs


def decode_feedback(targets, parents, inner_values, outer_values, coefficients=None):
    """Decode literal values, optionally supplying the physical unary-coefficient prices.

    `inner_values[t][i][q]` and `outer_values[q]` are literal prices for bit value q.
    `coefficients[t][i]=(u,v)` means F_i(parent,t)=u XOR (v AND parent).
    An inner crossing makes the outer prices immaterial, including fractional prices.
    """
    cycles = _cycles(parents)
    for last, ports in enumerate(inner_values):
        # A broken or even base cycle has complementary literals. The marked
        # active odd cycle has both literals of its largest vertex at price one.
        odd = [max(c) for c in cycles if all(_bit(p) for p in ports[max(c)])]
        if not odd:
            continue
        axis = min(odd)
        coeff = (_branch_coefficients(targets, parents, last) if coefficients is None else
                 [(_bit(u), _bit(v)) for u, v in coefficients[last]])
        branches = []
        for chosen in (0, 1):
            assigned = {i: 0 for i in range(axis + 1, len(parents))}
            assigned[axis] = chosen
            for start in range(axis):
                if start in assigned:
                    continue
                path, seen = [], set()
                i = start
                while i not in assigned and i not in seen:
                    u, v = coeff[i]
                    if not v:
                        assigned[i] = u
                        break
                    seen.add(i)
                    path.append(i)
                    i = parents[i]
                if i not in assigned:
                    # A surviving dependency cycle strictly below axis is even.
                    assigned[i] = _bit(ports[i][1])
                for vtx in reversed(path):
                    assigned[vtx] = coeff[vtx][0] ^ assigned[parents[vtx]]
            branches.append(tuple(assigned[i] for i in range(len(parents))) + (last,))
        return _crossing(targets, axis, *branches)

    roots = [tuple(_bit(rail[1]) for rail in ports) + (last,)
             for last, ports in enumerate(inner_values)]
    q0, q1 = (_bit(value) for value in outer_values)
    if q0 and q1:
        return _crossing(targets, len(parents), *roots)
    if q0 == q1:
        raise ValueError("Final selector has no active literal")
    point = roots[q1]
    if any(target.evaluate(point) != point[i] for i, target in enumerate(targets)):
        raise ValueError("The selected point is not a full fixed point")
    return "root", point


class _MarketBuilder:
    def __init__(self):
        self.capacities = {}
        self.buyers = {}
        self.incident = {}

    def good(self, name, capacity):
        if name in self.capacities or capacity <= 0:
            raise ValueError(f"Duplicate or nonpositive-capacity good {name!r}")
        self.capacities[name] = Fraction(capacity)

    def buyer(self, name, mass, offers):
        if name in self.buyers or mass <= 0:
            raise ValueError(f"Duplicate or nonpositive buyer {name!r}")
        mass = Fraction(mass)
        offers = {g: (Fraction(a), Fraction(b)) for g, (a, b) in offers.items()}
        self.buyers[name] = mass, offers
        for g in offers:
            self.incident[g] = self.incident.get(g, 0) + mass

    def source(self, name, value):
        readers = self.incident.get(name, 0)
        cap = 1 + readers
        self.good(name, cap)
        self.buyer(f"{name}/anchor", cap + 1, {name: (value, 1)})


class _Gates:
    """Logical circuit, instantiated backward to budget all market readers exactly."""

    def __init__(self, name, constants):
        self.name = name
        self.constants = constants
        self.gates = []

    def gate(self, op, a, b):
        out = f"{self.name}/gate-{len(self.gates)}"
        self.gates.append((out, op, a, b))
        return out

    def boolean(self, op, x, y=None):
        if op == "copy":
            return x
        if op == "not":
            return x[::-1]
        if op == "nand":
            return self.boolean("and", x, y)[::-1]
        if op == "xor":
            # This formula uses both rails and has no complement-price operation.
            return self.boolean("or", self.boolean("and", x, y[::-1]),
                                self.boolean("and", x[::-1], y))
        if op == "and":
            return self.gate("max", x[0], y[0]), self.gate("min", x[1], y[1])
        if op == "or":
            return self.gate("min", x[0], y[0]), self.gate("max", x[1], y[1])
        raise ValueError(f"Unknown gate {op!r}")

    def compile(self, circuit, assignments):
        _, gates = circuit.dependencies()
        wires = dict(assignments)
        for wire in gates:
            op, *args = circuit.gates[wire - circuit.inputs]
            if op == "const":
                value = self.constants[int(args[0])]
            else:
                value = self.boolean(op, *(wires[x] for x in args))
            wires[wire] = value
        return wires[circuit.output]

    def install(self, market):
        for name, op, a, b in reversed(self.gates):
            readers = market.incident.get(name, 0)
            mass = 4 * (1 + readers)
            cap = (Fraction(3, 2) if op == "min" else Fraction(1, 2)) * mass
            market.good(name, cap)
            for idx, arg in enumerate((a, b)):
                market.buyer(f"{name}/bid-{idx}", mass, {name: (1, 1), arg: (1, 1)})


class _Graph:
    """Controlled reachability. Each enabled edge can rebalance one unit in either direction."""

    def __init__(self, name, count):
        self.name = name
        self.source = f"{name}/source"
        self.ports = tuple((f"{name}/v{i}-0", f"{name}/v{i}-1") for i in range(count))
        self.vertices = (self.source,) + tuple(g for pair in self.ports for g in pair)
        self.edges = []

    def edge(self, u, v, on):
        self.edges.append((u, v, on))

    def install(self, market):
        n = len(self.vertices)
        eps = Fraction(1, 4 * n + 4)
        downstream = max(market.incident.get(g, 0) for g in self.vertices)
        unit = 1 + downstream / eps
        degree = dict.fromkeys(self.vertices, 0)
        for u, v, _ in self.edges:
            degree[u] += 1
            degree[v] += 1
        for g in self.vertices:
            market.good(g, unit * (1 + degree[g] + eps))
            market.buyer(f"{g}/home", unit, {g: (2, 1)})
        market.buyer(f"{self.source}/mark", unit, {self.source: (1, 1)})
        for idx, (u, v, choice) in enumerate(self.edges):
            name = f"{self.name}/edge-{idx}"
            # A high price on choice[1] enables edge endpoints; a high price
            # on the opposite rail enables the two home buyers instead.
            market.buyer(f"{name}/joint", 2 * unit, {u: (2, 1), v: (2, 1), choice[1]: (3, 3)})
            for end, g in enumerate((u, v)):
                market.buyer(f"{name}/home-{end}", unit, {g: (2, 1), choice[0]: (3, 3)})


def compile_market(targets: Sequence[Circuit], parents: Sequence[Optional[int]]) -> CompiledMarket:
    """Make one market from the local targets and designated inner parents, without selecting an answer."""
    targets = tuple(targets)
    parents = tuple(parents)
    k = len(targets)
    last = k - 1
    if not k or len(parents) != last:
        raise ValueError("Expected k>=1 targets and k-1 inner parent entries")
    if any(not isinstance(c, Circuit) or c.inputs != k for c in targets):
        raise ValueError("Every target must be a circuit on the same k original inputs")
    for i, parent in enumerate(parents):
        if parent is not None and (not isinstance(parent, int) or not 0 <= parent < last):
            raise ValueError(f"Invalid inner parent for bit {i}")
        live, _ = targets[i].dependencies()
        if any(w != parent and w != last for w in live):
            raise ValueError(f"Target {i} depends on a non-parent prefix coordinate")

    base = ("global/zero", "global/one")
    constants = (base[::-1], base)
    first = _Gates("selectors", constants)
    second = _Gates("last-target", constants)
    inner = [_Graph(f"inner-{b}", last) for b in (0, 1)]
    cycles = _cycles(parents)
    coefs, last_bits = [], []
    for b, graph in enumerate(inner):
        pairs = []
        for i, parent in enumerate(parents):
            cofactor = []
            for a in (0, 1):
                assigned = {last: constants[b]}
                if parent is not None:
                    assigned[parent] = constants[a]
                cofactor.append(first.compile(targets[i], assigned))
            u = cofactor[0]
            v = first.boolean("xor", cofactor[0], cofactor[1])
            pairs.append((u, v))
            for sign in (0, 1):
                u_is_sign = u if sign else u[::-1]
                const = first.boolean("and", v[::-1], u_is_sign)
                graph.edge(graph.source, graph.ports[i][sign], const)
                if parent is not None:
                    active = first.boolean("and", v, u_is_sign)
                    for q in (0, 1):
                        graph.edge(graph.ports[i][q], graph.ports[parent][q ^ sign], active)
        for cycle in cycles:
            activate = constants[1]
            for i in cycle:
                activate = first.boolean("and", activate, pairs[i][1])
            graph.edge(graph.source, graph.ports[max(cycle)][0], activate)
        coefs.append(tuple(pairs))
        assigned = {i: graph.ports[i] for i in range(last)}
        assigned[last] = constants[b]
        last_bits.append(second.compile(targets[last], assigned))

    outer = _Graph("outer", 1)
    low, high = last_bits
    # 00 and 11 are constant targets. On 01 (identity) choose branch 0.
    # On 10 (negation) connect both literals and expose the crossing.
    is11 = second.boolean("and", low, high)
    is10 = second.boolean("and", low, high[::-1])
    outer.edge(outer.source, outer.ports[0][0], is11[::-1])
    outer.edge(outer.source, outer.ports[0][1], is11)
    outer.edge(outer.ports[0][0], outer.ports[0][1], is10)

    market = _MarketBuilder()
    # Quantities are fixed from the sinks backward. The largest reader mass
    # increases by at most a polynomial factor per layer. Its binary length
    # and the binary length of every capacity therefore stay polynomial.
    outer.install(market)
    second.install(market)
    for graph in inner:
        graph.install(market)
    first.install(market)
    for i, name in enumerate(base):
        market.source(name, i)
    return CompiledMarket(market.capacities, market.buyers, targets, parents,
                          tuple(graph.ports for graph in inner), outer.ports[0], tuple(coefs))
