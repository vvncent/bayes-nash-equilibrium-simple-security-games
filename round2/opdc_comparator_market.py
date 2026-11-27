"""An ordinary affine matching market for cyclic signed comparator networks.

Every logical signal is defined once and consumed at most once. A comparator
produces AND and OR together, may complement either input/output, and may
discard either output. The two outputs can both be read by other comparators.
The market represents signals by pairs of allocation quantities. Its routers
and alternating switches can be connected around cycles.

`compile_market(net)` chooses dyadic damping delta <= 1/(32 n) and switch
quantum q <= delta/(128 n^2). The projected residual is bounded by
delta/2 + 4 n q/delta < 1/(16 n), sufficient for exact same-cell recovery.
Smaller exponents are available for component tests; at coarse settings
the observed active cell may lack a true undamped fixed point. Capacities and
offers use the (mass, {good: (intercept,slope)}) M1 convention, outside value 0.
`market.decode(flows)` accepts a sparse map (buyer,good) -> rational mass.
Switch generation uses the accompanying manuscript's exact two-copy builder;
Z3 is used by that builder's imported verifier and by rational LP recovery.
"""

from dataclasses import dataclass
from fractions import Fraction as F
from functools import lru_cache
import importlib.util
from pathlib import Path
import sys
from typing import Dict, Optional, Tuple

if __package__:
    from .opdc_feedback_market import Buyers, _MarketBuilder
else:
    from opdc_feedback_market import Buyers, _MarketBuilder


@dataclass(frozen=True)
class Literal:
    wire: int
    negated: bool = False

    def read(self, values):
        return 1 - values[self.wire] if self.negated else values[self.wire]


@dataclass(frozen=True)
class Comparator:
    left: Literal
    right: Literal
    and_output: Optional[Literal]
    or_output: Optional[Literal]


@dataclass(frozen=True)
class Unary:
    source: Literal
    output: Literal


@dataclass(frozen=True)
class Constant:
    value: int
    output: Literal


def _outputs(gate):
    return (gate.and_output, gate.or_output) if isinstance(gate, Comparator) else (gate.output,)


def _inputs(gate):
    if isinstance(gate, Comparator):
        return gate.left, gate.right
    return (gate.source,) if isinstance(gate, Unary) else ()


def _fraction(x):
    if hasattr(x, "numerator_as_long"):
        return F(x.numerator_as_long(), x.denominator_as_long())
    return F(x)


@dataclass(frozen=True)
class ComparatorNetwork:
    size: int
    gates: tuple

    def __post_init__(self):
        object.__setattr__(self, "gates", tuple(self.gates))
        if not isinstance(self.size, int) or self.size < 1:
            raise ValueError("A network has a positive integer number of wires")
        defined, consumed = set(), set()
        for gate in self.gates:
            if not isinstance(gate, (Comparator, Unary, Constant)):
                raise ValueError(f"Unrecognized gate {gate!r}")
            if isinstance(gate, Constant) and gate.value not in (0, 1):
                raise ValueError("Expected a zero or one source")
            outputs = tuple(x for x in _outputs(gate) if x is not None)
            if not outputs or (not isinstance(gate, Comparator) and gate.output is None):
                raise ValueError("Each gate must define at least one output")
            for items, used in ((_inputs(gate), consumed), (outputs, defined)):
                for lit in items:
                    if (not isinstance(lit, Literal) or not isinstance(lit.wire, int)
                            or not 0 <= lit.wire < self.size or lit.negated not in (False, True)):
                        raise ValueError(f"Invalid wire or sign on {lit!r}")
                    if lit.wire in used:
                        role = "read more than once" if used is consumed else "defined more than once"
                        raise ValueError(f"Wire {lit.wire} is {role}")
                    used.add(lit.wire)
        if len(defined) != self.size:
            raise ValueError("Every declared wire needs exactly one defining gate")

    def evaluate(self, values):
        """Evaluate the real, signed, undamped target on its full cube."""
        if len(values) != self.size or any(not 0 <= x <= 1 for x in values):
            raise ValueError("A state must lie in the network cube")
        result = [None] * self.size
        for gate in self.gates:
            if isinstance(gate, Comparator):
                total = gate.left.read(values) + gate.right.read(values)
                raw = (max(0, total - 1), min(1, total))
            elif isinstance(gate, Unary):
                raw = (gate.source.read(values),)
            else:
                raw = (gate.value,)
            for port, value in zip(_outputs(gate), raw):
                if port is not None:
                    result[port.wire] = 1 - value if port.negated else value
        return tuple(result)

    def recover_fixed_point(self, estimate):
        """Repair an inverse-polynomial residual. For coarser probes, try their exact linear cell."""
        estimate = tuple(_fraction(x) for x in estimate)
        if len(estimate) != self.size or any(not 0 <= v <= 1 for v in estimate):
            raise ValueError("The estimate must lie in the network cube")
        residual = max(abs(x - y) for x, y in zip(estimate, self.evaluate(estimate)))
        if residual < F(1, 16 * self.size):
            if __package__:
                from .opdc_comparator_repair import recover_approximate
            else:
                from opdc_comparator_repair import recover_approximate
            return recover_approximate(self, estimate)
        import z3

        variables = [z3.Real(f"signcomp_{i}") for i in range(self.size)]
        lp = z3.SolverFor("QF_LRA")
        for x in variables:
            lp.add(x >= 0, x <= 1)
        for gate in self.gates:
            if isinstance(gate, Comparator):
                total = gate.left.read(variables) + gate.right.read(variables)
                if gate.left.read(estimate) + gate.right.read(estimate) <= 1:
                    lp.add(total <= 1)
                    raw = (0, total)
                else:
                    lp.add(total >= 1)
                    raw = (total - 1, 1)
            elif isinstance(gate, Unary):
                raw = (gate.source.read(variables),)
            else:
                raw = (gate.value,)
            for port, value in zip(_outputs(gate), raw):
                if port is not None:
                    lp.add(variables[port.wire] == (1 - value if port.negated else value))
        if lp.check() != z3.sat:
            raise ValueError("The selected cell has no fixed point at this precision")
        model = lp.model()
        point = tuple(_fraction(model.eval(x, model_completion=True)) for x in variables)
        if self.evaluate(point) != point:
            raise ArithmeticError("The recovered point fails the original signed equations")
        return point

    def decode_fixed_point(self, point):
        """Round the signed permutation on the fractional coordinates, or extract an ordered crossing."""
        point = tuple(_fraction(x) for x in point)
        if self.evaluate(point) != point:
            raise ValueError("Need an exact fixed point of the undamped real targets")
        parent = {}
        for gate in self.gates:
            frac = [s for s in _inputs(gate) if 0 < point[s.wire] < 1]
            outputs = [s for s in _outputs(gate) if s is not None and 0 < point[s.wire] < 1]
            if not frac and not outputs:
                continue
            if len(frac) != 1 or len(outputs) != 1:
                raise ArithmeticError("Fractional conservation at the comparator failed")
            source, output = frac[0], outputs[0]
            parent[output.wire] = source.wire, int(output.negated ^ source.negated)
        if len(set(v for v, _ in parent.values())) != len(parent):
            raise ArithmeticError("Fractional dependencies do not form a signed permutation")
        cycles = []
        seen = set()
        for start in parent:
            if start in seen:
                continue
            cycle, i = [], start
            while i not in seen:
                cycle.append(i)
                seen.add(i)
                i = parent[i][0]
            cycles.append(cycle)
        odd = [max(c) for c in cycles if sum(parent[i][1] for i in c) % 2]

        def complete(pivot=None, pivot_value=None):
            values = {i: int(x) for i, x in enumerate(point) if x in (0, 1)}
            if pivot is not None:
                values.update({v: 0 for v in parent if v > pivot})
                values[pivot] = pivot_value
            for cycle in cycles:
                if not any(i in values for i in cycle):
                    values[cycle[0]] = 0
                for start in cycle:
                    path = []
                    while start not in values:
                        path.append(start)
                        start = parent[start][0]
                    for i in reversed(path):
                        predecessor, flip = parent[i]
                        values[i] = values[predecessor] ^ flip
            return tuple(values[i] for i in range(self.size))

        if not odd:
            root = complete()
            if self.evaluate(root) != root:
                raise ArithmeticError("Rounded point is not a Boolean root")
            return "root", root
        axis = min(odd)
        low, high = complete(axis, 0), complete(axis, 1)
        for x in (low, high):
            target = self.evaluate(x)
            if target[:axis] != x[:axis] or target[axis] == x[axis]:
                raise ArithmeticError("Rounding did not produce the proposed prefix crossing")
        if low[axis + 1:] != high[axis + 1:]:
            raise ArithmeticError("The crossing endpoints have different suffixes")
        return "OV2", axis, low, high


@lru_cache(maxsize=1)
def _switch_factory():
    """Use the same two-copy arc and price parameter generator as the checked manuscript."""
    path = Path(__file__).resolve().parent.parent / "code" / "lib" / "twocopy_gadget.py"
    spec = importlib.util.spec_from_file_location("opdc_comparator_twocopy", path)
    if spec is None or spec.loader is None:
        raise ImportError(f"Cannot load the manuscript switch generator at {path}")
    module = importlib.util.module_from_spec(spec)
    previous = sys.path[:]
    try:
        spec.loader.exec_module(module)
    finally:
        sys.path[:] = previous
    return module.gadget


@lru_cache(maxsize=4)
def _switch_template(precision_exponent):
    gadget, _, _ = _switch_factory()(precision_exponent)
    return gadget


class _Routing:
    def __init__(self):
        self.market = _MarketBuilder()
        self.routers = []
        self.rotors = []
        self.discard = "route/discard"

    def priority(self, name, successors):
        # All tranches have quota one. Pad only after all incoming rows exist.
        self.routers.append((name, len(successors)))
        n = len(successors)
        for j, destination in enumerate(successors, 1):
            if destination == name:
                raise ValueError("A priority tranche cannot use its own input good as its successor")
            # Normalize output slope to one, preserving all demand and prices.
            scale = 4 * (n + 1)
            self.market.buyer(f"{name}/forward-{j}", 1, {name: (scale, scale),
                              destination: (scale - 2 * j, 1)})

    def source(self, name, mass, destination):
        if mass:
            self.market.buyer(name, mass, {destination: (2, 1)})

    def switch(self, name, out0, out1, quantum, template):
        self.rotors.append(name)
        aliases = {"p": name, "a": out0, "b": out1}
        for g, cap in template["goods"].items():
            aliases[g] = f"{name}/{g}"
            self.market.good(aliases[g], quantum * cap)
        for i, (mass, offers) in enumerate(template["buyers"]):
            mapped = {aliases[g]: value for g, value in offers.items()}
            if "p" in offers:
                # This source row may be chosen later; its mass is simultaneously
                # the input capacity and affects no foreign port's incoming budget.
                self.rotors[-1] = (name, f"{name}/node-{i}", mapped)
            else:
                self.market.buyer(f"{name}/node-{i}", quantum * mass, mapped)
        if isinstance(self.rotors[-1], str):
            raise ArithmeticError("Switch template lacks its source buyer")

    def finish(self):
        for name, count in self.routers:
            # The count local tranche buyers have mass one each. The current
            # incidence may overestimate foreign arrivals, which is harmless.
            anchor = 1 + self.market.incident.get(name, 0)
            self.market.good(name, count + anchor)
            self.market.buyer(f"{name}/padding", anchor, {name: (1, 1)})
        for name, tag, offers in self.rotors:
            cap = 3 + self.market.incident.get(name, 0)
            self.market.good(name, cap)
            self.market.buyer(tag, cap, offers)
        self.market.good(self.discard, 1 + self.market.incident.get(self.discard, 0))


@dataclass
class CompiledComparatorMarket:
    network: ComparatorNetwork
    capacities: Dict[str, F]
    buyers: Buyers
    delivery: tuple  # [wire][0/1] is (buyer, good) for its positive/negative delivered quantity.
    damping_exponent: int
    precision_exponent: int

    def read_quantities(self, allocations):
        return tuple(tuple(_fraction(allocations.get(edge, 0)) for edge in pair)
                     for pair in self.delivery)

    def decode(self, allocations):
        quantities = self.read_quantities(allocations)
        estimate = tuple((p + 1 - r) / 2 for p, r in quantities)
        return self.network.decode_fixed_point(self.network.recover_fixed_point(estimate))


def compile_market(network, damping_exponent=None, precision_exponent=None):
    """Build the complete cyclic M1 table. Raw AND, OR and unary outputs each own a damping chain."""
    if not isinstance(network, ComparatorNetwork):
        raise TypeError("Expected a ComparatorNetwork")
    n = network.size
    m = (32 * n - 1).bit_length() if damping_exponent is None else damping_exponent
    if not isinstance(m, int) or m < 1:
        raise ValueError("The damping exponent must be a positive integer")
    k = m + (128 * n**2 - 1).bit_length() if precision_exponent is None else precision_exponent
    if not isinstance(m, int) or not isinstance(k, int) or min(m, k) < 1:
        raise ValueError("Damping and precision exponents must be positive integers")
    delta, quantum = F(1, 2**m), F(1, 2**k)
    routing = _Routing()
    template = _switch_template(k)
    clamp = {(i, rail): f"wire-{i}-{rail}/clip" for i in range(n) for rail in range(2)}
    destinations = {}

    def stage(i, rail, step=0):
        return f"wire-{i}-{rail}/split-{step}"

    def output(port, r):
        return routing.discard if port is None else stage(port.wire, r ^ port.negated)

    for g, gate in enumerate(network.gates):
        if isinstance(gate, Comparator):
            for rail in range(2):
                receiver = f"compare-{g}-{rail}"
                destinations[gate.left.wire, rail ^ gate.left.negated] = receiver
                destinations[gate.right.wire, rail ^ gate.right.negated] = receiver
                # First tranche is positive OR, negative AND. Second is the
                # complementary AND/OR port; each output quantity has one use.
                ports = ((gate.or_output, gate.and_output) if rail == 0 else
                         (gate.and_output, gate.or_output))
                routing.priority(receiver, tuple(output(p, rail) for p in ports))
        elif isinstance(gate, Unary):
            for rail in range(2):
                destinations[gate.source.wire, rail ^ gate.source.negated] = output(gate.output, rail)
        else:
            rail = 0 if gate.value else 1
            routing.source(f"constant-{g}", 1, output(gate.output, rail))

    delivery = []
    for i in range(n):
        pair = []
        for rail in range(2):
            clip = clamp[i, rail]
            dest = destinations.get((i, rail), routing.discard)
            routing.priority(clip, (dest,))
            pair.append((f"{clip}/forward-1", dest))
            routing.source(f"wire-{i}-{rail}/bias", delta / 2, clip)
            for h in range(m):
                first = clip
                second = stage(i, rail, h + 1) if h + 1 < m else routing.discard
                routing.switch(stage(i, rail, h), first, second, quantum, template)
        delivery.append(tuple(pair))
    routing.finish()
    return CompiledComparatorMarket(network, routing.market.capacities, routing.market.buyers,
                                    tuple(delivery), m, k)
