"""Ordinary affine matching markets for ordered Boolean systems with binary prefix constraints.

Each prefix target i can read its own bit, a designated other prefix parent,
and a common last bit. The last target is unrestricted. `compile_market`
emits a physical acyclic M1 market. `decision_circuit` exposes the same gate
DAG before market sizing, including distinct price ports for local forbidden
assignments. Both objects' `decode(prices)` returns ("root", point) or
("OV2", zero_based_axis, lower_point, upper_point).

The input Circuit and the output capacities and buyers use the same public
representation as opdc_feedback_market. Source and decision gates are built
without evaluating any source target or running a 2-SAT solver in the constructor.
"""

from dataclasses import dataclass
from fractions import Fraction
from typing import Dict, Optional, Sequence, Tuple

if __package__:
    from .opdc_feedback_market import Buyers, Circuit, Rail, _Gates, _MarketBuilder, _bit, _crossing
else:
    from opdc_feedback_market import Buyers, Circuit, Rail, _Gates, _MarketBuilder, _bit, _crossing


@dataclass(frozen=True)
class OutputPorts:
    is_root: Rail
    axes: Tuple[Rail, ...]  # One hot on a crossing; all zero on a root.
    low: Tuple[Rail, ...]
    high: Tuple[Rail, ...]  # On a root both endpoints equal the chosen point.


@dataclass
class DecisionCircuit:
    targets: Tuple[Circuit, ...]
    parents: Tuple[Optional[int], ...]
    ports: OutputPorts
    flags: Dict[Tuple[int, int, int, int], Rail]  # (last bit, row, own bit, parent bit)
    constants: Tuple[Rail, Rail]
    gates: Tuple[Tuple[str, str, str, str], ...]  # (output name, min/max, arg0, arg1)

    def evaluate(self):
        """Evaluate physical price relations directly. This is a test/reference entry point."""
        prices = {self.constants[1][0]: 0, self.constants[1][1]: 1}
        for name, op, x, y in self.gates:
            a, b = prices[x], prices[y]
            prices[name] = min(a, b) if op == "min" else max(a, b)
        return prices

    def decode(self, prices):
        def read(rail):
            zero, one = (_bit(prices[name]) for name in rail)
            if zero + one != 1:
                raise ValueError("Expected complementary Boolean prices at an output port")
            return one

        root = read(self.ports.is_root)
        low = tuple(read(rail) for rail in self.ports.low)
        high = tuple(read(rail) for rail in self.ports.high)
        axes = tuple(i for i, rail in enumerate(self.ports.axes) if read(rail))
        if root:
            if axes or low != high or any(c.evaluate(low) != low[i] for i, c in enumerate(self.targets)):
                raise ValueError("The output ports do not certify a full fixed point")
            return "root", low
        if len(axes) != 1:
            raise ValueError("A crossing needs exactly one selected axis")
        return _crossing(self.targets, axes[0], low, high)


@dataclass
class CompiledBinaryMarket:
    capacities: Dict[str, Fraction]
    buyers: Buyers
    decision: DecisionCircuit

    @property
    def ports(self):
        return self.decision.ports

    @property
    def flags(self):
        return self.decision.flags

    def decode(self, prices):
        return self.decision.decode(prices)


class _Logic:
    """Boolean compiler with wire identities and literal simplification, independent of source values."""

    def __init__(self, physical):
        self.physical = physical
        self.constants = physical.constants
        self.zero, self.one = self.constants
        self.memo = {}

    def boolean(self, op, x, y=None):
        if op == "copy":
            return x
        if op == "not":
            return x[::-1]
        if op == "nand":
            return self.boolean("and", x, y)[::-1]
        if op == "xor":
            if x == y:
                return self.zero
            if x == y[::-1]:
                return self.one
            return self.choose(x, y, y[::-1])
        if op not in ("and", "or"):
            raise ValueError(f"Unsupported logical gate {op!r}")
        neutral, absorbing = ((self.one, self.zero) if op == "and" else (self.zero, self.one))
        if x == y or y == neutral:
            return x
        if x == neutral:
            return y
        if x == absorbing or y == absorbing or x == y[::-1]:
            return absorbing
        if x > y:
            x, y = y, x
        key = (op, x, y)
        if key not in self.memo:
            self.memo[key] = self.physical.boolean(op, x, y)
        return self.memo[key]

    def choose(self, selector, when_zero, when_one):
        """Return when_zero or when_one according to selector."""
        if when_zero == when_one:
            return when_zero
        left = self.boolean("and", selector[::-1], when_zero)
        right = self.boolean("and", selector, when_one)
        return self.boolean("or", left, right)

    def every(self, values):
        result = self.one
        for v in values:
            result = self.boolean("and", result, v)
        return result

    def compile(self, circuit, inputs):
        _, gates = circuit.dependencies()
        values = dict(inputs)
        for i in gates:
            op, *args = circuit.gates[i - circuit.inputs]
            values[i] = (self.constants[int(args[0])] if op == "const" else
                         self.boolean(op, *(values[w] for w in args)))
        return values[circuit.output]


def _source_flags(targets, parents, source):
    """Named buffers separate source cofactors from the generic decision hardware."""
    m = len(parents)
    result = {}
    for b in range(2):
        for i, parent in enumerate(parents):
            for own in range(2):
                # With no distinct parent there are only two local assignments.
                for pv in (range(2) if parent not in (None, i) else (own,)):
                    inputs = {i: source.constants[own], m: source.constants[b]}
                    if parent is not None:
                        inputs[parent] = source.constants[pv]
                    target = source.compile(targets[i], inputs)
                    forbidden = target if own == 0 else target[::-1]
                    flag = tuple(source.gate("max", rail, rail) for rail in forbidden)
                    result[b, i, own, pv] = flag
    return result


class _Prefix:
    def __init__(self, parents, flags, branch, logic):
        self.parents = parents
        self.logic = logic
        self.rows = [[] for _ in parents]
        for (b, i, own, pv), flag in flags.items():
            if b != branch:
                continue
            parent = parents[i]
            x = 2 * i + own
            if parent in (None, i):
                # Forbidding x creates the unit implication x -> not x.
                self.rows[i].append((x, x ^ 1, flag))
            else:
                p = 2 * parent + pv
                self.rows[i].append((x, p ^ 1, flag))
                self.rows[i].append((p, x ^ 1, flag))

    def solve_slice(self, free, fixed):
        """2-SAT feasibility and a witness for a prefix with its later coordinates fixed."""
        L = self.logic
        n = len(self.parents)
        size = 2 * n
        reach = [[L.one if i == j else L.zero for j in range(size)] for i in range(size)]
        for row in self.rows[:free]:
            for u, v, flag in row:
                reach[u][v] = L.boolean("or", reach[u][v], flag)
        for i in range(free, n):
            x, bit = 2 * i, fixed[i]
            reach[x][x + 1] = L.boolean("or", reach[x][x + 1], bit)
            reach[x + 1][x] = L.boolean("or", reach[x + 1][x], bit[::-1])
        # Warshall with reflexive diagonals. Capture this stage's row and column
        # before mutating the matrix to preserve the Boolean reachability recurrence.
        for mid in range(size):
            via_row = tuple(reach[mid])
            via_col = tuple(row[mid] for row in reach)
            for i, before in enumerate(via_col):
                if i == mid or before == L.zero:
                    continue
                for j, after in enumerate(via_row):
                    if i == j or j == mid or after == L.zero:
                        continue
                    reach[i][j] = L.boolean("or", reach[i][j], L.boolean("and", before, after))
        possible = L.every(L.boolean("and", reach[i][i + 1], reach[i + 1][i])[::-1]
                           for i in range(0, size, 2))
        forced = [L.zero] * size
        witness = []
        for i in range(free):
            zero, one = 2 * i, 2 * i + 1
            # Prior forced literals form an implication-closed consistent set.
            # Adding zero is safe iff its closure does not force one and one
            # was not already forced. Contrapositive reachability supplies the
            # reverse paths in either possible conflict.
            bit = L.boolean("or", forced[one], reach[zero][one])
            witness.append(bit)
            for j in range(2 * (i + 1), size):
                extra = L.choose(bit, reach[zero][j], reach[one][j])
                forced[j] = L.boolean("or", forced[j], extra)
        return possible, tuple(witness) + tuple(fixed[free:])

    def certificate(self):
        L = self.logic
        n = len(self.parents)
        fixed = [L.zero] * n
        feasible, full = self.solve_slice(n, fixed)
        low, high = full, full
        active = feasible[::-1]
        axes = [L.zero] * n
        for i in reversed(range(n)):
            fixed[i] = L.zero
            ok0, x0 = self.solve_slice(i, fixed)
            fixed[i] = L.one
            ok1, x1 = self.solve_slice(i, fixed)
            both = L.boolean("and", ok0, ok1)
            choose_here = L.boolean("and", active, both)
            axes[i] = choose_here
            low = tuple(L.choose(choose_here, old, new) for old, new in zip(low, x0))
            high = tuple(L.choose(choose_here, old, new) for old, new in zip(high, x1))
            active = L.boolean("and", active, both[::-1])
            # Choose child zero if it is infeasible, otherwise choose child one.
            # Once a certificate was found the residual iterations are masked.
            fixed[i] = ok0
        return feasible, tuple(axes), low, high


def decision_circuit(targets: Sequence[Circuit], parents: Sequence[Optional[int]]) -> DecisionCircuit:
    """Compile a circuit with source-cofactor outputs, two 2-SAT searches, and final selection."""
    targets, parents = tuple(targets), tuple(parents)
    k = len(targets)
    m = k - 1
    if not k or len(parents) != m or any(not isinstance(c, Circuit) or c.inputs != k for c in targets):
        raise ValueError("Expected k>=1 circuits on k inputs and k-1 parent entries")
    for i, p in enumerate(parents):
        if p is not None and (not isinstance(p, int) or not 0 <= p < m):
            raise ValueError(f"Invalid prefix parent for row {i}")
        if any(w not in (i, p, m) for w in targets[i].dependencies()[0]):
            raise ValueError(f"Target {i} uses more than its own bit, designated parent, and last bit")

    constants = (("binary/one", "binary/zero"), ("binary/zero", "binary/one"))
    source = _Gates("binary/cofactors", constants)
    flags = _source_flags(targets, parents, source)
    physical = _Gates("binary/decision", constants)
    L = _Logic(physical)
    branches = [_Prefix(parents, flags, b, L).certificate() for b in (0, 1)]
    ok0, ax0, lo0, hi0 = branches[0]
    ok1, ax1, lo1, hi1 = branches[1]
    x0, x1 = lo0 + (L.zero,), lo1 + (L.one,)
    y0 = L.compile(targets[m], dict(enumerate(x0)))
    y1 = L.compile(targets[m], dict(enumerate(x1)))
    # On two feasible children prefer a fixed lower point, then a fixed upper
    # point. If neither is fixed, the two child roots witness the final crossing.
    rooted = L.boolean("and", L.boolean("and", ok0, ok1), L.boolean("or", y0[::-1], y1))
    last_cross = L.boolean("and", L.boolean("and", ok0, ok1), L.boolean("and", y0, y1[::-1]))
    good_low = tuple(L.choose(L.boolean("and", y0, y1), a, b) for a, b in zip(x0, x1))
    good_high = tuple(L.choose(y0, a, b) for a, b in zip(x0, x1))

    def select_outer(low_or_high, child0, child1):
        return tuple(L.choose(ok0, first, L.choose(ok1, second, valid))
                     for valid, first, second in zip(low_or_high, child0 + (L.zero,), child1 + (L.one,)))

    low = select_outer(good_low, lo0, lo1)
    high = select_outer(good_high, hi0, hi1)
    axes = tuple(L.choose(ok0, a, L.boolean("and", ok1[::-1], b)) for a, b in zip(ax0, ax1))
    ports = OutputPorts(rooted, axes + (last_cross,), low, high)
    return DecisionCircuit(targets, parents, ports, flags, constants, tuple(source.gates + physical.gates))


def compile_market(targets: Sequence[Circuit], parents: Sequence[Optional[int]]) -> CompiledBinaryMarket:
    """Instantiate every Boolean gate as a physical min/max price gate in one ordinary market."""
    decision = decision_circuit(targets, parents)
    market = _MarketBuilder()
    bank = _Gates("binary/full", decision.constants)
    bank.gates = decision.gates
    bank.install(market)
    for value, name in enumerate(decision.constants[1]):
        market.source(name, value)
    return CompiledBinaryMarket(market.capacities, market.buyers, decision)
