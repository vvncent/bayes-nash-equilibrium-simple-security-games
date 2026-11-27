"""Affine matching markets for ordered stationarity of bounded treewidth.

Each row i reads the distinct state variables in readers[i]; table[i] lists
F_i in lexicographic order of those input bits, with 0 preceding 1.
The supplied rooted tree decomposition must contain {i} U readers[i] in
some bag. Bag zero is the root. Each other parent precedes its child.
"""

from dataclasses import dataclass
from fractions import Fraction
from itertools import product

from opdc_boundary_feedback import _Logic
from opdc_feedback_market import _MarketBuilder


def _lookup(table, bits):
    index = 0
    for bit in bits:
        index = 2 * index + bit
    return table[index]


@dataclass(frozen=True)
class Instance:
    readers: tuple
    tables: tuple
    bags: tuple
    parents: tuple

    def layout(self):
        n = len(self.readers)
        if n < 1 or len(self.tables) != n:
            raise ValueError("Supply one target table per variable")
        for reads, table in zip(self.readers, self.tables):
            if (len(set(reads)) != len(reads) or any(v not in range(n) for v in reads)
                    or len(table) != 2 ** len(reads) or any(b not in (0, 1) for b in table)):
                raise ValueError("Invalid target scope or truth table")
        if not self.bags or len(self.bags) != len(self.parents) or self.parents[0] != -1:
            raise ValueError("Supply one rooted bag tree")
        children = [[] for _ in self.bags]
        for b, bag in enumerate(self.bags):
            if len(set(bag)) != len(bag) or any(v not in range(n) for v in bag):
                raise ValueError("Invalid bag variable")
            if b:
                if not 0 <= self.parents[b] < b:
                    raise ValueError("Bag parents must precede their children")
                children[self.parents[b]].append(b)
        occurrences = [{i for i, bag in enumerate(self.bags) if v in bag} for v in range(n)]
        for part in occurrences:
            if sum(self.parents[b] not in part for b in part) != 1:
                raise ValueError("Bags containing each variable must form a nonempty subtree")
        assigned = [[] for _ in self.bags]
        for i, readers in enumerate(self.readers):
            scope = {i, *readers}
            home = next((b for b, bag in enumerate(self.bags) if scope.issubset(bag)), None)
            if home is None:
                raise ValueError("A target and all its readers must share a bag")
            assigned[home].append(i)
        return children, assigned, tuple(min(part) for part in occurrences)

    def targets(self, point):
        return tuple(_lookup(table, (point[v] for v in reads))
                     for reads, table in zip(self.readers, self.tables))


class _Circuit(_Logic):
    def __init__(self):
        constants = (("source/one", "source/zero"), ("source/zero", "source/one"))
        super().__init__("width", constants)
        self.cache = {}

    def gate(self, op, left, right):
        key = (op, *sorted((left, right)))
        if key not in self.cache:
            self.cache[key] = super().gate(op, left, right)
        return self.cache[key]

    def fold(self, op, terms):
        value = self.constants[int(op == "and")]
        for term in terms:
            value = self.boolean(op, value, term)
        return value

    def mux(self, test, yes, no):
        if yes == no:
            return yes
        return self.boolean("or", self.boolean("and", test, yes),
                            self.boolean("and", test[::-1], no))


class _Messages:
    def __init__(self, source, logic, pins):
        self.source = source
        self.logic = logic
        self.pins = pins
        self.children, self.assigned, self.home = source.layout()
        self.positions = [{v: i for i, v in enumerate(bag)} for bag in source.bags]
        self.states = [tuple(product((0, 1), repeat=len(bag))) for bag in source.bags]
        self.separators = [()] + [
            tuple(v for v in source.bags[b] if v in self.positions[parent])
            for b, parent in enumerate(source.parents) if b
        ]

    def key(self, bag, state, separator):
        return tuple(state[self.positions[bag][v]] for v in separator)

    def slice(self, r, suffix):
        """One joint, symbolic bottom-up feasibility and top-down traceback."""
        l = self.logic
        ok, messages = {}, {}
        for b in reversed(range(len(self.source.bags))):
            groups = {}
            for a in self.states[b]:
                terms = []
                for i in self.assigned[b]:
                    bit = a[self.positions[b][i]]
                    if i < r:
                        index = self.key(b, a, self.source.readers[i])
                        port = _lookup(self.pins[i], index)
                        terms.append(port if bit else port[::-1])
                    else:
                        port = suffix[i - r]
                        terms.append(port if bit else port[::-1])
                for child in self.children[b]:
                    key = self.key(b, a, self.separators[child])
                    terms.append(messages[child][key])
                ok[b, a] = l.fold("and", terms)
                key = self.key(b, a, self.separators[b])
                groups.setdefault(key, []).append(ok[b, a])
            messages[b] = {key: l.fold("or", terms) for key, terms in groups.items()}

        values = [None] * len(self.source.readers)
        for b, bag in enumerate(self.source.bags):
            previous = l.constants[0]
            selected = []
            for a in self.states[b]:
                tests = [ok[b, a]]
                for v in self.separators[b]:
                    port = values[v]
                    tests.append(port if a[self.positions[b][v]] else port[::-1])
                available = l.fold("and", tests)
                selected.append(l.boolean("and", available, previous[::-1]))
                previous = l.boolean("or", previous, available)
            for j, v in enumerate(bag):
                if self.home[v] == b:
                    values[v] = l.fold("or", (s for a, s in zip(self.states[b], selected) if a[j]))
        return messages[0][()], tuple(values)


@dataclass
class Compiled:
    source: Instance
    capacities: dict
    buyers: dict
    success: tuple
    root: tuple
    crossings: tuple
    bits: tuple
    quarter_ports: tuple
    input_pins: dict
    gates: tuple

    def decode(self, prices):
        def read(pair):
            values = tuple(prices[g] for g in pair)
            if values not in ((1, 0), (0, 1)):
                raise ValueError("Expected an integral complementary price pair")
            return int(values[1])

        if read(self.success):
            return "root", tuple(read(x) for x in self.root)
        for j, flag, low, high in self.crossings:
            if read(flag):
                return ("OV2", j, tuple(map(read, low)), tuple(map(read, high)))
        raise ValueError("No certificate selector is marked")

    def circuit_prices(self):
        """Evaluate the open circuit for testing independently of market clearing."""
        prices = {"source/one": 1, "source/zero": 0, **self.input_pins}
        for out, op, a, b in self.gates:
            prices[out] = (min if op == "min" else max)(prices[a], prices[b])
        for pair, ports in zip(self.bits, self.quarter_ports):
            for rail, port in zip(pair, ports):
                prices[port] = Fraction(1, 4) + Fraction(prices[rail], 2)
        return prices


def compile_market(source):
    n = len(source.readers)
    l = _Circuit()
    pins = {}
    tables = []
    for i, table in enumerate(source.tables):
        ports = []
        for j, value in enumerate(table):
            pair = (f"table/{i}/{j}/no", f"table/{i}/{j}/yes")
            pins[pair[0]], pins[pair[1]] = 1 - value, value
            ports.append(pair)
        tables.append(tuple(ports))
    dp = _Messages(source, l, tables)
    full, root = dp.slice(n, ())
    active = full[::-1]
    suffix, crossings = (), []
    for j in reversed(range(n)):
        low_ok, low = dp.slice(j, (l.constants[0],) + suffix)
        high_ok, high = dp.slice(j, (l.constants[1],) + suffix)
        both = l.boolean("and", low_ok, high_ok)
        flag = l.boolean("and", active, both)
        crossings.append((j, flag, low, high))
        active = l.boolean("and", active, both[::-1])
        suffix = (low_ok,) + suffix

    def combine(which):
        return tuple(l.fold("or", [l.boolean("and", full, root[v])] + [
            l.boolean("and", row[1], row[which][v]) for row in crossings]) for v in range(n))

    # Fixed-format accepted witness: root marker, one crossing flag per
    # axis in descending order, both endpoints, and the forced success bit.
    bits = (full,) + tuple(row[1] for row in crossings) + combine(2) + combine(3) + (l.constants[1],)
    builder = _MarketBuilder()
    quarter_ports = []
    for i, pair in enumerate(bits):
        out = (f"quarter/{i}/no", f"quarter/{i}/yes")
        quarter_ports.append(out)
        for rail, name in zip(pair, out):
            builder.good(name, 1)
            builder.buyer(name + "/tie", 2, {name: (Fraction(5, 4), 1),
                                              rail: (1, Fraction(1, 2))})
    l.install(builder)
    for good, value in {**pins, "source/zero": 0, "source/one": 1}.items():
        builder.source(good, value)
    return Compiled(source, builder.capacities, builder.buyers, full, root,
                    tuple(crossings), bits, tuple(quarter_ports), pins, tuple(l.gates))
