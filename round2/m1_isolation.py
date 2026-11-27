"""Deterministic isolation of a rational ordinary affine matching market.

Goods map identifiers to capacities. Buyers map identifiers to (mass, offers),
where offers map goods to rational (intercept, strictly positive slope) pairs.
The order of the input dictionaries breaks ties between otherwise unprioritized
offer serials. Every choice of serials has the same certified guarantees.
"""

from dataclasses import dataclass
from fractions import Fraction
from math import lcm


@dataclass(frozen=True)
class Isolation:
    goods: dict
    buyers: dict
    delta: Fraction


def isolate_market(goods, buyers, *, first_offers=()):
    """Return a uniquely solvable market with an exactly repairable pattern."""
    capacities = {j: Fraction(cap) for j, cap in goods.items()}
    if any(cap <= 0 for cap in capacities.values()):
        raise ValueError("Good capacities must be positive")
    rows = {}
    data = list(capacities.values())
    edges = []
    for i, (mass, offers) in buyers.items():
        mass = Fraction(mass)
        if mass <= 0:
            raise ValueError("Buyer masses must be positive")
        data.append(mass)
        row = {}
        for j, (intercept, slope) in offers.items():
            intercept, slope = Fraction(intercept), Fraction(slope)
            if j not in capacities or slope <= 0:
                raise ValueError("Each listed offer needs an existing good and positive slope")
            row[j] = (intercept, slope)
            edges.append((i, j))
            data.extend((intercept, slope))
        rows[i] = (mass, row)

    first = list(first_offers)
    first_set = set(first)
    if len(first_set) != len(first) or not first_set.issubset(set(edges)):
        raise ValueError("Prioritized offers must be distinct listed buyer-good pairs")
    serial_order = first + [edge for edge in edges if edge not in first_set]

    # A common denominator suffices for every subset margin and every
    # support-pattern LP. Include the integer coefficients of the terminal
    # load tests from the ARRIVAL reduction when bounding their determinants.
    denominator = lcm(*(value.denominator for value in data))
    height = max([5, denominator] + [abs(int(value * denominator)) for value in data])
    dimension = len(rows) + len(capacities) + len(edges) + 1
    determinant_bound = (dimension * height) ** (dimension + 2)
    inverse_bound = max(8, 2 * (len(rows) + 1) * denominator,
                        2 * denominator * determinant_bound,
                        4 * dimension * height * determinant_bound)
    power = inverse_bound.bit_length()
    delta = Fraction(1, 1 << power)
    perturbed = {i: (mass + delta, row.copy()) for i, (mass, row) in rows.items()}
    for serial, (i, j) in enumerate(serial_order, start=1):
        intercept, slope = rows[i][1][j]
        perturbed[i][1][j] = (intercept + Fraction(1, 1 << (power * serial)), slope)
    return Isolation(capacities, perturbed, delta)


def decode_equilibrium(goods, buyers, prices, flows, values):
    """Recover an original equilibrium from the isolated solution's pattern.

    The feasibility problem is a single rational LP. The caller supplies the
    isolated equilibrium's dictionaries of prices, all listed flows and buyer
    utilities. Zero-valued active constraints can remain active after repair.
    """
    import z3
    from wardrop.check_wardrop import add, exact, q

    solver = z3.SolverFor("QF_LRA")
    restored_prices = {j: z3.FreshReal("price") for j in goods}
    restored_values = {i: z3.FreshReal("utility") for i in buyers}
    restored_flows = {}
    columns = {j: [] for j in goods}
    for i, (mass, offers) in buyers.items():
        best = restored_values[i]
        solver.add(best >= 0)
        row = []
        for j, (intercept, slope) in offers.items():
            flow = restored_flows[i, j] = z3.FreshReal("flow")
            payoff = q(intercept) - q(slope) * restored_prices[j]
            solver.add(flow >= 0, best >= payoff)
            solver.add(best == payoff if flows[i, j] > 0 else flow == 0)
            row.append(flow)
            columns[j].append(flow)
        used = add(*row)
        solver.add(used <= q(mass))
        solver.add(used == q(mass) if values[i] > 0 else best == 0)
    for j, cap in goods.items():
        price = restored_prices[j]
        load = add(*columns[j])
        solver.add(price >= 0, load <= q(cap))
        solver.add(load == q(cap) if prices[j] > 0 else price == 0)
    result = solver.check()
    if result == z3.unsat:
        raise ValueError("The supplied market pattern has no equilibrium in the original market")
    if result != z3.sat:
        raise RuntimeError(f"Linear feasibility returned {result}: {solver.reason_unknown()}")
    model = solver.model()
    return tuple({key: exact(model, value) for key, value in group.items()}
                 for group in (restored_prices, restored_flows, restored_values))
