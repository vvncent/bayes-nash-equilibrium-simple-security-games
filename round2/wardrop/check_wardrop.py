"""Exact small-instance checks for the multiclass Wardrop equivalence.

Requires Python 3 and z3-solver. All numeric model operations use rational
linear real arithmetic. This file works independently of the manuscript code.
"""

from decimal import Decimal
from fractions import Fraction as F
from math import lcm
import z3


def q(value):
    r = F(value)
    # Exact integer-to-Decimal conversion also supports the large integers
    # produced by isolation, without changing Python's process-wide limits.
    return z3.RealVal(f"{Decimal(r.numerator)}/{Decimal(r.denominator)}")


def exact(model, expr):
    val = model.eval(expr, model_completion=True)
    return F(int(Decimal(val.numerator().as_string())), int(Decimal(val.denominator().as_string())))


def add(*items):
    return z3.Sum(*items) if items else q(0)


def expect(solver, status, message):
    result = solver.check()
    if result != status:
        witness = solver.model() if result == z3.sat else solver.reason_unknown()
        raise AssertionError(f"{message}: expected {status}, found {result}: {witness}")


def rule_out(solver, claim, message):
    solver.push()
    solver.add(claim)
    expect(solver, z3.unsat, message)
    solver.pop()


def market(solver, tag, goods, buyers, external=None):
    external = external or {}
    prices = {j: z3.Real(f"{tag}_p_{j}") for j in goods}
    incoming = {j: [external[j]] if j in external else [] for j in goods}
    flow, values = {}, {}
    for i, (mass, opts) in buyers.items():
        values[i] = z3.Real(f"{tag}_v_{i}")
        solver.add(values[i] >= 0)
        row = []
        for j, (a, b) in opts.items():
            f = flow[i, j] = z3.Real(f"{tag}_f_{i}_{j}")
            payoff = q(a) - q(b) * prices[j]
            solver.add(f >= 0, values[i] >= payoff, z3.Or(f == 0, values[i] == payoff))
            row.append(f)
            incoming[j].append(f)
        used = add(*row)
        solver.add(used <= q(mass), z3.Or(used == q(mass), values[i] == 0))
    for j, cap in goods.items():
        load = add(*incoming[j])
        solver.add(prices[j] >= 0, load <= q(cap), z3.Or(prices[j] == 0, load == q(cap)))
    return prices, flow, values


def traffic(solver, tag, demands, costs, slack=0, support=None):
    """An explicit Wardrop oracle or one of the fixed-support recovery LPs."""
    links = sorted({j for _, j in costs})
    load = {j: z3.Real(f"{tag}_X_{j}") for j in links}
    flow = {ij: z3.Real(f"{tag}_f_{ij[0]}_{ij[1]}") for ij in costs}
    for i, mass in demands.items():
        solver.add(add(*(f for (h, _), f in flow.items() if h == i)) == q(mass))
    for j in links:
        solver.add(load[j] == add(*(f for (_, k), f in flow.items() if j == k)))
    actual = {ij: q(a) + q(b) * load[ij[1]] for ij, (a, b) in costs.items()}
    for ij, f in flow.items():
        solver.add(f >= 0)
        if support is not None and ij not in support:
            solver.add(f == 0)
            continue
        for hk, other in actual.items():
            if hk[0] == ij[0]:
                comparison = actual[ij] <= other + q(slack)
                solver.add(comparison if support is not None else z3.Or(f == 0, comparison))
    return flow, load


def support_of(model, variables):
    return {ij for ij, variable in variables.items() if exact(model, variable) > 0}


def check_wardrop_quantities(demands, costs, flows):
    loads = {j: sum(x for (_, k), x in flows.items() if k == j) for _, j in costs}
    for i, h in demands.items():
        assert sum(x for (g, _), x in flows.items() if i == g) == h
        values = {j: a + b * loads[j] for (g, j), (a, b) in costs.items() if g == i}
        assert all(x >= 0 and (not x or values[j] == min(values.values()))
                   for (g, j), x in flows.items() if g == i)
    return loads


def network(prefix, k, delta):
    def s(h):
        return f"{prefix}_s{h}"

    def t(h):
        return f"{prefix}_t{h}"

    arcs = [(s(0), t(0), delta, 0)]
    for h in range(1, k + 1):
        cap, fee = delta * 2 ** (h - 1), F(2**h - 1, 2)
        arcs.extend([(s(h), s(h - 1), cap, 0), (t(h - 1), t(h), cap, 0),
                     (s(h), t(h - 1), cap, fee), (s(h - 1), t(h), cap, fee)])
    return arcs, s(k), t(k)


def price_device(prefix, k, delta, total):
    arcs, source, sink = network(prefix, k, delta)
    K, cap = delta * 2**k, total + delta + 1
    assert K > total + delta
    big = 4 + sum(fee + (v == sink) for u, v, c, fee in arcs)
    price, discard = prefix + "_p", prefix + "_discard"
    options, masses = {}, {}
    goods = {price: cap, discard: K + 1}
    for e, (u, v, c, fee) in enumerate(arcs):
        name = f"{prefix}_e{e}"
        goods[name] = c
        options.setdefault(u, {})[name] = (big - fee, 1)
        options.setdefault(v, {})[name] = (big + (v == sink), 1)
        masses[v] = masses.get(v, 0) + c
    masses[source] = cap
    options[source][price] = (big + 1, 1)
    options[sink][discard] = (big, 1)
    buyers = {node: (masses[node], choices) for node, choices in options.items()}
    preload = prefix + "_preload"
    buyers[preload] = (delta, {price: (big + 2, 1)})
    return goods, buyers, price, discard, preload


def check_price_graph(k):
    delta = F(1, 2)
    total = delta * (2**k - 2)
    goods, buyers, port, discard, preload = price_device("gate", k, delta, total)
    solver = z3.SolverFor("QF_LRA")
    x = z3.Real("external_X")
    solver.add(x >= 0, x <= q(total))
    prices, flows, _ = market(solver, "device", goods, buyers, {port: x})
    estimate = q(delta) * (prices[port] - 2)
    expect(solver, z3.sat, "expanded price device is feasible")
    rule_out(solver, z3.Or(estimate < x, estimate > x + q(delta),
                           prices[discard] != 0, flows[preload, port] != q(delta)),
             "uniform price/preload law over the whole range")
    points = 0
    for index in range(2**k - 1):
        for endpoint in (index, index + 1):
            solver.push()
            solver.add(x == q(delta * index), prices[port] == 2 + endpoint)
            expect(solver, z3.sat, "endpoint of the full price interval at a breakpoint")
            solver.pop()
            points += 1
        if index < 2**k - 2:
            solver.push()
            solver.add(x > q(delta * index), x < q(delta * (index + 1)))
            expect(solver, z3.sat, "fractional load interval is nonempty")
            rule_out(solver, prices[port] != 3 + index, "unique correct price off the grid")
            solver.pop()
            points += 1
    return points


def two_class_market(delta, k):
    demands = {"A": F(1, 4), "B": F(3, 4)}
    costs = {("A", "L"): (F(0), F(1)), ("A", "R"): (F(2), F(1)),
             ("B", "L"): (F(0), F(2)), ("B", "R"): (F(1, 4), F(1))}
    total = sum(demands.values())
    goods, buyers, ports = {}, {}, {}
    for j in ("L", "R"):
        gs, bs, ports[j], _, _ = price_device(j, k, delta, total)
        goods.update(gs)
        buyers.update(bs)
    for i, mass in demands.items():
        R = 1 + max(abs(a) + b * (total + 1) for (h, _), (a, b) in costs.items() if h == i)
        buys = {ports[j]: (R - a + 2 * b * delta, b * delta)
                for (h, j), (a, b) in costs.items() if h == i}
        buyers[i] = (mass, buys)
    return goods, buyers, ports, demands, costs


def check_closed_traffic_market():
    goods, buyers, ports, demands, costs = two_class_market(F(1, 8), 4)
    solver = z3.SolverFor("QF_LRA")
    _, full, _ = market(solver, "closed", goods, buyers)
    flows = {ij: full[ij[0], ports[ij[1]]] for ij in costs}
    expect(solver, z3.sat, "sealed two-link traffic market")
    # The coarse device can choose a flow different from the exact Wardrop
    # flow. Verify one concrete such witness and then repair its support.
    solver.push()
    solver.add(flows["B", "L"] == q(F(1, 8)))
    expect(solver, z3.sat, "genuinely inexact coarse-price witness")
    mixed = support_of(solver.model(), flows)
    solver.pop()
    expected = {("A", "L"), ("B", "L"), ("B", "R")}
    assert mixed == expected
    # The theorem uses a much finer determinant threshold; the stronger
    # universal support statement is checked separately for this example.
    wrong = [flows[ij] == 0 if ij in expected else flows[ij] > 0 for ij in costs]
    rule_out(solver, z3.Or(*wrong), "all market solutions have a repairable support")
    repair = z3.SolverFor("QF_LRA")
    exact_f, _ = traffic(repair, "recovered", demands, costs, support=mixed)
    expect(repair, z3.sat, "unperturbed traffic support LP")
    recovered = {ij: exact(repair.model(), value) for ij, value in exact_f.items()}
    loads = check_wardrop_quantities(demands, costs, recovered)
    assert loads == {"L": F(5, 12), "R": F(7, 12)}
    return len(goods), len(buyers), loads


def traffic_threshold(demands, costs):
    """Compute the note's determinant threshold with explicit traffic rows."""
    links = {j for _, j in costs}
    variable_count = len(costs) + len(links) + 1
    H = 1

    def row(entries):
        nonlocal H
        entries = [F(a) for a in entries]
        multiplier = lcm(*(a.denominator for a in entries))
        H = max(H, *(abs(int(a * multiplier)) for a in entries))

    for mass in demands.values():
        row([1, mass])
    for (i, j), (a, b) in costs.items():
        for (h, t), (c, d) in costs.items():
            if h == i and t != j:
                row([b, -d, -1, c - a])
    return (variable_count * H) ** variable_count


def min_cost_flow(k, delta, load):
    """The optimal flow of G_k in its base-arc-then-layers ordering."""
    if not k:
        assert 0 <= load <= delta
        return [load]
    cap = delta * 2 ** (k - 1)
    middle = min(load, 2 * cap - load)
    direct, crossing = min(load, cap), max(0, load - cap)
    return min_cost_flow(k - 1, delta, middle) + [direct, direct, crossing, crossing]


def check_full_precision_witness():
    _, _, _, demands, costs = two_class_market(F(1, 8), 4)
    Q = traffic_threshold(demands, costs)
    total, max_slope = sum(demands.values()), max(b for _, b in costs.values())
    N = 1
    while 2 * max_slope * Q >= N:
        N *= 2
    delta = F(1, N)
    k = (int(total * N) + 1).bit_length()
    goods, buyers, ports, _, _ = two_class_market(delta, k)
    solver = z3.SolverFor("QF_LRA")
    prices, flows, _ = market(solver, "fine", goods, buyers)
    left_units = (5 * N) // 12
    units = {"L": left_units, "R": N - left_units}
    mu = {"L": F(N // 4 + units["R"], 2), "R": F(units["R"])}
    wallet = {"A": {"L": demands["A"], "R": F(0)},
              "B": {"L": F(left_units, N) - demands["A"], "R": F(units["R"], N)}}
    for name, choices in wallet.items():
        for j, amount in choices.items():
            solver.add(flows[name, ports[j]] == q(amount))
    for j, u in units.items():
        assert u <= mu[j] <= u + 1
        r = (u + 1) * delta
        arcs, source, sink = network(j, k, delta)
        forward = min_cost_flow(k, delta, r)
        assert len(forward) == len(arcs)
        for e, ((tail, head, cap, _), value) in enumerate(zip(arcs, forward)):
            good = f"{j}_e{e}"
            solver.add(flows[tail, good] == q(value), flows[head, good] == q(cap - value))
        solver.add(prices[ports[j]] == q(2 + mu[j]),
                   flows[source, ports[j]] == q(total + delta + 1 - r),
                   flows[sink, j + "_discard"] == q(r),
                   flows[j + "_preload", ports[j]] == q(delta))
    expect(solver, z3.sat, "full determinant-precision expanded market has an exact equilibrium")
    physical = {ij: flows[ij[0], ports[ij[1]]] for ij in costs}
    active = support_of(solver.model(), physical)
    assert F(left_units, N) != F(5, 12)
    repair = z3.SolverFor("QF_LRA")
    wf, _ = traffic(repair, "fine_exact", demands, costs, support=active)
    expect(repair, z3.sat, "LP recovers the exact mixed traffic equilibrium")
    final = {ij: exact(repair.model(), flow) for ij, flow in wf.items()}
    assert check_wardrop_quantities(demands, costs, final)["L"] == F(5, 12)
    return Q, N.bit_length() - 1, k, len(goods), len(buyers)


def check_forward():
    originals = {"A": F(1), "B": F(1), "U": F(1, 4)}
    caps = {"H": F(1), "L": F(2)}
    offers = {("A", "H"): (F(1), F(2)), ("B", "H"): (F(2), F(1)),
              ("U", "L"): (F(2), F(1))}
    demands = dict(originals)
    demands.update({f"fill_{j}": c for j, c in caps.items()})
    tau, zeta = F(1, 8), F(1, 2**40)
    costs = {ij: (-a - b * caps[ij[1]] / tau, b / tau) for ij, (a, b) in offers.items()}
    for j, c in caps.items():
        costs[f"fill_{j}", j] = (-c / tau, 1 / tau)
    for i in demands:
        costs[i, "out"] = (F(0), F(0))
    total = sum(demands.values())
    strict = {}
    for i in demands:
        offset = max([F(0)] + [-a for (h, _), (a, _) in costs.items() if h == i])
        dear = 1 + max(a + offset + (b + zeta) * total
                       for (h, _), (a, b) in costs.items() if h == i)
        for j in [*caps, "out"]:
            if (i, j) in costs:
                a, b = costs[i, j]
                strict[i, j] = (a + offset, b + zeta)
            else:
                strict[i, j] = (dear, F(1))
    assert all(a >= 0 and b > 0 for a, b in strict.values())
    # Check every realizable support at the strict oracle. Then solve a
    # no-disjunction LP with the retained support at zero perturbation.
    oracle = z3.SolverFor("QF_LRA")
    f, _ = traffic(oracle, "strict", demands, strict)
    count = 0
    while oracle.check() == z3.sat:
        active = support_of(oracle.model(), f)
        assert active <= set(costs)
        rec = z3.SolverFor("QF_LRA")
        raw_f, raw_x = traffic(rec, f"weak{count}", demands, costs, support=active)
        expect(rec, z3.sat, "recover weak affine routing from strict costs")
        wf = {ij: exact(rec.model(), x) for ij, x in raw_f.items()}
        loads = check_wardrop_quantities(demands, costs, wf)
        assert loads == {j: exact(rec.model(), l) for j, l in raw_x.items()}
        P = {j: (loads[j] - c) / tau for j, c in caps.items()}
        assert P == {"H": F(1, 2), "L": F(0)}
        assert wf["A", "H"] == F(1, 16) and wf["B", "H"] == 1
        assert wf["fill_H", "H"] == 0 and wf["fill_L", "L"] == F(7, 4)
        # Zero prices/values are fixed by their pattern. Positive labels force
        # their margins to fill. Best replies on every retained edge stay tight.
        m = z3.SolverFor("QF_LRA")
        buyers = {i: (mass, {j: opt for (h, j), opt in offers.items() if h == i})
                  for i, mass in originals.items()}
        prices, mf, mv = market(m, f"repaired_market{count}", caps, buyers)
        for ij in offers:
            a, b = offers[ij]
            if wf.get(ij, F(0)) > 0:
                m.add(mv[ij[0]] == q(a) - q(b) * prices[ij[1]])
            else:
                m.add(mf[ij] == 0)
        for j in caps:
            if P[j] == 0:
                m.add(prices[j] == 0)
            else:
                m.add(add(*(x for (_, h), x in mf.items() if h == j)) == q(caps[j]))
        for i, mass in originals.items():
            best = max([F(0)] + [a - b * P[j] for (h, j), (a, b) in offers.items() if h == i])
            if best == 0:
                m.add(mv[i] == 0)
            else:
                m.add(add(*(x for (h, _), x in mf.items() if h == i)) == q(mass))
        expect(m, z3.sat, "recover original market through its pattern")
        assert exact(m.model(), prices["H"]) == F(1, 2)
        assert exact(m.model(), mf["A", "H"]) == 0
        count += 1
        oracle.add(z3.Or(*(var == 0 if ij in active else var > 0 for ij, var in f.items())))
    assert count > 0
    return count


if __name__ == "__main__":
    checks = sum(check_price_graph(k) for k in (2, 3))
    print(f"Expanded price law at two depths, symbolic real X; {checks} interval/endpoint checks.")
    ng, nb, X = check_closed_traffic_market()
    print(f"Closed two-link market ({ng} goods, {nb} buyers); all supports recover loads {X}.")
    Q, d, k, ng, nb = check_full_precision_witness()
    print(f"Full-precision mixed witness at Q={Q}, delta=2^-{d}, k={k}, "
          f"{ng} goods and {nb} buyers; its coarse allocation repairs exactly.")
    count = check_forward()
    print(f"All {count} realizable supports of a strictly increasing, complete traffic oracle "
          "recover both the intermediate traffic and the exact original market.")
