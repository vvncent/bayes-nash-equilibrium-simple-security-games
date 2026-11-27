"""Check the physical Cayley fold and a closed two-coordinate matching market.

The fold proof is symbolic. The closed example expands every alternating
switch into the manuscript's buyers and goods at a deliberately coarse quantum.
Run with the repository's z3-solver environment.
"""

from fractions import Fraction as F
from pathlib import Path
import sys

import z3

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "code/lib"))
from referee_lib import Q, market_eq
from twocopy_gadget import gadget


def check_status(label, solver, expected):
    status = solver.check()
    if status != expected:
        detail = solver.model() if status == z3.sat else solver.reason_unknown()
        raise AssertionError(f"{label}: expected {expected}, got {status}: {detail}")
    print(f"{label}: {status}", flush=True)


def check_fold():
    goods = {"plus": 5, "minus": 5, "low": F(11, 2)}
    buyers = []
    for side in ("plus", "minus", "low"):
        # The second half of each state stream goes above the absolute-value
        # threshold. On the lower pool the second tranche is the retained one.
        ports = ("low", "upper_out") if side != "low" else ("discard", "lower_out")
        for index, port in enumerate(ports, 1):
            buyers.append((f"{side}_{index}", F(1, 2), {
                side: (12, 12), port: (12 - 2 * index, 1)
            }))
        buyers.append((f"{side}_anchor", goods[side] - 1, {side: (1, 1)}))

    solver = z3.SolverFor("QF_LRA")
    # The two output ports and the discard have externally specified prices.
    prices = {name: z3.Real(name) for name in [*goods, "upper_out", "lower_out", "discard"]}
    for name, price in prices.items():
        solver.add(price >= 0)
        if name not in goods:
            solver.add(price <= 1)
    positive, negative = z3.Reals("fold_input_p fold_input_n")
    solver.add(positive >= 0, positive <= 2, negative >= 0, negative <= 2)
    incoming = {name: [] for name in prices}
    incoming["plus"].append(positive)
    incoming["minus"].append(negative)
    for name, mass, offers in buyers:
        value = z3.Real(f"value_{name}")
        solver.add(value >= 0)
        row = []
        for good, (intercept, slope) in offers.items():
            quantity = z3.Real(f"allocation_{name}_{good}")
            payoff = Q(intercept) - Q(slope) * prices[good]
            solver.add(quantity >= 0, value >= payoff, z3.Or(quantity == 0, value == payoff))
            incoming[good].append(quantity)
            row.append(quantity)
        total = z3.Sum(row)
        solver.add(total <= Q(mass), z3.Or(total == Q(mass), value == 0))
    for good, capacity in goods.items():
        total = z3.Sum(incoming[good])
        solver.add(total <= Q(capacity), z3.Or(total == Q(capacity), prices[good] == 0))

    def clamp(t, lo, hi):
        return z3.If(t < lo, lo, z3.If(t > hi, hi, t))

    half = Q(F(1, 2))
    upper = half + sum(clamp(t - half, 0, half) for t in (positive, negative))
    lower_pool = sum(clamp(t, 0, half) for t in (positive, negative))
    lower = clamp(lower_pool - half, 0, half)
    # The upper port receives an additional constant source of mass 1/2.
    solver.push()
    solver.add(z3.Or(half + z3.Sum(incoming["upper_out"]) != upper,
                     z3.Sum(incoming["lower_out"]) != lower))
    check_status("Any wrong fold on independent loads in [0,2] or port prices in [0,1]",
                 solver, z3.unsat)
    solver.pop()
    solver.add(positive == Q(F(3, 2)), negative == Q(F(1, 2)))
    check_status("Overflow and threshold tie in the expanded fold", solver, z3.sat)


def closed_example():
    # R=((0,-1/2),(1/2,0)), lambda=1 give M=((3,4),(-4,3))/5.
    # For d=(1/8,-1/16), q=-(I+R)^-1 d=(-3/40,1/10).
    names = [f"state_{i}_{side}" for i in range(2) for side in ("plus", "minus")]
    goods, buyers = {}, []
    routers = []
    switches = []
    arrivals = {good: [] for good in names}

    def add_buyer(name, mass, offers, ports=()):
        buyers.append((name, mass, offers))
        for port in ports:
            if port in arrivals:
                arrivals[port].append((name, port))

    def router(good, quotas, successors):
        routers.append((good, sum(quotas)))
        d = len(quotas)
        factor = 4 * (d + 1)
        for j, (mass, port) in enumerate(zip(quotas, successors), 1):
            add_buyer(f"{good}_tranche{j}", mass,
                      {good: (factor, factor), port: (factor - 2*j, 1)}, (port,))

    half = F(1, 2)
    for i, bias in enumerate((F(1, 8), F(-1, 16))):
        for side, sign in (("plus", 1), ("minus", -1)):
            state = f"state_{i}_{side}"
            router(state, (half, half), (f"low_{i}", f"upper_{i}"))
            add_buyer(f"source_{state}", F(1, 4) + sign * bias, {state: (2, 1)}, (state,))
        router(f"low_{i}", (half, half), ("discard", f"lower_{i}"))
        add_buyer(f"fold_source_{i}", half, {f"upper_{i}": (2, 1)})
        # The sign is positive from state 0 to 1, negative from state 1 to 0.
        for fold_port, sign in (("upper", 1), ("lower", -1)):
            out_sign = sign if i == 0 else -sign
            target = f"state_{1-i}_{'plus' if out_sign == 1 else 'minus'}"
            switches.append((f"{fold_port}_{i}", target))

    # With a physical range of 2, gadget(1) has quantum 1/2. The retained
    # first exit differs from half the input by at most 1/4.
    template, _, _ = gadget(1)
    input_buyers = []
    for inlet, target in switches:
        mapping = {name: f"{inlet}_{name}" for name in template["goods"]}
        mapping.update({"p": inlet, "a": target, "b": "discard"})
        goods.update({mapping[name]: half * cap for name, cap in template["goods"].items()})
        for i, (mass, options) in enumerate(template["buyers"]):
            name = f"{inlet}_switch{i}"
            opts = {mapping[g]: offer for g, offer in options.items()}
            if "p" in options:
                input_buyers.append((name, inlet, opts))
            else:
                add_buyer(name, half * mass, opts, (target,) if "a" in options else ())

    def prospective(good):
        return sum(mass for _, mass, offers in buyers if good in offers)

    for name, inlet, offers in input_buyers:
        cap = 3 + prospective(inlet)
        goods[inlet] = cap
        add_buyer(name, cap, offers)
    for good, local_mass in routers:
        anchor = 1 + prospective(good) - local_mass
        goods[good] = local_mass + anchor
        add_buyer(f"anchor_{good}", anchor, {good: (1, 1)})
    goods["discard"] = 1 + prospective("discard")
    return goods, buyers, arrivals


def check_closed_example():
    goods, buyers, arrivals = closed_example()
    solver = z3.SolverFor("QF_LRA")
    _, allocations = market_eq(goods, buyers, solver)
    check_status(f"Expanded closed two-row market ({len(goods)} goods, {len(buyers)} buyers)",
                 solver, z3.sat)
    raw = {name: z3.Sum([allocations[edge] for edge in feeds]) for name, feeds in arrivals.items()}

    def first_exit(t):
        # h0(t/delta)*delta on 0 <= t <= 3/2 for delta=1/2.
        half = Q(F(1, 2))
        return z3.If(t <= half, t, z3.If(t <= 1, half, half + t - 1))

    def low(t):
        return z3.If(t < Q(F(1, 2)), t, Q(F(1, 2)))

    def high(t):
        return z3.If(t < Q(F(1, 2)), 0, z3.If(t < 1, t - Q(F(1, 2)), Q(F(1, 2))))

    wrong = []
    for i in range(2):
        p, n = (raw[f"state_{i}_{side}"] for side in ("plus", "minus"))
        upper = Q(F(1, 2)) + high(p) + high(n)
        remainder = low(p) + low(n) - Q(F(1, 2))
        lower = z3.If(remainder >= 0, remainder, 0)
        receive = 1 - i
        bias = (F(1, 8), F(-1, 16))[receive]
        for side, sign in (("plus", 1), ("minus", -1)):
            stream = upper if (i == 0) == (sign == 1) else lower
            predicted = Q(F(1, 4) + sign * bias) + first_exit(stream)
            wrong.append(raw[f"state_{receive}_{side}"] != predicted)
    solver.add(z3.Or(wrong))
    check_status("Any full-market equilibrium violating its four recurrent routing equations",
                 solver, z3.unsat)


if __name__ == "__main__":
    check_fold()
    check_closed_example()
