"""Exact one-switch regressions for ARRIVAL to security-game nonuniqueness.

The source composer and one-resource game generator are the archive's actual
implementations. The source and pre-isolation terminal statements use
unrestricted QF_LRA. The isolated witnesses are recovered/checked on a small
support forest, and branching of the split is checked for every real split.
"""

from collections import defaultdict, deque
from fractions import Fraction as F
from pathlib import Path
import sys

import z3

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "code" / "lib"))
from referee_lib import compose, market_to_game, run_arrival, terminal_sources
from m1_isolation import decode_equilibrium, isolate_market
from wardrop.check_wardrop import exact, expect, market, q, rule_out


T = "Tyes"
HIGH, LOW = "terminal_high", "terminal_low"
CLONES = ("high_clone_0", "high_clone_1")


def as_triples(buyers):
    return [(i, mass, offers) for i, (mass, offers) in buyers.items()]


def replace_reserve(goods, original):
    buyers = dict(original)
    mass, offers = buyers.pop("termyes")
    cap = F(goods[T])
    assert mass == cap+1 and offers == {T: (F(1, 2), 1)}
    buyers[HIGH] = (cap-F(1, 2), dict(offers))
    buyers[LOW] = (F(3, 2), dict(offers))
    return buyers


def check_unperturbed(goods, buyers, sources, reached, tag):
    solver = z3.SolverFor("QF_LRA")
    _, flow, _ = market(solver, tag, goods, buyers)
    load = z3.Sum([flow[i, T] for i in sources])
    expect(solver, z3.sat, tag+" has an equilibrium")
    rule_out(solver, load != int(reached), tag+" has a different terminal bit")


def trial_perturbation(original, isolated):
    # Take serials directly from the exact emitted intercepts; trial values
    # only propose a forest. Every resulting coordinate/inequality is later
    # reconstructed at the generator's full exact delta.
    delta = F(isolated.delta)
    assert delta.numerator == 1 and delta.denominator.bit_count() == 1
    width = delta.denominator.bit_length()-1
    small = F(1, 256)
    trial = {}
    for i, (mass, offers) in original.items():
        row = {}
        exact_mass, exact_offers = isolated.buyers[i]
        assert exact_mass == mass+delta
        for j, (a, b) in offers.items():
            perturbed, new_slope = exact_offers[j]
            inc = F(perturbed-a)
            assert b == new_slope and inc.numerator == 1 and inc.denominator.bit_count() == 1
            exponent, rem = divmod(inc.denominator.bit_length()-1, width)
            assert exponent > 0 and not rem
            row[j] = (a+small**exponent, b)
        trial[i] = (mass+small, row)
    return trial


def discover_forest(goods, buyers, tag):
    solver = z3.SolverFor("QF_LRA")
    p, f, u = market(solver, tag, goods, buyers)
    expect(solver, z3.sat, "trial market has an equilibrium")
    model = solver.model()
    p, u = ({j: exact(model, v) for j, v in table.items()} for table in (p, u))
    tight = [(i, j) for i, (_, opts) in buyers.items() for j, (a, b) in opts.items()
             if u[i] == a-b*p[j]]
    anchors = [("b", i) for i in u if u[i] == 0]+[("g", j) for j in p if p[j] == 0]
    return tight, anchors


def realize_forest(goods, buyers, tight, anchors):
    graph = defaultdict(list)
    for i, j in tight:
        graph["b", i].append(("g", j))
        graph["g", j].append(("b", i))
    rootset = set(anchors)
    potential = {}
    flow = {(i, j): F(0) for i, (_, opts) in buyers.items() for j in opts}
    all_nodes = {("b", i) for i in buyers} | {("g", j) for j in goods}
    for root in anchors:
        assert root not in potential
        queue = deque([root])
        potential[root] = F(0)
        parent = {root: None}
        order = []
        while queue:
            v = queue.popleft()
            order.append(v)
            for w in graph[v]:
                if w == parent[v]:
                    continue
                assert w not in potential and w not in rootset
                if v[0] == "b":
                    a, b = buyers[v[1]][1][w[1]]
                    potential[w] = (a-potential[v])/b
                else:
                    a, b = buyers[w[1]][1][v[1]]
                    potential[w] = a-b*potential[v]
                parent[w] = v
                queue.append(w)
        spent = defaultdict(F)
        for v in reversed(order[1:]):
            w = parent[v]
            amount = (buyers[v[1]][0] if v[0] == "b" else goods[v[1]])-spent[v]
            edge = (v[1], w[1]) if v[0] == "b" else (w[1], v[1])
            flow[edge] = amount
            spent[w] += amount
    assert set(potential) == all_nodes
    prices = {j: potential["g", j] for j in goods}
    values = {i: potential["b", i] for i in buyers}
    check_market(goods, buyers, prices, flow, values)
    exact_ties = {(i, j) for i, (_, opts) in buyers.items() for j, (a, b) in opts.items()
                  if values[i] == a-b*prices[j]}
    assert exact_ties == set(tight)
    assert set(anchors) == {v for v, value in potential.items() if value == 0}
    return prices, flow, values


def check_market(goods, buyers, p, f, u):
    for i, (mass, offers) in buyers.items():
        row = sum(f[i, j] for j in offers)
        assert u[i] >= 0 and row <= mass and (not u[i] or row == mass)
        for j, (a, b) in offers.items():
            value = a-b*p[j]
            assert u[i] >= value and f[i, j] >= 0 and (not f[i, j] or u[i] == value)
    for j, cap in goods.items():
        load = sum(f[i, j] for i, (_, opts) in buyers.items() if j in opts)
        assert p[j] >= 0 and load <= cap and (not p[j] or load == cap)


def no_balanced_margins(goods, buyers, delta):
    # All original capacities are integral and masses half-integral, so
    # every buyer subset of size k has total in (1/2)Z+k delta.
    assert all(F(x).denominator == 1 for x in goods.values())
    assert all((F(w)-delta).denominator <= 2 for w, _ in buyers.values())
    assert 0 < len(buyers)*delta < F(1, 2)


def check_split_interval(buyers, p, flow, values, reached):
    h, offers = buyers[HIGH]
    z = flow[HIGH, T]
    assert p[T] > 0 and (0 < z < h if reached else z == h)
    if reached:
        assert values[HIGH] == 0 and p[T] == offers[T][0] and flow[LOW, T] == 0
    else:
        assert values[HIGH] > 0 and flow[LOW, T] > 0
    merged_rest = dict(buyers)
    del merged_rest[HIGH]
    for i in CLONES:
        merged_rest[i] = (h/2, dict(offers))
    lo, hi = max(F(0), z-h/2), min(h/2, z)
    assert (hi > lo) == reached
    # This exact scalar quantification is legitimate after the proven
    # singleton merge fixes every other price, utility, and flow.
    a, b = z3.Reals("split_0 split_1")
    physical = z3.And(a >= 0, b >= 0, a <= q(h/2), b <= q(h/2), a+b == q(z))
    if values[HIGH] > 0:
        physical = z3.And(physical, a == q(h/2), b == q(h/2))
    interval = z3.And(a >= q(lo), a <= q(hi), b == q(z)-a)
    solver = z3.SolverFor("QF_LRA")
    rule_out(solver, z3.Xor(physical, interval), "wrong split interval on real flows")
    return merged_rest, lo, hi


def lifted_profile(game, buyers, p, f, u):
    S, W, A = (game[k] for k in ("S", "U", "A"))
    x = {f"R:{j}": value/S for j, value in p.items()}
    x.update({f"G:{i}": (A-value)/S for i, value in u.items()})
    x["O"] = F(0)
    x["H"] = 1-sum(x.values())
    attack = {}
    for i, (mass, offers) in buyers.items():
        row = {f"R:{j}": f[i, j] for j in offers if f[i, j]}
        row["O"] = mass-sum(row.values())
        row[f"G:{i}"] = W
        attack[f"src:{i}"] = {t: value/(W+mass) for t, value in row.items() if value}
    for j in p:
        attack[f"ded:{j}"] = {f"R:{j}": F(1)}
    attack["ctl"] = {"H": F(1)}
    return x, attack


def check_dense_game(game, profile):
    x, attack = profile
    assert game["resources"] == 1 and set(x) == set(game["targets"])
    assert sum(x.values()) == 1 and all(0 <= v <= 1 for v in x.values())
    loads = defaultdict(F)
    for i, mass, row in game["types"]:
        assert mass > 0 and set(row) == set(x) and sum(attack[i].values()) == 1
        utilities = {t: u0-(u0-u1)*x[t] for t, (u0, u1) in row.items()}
        assert all(u0-u1 > 0 for u0, u1 in row.values())
        best = max(utilities.values())
        for t, amount in attack[i].items():
            assert amount > 0 and utilities[t] == best
            loads[t] += mass*amount
    assert all(v == (0, 1) for v in game["defender"].values())
    peak = max(loads[t] for t in x)
    assert all(loads[t] == peak for t in x if x[t] > 0)


def check_no_game_uniqueness(game, profile):
    """Test the two complete opponent-fixed equilibrium sections directly.

    The global implication of these two tests uses the separate connected
    equilibrium-set/finite-product theorem for ordinary security games.
    """
    x, attack = profile
    targets = game["targets"]
    loads = {t: F(0) for t in targets}
    for i, weight, _ in game["types"]:
        for t, amount in attack[i].items():
            loads[t] += weight*amount

    fixed_attack = z3.SolverFor("QF_LRA")
    v = {t: z3.Real("second_defense_"+t) for t in targets}
    fixed_attack.add(z3.Sum(list(v.values())) == 1, *(y >= 0 for y in v.values()))
    best_score = max(loads.values())
    fixed_attack.add(*(v[t] == 0 for t in targets if loads[t] != best_score))
    for i, _, row in game["types"]:
        # Every unlisted offer is at most -2 throughout the simplex. For
        # each source, outside is at least -1; the dedicated/control offer
        # is at least 1. This drops dominated terms before constructing SMT.
        assert row.get("O") == (0, -1) or any(pair == (2, 1) for pair in row.values())
        offers = {t: q(a)-q(a-b)*v[t] for t, (a, b) in row.items() if (a, b) != (-2, -3)}
        for chosen in attack[i]:
            fixed_attack.add(*(offers[chosen] >= w for w in offers.values()))
    rule_out(fixed_attack, z3.Or(*(v[t] != q(x[t]) for t in targets)),
             "NO game allows a second defense against the supplied attacks")

    fixed_defense = z3.SolverFor("QF_LRA")
    flow = {}
    column = defaultdict(list)
    for i, weight, row in game["types"]:
        offers = {t: a-(a-b)*x[t] for t, (a, b) in row.items()}
        high = max(offers.values())
        attacks = [t for t in targets if offers[t] == high]
        for t in attacks:
            flow[i, t] = z3.Real("second_attack_"+i+"_"+t)
            fixed_defense.add(flow[i, t] >= 0)
            column[t].append(flow[i, t])
        fixed_defense.add(z3.Sum([flow[i, t] for t in attacks]) == q(weight))
    peak = z3.Real("second_peak")
    for t in targets:
        load = z3.Sum(column[t]) if column[t] else q(0)
        fixed_defense.add(load <= peak)
        if x[t]:
            fixed_defense.add(load == peak)
    weights = {i: w for i, w, _ in game["types"]}
    rule_out(fixed_defense, z3.Or(*(v != q(weights[i]*attack[i].get(t, 0))
                                    for (i, t), v in flow.items())),
             "NO game allows a second attack profile against the supplied defense")
    print(f"NO dense game: both full fixed-opponent equilibrium sections are singletons "
          f"({len(targets)} coverage variables, {len(flow)} maximizing attack edges).", flush=True)


def check_case(succ):
    want, steps = run_arrival(succ)
    reached = want == "yes"
    goods, original = compose(succ, 0, len(succ))
    source = terminal_sources(original, "yes")
    buyers = {i: (F(w), o) for i, w, o in original}
    check_unperturbed(goods, buyers, source, reached, want+"source")
    buyers = replace_reserve(goods, buyers)
    check_unperturbed(goods, buyers, source, reached, want+"original")
    isolated = isolate_market(goods, buyers, first_offers=((HIGH, T), (LOW, T)))
    delta = F(isolated.delta)
    no_balanced_margins(isolated.goods, isolated.buyers, delta)
    tight, anchors = discover_forest(goods, trial_perturbation(buyers, isolated), want+"trial")
    p, f, u = realize_forest(isolated.goods, isolated.buyers, tight, anchors)
    old_p, old_f, old_u = decode_equilibrium(goods, buyers, p, f, u)
    check_market(goods, buyers, old_p, old_f, old_u)
    assert sum(old_f[i, T] for i in source) == int(reached)
    L = sum(f[i, T] for i in source)
    if reached:
        assert F(3, 4) < L < F(5, 4)
    else:
        assert 0 <= L < F(1, 4)
    b, lo, hi = check_split_interval(isolated.buyers, p, f, u, reached)
    game = market_to_game(isolated.goods, as_triples(b))
    scenes = []
    for a in dict.fromkeys([lo, (lo+hi)/2, hi]):
        fs = {edge: v for edge, v in f.items() if edge[0] != HIGH}
        fs[CLONES[0], T], fs[CLONES[1], T] = a, f[HIGH, T]-a
        us = {i: u[HIGH] if i in CLONES else u[i] for i in b}
        check_market(isolated.goods, b, p, fs, us)
        profile = lifted_profile(game, b, p, fs, us)
        check_dense_game(game, profile)
        assert profile not in scenes
        scenes.append(profile)
    assert len(scenes) == (3 if reached else 1)
    if not reached:
        check_no_game_uniqueness(game, scenes[0])
    print(f"{want.upper()} run in {steps} step(s): M0 {len(goods)} goods / {len(buyers)} buyers / "
          f"{sum(len(o) for _, o in buyers.values())} edges; dyadic isolation exponent "
          f"{delta.denominator.bit_length()-1}; {len(tight)} tight edges, {len(anchors)} anchored "
          f"trees; split game {len(game['types'])} types × {len(game['targets'])} targets; "
          f"{len(scenes)} dense full-game profile(s) checked.", flush=True)


if __name__ == "__main__":
    if hasattr(sys, "set_int_max_str_digits"):
        sys.set_int_max_str_digits(0)
    check_case([("yes", "no")])
    check_case([("no", "yes")])
