"""Exact checks for the direct terminal-count market in the reductions book.

Run with a Python interpreter containing z3-solver. The shared checkers
encode the ordinary market equations and the local residual input equation.
"""

from collections import Counter, defaultdict
from fractions import Fraction
from pathlib import Path
import sys

import z3

ARTIFACT = Path(__file__).resolve().parents[1] / "code"
sys.path[:0] = [str(ARTIFACT / "lib"), str(ARTIFACT / "02_arrival_hardness")]
from eh_lib import eq_constraints
from switchcheck import check as check_local
sys.path.insert(0, str(ARTIFACT / "01_market_equivalence"))
from game_check import build_game, encode_bne, q


def counting_arcs(depth, branch):
    def source(level):
        return "s" if level == depth else (branch, level, "start")

    def sink(level):
        return branch if level == depth else (branch, level, "end")

    yield source(0), sink(0), 1, 0
    for level in range(1, depth + 1):
        cap = 1 << (level - 1)
        fee = 3 * ((1 << level) - 1)
        yield source(level), source(level - 1), cap, 0
        yield sink(level - 1), sink(level), cap, 0
        yield source(level), sink(level - 1), cap, fee
        yield source(level - 1), sink(level), cap, fee


def switch(depth, name, entry, exits, capacity):
    arcs = list(counting_arcs(depth, "a")) + list(counting_arcs(depth, "b"))
    scale = 6 + sum(fee + (head in ("a", "b")) for _, head, _, fee in arcs)
    goods, rows, masses = {}, defaultdict(dict), Counter()
    for index, (tail, head, cap, fee) in enumerate(arcs):
        good = f"{name}_e{index}"
        goods[good] = cap
        rows[tail][good] = (scale - fee, 1)
        rows[head][good] = (scale + (head in ("a", "b")), 1)
        masses[head] += cap
    rows["s"][entry] = (scale + 1, scale + 1)
    masses["s"] = capacity
    rows["a"][exits[0]] = (scale, 1)
    rows["b"][exits[1]] = (scale - 3, 1)
    buyers = [(f"{name}_{node}", masses[node], offers) for node, offers in rows.items()]
    return goods, buyers


def route(graph, supplies):
    rotor = [0] * len(graph)
    receipts = list(supplies[len(graph):])
    for origin, supply in enumerate(supplies[:len(graph)]):
        for _ in range(supply):
            v = origin
            while v < len(graph):
                nxt = graph[v][rotor[v]]
                rotor[v] ^= 1
                v = nxt
            receipts[v - len(graph)] += 1
    return receipts


def check_composed(graph, supplies, uniform_terminals):
    n = len(graph)
    depth = n + sum(supplies).bit_length() - 1
    limit = 1 << (depth + 1)
    indegree = Counter(w for pair in graph for w in pair)
    goods, buyers = {}, []
    for v, supply in enumerate(supplies):
        name = f"p{v}"
        cap = indegree[v] * (limit // 2) + supply + 1
        if v < n:
            cap = max(2 * limit, cap)
            exits = [f"p{w}" for w in graph[v]]
            private, nodes = switch(depth, f"v{v}", name, exits, cap)
            goods.update(private)
            buyers.extend(nodes)
        else:
            if uniform_terminals:
                cap = sum(supplies) + 1
            buyers.append((f"terminal{v}", cap + 1, {name: (Fraction(1, 2), 1)}))
        goods[name] = cap
        if supply:
            buyers.append((f"supply{v}", supply, {name: (2, 1)}))
    solver = z3.Solver()
    _, flows, _, _ = eq_constraints(goods, buyers, solver)
    assert solver.check() == z3.sat
    wrong = []
    for t, count in enumerate(route(graph, supplies), start=n):
        external = [f for (buyer, good), f in flows.items()
                    if good == f"p{t}" and buyer != f"terminal{t}"]
        wrong.append(z3.Sum(external) != count)
    solver.add(z3.Or(wrong))
    assert solver.check() == z3.unsat, (graph, supplies)


def check_one_resource_game():
    # Three chips at one switch send two to its first terminal and one to its second.
    private, buyers = switch(2, "switch", "entry", ("T0", "T1"), 16)
    goods = {**private, "entry": 16, "T0": 4, "T1": 4}
    for t in range(2):
        buyers.append((f"terminal{t}", 5, {f"T{t}": (Fraction(1, 2), 1)}))
    buyers.append(("dispatch", 3, {"entry": (2, 1)}))
    game = build_game(goods, buyers)
    solver = z3.Solver()
    _, attack, _, _, scale = encode_bne(game, solver, normalized=True)

    # A source can always obtain at least -1 outside; every unlisted action
    # pays at most -2. Each dedicated or control type strictly prefers its own target.
    for i, (_, _, offers) in enumerate(buyers):
        present = {game["gidx"][good] for good in offers}
        available = present | {len(goods) + i, game["out"]}
        for target in range(game["nT"]):
            if target not in available:
                solver.add(attack[i][target] == 0)
    for i in range(len(buyers), len(attack)):
        designated = game["ctl"] if i == len(attack) - 1 else i - len(buyers)
        for target in range(game["nT"]):
            if target != designated:
                solver.add(attack[i][target] == 0)

    assert solver.check() == z3.sat
    wrong = []
    for branch, good, expected in (("switch_a", "T0", 2), ("switch_b", "T1", 1)):
        buyer = next(i for i, row in enumerate(buyers) if row[0] == branch)
        wrong.append(q(scale) * attack[buyer][game["gidx"][good]] != expected)
    solver.add(z3.Or(wrong))
    assert solver.check() == z3.unsat


if __name__ == "__main__":
    regions = 0
    for depth in (1, 2):
        limit = 1 << (depth + 1)
        goods, buyers = switch(depth, "v", "p", ("a", "b"), 2 * limit)
        local = {"goods": goods, "buyers": [(mass, offers) for _, mass, offers in buyers],
                 "cp": 2 * limit}
        success, cases = check_local(local, limit, 1)
        assert success, cases
        regions += len(cases)
    print(f"{regions} local real-input regions passed, including saturation.", flush=True)
    cases = [
        ([(1, 2)], [3, 1, 0]),
        ([(0, 1)], [2, 0, 1]),
        ([(1, 1)], [1, 0, 2]),
        ([(2, 1)], [0, 1, 2]),
        ([(2, 1), (0, 3)], [1, 1, 0, 0]),
        ([(1, 2)], [1, 0, 1, 1]),
    ]
    for graph, supplies in cases:
        for uniform in (False, True):
            check_composed(graph, supplies, uniform)
    print(f"{len(cases)} graphs passed with both terminal capacity formulas.")
    check_one_resource_game()
    print("All equilibria of the 37-target, 36-type game give terminal counts (2, 1).")
