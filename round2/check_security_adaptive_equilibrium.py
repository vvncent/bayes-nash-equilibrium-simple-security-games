"""Exact checks for the transposed market and an adaptive ordinary-market circuit.

Run with z3-solver. The coupled fixtures use fixed tables on each input and
quantify over all real equilibria and all bounded nonnegative outside reads.
They exercise two coefficient choices, a true primal flow, and a third readout.
"""

from fractions import Fraction as F
from pathlib import Path
import sys

import z3

from check_security_equilibrium_predicate import model_for
from m1_isolation import isolate_market
from security_equilibrium_uniqueness import Game
from wardrop.check_wardrop import add, exact, expect, market, q, rule_out

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "code" / "lib"))
from referee_lib import market_to_game


def transpose(capacities, buyers):
    new_capacities = {i: mass for i, (mass, _) in buyers.items()}
    new_buyers = {j: (capacity, {}) for j, capacity in capacities.items()}
    for i, (_, offers) in buyers.items():
        for j, (intercept, slope) in offers.items():
            new_buyers[j][1][i] = (F(intercept) / slope, 1 / F(slope))
    return new_capacities, new_buyers


def market_conditions(capacities, buyers, prices, flows, utilities):
    conditions = [p >= 0 for p in prices.values()]
    conditions.extend(u >= 0 for u in utilities.values())
    for i, (mass, offers) in buyers.items():
        row_load = add(*(flows[i, j] for j in offers))
        conditions.extend([row_load <= q(mass),
                           z3.Or(utilities[i] == 0, row_load == q(mass))])
        for j, (a, b) in offers.items():
            residual = utilities[i] + q(b) * prices[j] - q(a)
            conditions.extend([residual >= 0, flows[i, j] >= 0,
                               z3.Or(residual == 0, flows[i, j] == 0)])
    for j, cap in capacities.items():
        load = add(*(amount for (_, k), amount in flows.items() if k == j))
        conditions.extend([load <= q(cap), z3.Or(prices[j] == 0, load == q(cap))])
    return z3.And(*conditions)


def minimum(values):
    result = q(0)
    for value in values:
        result = z3.If(value < result, value, result)
    return result


def check_transpose(tag, capacities, buyers):
    swapped_caps, swapped_buyers = transpose(capacities, buyers)
    solver = z3.SolverFor("QF_LRA")
    prices, flows, utilities = market(solver, tag, capacities, buyers)
    expect(solver, z3.sat, tag)
    swapped_flows = {(j, i): f for (i, j), f in flows.items()}
    conditions = [market_conditions(swapped_caps, swapped_buyers,
                                    utilities, swapped_flows, prices)]
    for i, (_, offers) in buyers.items():
        conditions.append(-utilities[i] == minimum(
            q(b) * prices[j] - q(a) for j, (a, b) in offers.items()))
    for j in capacities:
        conditions.append(-prices[j] == minimum(
            (utilities[i] - q(offers[j][0])) / q(offers[j][1])
            for i, (_, offers) in buyers.items() if j in offers))
    rule_out(solver, z3.Not(z3.And(*conditions)), tag + " transpose and both signs")


def check_scaled_programmable_gate():
    """Quantify over a positive external purchase inside a later scaled module."""
    for scale in (F(1, 8), F(1, 64), F(1, 512)):
        for bit in (0, 1):
            tag = f"scaled_{scale.denominator}_{bit}"
            capacities = {"bit": 2, "complement": 2,
                          "proxy": 8 * scale, "terminal": 2 * scale}
            buyers = {
                "set_bit": (4, {"bit": (1 + bit, 1)}),
                "set_complement": (4, {"complement": (2 - bit, 1)}),
                "source": (3 * scale, {"proxy": (7, 1)}),
                "guard": (scale, {"proxy": (21, 1)}),
                "arm0": (8 * scale, {"proxy": (20, 1), "terminal": (19, 2),
                                     "complement": (70, 40)}),
                "arm1": (8 * scale, {"proxy": (20, 1), "terminal": (18, 3),
                                     "bit": (70, 40)}),
            }
            solver = z3.SolverFor("QF_LRA")
            external = {j: z3.Real(f"{tag}_read_{j}") for j in ("terminal", "proxy")}
            reader_load = add(*external.values())
            solver.add(*(r >= 0 for r in external.values()), reader_load <= q(scale / 4))
            prices, flows, _ = market(solver, tag, capacities, buyers, external)
            for terminal, proxy in ((0, 0), (scale / 4, 0), (0, scale / 4)):
                solver.push()
                solver.add(external["terminal"] == q(terminal), external["proxy"] == q(proxy))
                expect(solver, z3.sat, tag + " reader corner")
                solver.pop()
            active, disabled = ("arm1", "arm0") if bit else ("arm0", "arm1")
            park = "complement" if bit else "bit"
            conditions = [
                prices["bit"] == 1 + bit, prices["complement"] == 2 - bit,
                prices["proxy"] == 7, prices["terminal"] == q(F(5, 3) if bit else 3),
                flows[disabled, park] == q(8 * scale),
                flows[active, "terminal"] == q(scale) + flows["source", "proxy"] + external["proxy"],
                flows["source", "proxy"] + reader_load == q(scale),
            ]
            rule_out(solver, z3.Not(z3.And(*conditions)), tag + " normalized clearing")


def adaptive_table(table_bit):
    """The price and utility in the first market program a second market.

    The first buyer offers 2-p to a good of capacity 4, with mass 1 or 8.
    The next buyer has mass 3, effective capacity 1 and an endogenously
    selected offer 6-2p or 5-3p. A final buyer tests the second price.
    """
    first_mass = 8 if table_bit else 1
    stage_scale = F(1, 128)
    read_scale = stage_scale / 32
    capacities = {"first": 4, "transposed": first_mass, "terminal": 2 * stage_scale,
                  "proxy": 8 * stage_scale, "answer": 2 * read_scale}
    buyers = {
        "old": (first_mass, {"first": (2, 1)}),
        "old_transposed": (4, {"transposed": (2, 1)}),
        "source": (3 * stage_scale, {"proxy": (7, 1)}),
        "guard": (stage_scale, {"proxy": (21, 1)}),
        "arm0": (8 * stage_scale,
                 {"proxy": (20, 1), "terminal": (19, 2), "transposed": (30, 25)}),
        "arm1": (8 * stage_scale,
                 {"proxy": (20, 1), "terminal": (18, 3), "first": (30, 25)}),
        "read": (2 * read_scale, {"answer": (1, 1), "terminal": (7, 3)}),
        "answer_guard": (read_scale, {"answer": (2, 1)}),
    }
    return capacities, buyers, stage_scale


def check_adaptive(table_bit):
    capacities, buyers, stage_scale = adaptive_table(table_bit)
    tag = "high" if table_bit else "low"
    solver = z3.SolverFor("QF_LRA")
    # Include all such external reads on both the private proxy and its
    # terminal. A later buyer's choices need not be independent in a market.
    # Permitting independent reads in this box is the stronger local test.
    external = {j: z3.Real(tag + "_external_" + j) for j in ("terminal", "proxy")}
    for amount in external.values():
        solver.add(amount >= 0, amount <= q(stage_scale / 32))
    prices, flows, _ = market(solver, tag, capacities, buyers, external)
    # Existence is also checked when no external client is present and at
    # each corner of the reader box, independently of the UNSAT query below.
    for terminal_read in (0, stage_scale / 32):
        for proxy_read in (0, stage_scale / 32):
            solver.push()
            solver.add(external["terminal"] == q(terminal_read),
                       external["proxy"] == q(proxy_read))
            expect(solver, z3.sat, tag + " read box corner")
            solver.pop()
    active, disabled = ("arm1", "arm0") if table_bit else ("arm0", "arm1")
    parked_at = "transposed" if table_bit else "first"
    expected = (
        prices["first"] == (2 if table_bit else 0),
        prices["transposed"] == (0 if table_bit else 2),
        prices["proxy"] == 7,
        prices["terminal"] == q(F(5, 3) if table_bit else 3),
        prices["answer"] == (0 if table_bit else 1),
        flows[disabled, parked_at] == q(8 * stage_scale),
        flows[active, "terminal"] ==
        q(stage_scale) + flows["source", "proxy"] + external["proxy"],
        flows["source", "proxy"] + flows["read", "terminal"] +
        external["terminal"] + external["proxy"] == q(stage_scale),
        flows["source", "proxy"] > 0,
    )
    rule_out(solver, z3.Not(z3.And(*expected)), tag + " full adaptive behavior")


def embedded_game(capacities, buyers, omega, *, slope_two_pairs=None):
    rows = [(name, mass, offers) for name, (mass, offers) in buyers.items()]
    embedded = market_to_game(capacities, rows, eps_prior=omega)
    targets, types = embedded["targets"], embedded["types"]
    total = sum(w for _, w, _ in types)
    game = Game(
        tuple(w / total for _, w, _ in types),
        tuple(embedded["defender"][j][1] - embedded["defender"][j][0] for j in targets),
        tuple(tuple(row[j][0] for j in targets) for _, _, row in types),
        tuple(tuple(row[j][0] - row[j][1] for j in targets) for _, _, row in types),
        embedded["resources"],
    )
    assert game.resources == 1 and set(embedded["defender"].values()) == {(0, 1)}
    assert all(min(row) > 0 for row in game.slopes)
    assert max(game.priors) / min(game.priors) <= 1 + omega
    if slope_two_pairs is not None:
        assert {v for row in game.slopes for v in row} == {1, 2}
        actual = {(name, target) for (name, _, _), row in zip(types, game.slopes)
                  for target, slope in zip(targets, row) if slope == 2}
        assert actual == {("src:" + i, "R:" + j) for i, j in slope_two_pairs}
    return game, [name for name, _, _ in types], targets, total


def check_embedded_shape(game, types, targets, upper, width, moving_targets):
    """The first clone's real flow parametrizes the segment about its two endpoints."""
    solver, coverage, flows = model_for(game)
    variables = coverage + list(flows.values())
    expect(solver, z3.sat, "adaptive embedded game")
    if width == 0:
        point = [exact(solver.model(), v) for v in variables]
        rule_out(solver, z3.Or(*(v != q(a) for v, a in zip(variables, point))),
                 "point game admits a second full profile")
        return

    left, right = (types.index("src:" + name) for name in ("left_read", "right_read"))
    column = targets.index(moving_targets[0])
    split = flows[left, column]
    lower = upper - width
    endpoints = []
    for amount in (lower, upper):
        solver.push()
        solver.add(split == q(amount))
        expect(solver, z3.sat, "adaptive segment endpoint")
        endpoints.append([exact(solver.model(), v) for v in variables])
        solver.pop()
    first, last = endpoints
    assert first != last and first[:len(coverage)] == last[:len(coverage)]
    moved = {edge for edge, a, b in zip(flows, first[len(coverage):], last[len(coverage):])
             if a != b}
    assert moved == {(i, targets.index(j)) for i in (left, right) for j in moving_targets}
    # With coverage fixed the attack best replies and defender score conditions
    # are linear, so both endpoints imply every intervening profile is valid.
    off_line = [v != q(a) + ((split - q(lower)) / q(width)) * q(b - a)
                for v, a, b in zip(variables, first, last)]
    rule_out(solver, z3.Or(split < q(lower), split > q(upper), *off_line),
             "a full equilibrium lies outside the endpoint segment")


def check_final_game(table_bit):
    capacities, buyers, _ = adaptive_table(table_bit)
    read_mass, read_offers = buyers.pop("read")
    buyers["left_read"] = (read_mass / 2, read_offers)
    buyers["right_read"] = (read_mass / 2, read_offers)
    game, types, targets, total = embedded_game(capacities, buyers, F(1))
    assert len(types) == 15 and len(targets) == 16
    upper = read_mass / (2 * total)
    check_embedded_shape(game, types, targets, upper, 0 if table_bit else upper,
                         ("R:answer", "O"))


def check_isolated_detector(bit):
    capacities = {"A": 8, "B": 8, "T": 3}
    buyers = {
        "rail_A": (16, {"A": (2 * (1 + bit), 2)}),
        "rail_B": (16, {"B": (2 - bit, 1)}),
        "detector_A": (2, {"T": (4, 1), "A": (4, 1)}),
        "detector_B": (2, {"T": (4, 1), "B": (4, 1)}),
    }
    # A literal dense slope-two rectangle, with a nontrading payoff on each
    # missing pair. The slope-two price setter pins A to 1 + bit.
    for i, (_, offers) in buyers.items():
        for j in capacities:
            offers.setdefault(j, (-1, 2 if (i, j) == ("rail_A", "A") else 1))
    isolated = isolate_market(capacities, buyers)
    solver = z3.SolverFor("QF_LRA")
    _, f, u = market(solver, "final_detector_" + str(bit), isolated.goods, isolated.buyers)
    expect(solver, z3.sat, "isolated physical detector")
    mass, offers = isolated.buyers["detector_B"]
    z = exact(solver.model(), f["detector_B", "T"])
    rule_out(solver, z3.Or(u["detector_B"] <= 0, f["detector_B", "T"] != q(z),
                          f["detector_B", "B"] != q(mass - z)),
             "an isolated detector violates its support")
    assert 0 < z < mass if bit else z == mass
    split_buyers = dict(isolated.buyers)
    del split_buyers["detector_B"]
    split_buyers["left_read"] = (mass / 2, offers)
    split_buyers["right_read"] = (mass / 2, offers)
    game, types, targets, total = embedded_game(
        isolated.goods, split_buyers, F(1, 1024), slope_two_pairs={("rail_A", "A")}
    )
    assert len(types) == 9 and len(targets) == 10
    lower = max(F(0), z - mass / 2) / total
    upper = min(z, mass / 2) / total
    check_embedded_shape(game, types, targets, upper, upper - lower, ("R:T", "R:B"))


def main():
    check_scaled_programmable_gate()
    print("Programmable gate: both control bits at three scales passed for all reader loads "
          "of total at most one quarter of the later module's scale.", flush=True)
    fixtures = [
        ({"j": 2}, {"i": (1, {"j": (2, 1)})}),
        ({"j": 1}, {"i": (3, {"j": (2, 1)})}),
        ({"j": 1}, {"i": (1, {"j": (2, 1)})}),
        ({"j": 1, "unused": 3}, {"empty": (2, {}), "i": (1, {"j": (-1, 3)})}),
        ({"j": 1, "k": 1},
         {"a": (1, {"j": (4, F(3, 2)), "k": (4, 2)}),
          "b": (1, {"j": (4, F(3, 2)), "k": (4, 2)})}),
        ({"j": F(3, 4), "k": F(1, 3)},
         {"a": (1, {"j": (5, F(5, 2)), "k": (4, F(7, 3))}),
          "b": (2, {"j": (2, F(1, 3)), "k": (3, F(3, 2))})}),
    ]
    for i, (capacities, buyers) in enumerate(fixtures):
        check_transpose("primal_" + str(i), capacities, buyers)
        check_transpose("dual_" + str(i), *transpose(capacities, buyers))
    for flag in (False, True):
        check_adaptive(flag)
    print("12 transposition and signed-price checks passed over all real equilibria.")
    print("Both adaptive 5-good, 8-buyer tables passed, including both reader ports.")
    print("Their second prices are 3 and 5/3, with final bits 1 and 0.", flush=True)
    for flag in (False, True):
        check_final_game(flag)
        print(f"Adaptive security game with 15 types and 16 targets is "
              f"{'one point' if flag else 'one nondegenerate closed segment'}.", flush=True)
    for bit in (0, 1):
        check_isolated_detector(bit)
    print("Both isolated nine-type, ten-target games passed at prior tolerance 1/1024.")
    print("Their dense slope tables have one slope-two rectangle. Exactly four named "
          "attack probabilities vary on the segment.")


if __name__ == "__main__":
    main()
