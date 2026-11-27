"""All-real-equilibrium checks for one-unit M1 binary margin refinement.

Requires z3-solver. Run with Python 3.10+ from any working directory.
"""

from dataclasses import dataclass
from fractions import Fraction as F
from math import lcm

import z3

from wardrop.check_wardrop import add, expect, market, q, rule_out


DUMMY_BUYER = "AddedBuyer"
DUMMY_GOOD = "AddedGood"


@dataclass
class Update:
    goods: dict
    buyers: dict
    old_mass: F
    row_scale: dict
    mass_scale: int
    height: F


def make_update(goods, buyers, multiplier=1):
    assert DUMMY_GOOD not in goods and DUMMY_BUYER not in buyers
    margins = [F(cap) for cap in goods.values()] + [F(mass) for mass, _ in buyers.values()]
    mass_scale = 2 * lcm(*(v.denominator for v in margins)) * multiplier
    row_scale = {i: 4 * max([F(1)] + [F(b) for _, b in offers.values()])
                 for i, (_, offers) in buyers.items()}
    height = 1 + max([F(0)] + [F(a) / row_scale[i] for i, (_, offers) in buyers.items()
                                for a, _ in offers.values()])
    query_goods = {j: mass_scale * F(cap) for j, cap in goods.items()}
    old_mass = sum(query_goods.values())
    query_goods[DUMMY_GOOD] = sum(mass_scale * F(mass) for mass, _ in buyers.values())
    query_buyers = {}
    for i, (mass, offers) in buyers.items():
        shifted = {j: ((F(a) + 4 * height * b) / row_scale[i], F(b) / row_scale[i])
                   for j, (a, b) in offers.items()}
        shifted[DUMMY_GOOD] = (3 * height, F(1))
        query_buyers[i] = (mass_scale * F(mass), shifted)
    dummy_offers = {j: (4 * height, F(1)) for j in goods}
    dummy_offers[DUMMY_GOOD] = (3 * height, F(1))
    query_buyers[DUMMY_BUYER] = (old_mass + 1, dummy_offers)
    return Update(query_goods, query_buyers, old_mass, row_scale, mass_scale, height)


def source_conditions(goods, buyers, prices, flows, utilities):
    conditions = []
    for i, (mass, offers) in buyers.items():
        conditions.append(utilities[i] >= 0)
        used = add(*(flows[i, j] for j in offers))
        conditions.extend((used <= q(mass), z3.Or(utilities[i] == 0, used == q(mass))))
        for j, (a, b) in offers.items():
            gap = utilities[i] + q(b) * prices[j] - q(a)
            conditions.extend((flows[i, j] >= 0, gap >= 0, z3.Or(flows[i, j] == 0, gap == 0)))
    for j, cap in goods.items():
        used = add(*(flows[i, j] for i, (_, offers) in buyers.items() if j in offers))
        conditions.extend((prices[j] >= 0, used <= q(cap), z3.Or(prices[j] == 0, used == q(cap))))
    return z3.And(*conditions)


def check_greatest_predecessor(name, goods, update, dummy_offer):
    one_short = dict(update.buyers)
    one_short[DUMMY_BUYER] = update.old_mass - 1, one_short[DUMMY_BUYER][1]
    largest_real_offer = max(
        [F(0)] + [intercept for i, (_, options) in one_short.items() if i != DUMMY_BUYER
                  for j, (intercept, _) in options.items() if j != DUMMY_GOOD]
    )
    greatest_dummy = dummy_offer - largest_real_offer
    assert greatest_dummy >= 0
    predecessor = z3.SolverFor("QF_LRA")
    prices, _, _ = market(predecessor, "one_short", update.goods, one_short)
    rule_out(predecessor, z3.Or(*(prices[j] != 0 for j in goods),
                                prices[DUMMY_GOOD] > q(greatest_dummy)),
             name + " greatest predecessor bound")

    test = z3.SolverFor("QF_LRA")
    dummy_price = z3.Real("candidate_predecessor_dummy_price")
    test.add(dummy_price >= 0, dummy_price <= q(greatest_dummy))
    candidate_prices = {j: q(0) for j in goods}
    candidate_prices[DUMMY_GOOD] = dummy_price
    candidate_values = {i: q(dummy_offer) - dummy_price for i in one_short}
    candidate_values[DUMMY_BUYER] = q(4 * update.height)
    candidate_flows = {(i, j): q(0) for i, (_, opts) in one_short.items() for j in opts}
    for i, (mass, _) in one_short.items():
        if i != DUMMY_BUYER:
            candidate_flows[i, DUMMY_GOOD] = q(mass)
    for j in goods:
        candidate_flows[DUMMY_BUYER, j] = q(update.goods[j])
    vacancy = next(iter(goods))
    candidate_flows[DUMMY_BUYER, vacancy] -= 1
    valid = source_conditions(update.goods, one_short, candidate_prices,
                              candidate_flows, candidate_values)
    rule_out(test, z3.Not(valid), name + " explicit predecessor flow throughout price interval")

    one_more = dict(one_short)
    one_more[DUMMY_BUYER] = update.old_mass, one_short[DUMMY_BUYER][1]
    candidate_flows[DUMMY_BUYER, vacancy] += 1
    valid = source_conditions(update.goods, one_more, candidate_prices,
                              candidate_flows, candidate_values)
    rule_out(test, z3.Not(valid), name + " feasible first addition at greatest predecessor price")


def run_case(name, goods, buyers, multiplier=1, unique_predecessor=False):
    update = make_update(goods, buyers, multiplier)
    dummy_offer = 3 * update.height
    if unique_predecessor:
        dummy_offer = max(
            [F(0)] + [intercept for i, (_, options) in update.buyers.items() if i != DUMMY_BUYER
                      for j, (intercept, _) in options.items() if j != DUMMY_GOOD]
        )
        for _, options in update.buyers.values():
            options[DUMMY_GOOD] = (dummy_offer, F(1))
    check_greatest_predecessor(name, goods, update, dummy_offer)
    old_buyers = dict(update.buyers)
    old_buyers[DUMMY_BUYER] = update.old_mass, old_buyers[DUMMY_BUYER][1]
    assert all(v.denominator == 1 and v.numerator % 2 == 0 for v in update.goods.values())
    assert all(v.denominator == 1 and v.numerator % 2 == 0 for v, _ in old_buyers.values())
    for divisor in (1, 2):
        before = z3.SolverFor("QF_LRA")
        prior_goods = {j: v / divisor for j, v in update.goods.items()}
        prior_buyers = {i: (v / divisor, options) for i, (v, options) in old_buyers.items()}
        prices, flows, utilities = market(before, "old", prior_goods, prior_buyers)
        before.add(*(p == 0 for p in prices.values()))
        expect(before, z3.sat, name + " old all-zero price exists")
        known = {edge: q(0) for edge in flows}
        for i, (mass, _) in buyers.items():
            known[i, DUMMY_GOOD] = q(update.mass_scale * F(mass) / divisor)
        for j, cap in goods.items():
            known[DUMMY_BUYER, j] = q(update.mass_scale * F(cap) / divisor)
        if unique_predecessor:
            before.add(*(flows[e] == x for e, x in known.items()))
            expect(before, z3.sat, name + " explicit allocation at zero on balanced successor")
        else:
            rule_out(before, z3.Or(*(flows[e] != x for e, x in known.items()),
                                   *(utilities[i] != q(dummy_offer) for i in buyers),
                                   utilities[DUMMY_BUYER] != q(4 * update.height)),
                     name + " any disagreement with explicit old profile at zero prices")

    after = z3.SolverFor("QF_LRA")
    prices, flows, utilities = market(after, "new", update.goods, update.buyers)
    expect(after, z3.sat, name + " successor equilibrium exists")
    true_prices = {j: prices[j] - q(4 * update.height) for j in goods}
    true_utilities = {i: q(scale) * utilities[i] for i, scale in update.row_scale.items()}
    true_flows = {(i, j): flows[i, j] / update.mass_scale for i, (_, opts) in buyers.items() for j in opts}
    target = source_conditions(goods, buyers, true_prices, true_flows, true_utilities)
    rule_out(after, z3.Or(z3.Not(target), prices[DUMMY_GOOD] != q(dummy_offer),
                          utilities[DUMMY_BUYER] != 0), name + " invalid source projection")

    endpoint = z3.SolverFor("QF_LRA")
    ep, ef, eu = market(endpoint, "chosen_endpoint", update.goods, old_buyers)
    rule_out(endpoint, ep[DUMMY_GOOD] > q(dummy_offer),
             name + " larger old dummy price")
    endpoint.add(ep[DUMMY_GOOD] == q(dummy_offer))
    expect(endpoint, z3.sat, name + " old endpoint attained")
    ep_old = {j: ep[j] - q(4 * update.height) for j in goods}
    eu_old = {i: eu[i] * q(t) for i, t in update.row_scale.items()}
    ef_old = {(i, j): ef[i, j] / update.mass_scale for i, (_, opts) in buyers.items() for j in opts}
    fallback = z3.Or(*(value < 0 for value in ep_old.values()))
    negative_only = all(a < 0 for _, opts in buyers.values() for a, _ in opts.values())
    ordinary = source_conditions(goods, buyers, ep_old, ef_old, eu_old)
    zeros = source_conditions(goods, buyers, {j: q(0) for j in goods},
                              {e: q(0) for e in ef_old}, {i: q(0) for i in buyers})
    rule_out(endpoint, z3.Not(z3.If(fallback, z3.And(negative_only, zeros), ordinary)),
             name + " invalid maximizing-old-dummy projection")
    if name == "empty-sparse":
        endpoint.add(fallback)
        expect(endpoint, z3.sat, name + " the negative-price decoder branch is attainable")

    original = z3.SolverFor("QF_LRA")
    p, f, u = market(original, "arbitrary_source", goods, buyers)
    expect(original, z3.sat, name + " original equilibrium exists")
    p_lift = {j: value + q(4 * update.height) for j, value in p.items()}
    p_lift[DUMMY_GOOD] = q(dummy_offer)
    u_lift = {i: value / q(update.row_scale[i]) for i, value in u.items()}
    u_lift[DUMMY_BUYER] = q(0)
    f_lift = {edge: update.mass_scale * x for edge, x in f.items()}
    for i, (mass, offers) in buyers.items():
        f_lift[i, DUMMY_GOOD] = update.mass_scale * (q(mass) - add(*(f[i, j] for j in offers)))
    for j, cap in goods.items():
        f_lift[DUMMY_BUYER, j] = update.mass_scale * (
            q(cap) - add(*(f[i, j] for i, (_, options) in buyers.items() if j in options)))
    f_lift[DUMMY_BUYER, DUMMY_GOOD] = update.mass_scale * add(*f.values())
    for view in (old_buyers, update.buyers):
        lifted = source_conditions(update.goods, view, p_lift, f_lift, u_lift)
        rule_out(original, z3.Not(lifted), name + " invalid simultaneous old/new lift")


def check_unique_full_predecessor(name, goods, buyers):
    buffer, protected = ("extra-good", "buffer"), ("extra-good", "protected")
    anchor, dedicated = ("extra-buyer", "anchor"), ("extra-buyer", "dedicated")
    margins = [F(m) for m, _ in buyers.values()] + [F(c) for c in goods.values()]
    scale = 4 * lcm(*(x.denominator for x in margins))
    row_scale = {i: 8 * max([F(1)] + [F(b) for _, b in opts.values()])
                 for i, (_, opts) in buyers.items()}
    H = 1 + max([F(0)] + [F(a) / row_scale[i] for i, (_, opts) in buyers.items()
                           for a, _ in opts.values()])
    caps = {j: scale * F(c) for j, c in goods.items()}
    caps.update({buffer: F(4), protected: F(4)})
    C = sum(caps.values())
    M = sum(scale * F(m) for m, _ in buyers.values()) + 6
    offset = {j: 8 * H + int(j != buffer) for j in caps}
    bidders = {}
    for i, (mass, opts) in buyers.items():
        bids = {j: ((F(a) + F(b) * offset[j]) / row_scale[i], F(b) / row_scale[i])
                for j, (a, b) in opts.items()}
        bidders[i] = scale * F(mass), bids
    bidders[dedicated] = F(4), {protected: (1 + offset[protected] / 8, F(1, 8))}
    bidders[anchor] = F(2), {buffer: (4 * H, F(1))}
    bids_d = {j: (o, F(1)) for j, o in offset.items()}
    bidders[DUMMY_BUYER] = C - 2, bids_d
    for _, bids in bidders.values():
        bids[DUMMY_GOOD] = (6 * H, F(1))
    caps[DUMMY_GOOD] = M - 1

    old = z3.SolverFor("QF_LRA")
    p, f, u = market(old, "unique_full_predecessor", caps, bidders)
    expect(old, z3.sat, name + " full predecessor exists")
    known_p = {j: q(int(j != buffer)) for j in offset}
    known_p[DUMMY_GOOD] = q(2 * H)
    known_f = {e: q(0) for e in f}
    for i in buyers:
        known_f[i, DUMMY_GOOD] = q(bidders[i][0])
    known_f[dedicated, DUMMY_GOOD] = q(4)
    known_f[anchor, DUMMY_GOOD] = known_f[anchor, buffer] = q(1)
    for j in offset:
        known_f[DUMMY_BUYER, j] = q(caps[j] if j != buffer else 2)
    wrong = [p[j] != v for j, v in known_p.items()] + [f[e] != v for e, v in known_f.items()]
    wrong.extend(u[i] != q(8 * H if i == DUMMY_BUYER else 4 * H) for i in u)
    rule_out(old, z3.Or(*wrong), name + " disagreement with any coordinate of unique old equilibrium")

    for increment in (1, 2):
        bidders[DUMMY_BUYER] = C - 2 + increment, bids_d
        after = z3.SolverFor("QF_LRA")
        p, f, u = market(after, "from_unique_old", caps, bidders)
        if increment == 1:
            rule_out(after, p[DUMMY_GOOD] > q(6 * H), name + " largest middle dummy price")
            after.add(p[DUMMY_GOOD] == q(6 * H))
        expect(after, z3.sat, name + " endpoint exists after increment " + str(increment))
        src_p = {j: p[j] - q(offset[j]) for j in goods}
        src_f = {(i, j): f[i, j] / scale for i, (_, opts) in buyers.items() for j in opts}
        src_u = {i: q(row_scale[i]) * u[i] for i in buyers}
        correct = source_conditions(goods, buyers, src_p, src_f, src_u)
        rule_out(after, z3.Or(p[DUMMY_GOOD] != q(6 * H), z3.Not(correct)),
                 name + " invalid projection after increment " + str(increment))


def rectangle_case():
    goods = {"X": F(3, 2), "Y": F(1), "Z": F(2)}
    buyers = {"A": (F(4, 3), {"X": (5, 1), "Y": (9, 1), "Z": (3, 1)}),
              "B": (2, {"X": (6, 2), "Y": (4, 1)}),
              "C": (F(3, 2), {"X": (3, 2), "Y": (5, 1), "Z": (9, 2)})}
    base = make_update_block(goods, buyers, {"B", "C"}, {"X", "Z"})
    market_goods, market_rows, s, H, reserves, W = base
    d, D, proxy = DUMMY_BUYER, DUMMY_GOOD, ("aux-good", 5)
    old = dict(market_rows)
    old[d] = old[d][0] - 1, old[d][1]
    for j, cap in market_goods.items():
        assert cap.denominator == 1 and cap.numerator % 2 == 0
    assert all(m.denominator == 1 and not m.numerator % 2 for m, _ in old.values())
    for scale in (1, 2):
        original = z3.SolverFor("QF_LRA")
        sm = {i: (m / scale, opts) for i, (m, opts) in old.items()}
        sg = {j: c / scale for j, c in market_goods.items()}
        p, f, u = market(original, "old_rectangle", sg, sm)
        original.add(*(x == 0 for x in p.values()))
        expect(original, z3.sat, "rectangle zero predecessor")
        plan = {e: q(0) for e in f}
        for i, (m, _) in buyers.items():
            plan[i, proxy] = q(s * m / scale)
        for j, c in goods.items():
            plan[d, j] = q(s * c / scale)
        load = s * sum(m for m, _ in buyers.values())
        for k in reversed(range(1, 6)):
            home = ("aux-good", k)
            pred = ("aux-good", k - 1) if k > 1 else D
            plan[("guard", k), home] = q(F(2, scale))
            plan[("gen", k), home] = q((reserves[k] - 2 - load) / scale)
            plan[("gen", k), pred] = q((2 + load) / scale)
            load += 2
        rule_out(original, z3.Or(*(var != plan[e] for e, var in f.items())),
                 "rectangle known least equilibrium unique allocation")
        assert load == sg[D] * scale

    new = z3.SolverFor("QF_LRA")
    p, f, u = market(new, "new_rectangle", market_goods, market_rows)
    expect(new, z3.sat, "single-rectangle fine instance exists")
    projected_p = {j: p[j] - q(4 * H) for j in goods}
    projected_u = {i: u[i] for i in buyers}
    projected_f = {(i, j): f[i, j] / s for i, (_, opts) in buyers.items() for j in opts}
    projection = source_conditions(goods, buyers, projected_p, projected_f, projected_u)
    rule_out(new, z3.Or(z3.Not(projection), p[D] != q(3 * H), p[proxy] != q(24 * H)),
             "invalid single-rectangle fine projection")
    before = z3.SolverFor("QF_LRA")
    p, f, u = market(before, "old_max_rectangle", market_goods, old)
    rule_out(before, p[D] > q(3 * H), "dummy price bound on whole old rectangle")
    before.add(p[D] == q(3 * H))
    expect(before, z3.sat, "old rectangle bound attained")
    p0 = {j: p[j] - q(4 * H) for j in goods}
    f0 = {(i, j): f[i, j] / s for i, (_, opts) in buyers.items() for j in opts}
    u0 = {i: u[i] for i in buyers}
    rule_out(before, z3.Not(source_conditions(goods, buyers, p0, f0, u0)),
             "old rectangular maximizing face projects")
    print("One actual slope-two rectangle: 14 buyers, 9 goods on the regression; "
          "both explicit old allocations, every fine projection and the old endpoint passed.")


def make_update_block(goods, buyers, high_rows, high_cols):
    """Compile the binary update without introducing a second nonunit slope class."""
    d, D = DUMMY_BUYER, DUMMY_GOOD
    proxy = ("aux-good", 5)
    margins = [F(c) for c in goods.values()] + [F(m) for m, _ in buyers.values()]
    s = 2 * lcm(*(x.denominator for x in margins))
    H = 1 + max([F(0)] + [F(a) / 8 for _, opts in buyers.values() for a, _ in opts.values()])
    M = sum(s * m for m, _ in buyers.values()); C = sum(s * c for c in goods.values())
    reserves = {5: 2 * (M + 16)}
    for k in range(4, 0, -1):
        reserves[k] = 2 * (reserves[k + 1] + 4)
    W = 32 * H
    physical_goods = {j: s * c for j, c in goods.items()}
    physical_goods[D] = M + 10
    for k in range(1, 6):
        physical_goods["aux-good", k] = reserves[k]
    rows = {}
    for i, (mass, options) in buyers.items():
        row = {j: (F(a) + 4 * H * b, b) for j, (a, b) in options.items()}
        row[proxy] = (24 * H, 1)
        rows[i] = s * mass, row
    row = {j: (4 * H, 1) for j in goods}
    row[D] = 3 * H, 1
    rows[d] = C + 1, row
    high_rows = set(high_rows)
    high_cols = set(high_cols) | {D, ("aux-good", 2), ("aux-good", 4)}
    for k in range(1, 6):
        output = ("aux-good", k)
        pred = ("aux-good", k - 1) if k > 1 else D
        ratio = 2 if k % 2 else 1
        if ratio == 2:
            high_rows.add(("gen", k))
        rows["gen", k] = reserves[k], {output: (W, 1), pred: (W, ratio)}
        rows["guard", k] = F(2), {output: (W + 1, 1)}
    for i, (_, opts) in rows.items():
        for j, (_, b) in opts.items():
            assert b == 1 + int(i in high_rows and j in high_cols)
    return physical_goods, rows, s, H, reserves, W


def main():
    cases = (
        ("price-interval", {0: 1}, {0: (1, {0: (2, 1)})}),
        ("flow-interval", {0: 1, 1: 1}, {0: (1, {0: (3, 1), 1: (3, 1)}),
                                          1: (1, {0: (3, 1), 1: (3, 1)})}),
        ("empty-sparse", {0: F(4, 9), 1: F(5, 6)}, {0: (F(8, 7), {}),
                                                   1: (F(2, 5), {0: (-1, F(2, 3))})}),
        ("rational-heterogeneous", {0: F(5, 7), 1: F(2, 3), 2: 1},
         {0: (2, {0: (F(9, 2), 3), 1: (F(8, 3), F(1, 7))}),
          1: (F(11, 5), {1: (F(13, 3), 2), 2: (1, F(6, 5))}),
          2: (F(1, 4), {0: (3, 1), 2: (1, 1)})}),
    )
    for name, goods, buyers in cases:
        run_case(name, goods, buyers)
        run_case(name, goods, buyers, unique_predecessor=True)
        check_unique_full_predecessor(name, goods, buyers)
    run_case("tiny-relative-insertion", cases[-1][1], cases[-1][2], multiplier=1 << 50)
    run_case("outside-attains-R", {"only": 1}, {"a": (1, {"only": (-100, 1)})},
             unique_predecessor=True)
    print("Five exact real-equilibrium checks passed for the binary successor, "
          "the complete one-short predecessor price interval and first update, "
          "the simultaneous old/new extension, and maximizing the named old price. "
          "The negative-price fallback and a 50-bit extra scaling were tested.")
    print("Five unique-price one-short predecessors passed, including R=0 and every "
          "real equilibrium of their one-unit maximizing face and two-unit successors.")
    print("Four unique full predecessor cases passed for every old price, flow and "
          "utility, every one-unit maximizing outcome, and every two-unit outcome.")
    rectangle_case()


if __name__ == "__main__":
    main()
