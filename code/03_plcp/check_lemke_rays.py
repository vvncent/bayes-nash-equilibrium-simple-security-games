"""Exact checks of the covered market LCP and the two independent split LPs.

Run: python -I -B 03_plcp/check_lemke_rays.py
"""
from fractions import Fraction as F
from math import ceil, lcm
from pathlib import Path
import sys

import z3

import os as _os, sys as _sys  # artifact: path bootstrap (relative to this file)
_HERE = _os.path.dirname(_os.path.abspath(__file__))
_sys.path[:0] = [_HERE, _os.path.join(_HERE, "..", "lib")]

import lp_market as fable  # artifact: module renamed market.py -> lib/lp_market.py
from splitcore import Market


def covered_lcp(masses, capacities, intercepts, slopes, edge_cover, row_cover, col_cover,
                diagonal=0, support=None):
    m, n = len(masses), len(capacities)
    tau = z3.Real("tau")
    u = [z3.Real(f"u_{i}") for i in range(m)]
    prices = [z3.Real(f"P_{j}") for j in range(n)]
    flow = [[z3.Real(f"f_{i}_{j}") for j in range(n)] for i in range(m)]
    solver = z3.SolverFor("QF_LRA")
    solver.add(tau >= 0)

    def pair(value, slack):
        slack = slack + diagonal * value
        solver.add(value >= 0, slack >= 0)
        if support is None:
            solver.add(z3.Or(value == 0, slack == 0))
        elif str(value) in support:
            solver.add(slack == 0)
        else:
            solver.add(value == 0)

    for i in range(m):
        pair(u[i], masses[i] + row_cover[i] * tau - sum(flow[i]))
        for j in range(n):
            slack = u[i] + slopes[i][j] * prices[j] - intercepts[i][j] + edge_cover[i][j] * tau
            pair(flow[i][j], slack)
    for j in range(n):
        pair(prices[j], capacities[j] + col_cover[j] * tau - sum(row[j] for row in flow))
    return solver, tau, u, prices, flow


def check_split(caps, beta, unit, other, p, f):
    split = [c - sum(row[j] for row in f[len(unit):]) for j, c in enumerate(caps)]
    complement = [c - s for c, s in zip(caps, split)]
    fixed = Market(caps, beta, unit, other)
    faces, first, second, _, _ = fixed.faces(split)
    for j, price in enumerate(p):
        faces.eqc({first[j]: 1}, price)
        faces.eqc({second[j]: 1}, beta[j] * price)
    assert faces.solve({}, "min")[0] == "optimal"
    independent = fable.Inst(caps, beta, other, unit)
    verdict = fable.c2_lp(independent, complement)
    assert verdict["feasible"]
    _, errors = fable.equilibrium_from_c2(independent, complement, verdict)
    assert not errors


def check_family(name, caps, beta, unit, other, scale):
    rows = unit + other
    masses = [mass for mass, _ in rows]
    a = [[F(x) for x in row] for _, row in rows]
    n = len(caps)
    b = [[F(1)] * n for _ in unit] + [list(beta) for _ in other]
    dr = [(i + 1) * scale for i in range(len(rows))]
    dc = [(j + 2) * scale for j in range(n)]
    de = [[F(1 + i + j, 1 + j) for j in range(n)] for i in range(len(rows))]
    solver, tau, u, prices, flow = covered_lcp(masses, caps, a, b, de, dr, dc)
    threshold = max([F(0)] + [x / h for row, cover in zip(a, de) for x, h in zip(row, cover)])
    variables = u + prices + [x for row in flow for x in row]
    bad = [z3.And(tau > threshold, z3.Or([x > 0 for x in variables]))]
    for i, row in enumerate(flow):
        bad.append(u[i] > max([F(0)] + a[i]))
        bad.extend(x > masses[i] + dr[i] * threshold for x in row)
    for j in range(n):
        bad.append(prices[j] > max([F(0)] + [a[i][j] / b[i][j] for i in range(len(rows))]))
    assert solver.check(z3.Or(bad)) == z3.unsat

    for value in (F(0), threshold / 3, threshold, threshold + 1):
        assert solver.check(tau == value) == z3.sat
        model = solver.model()
        p = [model.eval(x).as_fraction() for x in prices]
        f = [[model.eval(x).as_fraction() for x in row] for row in flow]
        shifted_caps = [c + d * value for c, d in zip(caps, dc)]
        shifted_rows = [(masses[i] + dr[i] * value, [x - h * value for x, h in zip(row, de[i])])
                        for i, row in enumerate(a)]
        check_split(shifted_caps, beta, shifted_rows[:len(unit)], shifted_rows[len(unit):], p, f)

    inputs = [F(x) for x in masses + list(caps) + [x for row in a + b for x in row] + [1]]
    denominator = lcm(*(x.denominator for x in inputs))
    size = len(variables) + 1
    largest = max(int(abs(x) * denominator) for x in inputs)
    max_intercept = max(F(0), *(x for row in a for x in row))
    min_slope = min(x for row in b for x in row)
    bound = 1 + max(max(masses) + max_intercept, max_intercept / min_slope)
    epsilon = F(1, 2 * ceil(bound) * (size * largest)**size)
    args = (masses, caps, a, b, de, dr, dc)
    perturbed, zero, *_ = covered_lcp(*args, diagonal=epsilon)
    assert perturbed.check(zero == 0) == z3.sat
    optimum = perturbed.model()
    support = {str(v) for v in variables if optimum.eval(v).as_fraction() > 0}
    linear, zero, _, prices, flow = covered_lcp(*args, support=support)
    assert linear.check(zero == 0) == z3.sat
    model = linear.model()
    p = [model.eval(x).as_fraction() for x in prices]
    f = [[model.eval(x).as_fraction() for x in row] for row in flow]
    check_split(caps, beta, unit, other, p, f)
    print(f"{name}: all-cover bound violations unsat, four quotas and P-LCP decode verified by both LPs")


def check_boundary():
    one = [1, 1]
    edge = [one, one]
    solver, tau, u, p, f = covered_lcp([1, 0], [1, 0], [[3, 5], [7, 9]],
                                        [[1, 2], [1, 2]], edge, one, one)
    witness = [tau == 0, u[0] == 1, u[1] == 5, p[0] == 2, p[1] == 5, f[0][0] == 1]
    assert solver.check(*witness) == z3.sat
    homogeneous, tau, u, p, f = covered_lcp([0], [0], [[0]], [[2]], [[1]], [1], [1])
    assert homogeneous.check(tau == 0, u[0] == 2**150, p[0] == 0, f[0][0] == 0) == z3.sat
    for masses, caps in (([-1], [0]), ([0], [-1])):
        solver, tau, *_ = covered_lcp(masses, caps, [[0]], [[2]], [[1]], [1], [1])
        assert solver.check(tau == 0) == z3.unsat
    print("Zero-margin lift and homogeneous direction sat, both negative margins infeasible")


if __name__ == "__main__":
    check_family("Fable price curve", [F(3, 2), F(1, 2)], [1, F(3, 2)],
                 [(1, [3, 3])], [(1, [4, F(9, 2)])], F(1))
    small = F(1, 2**80)
    beta = [1, 1 + F(1, 2**120)]
    check_family("tied split with binary margins", [F(9, 4) * small] * 2, beta,
                 [(small, [3, F(5, 2)]), (small, [F(1, 2), 4])], [(6 * small, beta)], small)
    check_family("slopes below and above one", [2, 3], [F(1, 4), 3],
                 [(2, [-1, 5])], [(4, [7, 2])], F(1))
    check_boundary()
