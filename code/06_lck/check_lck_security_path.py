"""Check the proposed coverage path against the full Bayesian security-game equilibrium conditions."""

import argparse
from fractions import Fraction
import importlib.util
from pathlib import Path

import z3


def load_fold_construction():
    path = Path(__file__).resolve().parent.parent / "lib" / "auction_levels_check.py"  # artifact: builder copied to lib/
    spec = importlib.util.spec_from_file_location("auction_levels", path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module.build_market


def signals(depth, domain, terminal):
    low, high = terminal, 2 * terminal
    outputs = [low, high]
    for level in range(1, depth + 1):
        shift = domain / 2 ** (level + 1)
        upper, lower = max(low, high) - shift, min(low, high) + shift
        outputs.extend((upper, lower))
        low, high = lower, upper
    return outputs


def exact(value):
    value = Fraction(value)
    return z3.Q(value.numerator, value.denominator)


def direct_endpoint(build_market, depth):
    goods = 2 * depth + 2
    domain = Fraction(1, 4 * goods)
    demands, capacities, values, slopes, _, _ = build_market(depth, domain)
    masses = [mass // 2 for mass in demands[:-1]]
    weights = [cap // 2 for cap in capacities]
    values, slopes = values[:-1], slopes[:-1]
    terminal = Fraction(1, 3 * (depth + 1))
    coverage = [v - base for v, base in zip(signals(depth, domain, terminal), signals(depth, domain, 0))]
    assert sum(coverage) == 1 and all(0 <= x <= 1 for x in coverage)
    payoff = [[v - b * x for v, b, x in zip(row, coeff, coverage)] for row, coeff in zip(values, slopes)]
    # The highest-numbered listed target of each type is the output of its gate.
    gate_members = [[] for _ in range(goods)]
    for i, row in enumerate(values):
        gate_members[max(j for j, value in enumerate(row) if value >= 0)].append(i)
    flows = [{} for _ in masses]
    load = [0] * goods
    for g in reversed(range(1, goods)):
        private, = [i for i in gate_members[g] if all(value < 0 for value in values[i][:g])]
        generators = [i for i in gate_members[g] if i != private]
        flows[private][g] = masses[private]
        load[g] += masses[private]
        residual = weights[g] - load[g]
        sharing = next(i for i in generators if payoff[i][g] == max(payoff[i][:g]))
        assert 0 < residual < masses[sharing]
        flows[sharing][g] = residual
        load[g] += residual
        for i in generators:
            best_input = max(range(g), key=lambda j: payoff[i][j])
            on_input = masses[i] - flows[i].get(g, 0)
            flows[i][best_input] = on_input
            load[best_input] += on_input
    for i, row in enumerate(flows):
        assert sum(row.values()) == masses[i]
        assert all(qty > 0 and payoff[i][j] == max(payoff[i]) for j, qty in row.items())
    # Equal loads to prescribed weights make every target's expected marginal defender utility one.
    actual_load = [sum(row.get(j, 0) for row in flows) for j in range(goods)]
    assert actual_load == weights and sum(masses) == sum(weights)
    print(f"Direct endpoint verified for depth {depth}, {len(masses)} types and {goods} targets. Published path bound: {2 ** (depth - 1):,} successful updates.", flush=True)


def check_depth(build_market, depth):
    goods = 2 * depth + 2
    domain = Fraction(1, 4 * goods)
    demands, capacities, values, slopes, output, _ = build_market(depth, domain)
    # Keep the balanced incumbent types. The auction's appended buyer and common factor of two are surplus here.
    masses = [d // 2 for d in demands[:-1]]
    weights = [c // 2 for c in capacities]
    values, slopes = values[:-1], slopes[:-1]
    assert len(masses) == 5 * depth + 2
    assert len(weights) == goods and sum(weights) == sum(masses)
    assert sum(slope == 2 for row in slopes for slope in row) == 1

    solver = z3.Solver()
    coverage = [z3.Real(f"x{j}") for j in range(goods)]
    maximum_defender_score = z3.Real("score")
    attacks = []
    for i, mass in enumerate(masses):
        row = [z3.Real(f"a{i}_{j}") for j in range(goods)]
        attacks.append(row)
        best = z3.Real(f"best{i}")
        solver.add(z3.Sum(row) == mass)
        for j in range(goods):
            payoff = exact(values[i][j]) - exact(slopes[i][j]) * coverage[j]
            solver.add(row[j] >= 0, best >= payoff)
            solver.add(z3.Implies(row[j] > 0, best == payoff))

    for j in range(goods):
        load = z3.Sum([row[j] for row in attacks])
        scaled_score = maximum_defender_score * weights[j]
        solver.add(coverage[j] >= 0, coverage[j] <= 1, load <= scaled_score)
        # With one resource and total coverage at most one, every positively covered target must have maximal score.
        solver.add(z3.Implies(coverage[j] > 0, load == scaled_score))

    offset = signals(depth, domain, Fraction(0))
    pieces = 2 ** (depth - 1)
    step = domain / (2 * pieces)
    expected_last = None
    prior_budget = None
    rates = []
    for k in range(2 * pieces + 1):
        terminal = k * step
        expected = [value - base for value, base in zip(signals(depth, domain, terminal), offset)]
        budget = sum(expected)
        assert budget == 3 * (depth + 1) * terminal
        assert budget <= Fraction(1, 2) and (prior_budget is None or prior_budget < budget)
        prior_budget = budget
        if expected_last is not None:
            rates.append((expected[output] - expected_last) / step)
        expected_last = expected[output]
        solver.push()
        solver.add(z3.Sum(coverage) == exact(budget))
        assert solver.check() == z3.sat
        solver.add(z3.Or(*[x != exact(e) for x, e in zip(coverage, expected)]))
        assert solver.check() == z3.unsat
        solver.pop()
    assert all(rates[2 * i] == rates[2 * i + 1] for i in range(pieces))
    assert set(rates) <= {1, 2}
    assert all(rates[2 * (i - 1)] != rates[2 * i] for i in range(1, pieces))
    final_terminal = Fraction(1, 3 * (depth + 1))
    final_coverage = [value - base for value, base in zip(signals(depth, domain, final_terminal), offset)]
    assert sum(final_coverage) == 1
    solver.add(*[x == exact(value) for x, value in zip(coverage, final_coverage)])
    assert solver.check() == z3.sat
    print(f"Depth {depth}: {len(masses)} types, {goods} targets, {2 * pieces + 1} unique intermediate coverages, {pieces} affine pieces, integer-budget equilibrium verified.", flush=True)


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--depth", type=int, default=3)
    parser.add_argument("--endpoint", type=int, help="Compute and check one integer-budget equilibrium directly at this depth.")
    args = parser.parse_args()
    if args.depth < 1 or (args.endpoint is not None and args.endpoint < 1):
        parser.error("depth must be positive")
    construct = load_fold_construction()
    if args.endpoint is not None:
        direct_endpoint(construct, args.endpoint)
    else:
        for selected in range(1, args.depth + 1):
            check_depth(construct, selected)
