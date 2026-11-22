"""Run exact fold markets through the unchanged capacity-scaling auction."""

import argparse
from fractions import Fraction
import importlib.util
import inspect
from pathlib import Path


PROJECT = Path(__file__).resolve().parents[1]
AUCTION_PATH = (
    PROJECT / "runs/20261121T205429Z/markets/scaling_auction.py"
)
DOMAIN = Fraction(1, 4)


def load_auction():
    spec = importlib.util.spec_from_file_location("scaling_auction", AUCTION_PATH)
    auction = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(auction)
    return auction


def build_market(depth, domain=DOMAIN):
    if depth < 1:
        raise ValueError("depth must be positive")
    baselines = [Fraction(0)]
    gates = []

    def add_gate(kind, inputs, shift):
        alternatives = [slope * baselines[j] + shift for j, slope in inputs]
        baseline = (min if kind == "min" else max)(alternatives)
        entries = [
            (j, slope, threshold - baseline)
            for (j, slope), threshold in zip(inputs, alternatives)
        ]
        gates.append((kind, entries))
        baselines.append(baseline)
        return len(baselines) - 1

    low = 0
    high = add_gate("min", [(0, 2)], Fraction(0))
    for level in range(1, depth + 1):
        shift = domain / 2 ** (level + 1)
        previous = [(low, 1), (high, 1)]
        high = add_gate("max", previous, -shift)
        low = add_gate("min", previous, shift)
    output = high

    demands = []
    supplies = [0] * len(baselines)
    intercepts = []
    slopes = []
    special_buyer = None

    def add_buyer(mass, payoffs, special=False):
        row_intercepts = [Fraction(-1)] * len(supplies)
        row_slopes = [Fraction(1)] * len(supplies)
        if special:
            row_slopes[0] = Fraction(2)
        for j, intercept in payoffs:
            row_intercepts[j] = intercept
        demands.append(mass)
        intercepts.append(row_intercepts)
        slopes.append(row_slopes)

    running_mass = 0
    for good in reversed(range(1, len(baselines))):
        kind, inputs = gates[good - 1]
        generator_mass = 2 + running_mass
        supplies[good] = 2 * generator_mass
        menus = [inputs] if kind == "min" else [[entry] for entry in inputs]
        for menu in menus:
            special = any(slope == 2 for _, slope, _ in menu)
            if special:
                special_buyer = len(demands)
            payoffs = [(good, Fraction(4))]
            payoffs.extend((j, 4 - threshold) for j, _, threshold in menu)
            add_buyer(2 * generator_mass, payoffs, special)
        add_buyer(2, [(good, Fraction(4))])
        running_mass += 1 + generator_mass * len(menus)
    supplies[0] = sum(demands) - sum(supplies)
    add_buyer(1, [(0, Fraction(4))])
    return demands, supplies, intercepts, slopes, output, special_buyer


def check_depth(auction, depth, show_trace):
    demands, supplies, intercepts, slopes, output, special_buyer = build_market(depth)
    root = len(demands) - 1
    trace = []

    def record_raise():
        state = inspect.currentframe().f_back.f_locals
        assert state["i0"] == root and state["unit"] == 1
        assert len(state["IR"]) == len(demands)
        assert len(state["JR"]) == len(supplies)
        trace.append((
            state["x"][0], state["x"][output], state["H"][output],
            state["kind_event"], state["stats"].cancel, state["g"][special_buyer][0],
        ))

    auction._on_raise = record_raise
    try:
        _, _, _, stats = auction.solve_market(demands, supplies, intercepts, slopes)
    finally:
        auction._on_raise = None
    internal_endpoints = [y for y, _, _, event, _, _ in trace if event == "internal"]
    expected = [DOMAIN * j / 2 ** (depth - 1) for j in range(1, 2 ** (depth - 1))]
    assert internal_endpoints == expected, (internal_endpoints, expected)
    assert len(trace) == len(expected) + 1 and trace[-1][0] == Fraction(1, 2)
    print(
        f"depth={depth} bidders={len(demands)} goods={len(supplies)} "
        f"largest_margin={max(demands + supplies)} raises={len(trace)} "
        f"internal={len(internal_endpoints)} cycle_cancellations={stats.cancel}",
        flush=True,
    )
    if show_trace:
        print("terminal_end  output_end  output_rate  event  cumulative_cancellations  high_edge_flow")
        for step in trace:
            print(" ".join(map(str, step)))


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("depths", nargs="*", type=int, default=[1, 2, 3, 4, 5, 6, 7, 8])
    parser.add_argument("--trace", action="store_true")
    args = parser.parse_args()
    solver = load_auction()
    for requested_depth in args.depths:
        check_depth(solver, requested_depth, args.trace)
