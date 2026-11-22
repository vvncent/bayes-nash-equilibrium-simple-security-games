"""Batch: every discriminating n-vertex instance (n = 2), or random ones (n >= 3), through the game.

Discriminating: both terminals reachable from the origin and the run's terminal changes when every
switch starts at successor 1. Gadget depth m = n, as in composed_check.main. For each instance the
correct gadget (eps = 3) must give Q1 sat, Q2 unsat, Q3 unsat; the swapped gadget (eps = -3) is a
control and should make Q2 sat.
Usage: batch_reduced.py n [count seed]
"""
import itertools
import random
import sys
import time

import os as _os, sys as _sys; _HERE = _os.path.dirname(_os.path.abspath(__file__)); _sys.path[:0] = [_HERE, _os.path.join(_HERE, "..", "lib")]  # artifact: path bootstrap (relative to this file)
import z3  # noqa: E402
from game_check import build_game, compose, decoded, inflow, run_arrival  # noqa: E402
from game_check_reduced import encode_bne_reduced  # noqa: E402
from composed_check import reach, reaches_terminal  # noqa: E402


def run_checks(n, succ, eps):
    want, _ = run_arrival(n, succ, 0)
    other = "no" if want == "yes" else "yes"
    goods, buyers = compose(n, succ, 0, n, eps=eps)
    G = build_game(goods, buyers)
    s = z3.Solver()
    x, f, v, peak, scale = encode_bne_reduced(G, s)
    P, fm, cond = decoded(G, x, f, v, peak, scale)
    yin, oin = inflow(G, fm, want), inflow(G, fm, other)
    r1 = s.check()
    s.push(); s.add(z3.Or(yin != 1, oin != 0)); r2 = s.check(); s.pop()
    s.push(); s.add(z3.Not(z3.And(*cond))); r3 = s.check(); s.pop()
    return want, str(r1), str(r2), str(r3), len(G["weights"])


def discriminating(n, succ):
    if not reaches_terminal(n, succ) or reach(n, succ, 0) != {"yes", "no"}:
        return False
    a, _ = run_arrival(n, succ, 0)
    b, _ = run_arrival(n, [(y, x) for (x, y) in succ], 0)
    return a != b


def main():
    n = int(sys.argv[1])
    targets = list(range(n)) + ["yes", "no"]
    if len(sys.argv) > 2:
        count, rng = int(sys.argv[2]), random.Random(int(sys.argv[3]))
        pool, seen = [], set()
        while len(pool) < count:
            succ = [(rng.choice(targets), rng.choice(targets)) for _ in range(n)]
            if tuple(succ) not in seen and discriminating(n, succ):
                seen.add(tuple(succ)); pool.append(succ)
    else:
        pool = [list(c) for c in itertools.product(itertools.product(targets, repeat=2), repeat=n)
                if discriminating(n, list(c))]
    ok_all, caught = True, 0
    for succ in pool:
        t0 = time.time()
        want, r1, r2, r3, nt = run_checks(n, succ, 3)
        ok = (r1, r2, r3) == ("sat", "unsat", "unsat")
        ok_all &= ok
        _, c1, c2, c3, _ = run_checks(n, succ, -3)
        caught += c2 == "sat"
        print(f"succ={succ} -> {want} | types={nt} | Q1 {r1} Q2 {r2} Q3 {r3} | "
              f"{'OK' if ok else 'FAIL'} | swapped control Q2 {c2} Q3 {c3} ({time.time() - t0:.1f}s)")
        sys.stdout.flush()
    print(f"{len(pool)} instances; all OK: {ok_all}; swapped control caught on {caught}/{len(pool)}")
    return ok_all and caught == len(pool)  # artifact: exit status (control must be caught on every instance)


if __name__ == "__main__":
    sys.exit(0 if main() else 1)  # artifact: exit status
