"""Random discriminating instances (both terminals reachable, answer flips with initial switch
state). Correct gadget must give OK on all; swapped gadget must be caught on all.
Usage: composed_random.py n count seed"""
import os
import random
import sys
import time

import os as _os, sys as _sys  # artifact: path bootstrap (relative to this file)
_HERE = _os.path.dirname(_os.path.abspath(__file__))
_sys.path[:0] = [_HERE, _os.path.join(_HERE, "..", "lib")]
from composed_check import run_arrival, reaches_terminal, check_instance, reach  # noqa: E402

n, count, seed = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
rng = random.Random(seed)
T = list(range(n)) + ["yes", "no"]
ok_all, caught_all, done, seen = True, True, 0, set()
t0 = time.time()
while done < count:
    succ = tuple((rng.choice(T), rng.choice(T)) for _ in range(n))
    if succ in seen or not reaches_terminal(n, succ) or reach(n, succ, 0) != {"yes", "no"}:
        continue
    want, steps = run_arrival(n, succ, 0)
    if run_arrival(n, [(b, a) for (a, b) in succ], 0)[0] == want:
        continue
    seen.add(succ)
    r_ok = check_instance(n, list(succ), 0, n, eps=3)
    r_sw = check_instance(n, list(succ), 0, n, eps=-3)
    ok = r_ok[2] == "sat" and r_ok[3] == "unsat"
    caught = not (r_sw[2] == "sat" and r_sw[3] == "unsat")
    ok_all &= ok
    caught_all &= caught
    done += 1
    if not ok or not caught:
        print(f"  !! succ={list(succ)} want={want} correct={r_ok[2:4]} swapped={r_sw[2:4]}")
print(f"n={n}: {count} random discriminating instances; correct gadget OK on all: {ok_all}; "
      f"swapped gadget caught on all: {caught_all} ({time.time() - t0:.0f}s)")
sys.exit(0 if (ok_all and caught_all) else 1)  # artifact: exit status
