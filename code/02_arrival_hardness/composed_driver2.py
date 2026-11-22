"""Discriminating end-to-end check. Picks the longest ARRIVAL runs among instances where both
terminals are reachable from the origin AND starting every switch at successor 1 instead of 0
changes the answer. Then:
  eps=3  (correct gadget)              -> every equilibrium must decode the true run (expect OK)
  eps=-3 (swapped gadget: b first)     -> must be caught (expect "caught")
  eps=0  (tied copies, price-routed)   -> reported, may or may not be caught
Usage: composed_driver2.py n count"""
import itertools
import os
import sys
import time

import os as _os, sys as _sys  # artifact: path bootstrap (relative to this file)
_HERE = _os.path.dirname(_os.path.abspath(__file__))
_sys.path[:0] = [_HERE, _os.path.join(_HERE, "..", "lib")]
from composed_check import run_arrival, reaches_terminal, check_instance, reach  # noqa: E402


def main():
    n, count = int(sys.argv[1]), int(sys.argv[2])
    T = list(range(n)) + ["yes", "no"]
    inst = []
    for succ in itertools.product(itertools.product(T, T), repeat=n):
        if not reaches_terminal(n, succ) or reach(n, succ, 0) != {"yes", "no"}:
            continue
        want, steps = run_arrival(n, succ, 0)
        flipped = [(b, a) for (a, b) in succ]
        alt, _ = run_arrival(n, flipped, 0)
        if alt == want:
            continue
        inst.append((steps, succ))
    inst.sort(key=lambda t: t[0], reverse=True)
    print(f"n={n}: {len(inst)} discriminating instances; testing the {count} longest")
    res = {3: True, -3: True, 0: True}
    for steps, succ in inst[:count]:
        line = []
        for eps in (3, -3, 0):
            t = time.time()
            want, steps, exists, wrong, nb, ng = check_instance(n, list(succ), 0, n, eps=eps)
            ok = exists == "sat" and wrong == "unsat"
            res[eps] &= ok
            line.append(f"eps={eps}: {'OK' if ok else 'caught'} ({time.time() - t:.1f}s)")
        print(f"succ={list(succ)} run->{want} in {steps} steps | " + " | ".join(line))
        sys.stdout.flush()
    print(f"correct gadget all OK: {res[3]}; swapped gadget all OK (should be False): {res[-3]}; "
          f"tied gadget all OK: {res[0]}")
    # artifact: exit status -- correct gadget OK on all; swapped and tied controls caught (not all OK)
    return res[3] and not res[-3] and not res[0]


if __name__ == "__main__":
    sys.exit(0 if main() else 1)  # artifact: exit status
