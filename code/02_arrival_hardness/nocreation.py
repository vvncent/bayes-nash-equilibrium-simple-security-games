"""Referee check for Theorem 1, step (b): does a gadget ever create mass (A + B > x) when its port
prices leave the box?  Exact z3 (linear real arithmetic) over every equilibrium.

For each gadget: UNSAT of  [gadget equilibrium, 0 <= x < c_p, P_a >= 0, P_b >= 0 (unbounded), A + B > x].
Non-vacuity: an equilibrium exists at out-of-box port prices (P_a = 3U, P_b = U/2) and (P_a = P_b = 5U).
Gadgets: two-copy (twocopy_gadget.gadget, m = 1..3, K = 4..16) and chain(K) (verify_chain.chain, K = 4, 8).
Usage: python -I -B nocreation.py
"""
import sys
import time
from fractions import Fraction as F

import os as _os, sys as _sys  # artifact: path bootstrap (relative to this file)
_HERE = _os.path.dirname(_os.path.abspath(__file__))
_sys.path[:0] = [_HERE, _os.path.join(_HERE, "..", "lib")]
# artifact: second sys.path entry folded into the bootstrap above
import z3  # noqa: E402
from switchcheck import Q, equilibrium  # noqa: E402
from twocopy_gadget import gadget  # noqa: E402
from verify_chain import chain  # noqa: E402


def no_creation(g, K, U):
    s = z3.Solver()
    x, Pa, Pb = z3.Real("x"), z3.Real("Pa"), z3.Real("Pb")
    s.add(x >= 0, x < Q(g["cp"]), Pa >= 0, Pb >= 0)
    A, B, Pp = equilibrium(g, x, Pa, Pb, s)
    s.push()
    s.add(A + B > x)
    r = str(s.check())
    s.pop()
    nv = []
    for (pa, pb) in [(3 * U, U / 2), (5 * U, 5 * U)]:
        s.push()
        s.add(x == Q(F(K, 2) + F(1, 3)), Pa == Q(pa), Pb == Q(pb))
        nv.append(str(s.check()))
        s.pop()
    return r, nv


def main():
    cases = []
    for m in (1, 2, 3):
        g, K, U = gadget(m)
        cases.append((f"two-copy m={m}", g, K, U))
    for K in (4, 8):
        cases.append((f"chain K={K}", chain(K), K, F(1)))
    allok = True
    for name, g, K, U in cases:
        t = time.time()
        r, nv = no_creation(g, K, U)
        ok = r == "unsat" and all(v == "sat" for v in nv)
        allok &= ok
        print(f"{name}: K={K} cp={g['cp']} | A+B>x at some port prices >= 0: {r} | "
              f"equilibrium exists out of box: {nv} | {'OK' if ok else 'FAIL'} ({time.time() - t:.1f}s)")
        sys.stdout.flush()
    print("ALL OK" if allok else "SOME FAILED")
    return allok  # artifact: exit status


if __name__ == "__main__":
    sys.exit(0 if main() else 1)  # artifact: exit status
