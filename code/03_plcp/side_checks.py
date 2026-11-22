"""Side checks on the composed markets (exact, Fractions):
  1. delta of e2e.delta_of equals check_plcp.epsilon_of (the earlier referee's code) on the same market;
  2. random principal minors of the composed M are >= 0 (P0 spot check) and of M + delta I are > 0;
  3. delta too large (delta = 1 and 1/2): does the decoder still work? (sensitivity of the composition to delta)
"""
import random
import sys
import time
from fractions import Fraction as F

sys.set_int_max_str_digits(0)
import os as _os, sys as _sys  # artifact: path bootstrap (relative to this file)
_HERE = _os.path.dirname(_os.path.abspath(__file__))
_sys.path[:0] = [_HERE, _os.path.join(_HERE, "..", "lib")]
from e2e import build_lcp, delta_of, compose, pipeline, show  # noqa: E402
import check_plcp  # noqa: E402


def dense(rows, N):
    M = [[F(0)] * N for _ in range(N)]
    for k, r in enumerate(rows):
        for l, v in r.items():
            M[k][l] = v
    return M


def main():
    rng = random.Random(7)
    allok = True  # artifact: exit status
    for n, succ in ((1, [("yes", "no")]), (2, [(1, "yes"), (0, "no")])):
        for geps in (3, -3):
            goods, buyers = compose(n, succ, 0, n, eps=geps)
            rows, q, edges, gnames = build_lcp(goods, buyers)
            N = len(q)
            delta, U, d, C, D = delta_of(rows, q, buyers, edges)
            # check_plcp.epsilon_of takes p, a, b tables and an edge list over buyer/good indices
            gidx = {g: j for j, g in enumerate(gnames)}
            p = [F(mass) for (_, mass, _) in buyers]
            a = [[F(0)] * len(gnames) for _ in buyers]
            b = [[F(1)] * len(gnames) for _ in buyers]
            el = []
            for (i, g, ai, bi) in edges:
                a[i][gidx[g]] = ai
                b[i][gidx[g]] = bi
                el.append((i, gidx[g]))
            Md = dense(rows, N)
            eps2, U2, d2, C2 = check_plcp.epsilon_of(Md, q, p, a, b, el)
            allok &= eps2 == delta  # artifact: exit status
            print(f"n={n} geps={geps}: N={N}, delta bits={delta.denominator.bit_length()}, "
                  f"same as check_plcp.epsilon_of: {eps2 == delta} (U={U}, d={d}, C={C}, D={D})")
            t = time.time()
            neg = 0
            for trial in range(300):
                size = rng.randint(1, 14)
                S = sorted(rng.sample(range(N), size))
                v = check_plcp.det([[Md[r][s] for s in S] for r in S])
                assert v >= 0, (n, S, v)
                vd = check_plcp.det([[Md[r][s] + (delta if r == s else 0) for s in S] for r in S])
                assert vd > 0, (n, S)
                neg += v > 0
            print(f"  300 random principal minors (size 1..14): all >= 0 for M ({neg} positive), all > 0 for "
                  f"M + delta I ({time.time() - t:.1f}s)")
            sys.stdout.flush()
    print("delta-sensitivity (decoder with a delta far larger than the reduction's):")
    for dl in (F(1), F(1, 2), F(1, 16)):
        r = pipeline(1, [("yes", "no")], geps=3, delta_override=dl)
        show(r)
        # artifact: exit status -- control: a delta this large must make system (1) infeasible
        allok &= (not r.get("ok")) and r.get("why") == "system (1) infeasible"
    return allok  # artifact: exit status


if __name__ == "__main__":
    sys.exit(0 if main() else 1)  # artifact: exit status
