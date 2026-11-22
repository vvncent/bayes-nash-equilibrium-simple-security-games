"""Bit-size of the reduction ARRIVAL(n vertices) -> composed market -> one-resource security game,
on the chain instance of Dohrau et al. Fig. 1 (worst-case long run), gadget depth m = n.
Prints agents, max number bit length, total bits; checks growth is polynomial (ratio test vs n^5).
Reproduce: $PY -I -B verify_bits.py 8
"""
import os, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'lib'))
from fractions import Fraction as F
from referee_lib import compose, market_to_game


def nb(v):
    v = F(v)
    return abs(v.numerator).bit_length() + v.denominator.bit_length()


N = int(sys.argv[1]) if len(sys.argv) > 1 else 8
ratios = []  # artifact: exit status
print(" n | buyers goods | market bits (max num) | game types targets | game bits (max num) | game bits / n^5")
for n in range(1, N + 1):
    succ = [((v + 1) if v + 1 < n else "yes", 0) for v in range(n)]  # chain: v -> v+1 (even), v -> 0 (odd)
    goods, buyers = compose(succ, 0, n)
    vals = list(goods.values()) + [b[1] for b in buyers] + [z for b in buyers for ab in b[2].values() for z in ab]
    mb, mm = sum(map(nb, vals)), max(map(nb, vals))
    g = market_to_game(goods, buyers)
    tot = sum(w for (_, w, _) in g["types"])
    gv = [w / tot for (_, w, _) in g["types"]] + [u for (_, _, r) in g["types"] for uu in r.values() for u in uu]
    gb, gm = sum(map(nb, gv)), max(map(nb, gv))
    print(f"{n:2d} | {len(buyers):5d} {len(goods):5d} | {mb:8d} ({mm:4d}) | {len(g['types']):5d} {len(g['targets']):5d} | {gb:11d} ({gm:5d}) | {gb / n ** 5:.1f}", flush=True)
    ratios.append(gb / n ** 5)  # artifact: exit status
    if n == 7:
        ok7 = gb == 2570302  # artifact: exit status (README/book: the n=7 game has 2,570,302 bits)
# artifact: exit status -- the ratio test of the docstring: game bits / n^5 non-increasing in n
# (growth at most n^5), and the n=7 bit count quoted in the book when n=7 is included
sys.exit(0 if (all(a >= b for a, b in zip(ratios, ratios[1:])) and (N < 7 or ok7)) else 1)
