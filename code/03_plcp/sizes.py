"""Sizes only: LCP dimension and delta bit size of the composed markets (no solving)."""
import sys

import os as _os, sys as _sys  # artifact: path bootstrap (relative to this file)
_HERE = _os.path.dirname(_os.path.abspath(__file__))
_sys.path[:0] = [_HERE, _os.path.join(_HERE, "..", "lib")]
from e2e import build_lcp, compose, delta_of, discriminating  # noqa: E402

# artifact: exit status -- sizes quoted in the book (README plcp-e2e-n1 / plcp-e2e-sizes):
# (n, geps) -> (LCP dimension N, delta bits or None)
BOOK = {(1, 3): (49, 676), (2, 3): (146, 2482), (3, 3): (299, None)}
allok = True
for n in (1, 2, 3, 4):
    inst = discriminating(n) if n <= 3 else [(0, [(1, "yes"), (2, "no"), (3, 0), ("yes", "no")])]
    steps, succ = inst[0]
    for geps in (3, -3):
        goods, buyers = compose(n, succ, 0, n, eps=geps)
        rows, q, edges, gnames = build_lcp(goods, buyers)
        delta, U, d, C, D = delta_of(rows, q, buyers, edges)
        print(f"n={n} geps={geps} discriminating={len(inst) if n <= 3 else '-'} N={len(q)} options={len(edges)} "
              f"buyers={len(buyers)} goods={len(goods)} U={U} C={C} delta_bits={delta.denominator.bit_length()}")
        if (n, geps) in BOOK:  # artifact: exit status
            bN, bbits = BOOK[(n, geps)]
            allok &= len(q) == bN and (bbits is None or delta.denominator.bit_length() == bbits)
sys.exit(0 if allok else 1)  # artifact: exit status
