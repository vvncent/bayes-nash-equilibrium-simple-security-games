"""Control: the embedding with a slope below one (outside the b_ij >= 1 hypothesis).

Market: one buyer (mass 2), one good (capacity 1), payoff 1 - P/100. Its unique M1 equilibrium
has P = 100 (any lower price leaves positive utility and demand 2 > 1). The game needs
x = P/S = 20 > 1, so no BNE can decode. z3 is asked for a BNE and for a BNE that fails decoding.
"""
import sys
import time
from fractions import Fraction as F

import os as _os, sys as _sys; _HERE = _os.path.dirname(_os.path.abspath(__file__)); _sys.path[:0] = [_HERE, _os.path.join(_HERE, "..", "lib")]  # artifact: path bootstrap (relative to this file)
import z3  # noqa: E402
from game_check import build_game, encode_bne, decoded  # noqa: E402

goods = {"g": F(1)}
buyers = [("buyer", F(2), {"g": (F(1), F(1, 100))})]
G = build_game(goods, buyers, strict=False)
print(f"U={G['U']} A={G['A']} S={G['S']}; market needs P=100, i.e. x={F(100) / G['S']}")
s = z3.Solver()
x, f, v, peak, scale = encode_bne(G, s, False)
P, fm, cond = decoded(G, x, f, v, peak, scale)
t0 = time.time()
r1 = s.check()
print(f"BNE exists: {r1}; witness x={[str(s.model().eval(xk)) for xk in x]}" if r1 == z3.sat else r1)
s.add(z3.Not(z3.And(*cond)))
r2 = s.check()  # artifact: result kept for the exit status (same query, printed below)
print(f"some BNE fails the M1 decoding: {r2} ({time.time() - t0:.1f}s)")
# Market side, solved directly: every M1 equilibrium has P = 100.
m = z3.Solver()
Pm, V, fl = z3.Reals("P V f")
m.add(Pm >= 0, V >= 0, V >= 1 - Pm / 100, fl >= 0, z3.Or(fl == 0, V == 1 - Pm / 100),
      fl <= 2, z3.Or(V == 0, fl == 2), fl <= 1, z3.Or(Pm == 0, fl == 1))
m.push(); m.add(Pm != 100); r3 = m.check(); print(f"market equilibrium with P != 100: {r3}"); m.pop()
r4 = m.check(); print(f"market equilibrium exists: {r4}")
# artifact: exit status -- success iff the game has a BNE (sat) that fails decoding (sat), and the
# market has an equilibrium (sat), none with P != 100 (unsat)  (README 01.slope_below_one)
sys.exit(0 if (r1 == z3.sat and r2 == z3.sat and r3 == z3.unsat and r4 == z3.sat) else 1)
