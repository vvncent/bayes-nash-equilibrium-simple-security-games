"""Mutation test for the s column: shrink the d'_j used inside T by 100x
(keeping D), so the s-column sum eta*D*sum(1/d'_j)/((1-2 delta) kappa) exceeds 1.
The exact z3 violation search must then find a pair that breaks (1-delta)."""
import os
import random
import sys
from fractions import Fraction as Fr

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import check as C
import sanity as S

g = C.rand_game(random.Random(11), 2, 2, zero_b=0, zero_d=0)
M = C.Model(g, structural_g=Fr(1, 10))
M.dp = [v / 100 for v in M.dp]
col = M.eta * M.D * sum(1 / v for v in M.dp) / (M.kappa * (1 - 2 * M.delta))
r, ratio = S.violation_search_with(M, 1 - M.delta)
print(f"mutated s-column sum {float(col):.2f} -> z3 {r}, exact ratio of witness {ratio}"
      f" ({'> 1-delta, caught' if ratio is not None and ratio > 1 - M.delta else 'not caught'})")
# artifact: exit status -- the mutation must be caught (z3 sat, exact witness ratio > 1-delta)
sys.exit(0 if (r == "sat" and ratio is not None and ratio > 1 - M.delta) else 1)
