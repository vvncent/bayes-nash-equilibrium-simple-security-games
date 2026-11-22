"""audit/003 findings §3 cases: (1) interpolation (5/27,10/27,4/9) supports no BNE flow, exactly;
(2) the two-target example from the audit's bracket L=(0,0), H=(1,1) at lambda=1/2 is repaired by §5.
Usage: $PY -I -B check_audit_cases.py"""
import sys, os
import os as _os, sys as _sys; _HERE = _os.path.dirname(_os.path.abspath(__file__)); _sys.path[:0] = [_HERE, _os.path.join(_HERE, "..", "lib")]  # artifact: path bootstrap (relative to this file)
from fractions import Fraction as F
import z3
from core import R, M1Oracle, check_bne, check_box, loads
from procedure import narrow_and_repair
from run_tests import three_target, two_target

G = three_target()
x = [F(5, 27), F(10, 27), F(4, 9)]
assert sum(x) == 1 and F(4, 9) * 0 + F(4, 9) * F(1) + F(5, 9) * F(1) == 1
# any BNE flow at x: attackers best respond, defender best responds for SOME cutoff lam (variable)
s = z3.Solver()
f = [[z3.Real(f"f{i}{j}") for j in range(3)] for i in range(3)]
lam = z3.Real("lam")
for i in range(3):
    s.add(z3.Sum(f[i]) == R(G.p[i]))
    V = max(G.U(i, k, x[k]) for k in range(3))
    for j in range(3):
        s.add(f[i][j] >= 0)
        if G.U(i, j, x[j]) != V:
            s.add(f[i][j] == 0)
for j in range(3):  # all coverages interior -> score equals cutoff
    s.add(R(G.d[j]) * z3.Sum([f[i][j] for i in range(3)]) == lam)
print("interpolated point admits a BNE flow:", s.check())
assert s.check() == z3.unsat
print("row-2 utilities at interpolation:", [str(G.U(1, j, x[j])) for j in range(3)])

H2 = two_target()
lamb = F(1, 2)
c = [lamb / dj for dj in H2.d]
L, Hh = [F(0), F(0)], [F(1), F(1)]
fL = [[F(1, 2), F(1, 2)]]
fH = [[F(1, 2), F(1, 2)]]
assert check_box(H2, c, [0, 0], [1, 1], L, fL)[0] and check_box(H2, c, [0, 0], [1, 1], Hh, fH)[0]
for mode in ("opt", "interior", "plain"):
    st = {}
    xr, fr = narrow_and_repair(H2, M1Oracle(mode, 11), lamb, L, fL, Hh, fH, st)
    ok, why = check_bne(H2, xr, fr)
    assert ok
    print("two-target from audit bracket:", mode, [str(q) for q in xr], st["exit"])
print("audit cases OK")
