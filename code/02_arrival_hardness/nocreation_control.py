"""Negative control for nocreation.py: the same query must find mass creation (A + B > x) when it
exists.  chain(4) plus a buyer Y of mass 1 whose only option is port b at (2, 1): at P_b = 2 > U
Y has value 0 and may buy any amount of b.  (This gadget breaks S1, so it is not a counterexample to
anything; it only shows the query is not vacuous.)
Usage: python -I -B nocreation_control.py
"""
import sys

import os as _os, sys as _sys  # artifact: path bootstrap (relative to this file)
_HERE = _os.path.dirname(_os.path.abspath(__file__))
_sys.path[:0] = [_HERE, _os.path.join(_HERE, "..", "lib")]
# artifact: second sys.path entry folded into the bootstrap above
from fractions import Fraction as F  # noqa: E402
from nocreation import no_creation  # noqa: E402
from verify_chain import chain  # noqa: E402
from switchcheck import check  # noqa: E402

g = chain(4)
g["buyers"] = g["buyers"] + [(1, {"b": (2, 1)})]
r, nv = no_creation(g, 4, F(1))
ok_s1, _ = check(g, 4, 1)
print(f"control: A+B>x satisfiable: {r} (expect sat); S1+S2 certified: {ok_s1} (expect False)")
sys.exit(0 if (r == "sat" and not ok_s1) else 1)  # artifact: exit status (control caught)
