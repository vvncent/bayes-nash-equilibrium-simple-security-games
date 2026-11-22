"""Market-level end-to-end check with the referee's independent composer (referee_lib.compose):
every equilibrium of the composed M1 market has terminal inflows (1 on run's terminal, 0 other).
Controls: 'swap' must be caught on every discriminating instance.
Reproduce: $PY -I -B verify_market_e2e.py 3 20
"""
import os, sys, time
import os as _os, sys as _sys  # artifact: path bootstrap (relative to this file)
_HERE = _os.path.dirname(_os.path.abspath(__file__))
_sys.path[:0] = [_HERE, _os.path.join(_HERE, "..", "lib")]
import z3
from referee_lib import discriminating, compose, market_eq, terminal_sources

n, count = int(sys.argv[1]), int(sys.argv[2])
inst = discriminating(n)
step = max(1, len(inst) // count)
sel = inst[::step][:count]
ok_all, caught_all = True, True
t0 = time.time()
for st, succ, want in sel:
    other = "no" if want == "yes" else "yes"
    res = {}
    for swap in (False, True):
        goods, buyers = compose(succ, 0, n, swap=swap)
        s = z3.Solver()
        P, fl = market_eq(goods, buyers, s)
        inflow = lambda t: z3.Sum([fl[(b, f"T{t}")] for b in terminal_sources(buyers, t)])
        ex = s.check()
        s.add(z3.Or(inflow(want) != 1, inflow(other) != 0))
        res[swap] = (ex, s.check())
    ok = res[False] == (z3.sat, z3.unsat)
    caught = res[True][1] == z3.sat
    ok_all &= ok; caught_all &= caught
    print(f"succ={succ} run->{want} ({st} steps): correct {'OK' if ok else 'FAIL'}; swap {'caught' if caught else 'NOT caught'}", flush=True)
print(f"n={n}: {len(sel)} of {len(inst)} discriminating instances; correct OK on all: {ok_all}; swap caught on all: {caught_all} ({time.time()-t0:.0f}s)")
sys.exit(0 if (ok_all and caught_all) else 1)  # artifact: exit status
