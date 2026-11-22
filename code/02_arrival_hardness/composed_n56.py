"""Composed-market check at n=5,6 with the book's construction (independent builder eh_lib).
For each instance: (1) SAT: an equilibrium exists (model is re-checked: decoded x is a fixed point
and terminal loads are right), (2) UNSAT: no equilibrium has non-terminal load != 1 on the run's
terminal or != 0 on the other.  Optional 'swap' negative control (ports exchanged) must give SAT.
Reproduce: .venv/bin/python -I composed_n56.py <instance-name> [swap]
"""
import sys, time, os
from fractions import Fraction as F
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import z3
from eh_lib import compose, eq_constraints, run, preprocess, h0, h1, Q

Y, N = "yes", "no"
INST = {
    "n2_fig": ({0: (1, 0), 1: (Y, N)}, 0),
    "n3_t": ({0: (1, 0), 1: (2, 1), 2: (N, Y)}, 0),
    # n=5. discriminating, self-loops, coincident successors, origin with in-edges
    "n5_selfloop_chain": ({0: (1, 0), 1: (2, 1), 2: (3, 0), 3: (4, 2), 4: (Y, N)}, 0),
    "n5_coincident": ({0: (1, 1), 1: (2, 0), 2: (3, 3), 3: (0, 4), 4: (N, Y)}, 0),
    "n5_bothterm_same": ({0: (1, 2), 1: (Y, Y), 2: (3, 0), 3: (N, N), 4: (4, Y)}, 0),
    "n5_counter": ({0: (1, Y), 1: (2, 0), 2: (3, 0), 3: (4, 0), 4: (N, 0)}, 0),
    "n5_unreach_cycle": ({0: (1, 0), 1: (N, Y), 2: (3, 3), 3: (2, Y), 4: (2, 4)}, 0),
    "n5_deleted": ({0: (1, 2), 1: (0, Y), 2: (3, 3), 3: (2, 2), 4: (0, N)}, 0),
    # n=6
    "n6_counter": ({0: (1, Y), 1: (2, 0), 2: (3, 0), 3: (4, 0), 4: (5, 0), 5: (N, 0)}, 0),
    "n6_mixed": ({0: (0, 1), 1: (2, 2), 2: (0, 3), 3: (4, 3), 4: (5, 1), 5: (Y, N)}, 0),
}


def term_load(fl, t):
    xs = [f for (b, j), f in fl.items() if j == f"T_{t}" and not b.startswith("term_")]
    return z3.Sum(xs) if xs else Q(0)


def val(md, e):
    r = md.eval(e, model_completion=True)
    return F(r.numerator_as_long(), r.denominator_as_long())


def main():
    name = sys.argv[1]
    swap = len(sys.argv) > 2 and sys.argv[2] == "swap"
    succ0, o0 = INST[name]
    n = len(succ0)
    want, steps, term = run(succ0, o0)
    succ, o = preprocess(succ0, o0)
    if swap:
        succ = {v: (b, a) for v, (a, b) in succ.items()}
    other = N if want == Y else Y
    # discriminating?  run with switches started at s1
    alt, _, _ = run({v: (b, a) for v, (a, b) in succ0.items()}, o0)
    goods, buyers = compose(succ, o, n)
    s = z3.Solver()
    P, fl, vv, load = eq_constraints(goods, buyers, s)
    yw, yo = term_load(fl, want), term_load(fl, other)
    t0 = time.time()
    r1 = s.check()
    okfp = None  # artifact: exit status
    msg = [f"{name}{' SWAP' if swap else ''}: n={n} run->{want} ({steps} steps; s1-start run->{alt}) "
           f"kept={sorted(succ)} buyers={len(buyers)} goods={len(goods)}",
           f"  exists: {r1} ({time.time()-t0:.1f}s)"]
    if r1 == z3.sat:
        md = s.model()
        x = {}
        for v in succ:
            x[v] = sum(val(md, f) for (b, j), f in fl.items()
                       if j == f"p_{v}" and not b == f"g{v}.s")
        port = lambda t: f"T_{t}" if t in (Y, N) else f"p_{t}"
        okfp = all(x[v] == (1 if v == o else 0) + sum(h0(x[u]) for u in succ if succ[u][0] == v)
                   + sum(h1(x[u]) for u in succ if succ[u][1] == v) for v in succ)
        msg.append(f"  model: x={ {v: str(x[v]) for v in x} } fixed point: {okfp}; "
                   f"load(want)={val(md, yw)} load(other)={val(md, yo)}")
    t0 = time.time()
    s.add(z3.Or(yw != 1, yo != 0))
    r2 = s.check()
    msg.append(f"  some equilibrium decodes wrongly: {r2} ({time.time()-t0:.1f}s)")
    if r2 == z3.sat:
        md = s.model()
        msg.append(f"  WITNESS load(want)={val(md, yw)} load(other)={val(md, yo)}")
    verdict = (r1 == z3.sat and r2 == z3.unsat) if not swap else (r2 == z3.sat)
    msg.append("  " + ("OK" if verdict else ("FAIL" if not swap else "control NOT caught")))
    print("\n".join(msg), flush=True)
    # artifact: exit status -- printed verdict OK; for the non-swap check the existence model must
    # also be a fixed point (docstring: model re-checked); swap control passes iff caught (r2 sat)
    return verdict and (swap or okfp is True)


if __name__ == "__main__":
    sys.exit(0 if main() else 1)  # artifact: exit status
