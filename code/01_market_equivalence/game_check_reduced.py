"""Same checks as game_check.py, with flow variables only on listed (type, target) pairs.

Exactness of the reduction (proved): every unlisted payoff is -2 - x_k <= -2, while every source
row has the outside at -x_o >= -1 and every dedicated or control row has its listed target at
2 - x >= 1. So (i) no BNE puts flow on an unlisted pair, and (ii) a solution of this encoding,
extended by zero flow on unlisted pairs, satisfies every full BNE condition, because each value
is >= -1 > -2 - x_k. The two encodings therefore have the same BNE set.
Usage: game_check_reduced.py instance [eps_gadget]
"""
import sys
import time

import os as _os, sys as _sys; _HERE = _os.path.dirname(_os.path.abspath(__file__)); _sys.path[:0] = [_HERE, _os.path.join(_HERE, "..", "lib")]  # artifact: path bootstrap (relative to this file)
import z3  # noqa: E402
from game_check import INSTANCES, build_game, compose, decoded, inflow, q, run_arrival  # noqa: E402


def encode_bne_reduced(G, s):
    nT, nG, mB = G["nT"], G["nG"], G["mB"]
    x = [z3.Real(f"x{k}") for k in range(nT)]
    s.add(*[xk >= 0 for xk in x])
    s.add(z3.Sum(x) == 1)
    f, v = [], []
    for t, w in enumerate(G["weights"]):
        kind, idx = G["kind"][t]
        if kind == "src":
            listed = [G["gidx"][g] for g in G["buyers"][idx][2]] + [nG + idx, G["out"]]
        elif kind == "ded":
            listed = [idx]
        else:
            listed = [G["ctl"]]
        row = [q(0)] * nT
        vt = z3.Real(f"v{t}")
        for k in listed:
            row[k] = z3.Real(f"f{t}_{k}")
            u = q(G["inter"][t][k]) - q(G["slope"][t][k]) * x[k]
            s.add(row[k] >= 0, vt >= u, z3.Or(row[k] == 0, vt == u))
        s.add(z3.Sum([row[k] for k in listed]) == q(w))
        f.append(row)
        v.append(vt)
    peak = z3.Real("peak")
    for k in range(nT):
        score = z3.Sum([f[t][k] for t in range(len(f))])
        s.add(score <= peak, z3.Or(x[k] == 0, score == peak))
    return x, f, v, peak, 1


def main():
    inst = sys.argv[1]
    geps = int(sys.argv[2]) if len(sys.argv) > 2 else 3
    n, succ, origin, m = INSTANCES[inst]
    want, steps = run_arrival(n, succ, origin)
    other = "no" if want == "yes" else "yes"
    goods, buyers = compose(n, succ, origin, m, eps=geps)
    G = build_game(goods, buyers)
    print(f"[reduced] instance {inst}: succ={succ} m={m} gadget eps={geps} -> run ends at {want}; "
          f"game {len(G['weights'])} types, {G['nT']} targets, U={G['U']} A={G['A']} S={G['S']}")
    sys.stdout.flush()
    s = z3.Solver()
    x, f, v, peak, scale = encode_bne_reduced(G, s)
    P, fm, cond = decoded(G, x, f, v, peak, scale)
    yin, oin = inflow(G, fm, want), inflow(G, fm, other)
    res = []  # artifact: exit status
    for label, extra in (("Q1 BNE exists", None),
                         ("Q2 some BNE decodes to the wrong terminal", z3.Or(yin != 1, oin != 0)),
                         ("Q3 some BNE fails the M1 decoding or the doc's lemmas", z3.Not(z3.And(*cond)))):
        s.push()
        if extra is not None:
            s.add(extra)
        t0 = time.time()
        r = s.check()
        note = ""
        if r == z3.sat:
            mdl = s.model()
            note = f" | inflow({want})={mdl.eval(yin)}, inflow({other})={mdl.eval(oin)}"
        print(f"{label}: {r} ({time.time() - t0:.1f}s){note}")
        sys.stdout.flush()
        s.pop()
        res.append(r)  # artifact: exit status
    # artifact: exit status -- success iff Q1 sat, Q2 unsat, Q3 unsat (README expected output)
    return res == [z3.sat, z3.unsat, z3.unsat]


if __name__ == "__main__":
    sys.exit(0 if main() else 1)  # artifact: exit status
