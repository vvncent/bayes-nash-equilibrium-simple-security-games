"""Referee check of the market-to-game embedding (round2/night/root/one-resource.md, theta = 1).

compose() market -> one-resource Bayesian simple security game, built exactly as the
theorem's table states (identical defender gains: uncovered 0, covered 1), with the market's
own slopes b_ij (1 and lambda) on the source rows. Unlisted (type, target) pairs, including
non-edges of the market, get the doc's unlisted payoff -2 - x_k.

z3 (exact linear real arithmetic) then checks, over EVERY Bayes-Nash equilibrium of the game:
  Q1  a BNE exists;
  Q2  no BNE decodes to the wrong ARRIVAL terminal (decoded inflow 1 on the run's terminal,
      0 on the other, read from non-terminal source rows as in composed_check.terminal_inflow);
  Q3  no BNE fails to decode to an M1 equilibrium (P = S x, V = S v, f = source rows' real flows),
      together with the doc's intermediate claims (x_o = 0, x_h > 0, peak = U, private
      coverage > 0 and private load U).
Usage: game_check.py instance [normalized] [eps_gadget]
  instance: n1 | n2     normalized: 0 = unnormalized weights, 1 = true probabilities
"""
import sys
import time
from fractions import Fraction as F

import os as _os, sys as _sys; _HERE = _os.path.dirname(_os.path.abspath(__file__)); _sys.path[:0] = [_HERE, _os.path.join(_HERE, "..", "lib")]  # artifact: path bootstrap (relative to this file)
import z3  # noqa: E402
from composed_check import compose, run_arrival  # noqa: E402


def q(v):
    v = F(v)
    return z3.RealVal(f"{v.numerator}/{v.denominator}")


def build_game(goods, buyers, eps=F(1), strict=True):
    """The theorem's table with identical gains (theta = 1). strict=False skips the b >= 1 check."""
    gnames = list(goods)
    gidx = {g: k for k, g in enumerate(gnames)}
    mB, nG = len(buyers), len(gnames)
    p = [F(b[1]) for b in buyers]
    c = [F(goods[g]) for g in gnames]
    D = 1 + max(sum(p), max(c))
    U = (2 + 2 / F(eps)) * D
    A = 1 + max(F(0), max(F(a) for (_, _, opts) in buyers for (a, _) in opts.values()))
    S = 1 + (mB + nG) * A
    nT = nG + mB + 2
    out, ctl = nG + mB, nG + mB + 1
    weights, inter, slope, kind = [], [], [], []
    for i, (name, mass, opts) in enumerate(buyers):
        a_row, b_row = [F(-2)] * nT, [F(1)] * nT
        for g, (a, b) in opts.items():
            a_row[gidx[g]], b_row[gidx[g]] = F(a) / S, F(b)
        a_row[nG + i] = A / S
        a_row[out] = F(0)
        weights.append(U + p[i]); inter.append(a_row); slope.append(b_row); kind.append(("src", i))
    for j in range(nG):
        a_row, b_row = [F(-2)] * nT, [F(1)] * nT
        a_row[j] = F(2)
        weights.append(U - c[j]); inter.append(a_row); slope.append(b_row); kind.append(("ded", j))
    a_row, b_row = [F(-2)] * nT, [F(1)] * nT
    a_row[ctl] = F(2)
    weights.append(U); inter.append(a_row); slope.append(b_row); kind.append(("ctl", None))
    gains = [F(1)] * nT
    T = sum(weights)
    probs = [w / T for w in weights]
    # Legality as Conitzer defines the game (arXiv:2610.08796 section 1).
    assert 1 <= nT                                   # r = 1 <= |T|
    assert all(pr > 0 for pr in probs) and sum(probs) == 1
    assert all(g >= 0 for g in gains)                # u1^0 = 0 <= u1^1 = gain
    assert all(b >= 0 for row in slope for b in row)  # u2^0 = a >= u2^1 = a - b
    assert max(weights) / min(weights) <= 1 + eps
    if strict:
        assert all(b >= 1 for row in slope for b in row)  # decoding step x_j <= A/S uses b >= 1
    return dict(gnames=gnames, gidx=gidx, mB=mB, nG=nG, nT=nT, out=out, ctl=ctl, p=p, c=c,
                D=D, U=U, A=A, S=S, T=T, weights=weights, probs=probs, inter=inter,
                slope=slope, gains=gains, kind=kind, buyers=buyers)


def encode_bne(G, s, normalized):
    nT = G["nT"]
    mass = G["probs"] if normalized else G["weights"]
    x = [z3.Real(f"x{k}") for k in range(nT)]
    s.add(*[xk >= 0 for xk in x])
    s.add(z3.Sum(x) == 1)
    f, v = [], []
    for t in range(len(mass)):
        row = [z3.Real(f"f{t}_{k}") for k in range(nT)]
        vt = z3.Real(f"v{t}")
        s.add(z3.Sum(row) == q(mass[t]))
        for k in range(nT):
            u = q(G["inter"][t][k]) - q(G["slope"][t][k]) * x[k]
            s.add(row[k] >= 0, vt >= u, z3.Or(row[k] == 0, vt == u))
        f.append(row)
        v.append(vt)
    peak = z3.Real("peak")
    for k in range(nT):
        score = q(G["gains"][k]) * z3.Sum([f[t][k] for t in range(len(mass))])
        s.add(score <= peak, z3.Or(x[k] == 0, score == peak))
    scale = G["T"] if normalized else F(1)  # factor back to the unnormalized (market) units
    return x, f, v, peak, scale


def decoded(G, x, f, v, peak, scale):
    """Market quantities and the M1 equilibrium conditions on them, plus the doc's lemmas."""
    S, nG, mB, gidx = G["S"], G["nG"], G["mB"], G["gidx"]
    P = [q(S) * x[j] for j in range(nG)]
    V = [q(S) * v[i] for i in range(mB)]
    fm = [[q(scale) * f[i][j] for j in range(nG)] for i in range(mB)]
    cond = []
    for i, (name, mass, opts) in enumerate(G["buyers"]):
        cond.append(V[i] >= 0)
        for j in range(nG):
            g = G["gnames"][j]
            if g in opts:
                a, b = opts[g]
                u = q(a) - q(b) * P[j]
                cond += [V[i] >= u, z3.Or(fm[i][j] == 0, V[i] == u)]
            else:
                cond.append(fm[i][j] == 0)
        rs = z3.Sum(fm[i])
        cond += [rs <= q(mass), z3.Or(V[i] == 0, rs == q(mass))]
    for j in range(nG):
        col = z3.Sum([fm[i][j] for i in range(mB)])
        cond += [col <= q(G["c"][j]), z3.Or(P[j] == 0, col == q(G["c"][j]))]
    cond += [x[G["out"]] == 0, x[G["ctl"]] > 0, q(scale) * peak == q(G["U"])]
    for i in range(mB):
        cond += [x[nG + i] > 0, q(scale) * f[i][nG + i] == q(G["U"])]
    return P, fm, cond


def inflow(G, fm, t):
    j = G["gidx"][f"T{t}"]
    terms = [fm[i][j] for i, b in enumerate(G["buyers"]) if not b[0].startswith("term_")]
    return z3.Sum(terms) if terms else q(0)


INSTANCES = {
    "n1": (1, [("yes", "no")], 0, 1),
    "n2": (2, [(0, 1), ("yes", "no")], 0, 2),
}


def main():
    inst = sys.argv[1]
    normalized = len(sys.argv) > 2 and sys.argv[2] == "1"
    geps = int(sys.argv[3]) if len(sys.argv) > 3 else 3
    n, succ, origin, m = INSTANCES[inst]
    want, steps = run_arrival(n, succ, origin)
    other = "no" if want == "yes" else "yes"
    goods, buyers = compose(n, succ, origin, m, eps=geps)
    G = build_game(goods, buyers)
    print(f"instance {inst}: succ={succ} origin={origin} m={m} gadget eps={geps} -> run ends at "
          f"{want} in {steps} steps")
    print(f"market: {len(buyers)} buyers, {len(goods)} goods; slopes used: "
          f"{sorted(set(F(b) for (_, _, o) in buyers for (_, b) in o.values()))}")
    print(f"game: {len(G['weights'])} types, {G['nT']} targets, 1 resource; U={G['U']} A={G['A']} "
          f"S={G['S']}; probabilities {'(normalized)' if normalized else '(unnormalized weights)'}")
    print(f"prob range: min {min(G['probs'])}, max {max(G['probs'])}")
    sys.stdout.flush()
    s = z3.Solver()
    x, f, v, peak, scale = encode_bne(G, s, normalized)
    P, fm, cond = decoded(G, x, f, v, peak, scale)
    yin, oin = inflow(G, fm, want), inflow(G, fm, other)
    t0 = time.time()
    r1 = s.check()
    extra = ""
    if r1 == z3.sat:
        mdl = s.model()
        extra = (f" | witness: inflow({want})={mdl.eval(yin)}, inflow({other})={mdl.eval(oin)}, "
                 f"P={[str(mdl.eval(Pj)) for Pj in P]}")
    print(f"Q1 BNE exists: {r1} ({time.time() - t0:.1f}s){extra}")
    sys.stdout.flush()
    s.push()
    s.add(z3.Or(yin != 1, oin != 0))
    t0 = time.time()
    r2 = s.check()
    extra = ""
    if r2 == z3.sat:
        mdl = s.model()
        extra = f" | counterexample inflow({want})={mdl.eval(yin)}, inflow({other})={mdl.eval(oin)}"
    print(f"Q2 some BNE decodes to the wrong terminal: {r2} ({time.time() - t0:.1f}s){extra}")
    sys.stdout.flush()
    s.pop()
    s.push()
    s.add(z3.Not(z3.And(*cond)))
    t0 = time.time()
    r3 = s.check()
    print(f"Q3 some BNE fails the M1 decoding or the doc's lemmas: {r3} ({time.time() - t0:.1f}s)")
    s.pop()
    ok = r1 == z3.sat and r2 == z3.unsat and r3 == z3.unsat
    print("RESULT:", "OK" if ok else "NOT OK")
    # artifact: exit status -- eps<0 (swapped gadget) is the negative control: it passes iff it is
    # caught, i.e. Q2 sat (a BNE loads the wrong terminal) and Q3 unsat (README 01.embed_n1_control)
    if geps < 0:
        return r2 == z3.sat and r3 == z3.unsat
    return ok


if __name__ == "__main__":
    sys.exit(0 if main() else 1)  # artifact: exit status
