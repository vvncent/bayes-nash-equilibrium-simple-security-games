"""Checks supporting the all-K proof of the two-copy gadget (referee-report.md s A).
(1) Lemma I (increment recursion) against direct exact min-cost flow (integer SSP) for m <= 6.
(2) The recursion's consequences for m <= 40: increments strictly increasing, delta_1 = 0,
    max = 2*3^m (m>=1), min gap >= 6 -- i.e. the hypotheses used in Lemma I's induction, checked to
    large m only as a sanity check of the algebra (the proof is for all m).
(3) Step 1 (LP structure) independently: z3 proves, for m = 1..3 and every x in [0, cp), every box
    price pair and every equilibrium: all arc goods full, all non-source buyers full, source buys
    exactly cp - x of p, and source out-flow = min(x, K).
Reproduce: $PY -I -B verify_gadget_allK.py
"""
import os, sys
import os as _os, sys as _sys  # artifact: path bootstrap (relative to this file)
_HERE = _os.path.dirname(_os.path.abspath(__file__))
_sys.path[:0] = [_HERE, _os.path.join(_HERE, "..", "lib")]
# artifact: second sys.path entry folded into the bootstrap above
from fractions import Fraction as F
import z3
from ds_twosink import mcf
from referee_lib import ds_arcs, Q


def inc_recursion(m):
    d = [0]
    for k in range(1, m + 1):
        d = d + [2 * 3 ** k - e for e in reversed(d)]
    return d


def inc_direct(m):
    arcs = ds_arcs(m, "s", "t", "")
    names = sorted({u for a in arcs for u in a[:2]})
    ix = {v: i for i, v in enumerate(names)}
    ia = [(ix[u], ix[v], c, w) for (u, v, c, w) in arcs]
    Fv = [mcf(len(names), ia, ix["s"], {ix["t"]: y}) for y in range(2 ** m + 1)]
    return [Fv[i + 1] - Fv[i] for i in range(2 ** m)]


ok = True
for m in range(0, 7):
    a, b = inc_recursion(m), inc_direct(m)
    ok &= a == b
    print(f"(1) m={m}: recursion == direct SSP increments: {a == b}")
for m in range(1, 41):
    d = inc_recursion(m) if m <= 20 else None
    if d is None:
        break
    gaps = [d[i + 1] - d[i] for i in range(len(d) - 1)]
    c = d[0] == 0 and max(d) == 2 * 3 ** m and min(gaps) >= 6 and all(g > 0 for g in gaps)
    ok &= c
print(f"(2) m=1..20: strictly increasing, delta_1=0, max=2*3^m, min gap>=6: {ok}")


def gadget(m, eps=3, H=1, w=1):
    K = 2 ** (m + 1)
    core = ds_arcs(m, "s", "a", "A") + ds_arcs(m, "s", "b", "B")
    M = 4 * (sum(c * cost for (_, _, c, cost) in core) + eps + H + 10)
    lam = F(M + 1) / w
    cp = 2 * K
    goods, outs, ins = {}, {}, {}
    for i, (u, v, c, cost) in enumerate(core):
        goods[f"e{i}"] = c
        outs.setdefault(u, []).append((f"e{i}", cost))
        ins.setdefault(v, []).append((f"e{i}", c))
    buyers = []
    for v in sorted(set(outs) | set(ins)):
        o = {}
        if v == "s":
            mass = cp; o["p"] = (M + 1, lam)
            for g, cost in outs[v]: o[g] = (M - cost, 1)
        elif v in ("a", "b"):
            mass = sum(c for _, c in ins[v])
            for g, _ in ins[v]: o[g] = (M + H, 1)
            o["PORT" + v] = (M if v == "a" else M - eps, 1)
        else:
            mass = sum(c for _, c in ins[v])
            for g, cost in outs.get(v, []): o[g] = (M - cost, 1)
            for g, _ in ins[v]: o[g] = (M, 1)
        buyers.append((v, mass, o))
    return goods, buyers, cp, K


for m in (1, 2, 3):
    goods, buyers, cp, K = gadget(m)
    s = z3.Solver()
    x, Pa, Pb = z3.Reals("x Pa Pb")
    s.add(x >= 0, x < cp, Pa >= 0, Pa <= 1, Pb >= 0, Pb <= 1)
    P = {j: z3.Real(f"P_{j}") for j in list(goods) + ["p"]}
    P["PORTa"], P["PORTb"] = Pa, Pb
    load = {j: [] for j in P}
    rows, fl = {}, {}
    for (nm, mass, o) in buyers:
        v = z3.Real(f"v_{nm}"); s.add(v >= 0); r = []
        for j, (a, b) in o.items():
            f = z3.Real(f"f_{nm}_{j}"); u = Q(a) - Q(b) * P[j]
            s.add(f >= 0, v >= u, z3.Or(f == 0, v == u)); r.append(f); load[j].append(f); fl[(nm, j)] = f
        s.add(z3.Sum(r) <= Q(mass), z3.Or(v == 0, z3.Sum(r) == Q(mass))); rows[nm] = (z3.Sum(r), mass)
    for j in list(goods) + ["p"]:
        s.add(P[j] >= 0)
        L = z3.Sum(load[j]) + (x if j == "p" else 0)
        c = goods[j] if j != "p" else cp
        s.add(L <= Q(c), z3.Or(P[j] == 0, L == Q(c)))
    srcout = z3.Sum([fl[("s", g)] for g in buyers[[b[0] for b in buyers].index("s")][2] if g != "p"])
    bad = z3.Or(*[z3.Sum(load[j]) != Q(goods[j]) for j in goods],
                *[rows[nm][0] != Q(rows[nm][1]) for nm in rows if nm != "s"],
                fl[("s", "p")] != Q(cp) - x,
                srcout != z3.If(x <= K, x, Q(K)))
    s.push(); s.add(bad); r = s.check(); s.pop()
    ok &= r == z3.unsat
    print(f"(3) m={m} K={K}: equilibrium violating Step-1 structure: {r}")
print("ALL OK" if ok else "FAILURES")
sys.exit(0 if ok else 1)  # artifact: exit status
