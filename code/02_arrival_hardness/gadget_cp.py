"""Referee variant of twocopy_gadget.gadget with free c_p (buyer s's mass = capacity of p = c_p),
free eps, H, w and an optional M override. Verdicts come from the unmodified exact verifier
switchcheck.check. For every failing configuration the first failing piece is re-solved with the
same constraints (copied from switchcheck.check) to extract a z3 model, and that model is
re-verified as an M1 gadget equilibrium in exact Fraction arithmetic, independently of z3.

Usage: gadget_cp.py OUT.jsonl WORKERS m1 [m2 ...]
"""
import json
import os
import sys
import time
from fractions import Fraction as F
from multiprocessing import Pool

import os as _os, sys as _sys  # artifact: path bootstrap (relative to this file)
_HERE = _os.path.dirname(_os.path.abspath(__file__))
_sys.path[:0] = [_HERE, _os.path.join(_HERE, "..", "lib")]
import z3  # noqa: E402
from switchcheck import Q, check, equilibrium, h  # noqa: E402


def ds_arcs(m, base, src, sink, prefix):  # copied from twocopy_gadget.ds_arcs
    def S(k):
        return src if k == m else f"{prefix}s{k}"

    def T(k):
        return sink if k == m else f"{prefix}t{k}"

    arcs = [(S(0), T(0), 1, 0)]
    for k in range(1, m + 1):
        c, w = 2 ** (k - 1), base ** k
        arcs += [(S(k), S(k - 1), c, 0), (T(k - 1), T(k), c, 0),
                 (S(k), T(k - 1), c, w), (S(k - 1), T(k), c, w)]
    return arcs


def gadget_cp(m, base=3, eps=3, H=1, w=1, cp=None, M=None):
    """Same construction as twocopy_gadget.gadget; cp defaults to 2K and M to the original rule."""
    K = 2 ** (m + 1)
    arcs = ds_arcs(m, base, "s", "a", "A") + ds_arcs(m, base, "s", "b", "B")
    if M is None:
        maxcost = sum(c * cost for (_, _, c, cost) in arcs) + eps + H + 10
        M = 4 * maxcost
    Mp = M + 1
    lam = F(Mp, 1) / w
    cp = 2 * K if cp is None else cp
    goods, out_of, into = {}, {}, {}
    for i, (u, v, c, cost) in enumerate(arcs):
        g = f"e{i}"
        goods[g] = c
        out_of.setdefault(u, []).append((g, cost))
        into.setdefault(v, []).append((g, c))
    buyers = []
    for v in sorted(set(out_of) | set(into)):
        opts = {}
        if v == "s":
            mass = cp
            opts["p"] = (Mp, lam)
            for g, cost in out_of[v]:
                opts[g] = (M - cost, 1)
        elif v in ("a", "b"):
            mass = sum(c for _, c in into[v])
            for g, _ in into[v]:
                opts[g] = (M + H, 1)
            opts[v] = (M if v == "a" else M - eps, 1)
        else:
            mass = sum(c for _, c in into[v])
            for g, cost in out_of.get(v, []):
                opts[g] = (M - cost, 1)
            for g, _ in into[v]:
                opts[g] = (M, 1)
        buyers.append((mass, opts))
    return {"cp": cp, "goods": goods, "buyers": buyers}, K, F(w)


def frac(model, var):
    val = model.eval(var, model_completion=True)
    return F(val.as_fraction())


def witness(g, K, U, lo, hi):
    """Re-solve one failing piece exactly as switchcheck.check does; return the violating model
    re-verified in exact rationals, or None if the piece fails only by vacuity."""
    U = F(U)
    s = z3.Solver()
    x, Pa, Pb = z3.Real("x"), z3.Real("Pa"), z3.Real("Pb")
    s.add(x >= Q(lo), (x <= Q(hi)) if lo < K else (x < Q(hi)), Pa >= 0, Pa <= Q(U), Pb >= 0, Pb <= Q(U))
    A, B, Pp = equilibrium(g, x, Pa, Pb, s)
    if lo < K:
        z = lo // 2
        if lo % 2 == 0:
            H0, H1 = Q(z) + (x - Q(lo)), Q(z)
        else:
            H0, H1 = Q(z + 1), Q(z) + (x - Q(lo))
        bad = z3.Or(A != H0, B != H1, Pp > Q(U))
    else:
        bad = z3.Or(A < Q(F(K, 2)), B < Q(F(K, 2)), A + B > x, Pp > Q(U))
    s.add(bad)
    if s.check() != z3.sat:
        return None
    mo = s.model()
    X, PA, PB = frac(mo, x), frac(mo, Pa), frac(mo, Pb)
    # independent exact re-verification of the M1 gadget-equilibrium conditions
    goods = dict(g["goods"])
    price = {j: frac(mo, z3.Real(f"P_{j}")) for j in list(goods) + ["p"]}
    price["a"], price["b"] = PA, PB
    load = {j: F(0) for j in list(goods) + ["p", "a", "b"]}
    errs = []
    for j in list(goods) + ["p"]:
        if price[j] < 0:
            errs.append(f"negative price {j}")
    for i, (m, edges) in enumerate(g["buyers"]):
        v = frac(mo, z3.Real(f"v_{i}"))
        if v < 0:
            errs.append(f"v_{i}<0")
        rs = F(0)
        for j, (aij, bij) in edges.items():
            f = frac(mo, z3.Real(f"f_{i}_{j}"))
            u = F(aij) - F(bij) * price[j]
            if f < 0 or v < u or (f > 0 and v != u):
                errs.append(f"buyer {i} option {j}")
            rs += f
            load[j] += f
        if rs > m or (v > 0 and rs != m):
            errs.append(f"buyer {i} row")
    for j, c in goods.items():
        if load[j] > c or (price[j] > 0 and load[j] != c):
            errs.append(f"good {j}")
    Lp = load["p"] + X
    if Lp > g["cp"] or (price["p"] > 0 and Lp != g["cp"]):
        errs.append("good p")
    Aw, Bw = load["a"], load["b"]
    if lo < K:
        h0, h1 = h(X)
        viol = Aw != h0 or Bw != h1 or price["p"] > U
        want = f"h0={h0}, h1={h1}"
    else:
        viol = Aw < F(K, 2) or Bw < F(K, 2) or Aw + Bw > X or price["p"] > U
        want = f"A,B >= {F(K, 2)}, A+B <= x"
    return {"x": str(X), "Pa": str(PA), "Pb": str(PB), "A": str(Aw), "B": str(Bw),
            "Pp": str(price["p"]), "want": want, "exact_equilibrium": not errs,
            "exact_violation": bool(viol), "errors": errs[:5]}


def run(cfg):
    t0 = time.time()
    m, eps, H, cp_label, cp = cfg["m"], cfg["eps"], cfg["H"], cfg["cp_label"], cfg["cp"]
    g, K, U = gadget_cp(m, eps=eps, H=H, cp=cp, M=cfg.get("M"))
    ok, res = check(g, K, U)
    bad = [r for r in res if not r[3]]
    viol = [r for r in bad if r[1] == "sat"]
    vac = [r for r in bad if r[2] != "sat"]
    out = dict(cfg, K=K, ok=ok, pieces=len(res), n_bad=len(bad), n_violating=len(viol),
               n_vacuous=len(vac), bad_pieces=[[str(a), str(b)] for (a, b), *_ in bad[:6]])
    if viol:
        (lo, hi) = viol[0][0]
        out["witness"] = witness(g, K, U, lo, hi)
        out["witness_piece"] = [str(lo), str(hi)]
    out["secs"] = round(time.time() - t0, 1)
    return out


def configs(ms):
    cl = []
    for m in ms:
        K = 2 ** (m + 1)
        cps = [(f"d={d}", d * K // 2 + 2) for d in range(1, 7)] + [("2K", 2 * K)]
        for eps in (2, 4, 3, 1, 5):  # in-condition eps first, boundary eps last
            for lab, cp in cps:
                cl.append({"m": m, "eps": eps, "H": 1, "cp_label": lab, "cp": cp})
        # negative controls outside the proof's conditions
        cl.append({"m": m, "eps": 3, "H": 0, "cp_label": "2K", "cp": 2 * K})
    return cl


if __name__ == "__main__":
    outpath, workers, ms = sys.argv[1], int(sys.argv[2]), [int(a) for a in sys.argv[3:]]
    cl = configs(ms)
    allok = True  # artifact: exit status
    with Pool(workers) as pool, open(outpath, "w") as fh:
        for r in pool.imap_unordered(run, cl):
            fh.write(json.dumps(r) + "\n")
            fh.flush()
            tag = "PASS" if r["ok"] else "FAIL"
            print(f"m={r['m']} K={r['K']} eps={r['eps']} H={r['H']} cp={r['cp']}({r['cp_label']}) {tag} "
                  f"bad={r['n_bad']} violating={r['n_violating']} vacuous={r['n_vacuous']} {r['secs']}s"
                  + (f" witness={r['witness']}" if r.get("witness") else ""))
            sys.stdout.flush()
            # artifact: exit status -- in-condition configurations (eps in {2,3,4}, H=1, c_p > K) must
            # PASS; all others (eps in {1,5}, H=0, c_p <= K) must FAIL with an exactly re-verified witness
            inc = r["eps"] in (2, 3, 4) and r["H"] == 1 and r["cp"] > r["K"]
            w = r.get("witness")
            allok &= bool(r["ok"]) if inc else (not r["ok"] and bool(w) and w["exact_equilibrium"]
                                                 and w["exact_violation"])
    sys.exit(0 if allok else 1)  # artifact: exit status
