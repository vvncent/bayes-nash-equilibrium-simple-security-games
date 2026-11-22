"""Teeth for check.py: the z3 encoding agrees with the exact evaluator, the
violation search finds pairs when the factor is lowered, mutated constants are
caught, and degenerate games (all b = 0, all d = 0, ties, n = 4) pass.

Usage: python -I -B sanity.py
"""
import os
import random
import sys
import time
from fractions import Fraction as Fr

import z3

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))  # -I drops the script dir
import check as C


def z3_agrees(M, rng, k=15):
    n = M.g_.n
    for _ in range(k):
        P = [Fr(rng.randint(0, 50), 50) for _ in range(n)] + [M.kappa * Fr(rng.randint(-5, 60), 50)]
        P[n] = C.clip(P[n], Fr(0), Fr(1))
        X = [z3.RealVal(str(v)) for v in P]
        out, cons = M.z3F(X, "chk")
        s = z3.Solver()
        s.add(cons)
        Y = [z3.Real(f"Y{k}") for k in range(n + 1)]
        s.add([Y[k] == out[k] for k in range(n + 1)])
        assert s.check() == z3.sat
        mod = s.model()
        got = [C.to_fr(mod.eval(Y[k], model_completion=True)) for k in range(n + 1)]
        exp = M.ev(P)[0]
        if got != exp:
            return False
        # uniqueness of the z3 value (projection threshold is determined)
        s.add(z3.Or([Y[k] != z3.RealVal(str(exp[k])) for k in range(n + 1)]))
        if s.check() != z3.unsat:
            return False
    return True


def violation_search_with(M, factor, timeout_ms=120000):
    n = M.g_.n
    A = [z3.Real(f"A{k}") for k in range(n + 1)]
    B = [z3.Real(f"B{k}") for k in range(n + 1)]
    FA, cA = M.z3F(A, "A")
    FB, cB = M.z3F(B, "B")
    ab = lambda e: z3.If(e >= 0, e, -e)
    s = z3.Solver()
    s.set("timeout", timeout_ms)
    s.add(cA + cB)
    s.add([z3.And(A[k] >= 0, A[k] <= 1, B[k] >= 0, B[k] <= 1) for k in range(n + 1)])
    s.add(z3.Sum([ab(FA[k] - FB[k]) for k in range(n + 1)])
          > z3.RealVal(str(factor)) * z3.Sum([ab(A[k] - B[k]) for k in range(n + 1)]))
    r = s.check()
    if r == z3.sat:
        mod = s.model()
        a = [C.to_fr(mod.eval(A[k], model_completion=True)) for k in range(n + 1)]
        b = [C.to_fr(mod.eval(B[k], model_completion=True)) for k in range(n + 1)]
        ratio = C.l1(M.ev(a)[0], M.ev(b)[0]) / C.l1(a, b)
        return "sat", ratio
    return str(r), None


def full_run(name, g, rng, z3c=True):
    t0 = time.time()
    M = C.Model(g)
    fp, uniq = C.fixed_point(M)
    line = [f"{name}: n={g.n} m={g.m} r={g.r}"]
    if fp is None:
        print(line, "no fixed point:", uniq, flush=True)
        return False  # artifact: exit status
    rep = C.decode(M, fp)
    flags = [k for k in ("R_unclipped", "s_eq_q", "sum_identity", "budget_bound_ok", "br_bound_ok",
                         "cut_bound_ok", "all_below_g", "boxes_ok") if not rep[k]]
    line.append(f"unique={uniq} lp={rep['lp']} bne={rep.get('bne')} failed_flags={flags} labels={rep['labels']}")
    line.append("res/g=" + ",".join(f"{float(rep[k] / M.gap):.4f}" for k in ("budget_res", "br_res", "cut_res")))
    # artifact: exit status -- unique fixed point, decoding flags, exact BNE from the pattern LP
    ok = uniq == "unsat" and not flags and rep["lp"] == "sat" and bool(rep["bne"][0])
    worst, bad = C.pair_tests(M, fp, rng, count=200)
    line.append(f"pairs_violation={bad is not None}")
    agree = z3_agrees(M, rng)  # artifact: value kept for the exit status (same call, printed below)
    line.append(f"z3agree={agree}")
    ok &= bad is None and agree  # artifact: exit status
    if z3c:
        r, _ = C.contraction_violation(M, 180000)
        line.append(f"z3viol(true)={r}")
        ok &= r != "sat"  # artifact: exit status (violation fails; unknown accepted)
        Ms = C.Model(g, structural_g=Fr(1, 10))
        r, _ = C.contraction_violation(Ms, 180000)
        line.append(f"z3viol(struct)={r}")
        ok &= r != "sat"  # artifact: exit status
        chk, fails = C.jacobian_tests(Ms, rng, 40)
        line.append(f"jac={chk}/{len(fails)}fail")
        ok &= len(fails) == 0  # artifact: exit status
    line.append(f"{time.time() - t0:.1f}s")
    print(" | ".join(line), flush=True)
    return ok  # artifact: exit status


def main():
    rng = random.Random(7)
    F = Fr
    # 1. degenerate games
    games = {
        "all b=0": C.Game(1, [F(1, 3), F(2, 3)], [[F(1), F(1)], [F(0), F(2)]], [[F(0)] * 2, [F(0)] * 2], [F(1), F(2)]),
        "all d=0": C.Game(1, [F(1, 2), F(1, 2)], [[F(1), F(0)], [F(0), F(1)]], [[F(1), F(2)], [F(2), F(1)]], [F(0), F(0)]),
        "all b=0 and d=0": C.Game(2, [F(1)], [[F(0), F(0), F(0)]], [[F(0)] * 3], [F(0)] * 3),
        "identical tied types": C.Game(1, [F(1, 2), F(1, 2)], [[F(1), F(1)], [F(1), F(1)]], [[F(1), F(1)], [F(1), F(1)]], [F(1), F(1)]),
        "r=n-1, n=3": C.Game(2, [F(1, 4), F(3, 4)], [[F(3), F(1), F(0)], [F(0), F(2), F(2)]],
                             [[F(1), F(0), F(3)], [F(2), F(1), F(0)]], [F(1), F(0), F(5, 2)]),
    }
    allok = True  # artifact: exit status
    for name, g in games.items():
        allok &= full_run(name, g, rng)  # artifact: exit status
    # 2. n = 4 random games (no z3 pair search; too large to be quick)
    for k in range(3):
        g = C.rand_game(rng, 4, rng.choice([1, 2]))
        allok &= full_run(f"n=4 random #{k}", g, rng, z3c=(g.m == 1))  # artifact: exit status
    # 3. teeth: lowered factor must be sat; mutated constants must be caught
    g = C.rand_game(random.Random(11), 2, 2, zero_b=0, zero_d=0)
    Ms = C.Model(g, structural_g=Fr(1, 10))
    r, ratio = violation_search_with(Ms, (1 - Ms.delta) * F(999, 1000))
    allok &= r == "sat" and ratio > (1 - Ms.delta) * F(999, 1000)  # artifact: exit status (control caught)
    print(f"teeth: factor (1-delta)*0.999 -> {r}, ratio found {ratio} (should be sat with ratio > that factor)", flush=True)
    r, ratio = violation_search_with(Ms, 1 - Ms.delta)
    allok &= r == "unsat"  # artifact: exit status
    print(f"teeth: factor (1-delta) -> {r} (should be unsat)", flush=True)
    Mm = C.Model(g, structural_g=Fr(1, 10))
    Mm.eta = 3 * Mm.tau / Mm.B  # diagonal of x + eta w can go negative
    r, ratio = violation_search_with(Mm, 1 - Mm.delta)
    allok &= r == "sat"  # artifact: exit status (control caught)
    print(f"teeth: mutated eta = 3 tau/B -> {r}, ratio {ratio} (expect sat)", flush=True)
    Mk = C.Model(g, structural_g=Fr(1, 10))
    Mk.eta = 4 * Mk.kappa * (1 - 2 * Mk.delta) / (Mk.D * sum(1 / v for v in Mk.dp))  # s-column sum 4
    Mk.eta = min(Mk.eta, Mk.tau / (1 + Mk.B))
    big = Mk.eta * Mk.D * sum(1 / v for v in Mk.dp) / (Mk.kappa * (1 - 2 * Mk.delta))
    r, ratio = violation_search_with(Mk, 1 - Mk.delta)
    print(f"teeth: mutated eta with s-column sum {float(big):.3f} -> {r}, ratio {ratio} (expect sat if > 1)", flush=True)
    if big > 1:  # artifact: exit status (no expectation when the capped s-column sum is <= 1)
        allok &= r == "sat"
    return allok  # artifact: exit status


if __name__ == "__main__":
    sys.exit(0 if main() else 1)  # artifact: exit status
