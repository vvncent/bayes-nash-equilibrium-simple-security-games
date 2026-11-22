"""End-to-end exact run: ARRIVAL -> composed M1 market (compose() of composed_check.py, imported
unchanged) -> LCP(q, M) of monitor findings 'Regular pass 16' -> P-LCP(q, M + delta I) with the
reduction's explicit delta = 1/(2 ceil(U) (dC)^d) -> exact unique solution -> decoder (support + one
exact LP, system (1)) -> direct check of every M1 condition -> load on the two terminal goods ->
compare with run_arrival.

Naming: 'geps' is the gadget parameter epsilon of compose() (3 correct, -3 swapped);
'delta' is the LCP perturbation epsilon of the reduction.

All arithmetic is exact (Fractions, z3 QF_LRA rationals). Nothing is rounded.
Usage: e2e.py n1 | n2 [start count] | n3 [count] | ctrl
"""
import itertools
import os
import sys
import time
from fractions import Fraction as F
from math import ceil, lcm

sys.set_int_max_str_digits(0)
import os as _os, sys as _sys  # artifact: path bootstrap (relative to this file)
_HERE = _os.path.dirname(_os.path.abspath(__file__))
_sys.path[:0] = [_HERE, _os.path.join(_HERE, "..", "lib")]
import z3  # noqa: E402
from composed_check import compose, run_arrival, reach, reaches_terminal  # noqa: E402


def zr(x):
    x = F(x)
    return z3.RealVal(f"{x.numerator}/{x.denominator}")


def build_lcp(goods, buyers):
    """z = (f_e for every option e, u_i for every buyer, P_j for every good); w = q + M z with
    w_e = u_i + b_e P_j - a_e, w_i = p_i - sum_e f_e, w_j = c_j - sum_e f_e. Sparse rows."""
    gnames = list(goods)
    gidx = {g: k for k, g in enumerate(gnames)}
    edges = []
    for i, (_, _, opts) in enumerate(buyers):
        for g, (a, b) in opts.items():
            edges.append((i, g, F(a), F(b)))
    E, m, n = len(edges), len(buyers), len(gnames)
    N = E + m + n
    rows = [dict() for _ in range(N)]
    q = [F(0)] * N
    for e, (i, g, a, b) in enumerate(edges):
        j = gidx[g]
        rows[e][E + i] = F(1)
        rows[e][E + m + j] = b
        q[e] = -a
        rows[E + i][e] = F(-1)
        rows[E + m + j][e] = F(-1)
    for i, (_, mass, _) in enumerate(buyers):
        q[E + i] = F(mass)
    for j, g in enumerate(gnames):
        q[E + m + j] = F(goods[g])
    return rows, q, edges, gnames


def delta_of(rows, q, buyers, edges):
    """The findings' explicit perturbation, computed from its definition."""
    N = len(q)
    entries = [x for r in rows for x in r.values()] + q  # zero entries have denominator 1
    D = lcm(*(x.denominator for x in entries))
    C = D * max([F(1)] + [abs(x) for x in entries])
    assert C.denominator == 1
    C = int(C)
    d = N + 1
    H = max([F(0)] + [a for (_, _, a, _) in edges])
    bmin = min(b for (_, _, _, b) in edges)
    U = 1 + max(max(F(mass) for (_, mass, _) in buyers) + H, H / bmin)
    return F(1, 2 * ceil(U) * (d * C) ** d), U, d, C, D


def wvec(rows, q, z, diag=F(0)):
    return [q[k] + sum(v * z[l] for l, v in rows[k].items()) + diag * z[k] for k in range(len(q))]


def solve_plcp(rows, q, delta, timeout_ms=None):
    """Exact solution of LCP(q, M + delta I) by z3 over the complementarity conditions."""
    N = len(q)
    z = [z3.Real(f"z{k}") for k in range(N)]
    s = z3.SolverFor("QF_LRA")
    if timeout_ms:
        s.set("timeout", timeout_ms)
    dz = zr(delta)
    for k in range(N):
        w = zr(q[k]) + z3.Sum([zr(v) * z[l] for l, v in rows[k].items()]) + dz * z[k]
        s.add(z[k] >= 0, w >= 0, z3.Or(z[k] == 0, w == 0))
    r = s.check()
    if r != z3.sat:
        return None, str(r)
    mdl = s.model()
    return [mdl.eval(x, model_completion=True).as_fraction() for x in z], "sat"


def decode(rows, q, support, extra=None):
    """System (1): z >= 0, z_notA = 0, q + M z >= 0, (q + M z)_A = 0. One exact LP (z3 QF_LRA)."""
    N = len(q)
    z = [z3.Real(f"y{k}") for k in range(N)]
    s = z3.SolverFor("QF_LRA")
    for k in range(N):
        w = zr(q[k]) + z3.Sum([zr(v) * z[l] for l, v in rows[k].items()])
        s.add(z[k] >= 0, w >= 0)
        s.add(w == 0 if k in support else z[k] == 0)
    if extra is not None:
        s.add(extra(z))
    r = s.check()
    if r != z3.sat:
        return None, str(r)
    mdl = s.model()
    return [mdl.eval(x, model_completion=True).as_fraction() for x in z], "sat"


def unpack(z, buyers, edges, gnames):
    E, m = len(edges), len(buyers)
    flows = {(i, g): z[e] for e, (i, g, _, _) in enumerate(edges)}
    util = z[E:E + m]
    price = {g: z[E + m + j] for j, g in enumerate(gnames)}
    return flows, util, price


def m1_violations(goods, buyers, flows, util, price):
    """Every M1 condition, checked from the market itself (not through the LCP)."""
    bad = []
    load = {g: F(0) for g in goods}
    for g in goods:
        if price[g] < 0:
            bad.append(("price<0", g))
    for i, (name, mass, opts) in enumerate(buyers):
        v = util[i]
        if v < 0:
            bad.append(("util<0", name))
        row = F(0)
        for g, (a, b) in opts.items():
            f = flows[(i, g)]
            pay = F(a) - F(b) * price[g]
            if f < 0:
                bad.append(("flow<0", name, g))
            if v < pay:
                bad.append(("not best reply", name, g))
            if f > 0 and v != pay:
                bad.append(("flow on non-tight option", name, g))
            row += f
            load[g] += f
        if row > mass:
            bad.append(("over mass", name))
        if v > 0 and row != mass:
            bad.append(("positive utility, mass not full", name))
    for g, c in goods.items():
        if load[g] > c:
            bad.append(("over capacity", g))
        if price[g] > 0 and load[g] != c:
            bad.append(("positive price, good not full", g))
    return bad


def terminal_loads(buyers, flows):
    """Load on T_yes / T_no from the gadget buyers (the terminal buyer's own fill excluded), and total."""
    gad = {"yes": F(0), "no": F(0)}
    tot = {"yes": F(0), "no": F(0)}
    for (i, g), f in flows.items():
        for t in ("yes", "no"):
            if g == f"T{t}":
                tot[t] += f
                if not buyers[i][0].startswith("term_"):
                    gad[t] += f
    return gad, tot


def bits(x):
    x = F(x)
    return max(abs(x.numerator).bit_length(), x.denominator.bit_length())


def pipeline(n, succ, origin=0, geps=3, delta_override=None, check_all_decodes=True, timeout_ms=None,
             solver="cert"):
    t0 = time.time()
    goods, buyers = compose(n, list(succ), origin, n, eps=geps)
    rows, q, edges, gnames = build_lcp(goods, buyers)
    N = len(q)
    delta, U, d, C, D = delta_of(rows, q, buyers, edges)
    if delta_override is not None:
        delta = delta_override
    t1 = time.time()
    info = {}
    if solver == "z3":
        z, st = solve_plcp(rows, q, delta, timeout_ms)
    else:
        from cert import exact_plcp
        z, info = exact_plcp(rows, q, delta, delta_guess=GUESS)
        st = "certified basis"
    t2 = time.time()
    res = dict(n=n, succ=list(succ), geps=geps, N=N, buyers=len(buyers), goods=len(goods), E=len(edges),
               delta_bits=delta.denominator.bit_length(), U=U, d=d, C=C, D=D, plcp=st, solver_info=info)
    if z is None:
        res.update(ok=False, why="P-LCP not solved: " + st, t_build=t1 - t0, t_plcp=t2 - t1)
        return res
    # independent exact verification of the P-LCP solution (Fractions, not z3's word)
    w = wvec(rows, q, z, delta)
    plcp_ok = all(x >= 0 for x in z) and all(x >= 0 for x in w) and all(a * b == 0 for a, b in zip(z, w))
    support = {k for k, x in enumerate(z) if x > 0}
    zb = max(bits(x) for x in z)
    fz, uz, pz = unpack(z, buyers, edges, gnames)
    gz, _ = terminal_loads(buyers, fz)
    y, dst = decode(rows, q, support)
    t3 = time.time()
    res.update(plcp_verified=plcp_ok, support=len(support), zbits=zb, zmax=float(max(z)),
               zbound_ok=max(z) <= U - 1, perturbed_terminal_inflow={k: float(v) for k, v in gz.items()},
               decode=dst, t_build=t1 - t0, t_plcp=t2 - t1, t_decode=t3 - t2)
    if y is None:
        res.update(ok=False, why="system (1) infeasible")
        return res
    lcp0 = wvec(rows, q, y)
    lcp_ok = all(x >= 0 for x in y) and all(x >= 0 for x in lcp0) and all(a * b == 0 for a, b in zip(y, lcp0))
    fl, ut, pr = unpack(y, buyers, edges, gnames)
    viol = m1_violations(goods, buyers, fl, ut, pr)
    gad, tot = terminal_loads(buyers, fl)
    want, steps = run_arrival(n, list(succ), origin)
    flipped, _ = run_arrival(n, [(b, a) for (a, b) in succ], origin)
    other = "no" if want == "yes" else "yes"
    decoded = [t for t in ("yes", "no") if gad[t] == 1 and gad["no" if t == "yes" else "yes"] == 0]
    pos = [t for t in ("yes", "no") if gad[t] > 0]
    res["positive_load_terminal"] = pos[0] if len(pos) == 1 else str(pos)
    decoded = decoded[0] if decoded else f"none (yes={gad['yes']}, no={gad['no']})"
    res.update(lcp_ok=lcp_ok, m1_violations=viol[:5], n_viol=len(viol),
               load_yes=gad["yes"], load_no=gad["no"], total_yes=tot["yes"], total_no=tot["no"],
               cap_yes=goods["Tyes"], cap_no=goods["Tno"],
               price_yes=pr["Tyes"], price_no=pr["Tno"],
               decoded=decoded, run=want, steps=steps, flipped_run=flipped)
    # adversarial: can ANY feasible point of system (1) decode differently?
    if check_all_decodes:
        E, m = len(edges), len(buyers)

        def inflow(zv, t):
            ks = [e for e, (i, g, _, _) in enumerate(edges) if g == f"T{t}" and not buyers[i][0].startswith("term_")]
            return z3.Sum([zv[k] for k in ks]) if ks else z3.RealVal(0)

        alt, ast = decode(rows, q, support, extra=lambda zv: z3.Or(inflow(zv, "yes") != zr(gad["yes"]),
                                                                    inflow(zv, "no") != zr(gad["no"])))
        res.update(alt_decode=ast)
    res["t_total"] = time.time() - t0
    res["ok"] = plcp_ok and lcp_ok and not viol
    return res


def discriminating(n):
    T = list(range(n)) + ["yes", "no"]
    inst = []
    for succ in itertools.product(itertools.product(T, T), repeat=n):
        if not reaches_terminal(n, succ) or reach(n, succ, 0) != {"yes", "no"}:
            continue
        want, steps = run_arrival(n, succ, 0)
        alt, _ = run_arrival(n, [(b, a) for (a, b) in succ], 0)
        if alt == want:
            continue
        inst.append((steps, list(succ)))
    inst.sort(key=lambda t: t[0], reverse=True)
    return inst


def show(r):
    keys = ["n", "succ", "geps", "N", "buyers", "goods", "E", "delta_bits", "plcp", "solver_info", "plcp_verified", "support",
            "zbits", "zbound_ok", "perturbed_terminal_inflow", "decode", "lcp_ok", "n_viol", "m1_violations",
            "load_yes", "load_no", "total_yes", "cap_yes", "total_no", "cap_no", "price_yes", "price_no",
            "decoded", "positive_load_terminal", "run", "steps", "flipped_run", "alt_decode", "t_build", "t_plcp", "t_decode", "t_total",
            "ok", "why"]
    print("RESULT " + " | ".join(f"{k}={r[k]:.2f}" if isinstance(r.get(k), float) and k.startswith("t_")
                                 else f"{k}={r[k]}" for k in keys if k in r))
    sys.stdout.flush()


GUESS = F(1, 2 ** 16)
if os.environ.get("E2E_GUESS") == "0":
    GUESS = F(0)

def _passes(r):  # artifact: exit status, not used by the computation
    # geps=3: certified, decoded equilibrium loads the run's terminal and no feasible point decodes
    # differently; geps=-3 (negative control): pipeline ok but the decoded point does NOT load the
    # run's terminal (README plcp-e2e-n1: control loads no=2, yes=0)
    if not r.get("ok"):
        return False
    if r["geps"] == 3:
        return r.get("decoded") == r.get("run") and str(r.get("alt_decode", "unsat")) == "unsat"
    return r.get("decoded") != r.get("run")


if __name__ == "__main__":
    mode = sys.argv[1]
    allok = True  # artifact: exit status
    if mode == "n1":
        solver = sys.argv[2] if len(sys.argv) > 2 else "z3"
        for geps in (3, -3):
            r = pipeline(1, [("yes", "no")], geps=geps, solver=solver)
            show(r)
            allok &= _passes(r)  # artifact: exit status
    elif mode == "n2":
        inst = discriminating(2)
        start = int(sys.argv[2]) if len(sys.argv) > 2 else 0
        count = int(sys.argv[3]) if len(sys.argv) > 3 else len(inst)
        print(f"n=2: {len(inst)} discriminating instances; running {start}..{start + count - 1}")
        for steps, succ in inst[start:start + count]:
            for geps in (3, -3):
                r = pipeline(2, succ, geps=geps)
                show(r)
                allok &= _passes(r)  # artifact: exit status
    elif mode == "n3":
        inst = discriminating(3)
        count = int(sys.argv[2]) if len(sys.argv) > 2 else 3
        print(f"n=3: {len(inst)} discriminating instances; running the {count} longest")
        for steps, succ in inst[:count]:
            for geps in (3, -3):
                r = pipeline(3, succ, geps=geps)
                show(r)
                allok &= _passes(r)  # artifact: exit status
    else:
        allok = False  # artifact: exit status (unknown mode)
    sys.exit(0 if allok else 1)  # artifact: exit status
