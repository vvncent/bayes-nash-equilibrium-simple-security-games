"""End-to-end exact check: ARRIVAL instance -> composed M1 market of two-copy gadgets
(construction of findings.md Theorem 1) -> z3 proves that EVERY equilibrium puts load 1 on the
terminal the ARRIVAL run reaches and 0 on the other.

Composition (findings.md §1.2): port goods of v = input goods of its successors; dispatch buyer
of mass 1 on p_origin with ratio 2 > U; terminal goods with a buyer of larger mass and ratio
r_T = 1/2 in (0, U); c_p sized above all outside buyers that can buy p (S3).
Usage: composed_check.py n trials seed [eps]
"""
import os
import random
import sys
import time
from fractions import Fraction as F

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))  # artifact: absolute path replaced by lib/
import z3  # noqa: E402
from switchcheck import Q  # noqa: E402
from twocopy_gadget import ds_arcs  # noqa: E402


def run_arrival(n, succ, origin):
    """Simulate the ARRIVAL run. Switches start at successor 0. Returns terminal name."""
    state = [0] * n
    v, steps = origin, 0
    while isinstance(v, int):
        nxt = succ[v][state[v]]
        state[v] ^= 1
        v = nxt
        steps += 1
        if steps > 10 ** 6:
            raise RuntimeError("run did not terminate")
    return v, steps


def reach(n, succ, origin):
    """Terminals reachable from origin."""
    seen, stack, terms = {origin}, [origin], set()
    while stack:
        v = stack.pop()
        for w in succ[v]:
            if isinstance(w, int):
                if w not in seen:
                    seen.add(w)
                    stack.append(w)
            else:
                terms.add(w)
    return terms


def reaches_terminal(n, succ):
    good = set()
    changed = True
    while changed:
        changed = False
        for v in range(n):
            if v not in good and any((not isinstance(w, int)) or w in good for w in succ[v]):
                good.add(v)
                changed = True
    return len(good) == n


def compose(n, succ, origin, m, base=3, eps=3, H=1, w=1):
    K = 2 ** (m + 1)
    half = 2 ** m  # mass of each sink buyer (sum of in-arc capacities)
    arcs_core = ds_arcs(m, base, "s", "a", "A") + ds_arcs(m, base, "s", "b", "B")
    maxcost = sum(c * cost for (_, _, c, cost) in arcs_core) + eps + H + 10
    M = 4 * maxcost
    Mp = M + 1
    lam = F(Mp) / w
    indeg = {t: 0 for t in list(range(n)) + ["yes", "no"]}
    for v in range(n):
        for t in succ[v]:
            indeg[t] += 1
    goods, buyers = {}, []
    port = lambda t: f"p{t}" if isinstance(t, int) else f"T{t}"
    for v in range(n):
        cp = max(2 * K, indeg[v] * half + 2)
        goods[f"p{v}"] = cp
        out_of, into = {}, {}
        for i, (u, x, c, cost) in enumerate(arcs_core):
            g = f"v{v}e{i}"
            goods[g] = c
            out_of.setdefault(u, []).append((g, cost))
            into.setdefault(x, []).append(g)
        caps = {f"v{v}e{i}": c for i, (_, _, c, _) in enumerate(arcs_core)}
        for node in sorted(set(out_of) | set(into)):
            opts = {}
            if node == "s":
                mass = cp
                opts[f"p{v}"] = (Mp, lam)
                for g, cost in out_of[node]:
                    opts[g] = (M - cost, 1)
            elif node in ("a", "b"):
                mass = sum(caps[g] for g in into[node])
                for g in into[node]:
                    opts[g] = (M + H, 1)
                tgt = succ[v][0] if node == "a" else succ[v][1]
                opts[port(tgt)] = (M if node == "a" else M - eps, 1)
            else:
                mass = sum(caps[g] for g in into[node])
                for g, cost in out_of.get(node, []):
                    opts[g] = (M - cost, 1)
                for g in into[node]:
                    opts[g] = (M, 1)
            buyers.append((f"v{v}{node}", mass, opts))
    for t in ("yes", "no"):
        CT = indeg[t] * half + 2
        goods[f"T{t}"] = CT
        buyers.append((f"term_{t}", CT + 1, {f"T{t}": (F(1, 2), 1)}))
    buyers.append(("dispatch", 1, {f"p{origin}": (2, 1)}))
    return goods, buyers


def equilibrium(goods, buyers, s):
    P = {j: z3.Real(f"P_{j}") for j in goods}
    load = {j: [] for j in goods}
    flows = {}
    for j in goods:
        s.add(P[j] >= 0)
    for (name, m, opts) in buyers:
        v = z3.Real(f"v_{name}")
        s.add(v >= 0)
        row = []
        for j, (a, b) in opts.items():
            f = z3.Real(f"f_{name}_{j}")
            s.add(f >= 0)
            u = Q(a) - Q(b) * P[j]
            s.add(v >= u, z3.Or(f == 0, v == u))
            row.append(f)
            load[j].append(f)
            flows[(name, j)] = f
        rs = z3.Sum(row)
        s.add(rs <= Q(m), z3.Or(v == 0, rs == Q(m)))
    for j, c in goods.items():
        L = z3.Sum(load[j]) if load[j] else Q(0)
        s.add(L <= Q(c), z3.Or(P[j] == 0, L == Q(c)))
    return P, flows


def terminal_inflow(flows, t):
    fl = [f for (name, j), f in flows.items() if j == f"T{t}" and not name.startswith("term_")]
    return z3.Sum(fl) if fl else Q(0)


def check_instance(n, succ, origin, m, **kw):
    want, steps = run_arrival(n, succ, origin)
    other = "no" if want == "yes" else "yes"
    goods, buyers = compose(n, succ, origin, m, **kw)
    s = z3.Solver()
    P, flows = equilibrium(goods, buyers, s)
    yin, oin = terminal_inflow(flows, want), terminal_inflow(flows, other)
    exists = s.check()
    s.push()
    s.add(z3.Or(yin != 1, oin != 0))
    wrong = s.check()
    s.pop()
    return want, steps, str(exists), str(wrong), len(buyers), len(goods)


def main():
    n, trials, seed = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
    eps = int(sys.argv[4]) if len(sys.argv) > 4 else 3
    min_steps = int(sys.argv[5]) if len(sys.argv) > 5 else 1
    rng = random.Random(seed)
    targets = list(range(n)) + ["yes", "no"]
    done = 0
    allok = True
    seen = set()
    while done < trials:
        succ = [(rng.choice(targets), rng.choice(targets)) for _ in range(n)]
        if not reaches_terminal(n, succ) or tuple(succ) in seen:
            continue
        origin = 0
        want, steps = run_arrival(n, succ, origin)
        if steps < min_steps:
            continue
        seen.add(tuple(succ))
        t = time.time()
        want, steps, exists, wrong, nb, ng = check_instance(n, succ, origin, n, eps=eps)
        ok = exists == "sat" and wrong == "unsat"
        allok &= ok
        print(f"succ={succ} run->{want} in {steps} steps | buyers={nb} goods={ng} | "
              f"equilibrium exists: {exists}; some equilibrium decodes wrongly: {wrong} | "
              f"{'OK' if ok else 'FAIL'} ({time.time() - t:.1f}s)")
        sys.stdout.flush()
        done += 1
    print("ALL OK" if allok else "SOME FAILED")


if __name__ == "__main__":
    main()
