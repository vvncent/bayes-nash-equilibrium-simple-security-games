"""Embed the two-copy counting-network core as an M1 market gadget and certify S1+S2 with the
arrival-switch agent's own exact verifier (switchcheck.check, z3 linear real arithmetic).

Core network: shared source s; copy A = Disser-Skutella G_m from s to sink a; copy B = G_m from s
to sink b, every unit into b costing eps more. Arc costs base^k on level-k cross arcs.

Market embedding (unit slopes except on p; standard arc-to-good transformation):
  - each arc e=(u,v) -> private good g_e with capacity cap(e)
  - each internal node v -> buyer with mass sum of in-arc capacities; options:
        out-arc goods at margin M - cost(e)  (flow), in-arc goods at margin M (slack)
  - source s -> buyer with mass cp; options: p at margin Mp (slope lam), out-arc goods M - cost(e)
  - sink a (b) -> buyer with mass sum of in-arc capacities; options: in-arc goods at margin M + H
        (slack, H > 0 rules out phantom flow at zero port price), port a at margin M (port b at M - eps)
  - lam = Mp / w (R2 input compression), port box U = w.
"""
import os
import sys
from fractions import Fraction as F

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))  # artifact: absolute path replaced by lib/
from switchcheck import check, size, bits  # noqa: E402


def ds_arcs(m, base, src, sink, prefix):
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


def gadget(m, base=3, eps=3, H=1, w=1):
    K = 2 ** (m + 1)
    arcs = ds_arcs(m, base, "s", "a", "A") + ds_arcs(m, base, "s", "b", "B")
    maxcost = sum(c * cost for (_, _, c, cost) in arcs) + eps + H + 10
    M = 4 * maxcost
    Mp = M + 1
    lam = F(Mp, 1) / w
    cp = 2 * K
    goods = {}
    out_of, into = {}, {}
    for i, (u, v, c, cost) in enumerate(arcs):
        g = f"e{i}"
        goods[g] = c
        out_of.setdefault(u, []).append((g, cost))
        into.setdefault(v, []).append((g, c))
    nodes = sorted(set(out_of) | set(into))
    buyers = []
    for v in nodes:
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


if __name__ == "__main__":
    print("m  K  agents(buyers+goods+p)  bits  certified(S1+S2)  failing pieces")
    allok = True  # artifact: exit status
    for m in range(1, int(sys.argv[1]) + 1 if len(sys.argv) > 1 else 5):
        g, K, U = gadget(m)
        ok, res = check(g, K, U)
        bad = [r for r in res if not r[3]]
        print(m, K, size(g), bits(g), ok, bad[:3])
        sys.stdout.flush()
        allok &= ok  # artifact: exit status
    sys.exit(0 if allok else 1)  # artifact: exit status (S1+S2 certified for every m)
