"""Exact test: does a Disser-Skutella counting network with its source-side cross arcs
redirected to a second sink b alternate its output split?

Network M_n (sink a = t_n, extra sink b):
  S-rail  s_k -> s_{k-1}      cost 0,      cap 2^(k-1)
  T-rail  t_{k-1} -> t_k      cost 0,      cap 2^(k-1)
  central s_0 -> t_0          cost 0,      cap 1
  c1      s_k -> t_{k-1}      cost base^k, cap 2^(k-1)   (unchanged from DS)
  c2      s_{k-1} -> b        cost base^k, cap 2^(k-1)   (DS has s_{k-1} -> t_k)
For each x in 0..K=2^n and each split A (to a), B = x - A (to b), compute the exact
min cost G(A, B) by successive shortest paths with integer arithmetic. Pass iff for every x
the unique minimiser over A is ceil(x/2). Also reports the smallest kink (robustness gap).
"""
import sys


def mcf(n_nodes, arcs, s, demands):
    """Min cost to send demands[v] units from s to each sink v. Integer SSP with Bellman-Ford.
    Returns cost, or None if infeasible."""
    T = n_nodes
    N = n_nodes + 1
    # residual graph as adjacency of edge indices
    to, cap, cost, adj = [], [], [], [[] for _ in range(N)]

    def add(u, v, c, w):
        adj[u].append(len(to)); to.append(v); cap.append(c); cost.append(w)
        adj[v].append(len(to)); to.append(u); cap.append(0); cost.append(-w)

    for (u, v, c, w) in arcs:
        add(u, v, c, w)
    need = 0
    for v, d in demands.items():
        if d > 0:
            add(v, T, d, 0)
            need += d
    total = 0
    sent = 0
    while sent < need:
        dist = [None] * N
        prev = [None] * N
        dist[s] = 0
        for _ in range(N):
            changed = False
            for u in range(N):
                if dist[u] is None:
                    continue
                for e in adj[u]:
                    if cap[e] > 0:
                        v = to[e]
                        nd = dist[u] + cost[e]
                        if dist[v] is None or nd < dist[v]:
                            dist[v] = nd
                            prev[v] = e
                            changed = True
            if not changed:
                break
        if dist[T] is None:
            return None
        # bottleneck
        f = need - sent
        v = T
        while v != s:
            e = prev[v]
            f = min(f, cap[e])
            v = to[e ^ 1]
        v = T
        while v != s:
            e = prev[v]
            cap[e] -= f
            cap[e ^ 1] += f
            v = to[e ^ 1]
        sent += f
        total += f * dist[T]
    return total


def build(n, base):
    # node ids: s_k -> k (0..n), t_k -> n+1+k, b -> 2n+2
    S = lambda k: k
    Tn = lambda k: n + 1 + k
    b = 2 * n + 2
    arcs = [(S(0), Tn(0), 1, 0)]
    for k in range(1, n + 1):
        c = 2 ** (k - 1)
        w = base ** k
        arcs += [(S(k), S(k - 1), c, 0), (Tn(k - 1), Tn(k), c, 0),
                 (S(k), Tn(k - 1), c, w), (S(k - 1), b, c, w)]
    return 2 * n + 3, arcs, S(n), Tn(n), b


def check(n, base, verbose=False):
    N, arcs, s, a, b = build(n, base)
    K = 2 ** n
    ok = True
    min_gap = None
    rows = []
    for x in range(K + 1):
        G = {}
        for A in range(x + 1):
            G[A] = mcf(N, arcs, s, {a: A, b: x - A})
        feas = {A: g for A, g in G.items() if g is not None}
        best = min(feas.values())
        arg = [A for A, g in feas.items() if g == best]
        want = (x + 1) // 2
        good = arg == [want]
        if good:
            nb = [feas[A] - best for A in (want - 1, want + 1) if A in feas]
            gap = min(nb) if nb else None
            if gap is not None:
                min_gap = gap if min_gap is None else min(min_gap, gap)
        ok &= good
        rows.append((x, arg, want, best, good))
        if verbose:
            print(f"  x={x:3d} argmin A={arg} want {want} cost {best} {'ok' if good else 'FAIL'}")
    return ok, min_gap, rows


if __name__ == "__main__":
    for base in (3, 4):
        for n in range(1, 6):
            ok, gap, rows = check(n, base)
            fails = [r for r in rows if not r[4]]
            print(f"base={base} n={n} K={2**n}: {'PASS' if ok else 'FAIL'}"
                  f" min kink={gap} first failures={[(r[0], r[1], r[2]) for r in fails[:4]]}")
            sys.stdout.flush()
