"""Exact capacity-scaling min-cost circulation (Edmonds-Karp scaling; Ahuja-Magnanti-Orlin
Sec. 10.2).  Polynomial: O(m log U) shortest-path computations.  Integer capacities,
rational costs, all node supplies zero.  A hub with expensive artificial arcs keeps every
Delta-residual network strongly connected, as the textbook analysis assumes.
"""
import heapq
from fractions import Fraction as Fr


def min_cost_circulation(n, tail, head, cap, cost):
    m = len(tail)
    big_cap = sum(cap) + 1
    Mart = sum(abs(c) for c in cost) + 1
    T = list(tail) + [u for u in range(n)] + [n] * n
    H = list(head) + [n] * n + [u for u in range(n)]
    Cp = list(cap) + [big_cap] * (2 * n)
    Co = [Fr(c) for c in cost] + [Fr(Mart)] * (2 * n)
    N = n + 1
    M = len(T)
    f = [0] * M
    pi = [Fr(0)] * N
    exc = [0] * N
    out = [[] for _ in range(N)]
    for k in range(M):
        out[T[k]].append(k)
        out[H[k]].append(k)
    U = max(Cp)
    Delta = 1 << (U.bit_length() - 1)
    n_aug = 0
    while Delta >= 1:
        for k in range(M):
            u, w = T[k], H[k]
            rc = Co[k] + pi[u] - pi[w]
            if rc < 0 and Cp[k] - f[k] >= Delta:
                amt = Cp[k] - f[k]
                f[k] += amt; exc[u] -= amt; exc[w] += amt
            elif rc > 0 and f[k] >= Delta:
                amt = f[k]
                f[k] -= amt; exc[u] += amt; exc[w] -= amt
        while True:
            S = [v for v in range(N) if exc[v] >= Delta]
            Tn = set(v for v in range(N) if exc[v] <= -Delta)
            if not S or not Tn:
                break
            src = S[0]
            dist = [None] * N
            pred = [None] * N
            dist[src] = Fr(0)
            pq = [(Fr(0), src)]
            done = [False] * N
            while pq:
                dv, v = heapq.heappop(pq)
                if done[v] or dv != dist[v]:
                    continue
                done[v] = True
                for k in out[v]:
                    if T[k] == v and Cp[k] - f[k] >= Delta:
                        w, rc, d = H[k], Co[k] + pi[v] - pi[H[k]], +1
                    elif H[k] == v and f[k] >= Delta:
                        w, rc, d = T[k], -Co[k] + pi[v] - pi[T[k]], -1
                    else:
                        continue
                    assert rc >= 0, "reduced-cost invariant violated"
                    nd = dv + rc
                    if dist[w] is None or nd < dist[w]:
                        dist[w] = nd
                        pred[w] = (k, d, v)
                        heapq.heappush(pq, (nd, w))
            reach_T = [v for v in Tn if dist[v] is not None]
            assert reach_T, "hub should make the residual network strongly connected"
            dest = min(reach_T, key=lambda v: dist[v])
            Dmax = max(dv for dv in dist if dv is not None)
            # reduced cost convention c + pi_u - pi_w  =>  update pi := pi + dist
            for v in range(N):
                pi[v] += dist[v] if dist[v] is not None else Dmax
            v = dest
            while v != src:
                k, d, pv = pred[v]
                f[k] += d * Delta
                v = pv
            exc[src] -= Delta
            exc[dest] += Delta
            n_aug += 1
        Delta //= 2
    assert all(e == 0 for e in exc)
    assert all(f[k] == 0 for k in range(m, M)), "artificial arcs used: costs too small?"
    return f[:m], pi[:n], n_aug


def potentials_from_flow(n, tail, head, cap, cost, f):
    """Exact optimality certificate: Bellman-Ford potentials on the residual graph."""
    from mcf import bellman_ford
    res = []
    for k in range(len(tail)):
        if f[k] < cap[k]:
            res.append((tail[k], head[k], cap[k] - f[k], Fr(cost[k]), k, +1))
        if f[k] > 0:
            res.append((head[k], tail[k], f[k], -Fr(cost[k]), k, -1))
    arcs = res + [(n, u, 1, Fr(0), -1, 0) for u in range(n)]
    dist, _ = bellman_ford(n + 1, arcs, [n])
    return dist[:n]


if __name__ == "__main__":
    import random, time
    from game import Gn
    from mcf import ds_recursive_flow
    for n in range(1, 9):
        G = Gn(n)
        circ = G.circ
        okall = True
        for trial in range(12):
            mu = Fr(random.randrange(1, 2 ** (n + 3)), 8) + Fr(1, 16)
            if mu >= 2 ** n:
                mu = Fr(2 ** n) - Fr(1, 16)
            circ.cost[G.rho] = -mu
            f, pi, naug = min_cost_circulation(circ.n, circ.tail, circ.head, circ.cap, circ.cost)
            v = -(-mu.numerator // mu.denominator)
            okall &= (f[G.rho] == v)
            potentials_from_flow(circ.n, circ.tail, circ.head, circ.cap, circ.cost, f)
        print(f"n={n}: capacity-scaling optimum has return flow ceil(mu) on 12 random mu: {okall}")
    for n in (10, 20, 30, 40):
        G = Gn(n)
        circ = G.circ
        mu = Fr(2 ** (n - 1)) + Fr(1, 3)
        circ.cost[G.rho] = -mu
        t0 = time.time()
        f, pi, naug = min_cost_circulation(circ.n, circ.tail, circ.head, circ.cap, circ.cost)
        print(f"n={n}: mu=2^(n-1)+1/3 -> return flow {f[G.rho]} (expect {2**(n-1)+1}), "
              f"augmentations {naug}, {time.time()-t0:.2f}s")
