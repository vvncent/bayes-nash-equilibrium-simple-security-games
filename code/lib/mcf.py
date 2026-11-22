"""Exact (rational) min-cost flow utilities and the Disser-Skutella counting gadget.

All arithmetic uses Python ints and fractions.Fraction, so every reported value is exact.
"""
from fractions import Fraction as Fr


class Net:
    """Directed network with integer capacities and rational costs."""

    def __init__(self, n_nodes):
        self.n = n_nodes
        self.tail, self.head, self.cap, self.cost = [], [], [], []
        self.names = [str(i) for i in range(n_nodes)]

    def add_arc(self, u, w, cap, cost):
        self.tail.append(u)
        self.head.append(w)
        self.cap.append(int(cap))
        self.cost.append(Fr(cost))
        return len(self.tail) - 1

    @property
    def m(self):
        return len(self.tail)


def ds_gadget(n):
    """Disser-Skutella counting gadget N_n (v = 0) from arXiv:1311.5935, Section 3.1.

    Nodes s_0,t_0,...,s_n,t_n.  Arc (s_0,t_0): cost 0, cap 1.  For i = 1..n:
    (s_i,s_{i-1}) and (t_{i-1},t_i): cost 0, cap 2^{i-1};
    (s_i,t_{i-1}) and (s_{i-1},t_i): cost 2^{i-1}-1/2, cap 2^{i-1}.
    Returns (net, s, t, node index dict).
    """
    idx = {}
    for i in range(n + 1):
        idx[('s', i)] = 2 * i
        idx[('t', i)] = 2 * i + 1
    net = Net(2 * n + 2)
    for (k, i), v in idx.items():
        net.names[v] = f"{k}{i}"
    net.add_arc(idx[('s', 0)], idx[('t', 0)], 1, 0)
    for i in range(1, n + 1):
        c = 2 ** (i - 1)
        exp_cost = Fr(2 ** (i - 1)) - Fr(1, 2)
        net.add_arc(idx[('s', i)], idx[('s', i - 1)], c, 0)
        net.add_arc(idx[('t', i - 1)], idx[('t', i)], c, 0)
        net.add_arc(idx[('s', i)], idx[('t', i - 1)], c, exp_cost)
        net.add_arc(idx[('s', i - 1)], idx[('t', i)], c, exp_cost)
    return net, idx[('s', n)], idx[('t', n)], idx


def residual_arcs(net, f):
    """List of residual arcs (u, w, residual capacity, cost, arc index, direction)."""
    res = []
    for k in range(net.m):
        u, w = net.tail[k], net.head[k]
        if f[k] < net.cap[k]:
            res.append((u, w, net.cap[k] - f[k], net.cost[k], k, +1))
        if f[k] > 0:
            res.append((w, u, f[k], -net.cost[k], k, -1))
    return res


def bellman_ford(n_nodes, arcs, sources):
    """Shortest distances from a set of sources (dist 0) over arcs (u,w,cap,cost,...).

    Returns (dist, pred) or raises ValueError on a negative cycle.
    """
    INF = None
    dist = [INF] * n_nodes
    pred = [None] * n_nodes
    for s in sources:
        dist[s] = Fr(0)
    for it in range(n_nodes):
        changed = False
        for a in arcs:
            u, w, c = a[0], a[1], a[3]
            if dist[u] is not None and (dist[w] is None or dist[u] + c < dist[w]):
                dist[w] = dist[u] + c
                pred[w] = a
                changed = True
        if not changed:
            return dist, pred
    raise ValueError("negative cycle")


def ssp(net, s, t, max_iters=None):
    """Successive shortest path algorithm from s to t (exact).

    Returns (flow, list of (path cost, amount augmented)).
    """
    f = [0] * net.m
    log = []
    while True:
        res = residual_arcs(net, f)
        dist, pred = bellman_ford(net.n, res, [s])
        if dist[t] is None:
            break
        # recover path
        path = []
        v = t
        while v != s:
            a = pred[v]
            path.append(a)
            v = a[0]
        amt = min(a[2] for a in path)
        for a in path:
            k, d = a[4], a[5]
            f[k] += d * amt
        log.append((dist[t], amt))
        if max_iters is not None and len(log) >= max_iters:
            break
    return f, log


def flow_cost(net, f):
    return sum(net.cost[k] * f[k] for k in range(net.m))


def ds_recursive_flow(n, v, idx=None, net=None):
    """Closed-form recursive min-cost flow of value v in the DS gadget N_n (our derivation).

    v <= 2^{i-1}: send v through N_{i-1} on the cheap arcs.
    v >  2^{i-1}: saturate cheap arcs, put v-2^{i-1} on each expensive arc,
                  and send 2^i - v through N_{i-1}.
    Arc order matches ds_gadget.
    """
    if net is None:
        net, _, _, idx = ds_gadget(n)
    f = [0] * net.m

    def rec(i, val):
        if i == 0:
            f[0] = val
            return
        base = 1 + 4 * (i - 1)
        c = 2 ** (i - 1)
        if val <= c:
            f[base + 0] = val
            f[base + 1] = val
            f[base + 2] = 0
            f[base + 3] = 0
            rec(i - 1, val)
        else:
            f[base + 0] = c
            f[base + 1] = c
            f[base + 2] = val - c
            f[base + 3] = val - c
            rec(i - 1, 2 ** i - val)

    rec(n, v)
    return f


def check_flow(net, f, s, t, value):
    for k in range(net.m):
        assert 0 <= f[k] <= net.cap[k], (k, f[k])
    bal = [0] * net.n
    for k in range(net.m):
        bal[net.tail[k]] -= f[k]
        bal[net.head[k]] += f[k]
    for u in range(net.n):
        want = -value if u == s else (value if u == t else 0)
        assert bal[u] == want, (u, bal[u], want)


def is_min_cost(net, f):
    """Exact optimality test: no negative-cost cycle in the residual graph."""
    res = residual_arcs(net, f)
    # add a virtual source connected to all nodes with cost 0
    arcs = list(res) + [(net.n, u, 1, Fr(0), -1, 0) for u in range(net.n)]
    try:
        bellman_ford(net.n + 1, arcs, [net.n])
        return True
    except ValueError:
        return False


if __name__ == "__main__":
    import sys
    nmax = int(sys.argv[1]) if len(sys.argv) > 1 else 7
    allok = True  # artifact: exit status
    for n in range(1, nmax + 1):
        net, s, t, idx = ds_gadget(n)
        f, log = ssp(net, s, t)
        costs = [c for c, a in log]
        amts = [a for c, a in log]
        ok_costs = costs == [Fr(j) for j in range(2 ** n)]
        ok_amts = all(a == 1 for a in amts)
        # recursive closed form agrees with an exact optimum for every value v
        ok_rec = True
        for v in range(0, 2 ** n + 1):
            fr = ds_recursive_flow(n, v, idx, net)
            check_flow(net, fr, s, t, v)
            # cost must equal sum_{j<v} j
            if flow_cost(net, fr) != Fr(v * (v - 1), 2):
                ok_rec = False
            if not is_min_cost(net, fr):
                ok_rec = False
        print(f"n={n}: nodes={net.n} arcs={net.m} SSP iterations={len(log)} "
              f"path costs 0..2^n-1: {ok_costs}, unit augmentations: {ok_amts}, "
              f"recursive flows optimal with cost v(v-1)/2: {ok_rec}")
        allok &= ok_costs and ok_amts and ok_rec  # artifact: exit status
    sys.exit(0 if allok else 1)  # artifact: exit status
