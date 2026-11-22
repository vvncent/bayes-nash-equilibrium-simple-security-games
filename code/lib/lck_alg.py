"""Exact-rational implementation of Algorithm 1 (with Algorithms 2, 3, 4) of
Li, Conitzer, Korzhyk, "Catcher-Evader Games", IJCAI-16, arXiv:1602.01896.

Log costs w = log(-d) are handled exactly in multiplicative form: a path length
sum(+-log(-d)) is stored as the positive rational exp(length) = prod((-d)^{+-1}),
so gamma = exp(-dist) = 1/exp(dist) is an exact rational and comparisons of
lengths are comparisons of rational products.

Tie-breaking rules are explicit (class Rule); every choice the paper leaves open
is routed through it.
"""
from fractions import Fraction as F
import random


class CEGame:
    def __init__(self, r0, l0, b0, d0, r, l, b, d):
        self.m = len(l0)
        self.n = len(r)
        self.r0, self.l0, self.b0, self.d0 = F(r0), [F(v) for v in l0], [F(v) for v in b0], [F(v) for v in d0]
        self.r = [F(v) for v in r]
        self.l = [[F(v) for v in row] for row in l]
        self.b = [[F(v) for v in row] for row in b]
        self.d = [[F(v) for v in row] for row in d]
        assert all(v > 0 for v in self.d0)
        assert all(v < 0 for row in self.d for v in row)
        assert self.r0 <= sum(self.l0)
        assert all(self.r[i] <= sum(self.l[i]) for i in range(self.n))
        assert all(v > 0 for v in self.r)


class Rule:
    """order: 'asc' | 'desc' | 'rand'. flow: 'cancel' (cycle-cancel from current x) | 'ssp' (from scratch)."""

    def __init__(self, init='asc', flow='cancel', alg3='asc', maxflow='asc', cycle='asc', seed=0):
        self.init, self.flow, self.alg3, self.maxflow, self.cycle = init, flow, alg3, maxflow, cycle
        self.rng = random.Random(seed)
        self.name = f"init={init},flow={flow},alg3={alg3},maxflow={maxflow},cycle={cycle},seed={seed}"

    def order(self, kind, items):
        items = list(items)
        mode = getattr(self, kind)
        if mode == 'asc':
            return items
        if mode == 'desc':
            return items[::-1]
        self.rng.shuffle(items)
        return items


class Stuck(Exception):
    pass


def mu0(G, x, j):
    return G.b0[j] + G.d0[j] * sum(x[i][j] for i in range(G.n))


def mu(G, x0, i, j):
    return G.b[i][j] + G.d[i][j] * x0[j]


def theta0(G, x0, x):
    vals = [mu0(G, x, j) for j in range(G.m) if x0[j] < G.l0[j]]
    return max(vals) if vals else None


def theta_i(G, x0, x, i):
    # Section 2 definition: theta_i = min over sites with x_{i,psi} > 0.
    return min(mu(G, x0, i, j) for j in range(G.m) if x[i][j] > 0)


def active_edges(G, x0, x):
    A = []
    for i in range(G.n):
        th = theta_i(G, x0, x, i)
        for j in range(G.m):
            if mu(G, x0, i, j) == th:
                A.append((i, j))
    return A


# ---------- residual graph helpers (nodes: ('e',i) evaders, ('s',j) sites) ----------

def residual_edges(G, A, f):
    """Residual edges among active edges. Each: (u, v, mult, cap, key, sign).
    mult = exp(weight): forward i->j weight log(-d) => mult -d; backward j->i weight -log(-d) => 1/(-d)."""
    E = []
    for (i, j) in A:
        md = -G.d[i][j]
        if f[(i, j)] < G.l[i][j]:
            E.append((('e', i), ('s', j), md, G.l[i][j] - f[(i, j)], (i, j), +1))
        if f[(i, j)] > 0:
            E.append((('s', j), ('e', i), 1 / md, f[(i, j)], (i, j), -1))
    return E


def bellman_ford(nodes, edges, source):
    """Multiplicative Bellman-Ford. Returns P (node -> exp(dist)) for reachable nodes.
    Raises if a negative (product < 1) cycle is reachable."""
    P = {source: F(1)}
    for _ in range(len(nodes)):
        changed = False
        for (u, v, w, cap, key, sign) in edges:
            if u in P:
                cand = P[u] * w
                if v not in P or cand < P[v]:
                    P[v] = cand
                    changed = True
        if not changed:
            return P
    raise AssertionError("negative cycle reachable in residual graph")


def find_negative_cycle(nodes, edges):
    P = {v: F(1) for v in nodes}
    pred = {}
    last = None
    for _ in range(len(nodes)):
        last = None
        for e in edges:
            u, v, w = e[0], e[1], e[2]
            cand = P[u] * w
            if cand < P[v]:
                P[v] = cand
                pred[v] = e
                last = v
        if last is None:
            return None
    v = last
    for _ in range(len(nodes)):
        v = pred[v][0]
    cycle = []
    u = v
    while True:
        e = pred[u]
        cycle.append(e)
        u = e[0]
        if u == v:
            break
    cycle.reverse()
    prod = F(1)
    for e in cycle:
        prod *= e[2]
    assert prod < 1
    return cycle


# ---------- Algorithm 2 ----------

def algorithm2(G, x0, x, rule, stats):
    A = active_edges(G, x0, x)
    nodes = [('e', i) for i in range(G.n)] + [('s', j) for j in range(G.m)]
    if rule.flow == 'cancel':
        f = {(i, j): x[i][j] for (i, j) in A}
        while True:
            E = residual_edges(G, A, f)
            E = rule.order('cycle', E)
            cyc = find_negative_cycle(rule.order('cycle', nodes), E)
            if cyc is None:
                break
            stats['cancel'] += 1
            amt = min(e[3] for e in cyc)
            for e in cyc:
                f[e[4]] += e[5] * amt
    else:
        f = ssp_flow(G, x0, x, A, rule)
    # write back
    for (i, j) in A:
        x[i][j] = f[(i, j)]
    return A, f


def ssp_flow(G, x0, x, A, rule):
    """Min-cost flow from scratch by successive shortest paths (multiplicative lengths)."""
    capS = {i: sum(x[i][j] for (ii, j) in A if ii == i) for i in range(G.n)}
    capT = {j: sum(x[i][jj] for (i, jj) in A if jj == j) for j in range(G.m)}
    f = {e: F(0) for e in A}
    fs = {i: F(0) for i in range(G.n)}
    ft = {j: F(0) for j in range(G.m)}
    total = sum(capS.values())
    assert total == sum(capT.values())
    S, T = ('S',), ('T',)
    nodes = [S, T] + [('e', i) for i in range(G.n)] + [('s', j) for j in range(G.m)]
    while sum(fs.values()) < total:
        E = []
        for i in range(G.n):
            if fs[i] < capS[i]:
                E.append((S, ('e', i), F(1), capS[i] - fs[i], ('S', i), +1))
            if fs[i] > 0:
                E.append((('e', i), S, F(1), fs[i], ('S', i), -1))
        for j in range(G.m):
            if ft[j] < capT[j]:
                E.append((('s', j), T, F(1), capT[j] - ft[j], ('T', j), +1))
            if ft[j] > 0:
                E.append((T, ('s', j), F(1), ft[j], ('T', j), -1))
        E += residual_edges(G, A, f)
        E = rule.order('cycle', E)
        # shortest path with predecessor
        P = {S: F(1)}
        pred = {}
        for _ in range(len(nodes)):
            changed = False
            for e in E:
                u, v, w = e[0], e[1], e[2]
                if u in P:
                    cand = P[u] * w
                    if v not in P or cand < P[v]:
                        P[v] = cand
                        pred[v] = e
                        changed = True
            if not changed:
                break
        else:
            raise AssertionError("negative cycle in SSP")
        assert T in P, "SSP could not saturate"
        path = []
        v = T
        while v != S:
            e = pred[v]
            path.append(e)
            v = e[0]
        amt = min(e[3] for e in path)
        for e in path:
            k = e[4]
            if k[0] == 'S':
                fs[k[1]] += e[5] * amt
            elif k[0] == 'T':
                ft[k[1]] += e[5] * amt
            else:
                f[k] += e[5] * amt
    return f


# ---------- Algorithm 3 ----------

def algorithm3(G, x0, x, A, f, rule, log):
    th0 = theta0(G, x0, x)
    Bhat0 = [j for j in range(G.m) if x0[j] < G.l0[j] and mu0(G, x, j) == th0]
    unincreasable = set(range(G.m)) - set(Bhat0)
    E = residual_edges(G, A, f)
    nodes = [('e', i) for i in range(G.n)] + [('s', j) for j in range(G.m)]
    star = None
    for psi in rule.order('alg3', Bhat0):
        P = bellman_ford(nodes, E, ('s', psi))
        reach = {v[1] for v in P if v[0] == 's'}
        if not (reach & unincreasable):
            star, Pstar = psi, P
            break
    if star is None:
        return False
    gs = [(1 / Pstar[('s', j)]) if ('s', j) in Pstar else F(0) for j in range(G.m)]
    ge = [(1 / Pstar[('e', i)]) if ('e', i) in Pstar else F(0) for i in range(G.n)]
    th = [theta_i(G, x0, x, i) for i in range(G.n)]
    Delta = (G.r0 - sum(x0)) / sum(gs)
    binding = 'budget'
    for j in range(G.m):
        if gs[j] > 0:
            cand = (G.l0[j] - x0[j]) / gs[j]
            if cand < Delta:
                Delta, binding = cand, ('cap', j)
        for i in range(G.n):
            mij = mu(G, x0, i, j)
            if mij != th[i]:
                den = gs[j] * (-G.d[i][j]) - ge[i]
                if den != 0:
                    cand = (mij - th[i]) / den
                    if cand > 0 and cand < Delta:
                        Delta, binding = cand, ('edge', i, j)
    assert Delta > 0
    before = list(x0)
    for j in range(G.m):
        x0[j] += Delta * gs[j]
    log.append({'star': star, 'Delta': Delta, 'gamma': gs, 'binding': binding,
                'budget_before': sum(before), 'budget_after': sum(x0), 'x0_before': before, 'x0_after': list(x0)})
    return True


# ---------- Algorithm 4 ----------

def maxflow(nodes, edges, s, t, rule):
    """Edmonds-Karp on an edge list [(u, v, cap)] with cap None = infinity. Returns (value, flows, reachable-set)."""
    adj = {v: [] for v in nodes}
    cap, flow, rev, head = [], [], [], []
    for (u, v, c) in edges:
        k = len(cap)
        cap.append(c); flow.append(F(0)); head.append(v); rev.append(k + 1)
        adj[u].append(k)
        cap.append(F(0)); flow.append(F(0)); head.append(u); rev.append(k)
        adj[v].append(k + 1)
    order_nodes = rule.order('maxflow', nodes)
    pos = {v: n for n, v in enumerate(order_nodes)}
    for v in adj:
        adj[v].sort(key=lambda k: pos[head[k]])

    def res(k):
        return None if cap[k] is None else cap[k] - flow[k]

    value = F(0)
    while True:
        parent = {s: None}
        queue = [s]
        qi = 0
        while qi < len(queue) and t not in parent:
            u = queue[qi]; qi += 1
            for k in adj[u]:
                v = head[k]
                rk = res(k)
                if v not in parent and (rk is None or rk > 0):
                    parent[v] = k
                    queue.append(v)
        if t not in parent:
            return value, flow, set(parent), cap, head, rev
        amt = None
        v = t
        while v != s:
            k = parent[v]
            rk = res(k)
            if rk is not None and (amt is None or rk < amt):
                amt = rk
            v = head[rev[k]]
        assert amt is not None, "infinite augmenting path"
        v = t
        while v != s:
            k = parent[v]
            flow[k] += amt
            flow[rev[k]] -= amt
            v = head[rev[k]]
        value += amt


def algorithm4(G, x0, x, A, f, rule, stats):
    th0 = theta0(G, x0, x)
    m0 = [mu0(G, x, j) for j in range(G.m)]
    Bhat0 = [j for j in range(G.m) if x0[j] < G.l0[j] and m0[j] == th0]
    gaps = [th0 - m0[j] for j in range(G.m) if th0 > m0[j]]
    Dbar = min(gaps) if gaps else None
    E = residual_edges(G, A, f)
    S, T = ('S',), ('T',)
    nodes = [S, T] + [('e', i) for i in range(G.n)] + [('s', j) for j in range(G.m)]
    xs = [sum(x[i][j] for i in range(G.n)) for j in range(G.m)]
    hi = min(G.d0[j] * xs[j] for j in Bhat0)
    if Dbar is not None:
        hi = min(hi, Dbar)
    delta = sum(1 / G.d0[j] for j in Bhat0)

    def build(D):
        edges = [(e[0], e[1], e[3]) for e in E]
        affine = [(F(0), F(0))] * len(E)  # (const, slope) of capacity
        for j in range(G.m):
            if j in Bhat0:
                edges.append((S, ('s', j), D / G.d0[j]))
                affine.append((F(0), 1 / G.d0[j]))
            else:
                if m0[j] >= th0:
                    edges.append((('s', j), T, None))
                    affine.append(None)
                else:
                    edges.append((('s', j), T, (th0 - D - m0[j]) / G.d0[j]))
                    affine.append(((th0 - m0[j]) / G.d0[j], -1 / G.d0[j]))
        affine = [(e[3], F(0)) for e in E] + affine[len(E):]
        return edges, affine

    D = hi
    while True:
        stats['alg4_newton'] += 1
        edges, affine = build(D)
        value, flow, Sset, cap, head, rev = maxflow(nodes, edges, S, T, rule)
        if value == D * delta:
            break
        alpha = beta = F(0)
        for k, (u, v, c) in enumerate(edges):
            if u in Sset and v not in Sset:
                assert affine[k] is not None
                alpha += affine[k][0]
                beta += affine[k][1]
        newD = alpha / (delta - beta)
        assert 0 <= newD < D
        D = newD
    if D == 0:
        raise Stuck("Algorithm 4 found Delta = 0")
    # apply: edge index k in edges corresponds to arc 2k in maxflow arrays
    for k, e in enumerate(E):
        fl = flow[2 * k]
        if fl != 0:
            i, j = e[4]
            x[i][j] += e[5] * fl
    return D


# ---------- Algorithm 1 ----------

def initialize(G, rule):
    x0 = [F(0)] * G.m
    x = [[F(0)] * G.m for _ in range(G.n)]
    for i in range(G.n):
        th = max(G.b[i])  # comment in Alg. 1: theta_i = max mu, mu = b at x0 = 0
        for j in rule.order('init', range(G.m)):
            if G.b[i][j] == th:
                x[i][j] = min(G.l[i][j], G.r[i] - sum(x[i]))
        assert sum(x[i]) == G.r[i], "initialization as written does not place all of r_i"
    return x0, x


def is_ne(G, x0, x):
    if sum(x0) != G.r0 or any(not (0 <= x0[j] <= G.l0[j]) for j in range(G.m)):
        return False
    m0 = [mu0(G, x, j) for j in range(G.m)]
    lo = [m0[j] for j in range(G.m) if x0[j] < G.l0[j]]
    hi = [m0[j] for j in range(G.m) if x0[j] > 0]
    if lo and hi and max(lo) > min(hi):
        return False
    for i in range(G.n):
        if sum(x[i]) != G.r[i] or any(not (0 <= x[i][j] <= G.l[i][j]) for j in range(G.m)):
            return False
        mi = [mu(G, x0, i, j) for j in range(G.m)]
        lo = [mi[j] for j in range(G.m) if x[i][j] < G.l[i][j]]
        hi = [mi[j] for j in range(G.m) if x[i][j] > 0]
        if lo and hi and max(lo) > min(hi):
            return False
    return True


def is_ne_partial(G, x0, x):
    """Equilibrium of the game whose catcher budget is the current sum(x0)."""
    saved = G.r0
    G.r0 = sum(x0)
    try:
        return is_ne(G, x0, x)
    finally:
        G.r0 = saved


def algorithm1(G, rule, max_iter=10 ** 6, check_every=True):
    stats = {'alg3_success': 0, 'alg3_fail': 0, 'alg4_newton': 0, 'cancel': 0, 'iterations': 0}
    log = []
    x0, x = initialize(G, rule)
    assert is_ne_partial(G, x0, x)
    while sum(x0) < G.r0:
        stats['iterations'] += 1
        if stats['iterations'] > max_iter:
            raise Stuck("iteration cap")
        A, f = algorithm2(G, x0, x, rule, stats)
        if check_every:
            assert is_ne_partial(G, x0, x), "NE broken after Alg 2"
        if algorithm3(G, x0, x, A, f, rule, log):
            stats['alg3_success'] += 1
            if check_every:
                assert is_ne_partial(G, x0, x), "NE broken after Alg 3"
        else:
            stats['alg3_fail'] += 1
            algorithm4(G, x0, x, A, f, rule, stats)
            if check_every:
                assert is_ne_partial(G, x0, x), "NE broken after Alg 4"
    return x0, x, stats, log
