# Independent referee builder for simple-proof.md (written from the text only).
# All arithmetic exact (Fractions / z3 rationals).
from fractions import Fraction as Fr
import itertools
import z3

YES, NO = 'yes', 'no'

# ---------------- ARRIVAL ----------------
def run(n, s0, s1, o, limit=None):
    """Return 'yes'/'no'/None(no termination within limit)."""
    if limit is None:
        limit = (n + 1) * (2 ** (n + 2)) + 10
    sw = [0] * n
    cur = o
    for _ in range(limit):
        if cur in (YES, NO):
            return cur
        nxt = s0[cur] if sw[cur] == 0 else s1[cur]
        sw[cur] ^= 1
        cur = nxt
    return None

def preprocess(n, s0, s1, o):
    """Delete vertices that cannot reach a terminal; redirect edges into them to 'no'.
    If o is deleted, return fixed no-instance (1 vertex, both successors no). Relabel."""
    reach = set()
    changed = True
    while changed:
        changed = False
        for v in range(n):
            if v in reach:
                continue
            for w in (s0[v], s1[v]):
                if w in (YES, NO) or w in reach:
                    reach.add(v); changed = True; break
    if o not in reach:
        return 1, [NO], [NO], 0
    keep = sorted(reach)
    idx = {v: i for i, v in enumerate(keep)}
    def mp(w):
        if w in (YES, NO):
            return w
        return idx[w] if w in idx else NO
    return len(keep), [mp(s0[v]) for v in keep], [mp(s1[v]) for v in keep], idx[o]

def all_instances(n, origin0=True):
    targets = list(range(n)) + [YES, NO]
    for succ in itertools.product(targets, repeat=2 * n):
        s0 = list(succ[:n]); s1 = list(succ[n:])
        for o in ([0] if origin0 else range(n)):
            yield s0, s1, o

def canon(n, s0, s1, o):
    best = None
    for perm in itertools.permutations(range(n)):
        def mp(w):
            return w if w in (YES, NO) else perm[w]
        t0 = [None] * n; t1 = [None] * n
        for v in range(n):
            t0[perm[v]] = mp(s0[v]); t1[perm[v]] = mp(s1[v])
        key = (tuple(map(str, t0)), tuple(map(str, t1)), perm[o])
        if best is None or key < best:
            best = key
    return (n,) + best

# ---------------- network ----------------
def G(k, tag):
    """arcs of G_k: list of (tail, head, cap, cost); nodes (tag,'s',i),(tag,'t',i)."""
    arcs = [((tag, 's', 0), (tag, 't', 0), 1, 0)]
    for i in range(1, k + 1):
        c = 2 ** (i - 1); w = 3 ** i
        si, ti, sp, tp = (tag, 's', i), (tag, 't', i), (tag, 's', i - 1), (tag, 't', i - 1)
        arcs += [(si, sp, c, 0), (tp, ti, c, 0), (si, tp, c, w), (sp, ti, c, w)]
    return arcs

def splitter(m):
    S = ('S',)
    arcs = []
    for tag in ('A', 'B'):
        for (u, w, c, k) in G(m, tag):
            u = S if u == (tag, 's', m) else u
            w = S if w == (tag, 's', m) else w
            arcs.append((u, w, c, k))
    nodes = sorted({x for a in arcs for x in a[:2]}, key=str)
    return nodes, arcs, S, ('A', 't', m), ('B', 't', m)

def h0(x):
    x = Fr(x); z = int(x // 2); r = x - 2 * z
    return z + min(r, 1)

def h1(x):
    x = Fr(x); z = int(x // 2); r = x - 2 * z
    return z + max(r - 1, 0)

# ---------------- market of section 5 ----------------
def build_market(n, s0, s1, o, M=None, lam=None, eps=3, m=None):
    if m is None: m = n
    K = 2 ** (m + 1)
    if M is None: M = 2 * 3 ** (m + 1)
    if lam is None: lam = 2 * M
    nodes, arcs, S, a, b = splitter(m)
    indeg = {w: 0 for w in list(range(n)) + [YES, NO]}
    for v in range(n):
        indeg[s0[v]] += 1; indeg[s1[v]] += 1
    goods = {}
    cv = {v: 1 + 2 ** m * indeg[v] for v in range(n)}
    for v in range(n):
        goods[('p', v)] = cv[v]
        for ei, e in enumerate(arcs):
            goods[('g', v, ei)] = e[2]
    goods[('E',)] = 1 + 2 ** m * (indeg[YES] + indeg[NO])
    def port(w):
        return ('E',) if w in (YES, NO) else ('p', w)
    incap = {u: sum(e[2] for e in arcs if e[1] == u) for u in nodes}
    buyers = {}  # name -> (mass, [(good, a, b)])
    for v in range(n):
        for u in nodes:
            mass = cv[v] + (1 if v == o else 0) if u == S else incap[u]
            opts = []
            for ei, e in enumerate(arcs):
                if e[0] == u: opts.append((('g', v, ei), 2 * M - e[3], 1))
                if e[1] == u: opts.append((('g', v, ei), 2 * M, 1))
            if u == S: opts.append((('p', v), 2 * M, lam))
            if u == a: opts.append((port(s0[v]), M, 1))
            if u == b: opts.append((port(s1[v]), M - eps, 1))
            assert len({g for g, _, _ in opts}) == len(opts)
            buyers[(v, u)] = (mass, opts)
    return dict(goods=goods, buyers=buyers, a=a, b=b, S=S, K=K, M=M, lam=lam)

def yes_sinks(n, s0, s1, mk):
    out = []
    for v in range(n):
        if s0[v] == YES: out.append((v, mk['a']))
        if s1[v] == YES: out.append((v, mk['b']))
    return out

def no_sinks(n, s0, s1, mk):
    out = []
    for v in range(n):
        if s0[v] == NO: out.append((v, mk['a']))
        if s1[v] == NO: out.append((v, mk['b']))
    return out

def eq_constraints(mk, s):
    """Add (M1) equilibrium constraints; return (P, V, F) z3 vars."""
    P = {g: z3.Real('P_%s' % (g,)) for g in mk['goods']}
    V = {i: z3.Real('v_%s' % (i,)) for i in mk['buyers']}
    F = {}
    load = {g: [] for g in mk['goods']}
    for i, (mu, opts) in mk['buyers'].items():
        s.add(V[i] >= 0)
        tot = []
        for (g, aa, bb) in opts:
            f = z3.Real('f_%s_%s' % (i, g)); F[(i, g)] = f
            s.add(f >= 0)
            pay = aa - bb * P[g]
            s.add(V[i] >= pay)
            s.add(z3.Or(f == 0, V[i] == pay))
            tot.append(f); load[g].append(f)
        s.add(z3.Sum(tot) <= mu)
        s.add(z3.Or(V[i] == 0, z3.Sum(tot) == mu))
    for g, c in mk['goods'].items():
        s.add(P[g] >= 0)
        L = z3.Sum(load[g]) if load[g] else z3.RealVal(0)
        s.add(L <= c)
        s.add(z3.Or(P[g] == 0, L == c))
    return P, V, F
