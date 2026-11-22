# referee2: independent implementation of the construction in simple-proof.md
from fractions import Fraction as Fr
import itertools, random
import z3

YES, NO = 'yes', 'no'

# ---------------- ARRIVAL ----------------
def run(V, o, s0, s1, limit=10**6):
    cur = {v: 0 for v in V}
    v = o
    steps = 0
    while v in cur:
        w = s0[v] if cur[v] == 0 else s1[v]
        cur[v] ^= 1
        v = w
        steps += 1
        if steps > limit:
            return None
    return v

def preprocess(V, o, s0, s1):
    # vertices that can reach a terminal
    good = set()
    changed = True
    while changed:
        changed = False
        for v in V:
            if v not in good and any(s in (YES, NO) or s in good for s in (s0[v], s1[v])):
                good.add(v); changed = True
    if o not in good:
        return None
    V2 = [v for v in V if v in good]
    r = lambda s: s if (s in (YES, NO) or s in good) else NO
    return V2, o, {v: r(s0[v]) for v in V2}, {v: r(s1[v]) for v in V2}

def all_instances(n):
    V = list(range(n))
    succ = V + [YES, NO]
    out = []
    for choice in itertools.product(succ, repeat=2 * n):
        s0 = {v: choice[2 * v] for v in V}
        s1 = {v: choice[2 * v + 1] for v in V}
        p = preprocess(V, 0, s0, s1)
        if p is not None and len(p[0]) == n:
            out.append(p)
    return out

def random_instance(n, rng):
    V = list(range(n))
    succ = V + [YES, NO]
    while True:
        s0 = {v: rng.choice(succ) for v in V}
        s1 = {v: rng.choice(succ) for v in V}
        p = preprocess(V, 0, s0, s1)
        if p is not None and len(p[0]) == n:
            return p

# ---------------- switch map ----------------
def h0(x):
    x = Fr(x); z = x // 2; rho = x - 2 * z
    return z + min(rho, 1)
def h1(x):
    x = Fr(x); z = x // 2; rho = x - 2 * z
    return z + max(rho - 1, 0)

# ---------------- splitter N_m ----------------
def splitter(m):
    """nodes, arcs list of (tail, head, cap, cost); source 's', sinks 'a','b'"""
    arcs = []
    for c in 'AB':
        def nm(kind, k):
            if kind == 's' and k == m: return 's'
            if kind == 't' and k == m: return 'a' if c == 'A' else 'b'
            return f'{c}{kind}{k}'
        arcs.append((nm('s', 0), nm('t', 0), 1, 0))
        for k in range(1, m + 1):
            cap = 2 ** (k - 1)
            arcs += [(nm('s', k), nm('s', k - 1), cap, 0), (nm('t', k - 1), nm('t', k), cap, 0),
                     (nm('s', k), nm('t', k - 1), cap, 3 ** k), (nm('s', k - 1), nm('t', k), cap, 3 ** k)]
    nodes = sorted({a[0] for a in arcs} | {a[1] for a in arcs})
    return nodes, arcs

# ---------------- market ----------------
def build_market(inst, m=None, eps=3, Mfac=None, lamfac=2, capplus=1, swap=False):
    """returns buyers {id: mass}, goods {id: cap}, options list (buyer, good, a, b), meta.
    knobs for negative controls: m, eps, M, lambda = lamfac*M, capplus (the +1 in c_v), swap ports."""
    V, o, s0, s1 = inst
    n = len(V)
    if m is None: m = n
    K = 2 ** (m + 1)
    M = 2 * 3 ** (m + 1) if Mfac is None else Mfac
    lam = Fr(lamfac) * M
    nodes, arcs = splitter(m)
    incap = {u: 0 for u in nodes}
    for (t, h, c, k) in arcs: incap[h] += c
    indeg = {w: 0 for w in list(V) + [YES, NO]}
    for v in V:
        indeg[s0[v]] += 1; indeg[s1[v]] += 1
    port = lambda w: ('E',) if w in (YES, NO) else ('p', w)
    goods, buyers, opts = {}, {}, []
    for v in V:
        goods[('p', v)] = capplus + 2 ** m * indeg[v]
        for ei, (t, h, c, k) in enumerate(arcs):
            goods[('g', v, ei)] = c
    goods[('E',)] = capplus + 2 ** m * (indeg[YES] + indeg[NO])
    for v in V:
        cv = goods[('p', v)]
        for u in nodes:
            b = (v, u)
            buyers[b] = cv + (1 if v == o else 0) if u == 's' else incap[u]
            for ei, (t, h, c, k) in enumerate(arcs):
                if t == u: opts.append((b, ('g', v, ei), 2 * M - k, 1))
                if h == u: opts.append((b, ('g', v, ei), 2 * M, 1))
            if u == 's': opts.append((b, ('p', v), 2 * M, lam))
            ea, eb = (s1[v], s0[v]) if swap else (s0[v], s1[v])
            if u == 'a': opts.append((b, port(ea), M, 1))
            if u == 'b': opts.append((b, port(eb), M - eps, 1))
    # yes-sinks: buyers whose port option is E and whose edge leads to yes
    yes_sinks = [(v, 'a') for v in V if s0[v] == YES] + [(v, 'b') for v in V if s1[v] == YES]
    no_sinks = [(v, 'a') for v in V if s0[v] == NO] + [(v, 'b') for v in V if s1[v] == NO]
    if swap:
        yes_sinks = [(v, 'a') for v in V if s1[v] == YES] + [(v, 'b') for v in V if s0[v] == YES]
        no_sinks = [(v, 'a') for v in V if s1[v] == NO] + [(v, 'b') for v in V if s0[v] == NO]
    meta = dict(K=K, M=M, lam=lam, m=m, yes_sinks=yes_sinks, no_sinks=no_sinks)
    return buyers, goods, opts, meta

def market_eq_constraints(buyers, goods, opts, pre='', extra_real=None):
    P = {j: z3.Real(f'{pre}P_{j}') for j in goods}
    v = {i: z3.Real(f'{pre}v_{i}') for i in buyers}
    f = {}
    cons = []
    for idx, (i, j, a, b) in enumerate(opts):
        f[(i, j)] = z3.Real(f'{pre}f_{idx}')
    for j in goods: cons.append(P[j] >= 0)
    for i in buyers: cons.append(v[i] >= 0)
    row = {i: [] for i in buyers}; col = {j: [] for j in goods}
    for (i, j, a, b) in opts:
        x = f[(i, j)]
        pay = z3.RealVal(str(a)) - z3.RealVal(str(b)) * P[j]
        cons += [x >= 0, v[i] >= pay, z3.Or(x == 0, v[i] == pay)]
        row[i].append(x); col[j].append(x)
    for i in buyers:
        s = z3.Sum(row[i]) if row[i] else z3.RealVal(0)
        cons += [s <= buyers[i], z3.Or(v[i] == 0, s == buyers[i])]
    for j in goods:
        s = z3.Sum(col[j]) if col[j] else z3.RealVal(0)
        cons += [s <= goods[j], z3.Or(P[j] == 0, s == goods[j])]
    return P, v, f, cons

def to_fr(val):
    if z3.is_rational_value(val):
        return Fr(val.numerator_as_long(), val.denominator_as_long())
    raise ValueError(val)
