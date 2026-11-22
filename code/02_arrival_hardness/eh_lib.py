"""Independent builders written from the book text (ch.2, ch.4 Sec. 4.3) -- no import of prior code.

Market (M1): buyers = (name, mass, {good: (a, b)}), goods = {name: capacity}.
"""
from fractions import Fraction as F
import z3

EPS, H, PBAR = F(3), F(1), F(1)


def Q(v):
    v = F(v)
    return z3.RealVal(f"{v.numerator}/{v.denominator}")


def h0(x):
    x = F(x)
    z = (x // 2)
    rho = x - 2 * z
    return z + min(rho, 1)


def h1(x):
    return F(x) - h0(x)


# ---------------- ARRIVAL ----------------
def run(succ, origin):
    """succ: dict v -> (s0, s1); terminals are 'yes'/'no'. Returns terminal or 'no' if loops."""
    state = {v: 0 for v in succ}
    v, steps, seen = origin, 0, set()
    while v in succ:
        key = (v, tuple(sorted(state.items())))
        if key in seen:
            return "no", steps, False
        seen.add(key)
        nxt = succ[v][state[v]]
        state[v] ^= 1
        v = nxt
        steps += 1
    return v, steps, True


def preprocess(succ, origin):
    good = set()
    ch = True
    while ch:
        ch = False
        for v, (s0, s1) in succ.items():
            if v not in good and any(w in ("yes", "no") or w in good for w in (s0, s1)):
                good.add(v)
                ch = True
    if origin not in good:
        return {0: ("no", "no")}, 0  # fixed no instance
    red = lambda w: w if (w in ("yes", "no") or w in good) else "no"
    return {v: (red(s0), red(s1)) for v, (s0, s1) in succ.items() if v in good}, origin


# ---------------- gadget ----------------
def network(m):
    """Arcs (tail, head, cap, cost) of N_m: two copies of G_m sharing source 's'; sinks 'a','b'."""
    arcs = []
    for cp_, sink in (("A", "a"), ("B", "b")):
        S = lambda k: "s" if k == m else f"{cp_}s{k}"
        T = lambda k: sink if k == m else f"{cp_}t{k}"
        arcs.append((S(0), T(0), 1, 0))
        for k in range(1, m + 1):
            c, w = 2 ** (k - 1), 3 ** k
            arcs += [(S(k), S(k - 1), c, 0), (T(k - 1), T(k), c, 0),
                     (S(k), T(k - 1), c, w), (S(k - 1), T(k), c, w)]
    return arcs


def params(m):
    arcs = network(m)
    M = 4 * (sum(c * k for _, _, c, k in arcs) + EPS + H + 10)
    Mp = M + 1
    lam = Mp / PBAR
    return arcs, M, Mp, lam


def add_gadget(goods, buyers, tag, m, cp, pgood, agood, bgood):
    arcs, M, Mp, lam = params(m)
    goods[pgood] = cp
    nodes = {}
    for i, (u, w, c, k) in enumerate(arcs):
        g = f"{tag}.e{i}"
        goods[g] = c
        nodes.setdefault(u, {"in": [], "out": []})["out"].append((g, c, k))
        nodes.setdefault(w, {"in": [], "out": []})["in"].append((g, c, k))
    for nd, io in nodes.items():
        opts = {}
        for g, c, k in io["out"]:
            opts[g] = (M - k, F(1))
        for g, c, k in io["in"]:
            opts[g] = (M + (H if nd in ("a", "b") else 0), F(1))
        if nd == "s":
            mass = cp
            opts[pgood] = (Mp, lam)
        else:
            mass = sum(c for _, c, _ in io["in"])
        if nd == "a":
            assert agood not in opts
            opts[agood] = (M, F(1))
        if nd == "b":
            assert bgood not in opts
            opts[bgood] = (M - EPS, F(1))
        buyers.append((f"{tag}.{nd}", F(mass), opts))


def compose(succ, origin, m):
    K = 2 ** (m + 1)
    half = 2 ** m
    port = lambda t: f"T_{t}" if t in ("yes", "no") else f"p_{t}"
    indeg = {t: 0 for t in list(succ) + ["yes", "no"]}
    for v, (s0, s1) in succ.items():
        indeg[s0] += 1
        indeg[s1] += 1
    goods, buyers = {}, []
    for v, (s0, s1) in succ.items():
        cp = max(2 * K, indeg[v] * half + 2)
        add_gadget(goods, buyers, f"g{v}", m, F(cp), port(v), port(s0), port(s1))
    for t in ("yes", "no"):
        CT = indeg[t] * half + 2
        goods[f"T_{t}"] = F(CT)
        buyers.append((f"term_{t}", F(CT + 1), {f"T_{t}": (F(1, 2), F(1))}))
    buyers.append(("dispatch", F(1), {port(origin): (F(2), F(1))}))
    return goods, buyers


def eq_constraints(goods, buyers, s, pre="", fixedP=None):
    """(M1) equilibrium conditions (a)-(d). fixedP: dict of goods whose price is a given constant and
    which have no capacity condition (port goods of a standalone gadget)."""
    fixedP = fixedP or {}
    P = {}
    for j in goods:
        P[j] = z3.Real(f"{pre}P[{j}]")
        s.add(P[j] >= 0)
    load = {j: [] for j in goods}
    fl, val = {}, {}
    for name, mass, opts in buyers:
        v = z3.Real(f"{pre}v[{name}]")
        val[name] = v
        s.add(v >= 0)
        row = []
        for j, (a, b) in opts.items():
            f = z3.Real(f"{pre}f[{name},{j}]")
            fl[(name, j)] = f
            s.add(f >= 0)
            pj = Q(fixedP[j]) if j in fixedP else P[j]
            u = Q(a) - Q(b) * pj
            s.add(v >= u, z3.Or(f == 0, v == u))
            row.append(f)
            if j in load:
                load[j].append(f)
        r = z3.Sum(row)
        s.add(r <= Q(mass), z3.Or(v == 0, r == Q(mass)))
    for j, c in goods.items():
        L = z3.Sum(load[j]) if load[j] else Q(0)
        s.add(L <= Q(c), z3.Or(P[j] == 0, L == Q(c)))
    return P, fl, val, load
