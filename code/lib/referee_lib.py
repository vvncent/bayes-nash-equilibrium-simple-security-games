"""Independent re-implementation (referee) of: two-copy gadget market, ARRIVAL composition
(findings.md s1.2 with the S3-style terminal capacity), and the one-resource market-to-game embedding
(round2/night/root/one-resource.md, theta = 1: identical defender gains 1). Exact arithmetic only.

Market format: goods {name: capacity}, buyers [(name, mass, {good: (a, b)})], outside option 0, prices >= 0.
"""
from fractions import Fraction as F
import itertools

import z3


def Q(v):
    v = F(v)
    return z3.RealVal(f"{v.numerator}/{v.denominator}")


# ---------------------------------------------------------------- ARRIVAL
def run_arrival(succ, origin=0):
    """Dohrau et al. Run; vertices 0..n-1, terminals are strings. Switches start at s0."""
    state = [0] * len(succ)
    v, steps = origin, 0
    while isinstance(v, int):
        w = succ[v][state[v]]
        state[v] ^= 1
        v, steps = w, steps + 1
        assert steps < 10 ** 7
    return v, steps


def all_reach_terminal(succ):
    good, ch = set(), True
    while ch:
        ch = False
        for v in range(len(succ)):
            if v not in good and any((not isinstance(w, int)) or w in good for w in succ[v]):
                good.add(v)
                ch = True
    return len(good) == len(succ)


def reachable_terminals(succ, origin=0):
    seen, st, terms = {origin}, [origin], set()
    while st:
        v = st.pop()
        for w in succ[v]:
            if isinstance(w, int):
                if w not in seen:
                    seen.add(w)
                    st.append(w)
            else:
                terms.add(w)
    return terms


def discriminating(n):
    T = list(range(n)) + ["yes", "no"]
    out = []
    for succ in itertools.product(itertools.product(T, T), repeat=n):
        succ = [tuple(s) for s in succ]
        if not all_reach_terminal(succ) or reachable_terminals(succ) != {"yes", "no"}:
            continue
        want, steps = run_arrival(succ)
        if run_arrival([(b, a) for (a, b) in succ])[0] == want:
            continue
        out.append((steps, succ, want))
    out.sort(key=lambda t: -t[0])
    return out


# ---------------------------------------------------------------- gadget core
def ds_arcs(m, src, sink, prefix, base=3):
    """Disser-Skutella G_m: (tail, head, cap, cost)."""
    S = lambda k: src if k == m else f"{prefix}s{k}"
    T = lambda k: sink if k == m else f"{prefix}t{k}"
    arcs = [(S(0), T(0), 1, 0)]
    for k in range(1, m + 1):
        c, w = 2 ** (k - 1), base ** k
        arcs += [(S(k), S(k - 1), c, 0), (T(k - 1), T(k), c, 0),
                 (S(k), T(k - 1), c, w), (S(k - 1), T(k), c, w)]
    return arcs


def compose(succ, origin, m, eps=3, H=1, w=1, term_cap="S3", base=3, swap=False):
    """Composed M1 market. swap=True: the +eps penalty sits on port a instead of b (a b-first
    switch: a correct gadget for the instance with s0/s1 exchanged; negative control). term_cap='S3' -> C_T = indeg*2^m + 2; a number -> that capacity."""
    n = len(succ)
    K = 2 ** (m + 1)
    half = 2 ** m
    core = ds_arcs(m, "s", "a", "A", base) + ds_arcs(m, "s", "b", "B", base)
    M = 4 * (sum(c * cost for (_, _, c, cost) in core) + abs(eps) + H + 10)
    Mp = M + 1
    lam = F(Mp) / w
    indeg = {t: 0 for t in list(range(n)) + ["yes", "no"]}
    for v in range(n):
        for t in succ[v]:
            indeg[t] += 1
    pname = lambda t: f"p{t}" if isinstance(t, int) else f"T{t}"
    goods, buyers = {}, []
    for v in range(n):
        cp = max(2 * K, indeg[v] * half + 2)
        goods[f"p{v}"] = cp
        outs, ins = {}, {}
        for i, (u, x, c, cost) in enumerate(core):
            g = f"g{v}_{i}"
            goods[g] = c
            outs.setdefault(u, []).append((g, cost))
            ins.setdefault(x, []).append((g, c))
        for node in sorted(set(outs) | set(ins)):
            opts = {}
            if node == "s":
                mass = cp
                opts[f"p{v}"] = (Mp, lam)
                for g, cost in outs[node]:
                    opts[g] = (M - cost, 1)
            elif node in ("a", "b"):
                mass = sum(c for _, c in ins[node])
                for g, _ in ins[node]:
                    opts[g] = (M + H, 1)
                tgt = succ[v][0] if node == "a" else succ[v][1]
                pen = (node == "b") != swap
                opts[pname(tgt)] = (M - eps, 1) if pen else (M, 1)
            else:
                mass = sum(c for _, c in ins[node])
                for g, cost in outs.get(node, []):
                    opts[g] = (M - cost, 1)
                for g, _ in ins[node]:
                    opts[g] = (M, 1)
            buyers.append((f"b{v}{node}", mass, opts))
    for t in ("yes", "no"):
        CT = indeg[t] * half + 2 if term_cap == "S3" else F(term_cap)
        goods[f"T{t}"] = CT
        buyers.append((f"term{t}", CT + 1, {f"T{t}": (F(1, 2), 1)}))
    buyers.append(("dispatch", 1, {f"p{origin}": (2, 1)}))
    return goods, buyers


def terminal_sources(buyers, t):
    """Buyers (other than the terminal's own buyer) with an option on terminal good t."""
    return [name for (name, _, opts) in buyers if f"T{t}" in opts and not name.startswith("term")]


# ---------------------------------------------------------------- market equilibrium in z3
def market_eq(goods, buyers, s, tag="m"):
    P = {j: z3.Real(f"{tag}P_{j}") for j in goods}
    load = {j: [] for j in goods}
    fl = {}
    for j in goods:
        s.add(P[j] >= 0)
    for (name, mass, opts) in buyers:
        v = z3.Real(f"{tag}v_{name}")
        s.add(v >= 0)
        row = []
        for j, (a, b) in opts.items():
            f = z3.Real(f"{tag}f_{name}_{j}")
            u = Q(a) - Q(b) * P[j]
            s.add(f >= 0, v >= u, z3.Or(f == 0, v == u))
            row.append(f)
            load[j].append(f)
            fl[(name, j)] = f
        s.add(z3.Sum(row) <= Q(mass), z3.Or(v == 0, z3.Sum(row) == Q(mass)))
    for j, c in goods.items():
        L = z3.Sum(load[j]) if load[j] else Q(0)
        s.add(L <= Q(c), z3.Or(P[j] == 0, L == Q(c)))
    return P, fl


# ---------------------------------------------------------------- one-resource game
def market_to_game(goods, buyers, eps_prior=F(1)):
    """one-resource.md construction, theta = 1 (defender gains all 1).
    Returns dict with targets, types (name, weight, {target: (u_unc, u_cov)}), defender payoffs,
    plus bookkeeping (S, real target names)."""
    gnames = list(goods)
    bnames = [b[0] for b in buyers]
    m, n = len(buyers), len(goods)
    D = 1 + max(sum(F(b[1]) for b in buyers), max(F(c) for c in goods.values()))
    U = (2 + 2 / F(eps_prior)) * D
    A = 1 + max(F(0), max(F(a) for (_, _, o) in buyers for (a, _) in o.values()))
    S = 1 + (m + n) * A
    targets = [f"R:{j}" for j in gnames] + [f"G:{i}" for i in bnames] + ["O", "H"]
    types = []
    unl = (F(-2), F(-3))  # unlisted payoff -2 - x: uncovered -2, covered -3

    def row(listed):
        r = {t: unl for t in targets}
        for t, (a0, slope) in listed.items():
            r[t] = (a0, a0 - slope)  # payoff a0 - slope*x : uncovered a0, covered a0 - slope
        return r

    for (name, mass, opts) in buyers:
        listed = {f"R:{j}": (F(a) / S, F(b)) for j, (a, b) in opts.items()}
        listed[f"G:{name}"] = (A / S, F(1))
        listed["O"] = (F(0), F(1))
        types.append((f"src:{name}", U + F(mass), row(listed)))
    for j in gnames:
        types.append((f"ded:{j}", U - F(goods[j]), row({f"R:{j}": (F(2), F(1))})))
    types.append(("ctl", U, row({"H": (F(2), F(1))})))
    defender = {t: (F(0), F(1)) for t in targets}  # (uncovered, covered)
    for (_, wgt, r) in types:
        assert wgt > 0
        for t, (u0, u1) in r.items():
            assert u0 >= u1
    return dict(targets=targets, types=types, defender=defender, resources=1, S=S, U=U, A=A)


def game_bne(game, s, tag="g"):
    """Every BNE of the one-resource game: defender mixes over single targets (coverage x, sum 1);
    defender best-responds to the attack distribution; each type best-responds to x."""
    T = game["targets"]
    tot = sum(w for (_, w, _) in game["types"])
    x = {t: z3.Real(f"{tag}x_{t}") for t in T}
    s.add(z3.Sum(list(x.values())) == 1)
    for t in T:
        s.add(x[t] >= 0)
    sig = {}
    load = {t: [] for t in T}
    for (name, w, r) in game["types"]:
        V = z3.Real(f"{tag}V_{name}")
        row = []
        for t in T:
            u0, u1 = r[t]
            sg = z3.Real(f"{tag}s_{name}_{t}")
            u = Q(u0) - Q(u0 - u1) * x[t]
            s.add(sg >= 0, V >= u, z3.Or(sg == 0, V == u))
            row.append(sg)
            sig[(name, t)] = sg
            load[t].append(Q(w / tot) * sg)
        s.add(z3.Sum(row) == 1)
    # defender: payoff sum_t L_t (x_t d1 + (1-x_t) d0); with d0=0,d1=1 -> sum_t x_t L_t (score gain*load)
    peak = z3.Real(f"{tag}peak")
    for t in T:
        d0, d1 = game["defender"][t]
        sc = Q(d1 - d0) * z3.Sum(load[t])
        s.add(sc <= peak, z3.Or(x[t] == 0, sc == peak))
    return x, sig, tot


def game_terminal_inflow(game, goods_buyers, sig, tot, t):
    """Unnormalised source flow into real target T<t> from non-terminal source types."""
    _, buyers = goods_buyers
    w = {name: wt for (name, wt, _) in game["types"]}
    srcs = terminal_sources(buyers, t)
    return z3.Sum([Q(w[f"src:{b}"]) * sig[(f"src:{b}", f"R:T{t}")] for b in srcs])


def unlisted_never_used(game):
    """Lemma L1 (proved per type by z3 from that type's own best-response constraints plus
    x in the simplex): every target whose payoff is the unlisted (-2, -3) is never in any best response.
    Returns the set of (type, target) pairs proved unusable; asserts every proof succeeded."""
    T = game["targets"]
    pruned = set()
    for (name, w, r) in game["types"]:
        unl = [t for t in T if r[t] == (F(-2), F(-3))]
        lst = [t for t in T if t not in unl]
        s = z3.Solver()
        x = {t: z3.Real(f"x_{t}") for t in T}
        s.add(z3.Sum(list(x.values())) == 1, *[x[t] >= 0 for t in T])
        V = z3.Real("V")
        for t in T:
            u0, u1 = r[t]
            s.add(V >= Q(u0) - Q(u0 - u1) * x[t])
        # V is the max: attained by some target
        s.add(z3.Or(*[V == Q(r[t][0]) - Q(r[t][0] - r[t][1]) * x[t] for t in T]))
        # some unlisted target attains V
        s.add(z3.Or(*[V == -2 - x[t] for t in unl]))
        assert s.check() == z3.unsat, name
        pruned |= {(name, t) for t in unl}
    return pruned


def game_bne_pruned(game, s, pruned, tag="g"):
    """Same as game_bne, but pairs in `pruned` (proved never best responses) have sigma = 0 and
    their best-response inequality V >= payoff is still imposed (so no BNE is lost or added)."""
    T = game["targets"]
    tot = sum(w for (_, w, _) in game["types"])
    x = {t: z3.Real(f"{tag}x_{t}") for t in T}
    s.add(z3.Sum(list(x.values())) == 1, *[x[t] >= 0 for t in T])
    sig, load = {}, {t: [] for t in T}
    for (name, w, r) in game["types"]:
        V = z3.Real(f"{tag}V_{name}")
        row = []
        for t in T:
            u0, u1 = r[t]
            u = Q(u0) - Q(u0 - u1) * x[t]
            s.add(V >= u)
            if (name, t) in pruned:
                sig[(name, t)] = Q(0)
                continue
            sg = z3.Real(f"{tag}s_{name}_{t}")
            s.add(sg >= 0, z3.Or(sg == 0, V == u))
            row.append(sg)
            sig[(name, t)] = sg
            load[t].append(Q(w / tot) * sg)
        s.add(z3.Sum(row) == 1)
    peak = z3.Real(f"{tag}peak")
    for t in T:
        d0, d1 = game["defender"][t]
        sc = Q(d1 - d0) * (z3.Sum(load[t]) if load[t] else Q(0))
        s.add(sc <= peak, z3.Or(x[t] == 0, sc == peak))
    return x, sig, tot
