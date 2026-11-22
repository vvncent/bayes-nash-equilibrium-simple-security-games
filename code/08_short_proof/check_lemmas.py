# Lemma 2 (increments), Lemma 5 (big M) on random LPs, Lemma 8 on random markets with slopes >= 1.
# usage: python -I check_lemmas.py
import sys, os, random
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from fractions import Fraction as Fr
import z3
from ref_lib import G
from check_game import bne

# ---- Lemma 2: F_k(j) by exact LP, compare with recursion; convexity/integer breakpoints at half-points
def mincost(k, val):
    arcs = G(k, 'X'); o = z3.Optimize()
    fl = [z3.Real('f%d' % i) for i in range(len(arcs))]
    nodes = {u for a in arcs for u in a[:2]}
    src, snk = ('X', 's', k), ('X', 't', k)
    for i, (t, h, c, w) in enumerate(arcs): o.add(fl[i] >= 0, fl[i] <= c)
    for u in nodes:
        net = z3.Sum([fl[i] for i, a in enumerate(arcs) if a[0] == u] + [-fl[i] for i, a in enumerate(arcs) if a[1] == u])
        o.add(net == (val if u == src else -val if u == snk else 0))
    obj = z3.Sum([a[3] * fl[i] for i, a in enumerate(arcs)])
    o.minimize(obj); assert o.check() == z3.sat
    v = o.model().eval(obj); return Fr(v.as_fraction())

def lemma2(kmax=4):
    D = [0]
    out = []
    for k in range(1, kmax + 1):
        D = D + [2 * 3 ** k - d for d in reversed(D)]
        F = [mincost(k, j) for j in range(2 ** k + 1)]
        inc = [F[j] - F[j - 1] for j in range(1, len(F))]
        half = all(mincost(k, Fr(2 * j + 1, 2)) == (F[j] + F[j + 1]) / 2 for j in range(2 ** k))
        gaps = min(b - a for a, b in zip(inc, inc[1:]))
        out.append((k, inc == D, half, gaps, F[0] == 0, D[0] == 0 and D[-1] == 2 * 3 ** k))
    return out

# ---- Lemma 5 on random allocation LPs
def lemma5(trials=300, seed=5, control=False):
    rng = random.Random(seed); fails = 0
    for _ in range(trials):
        nI = rng.randint(1, 4); nJ = rng.randint(1, 3); nJi = rng.randint(0, 2)
        mu = [Fr(rng.randint(1, 6), rng.randint(1, 3)) for _ in range(nI)]
        cap = [Fr(rng.randint(0, 6), rng.randint(1, 3)) for _ in range(nJ)]
        goods = [('f', j) for j in range(nJ)] + [('u', j) for j in range(nJi)]
        E = [(i, g) for i in range(nI) for g in goods if rng.random() < 0.6]
        if not E: continue
        kap = {e: Fr(rng.randint(0, 9), rng.randint(1, 4)) for e in E}
        Sk = sum(kap.values())
        M = Sk / 3 if control else Sk + Fr(1, 97)
        a = {e: M * (2 if e[1][0] == 'f' else 1) - kap[e] for e in E}
        def feas(s, tag):
            f = {e: z3.Real('%s%s' % (tag, e)) for e in E}
            for e in E: s.add(f[e] >= 0)
            for i in range(nI): s.add(z3.Sum([f[e] for e in E if e[0] == i] + [z3.RealVal(0)]) <= mu[i])
            for j in range(nJ): s.add(z3.Sum([f[e] for e in E if e[1] == ('f', j)] + [z3.RealVal(0)]) <= cap[j])
            T = z3.Sum([f[e] for e in E] + [f[e] for e in E if e[1][0] == 'f'])
            return f, T
        o = z3.Optimize(); f, T = feas(o, 'g'); o.maximize(T); o.check()
        Tmax = o.model().eval(T)
        s = z3.Solver(); f, T = feas(s, 'f')
        v = [z3.Real('v%d' % i) for i in range(nI)]; pi = [z3.Real('p%d' % j) for j in range(nJ)]
        for t in v + pi: s.add(t >= 0)
        for e in E:
            pj = pi[e[1][1]] if e[1][0] == 'f' else 0
            s.add(v[e[0]] + pj >= a[e], z3.Or(f[e] == 0, v[e[0]] + pj == a[e]))
        for i in range(nI):
            s.add(z3.Or(v[i] == 0, z3.Sum([f[e] for e in E if e[0] == i] + [z3.RealVal(0)]) == mu[i]))
        for j in range(nJ):
            s.add(z3.Or(pi[j] == 0, z3.Sum([f[e] for e in E if e[1] == ('f', j)] + [z3.RealVal(0)]) == cap[j]))
        s.add(T < Tmax)
        if s.check() == z3.sat: fails += 1
    return fails

# ---- Lemma 8 on random markets (slopes >= 1): every BNE decodes to an (M1) equilibrium
def lemma8(trials=60, seed=8, control=False):
    from check_game import build_game
    rng = random.Random(seed); bad = 0; done = 0
    for _ in range(trials):
        nI = rng.randint(1, 3); nJ = rng.randint(1, 3)
        goods = {('g', j): Fr(rng.randint(1, 4), rng.randint(1, 2)) for j in range(nJ)}
        buyers = {}
        for i in range(nI):
            opts = [(('g', j), Fr(rng.randint(-2, 6), rng.randint(1, 2)), (Fr(1, rng.randint(20, 60)) if control else Fr(rng.randint(2, 8), 2)))
                    for j in range(nJ) if rng.random() < 0.7]
            buyers[('b', i)] = (Fr(rng.randint(1, 4), rng.randint(1, 2)), opts)
        mk = dict(goods=goods, buyers=buyers)
        targets, types, W = build_game(mk)
        I = list(buyers); J = list(goods)
        A = 1 + max([0] + [a for i in I for (_, a, _) in buyers[i][1]])
        S = 1 + (len(I) + len(J)) * A
        s = z3.Solver(); xi, sig = bne(targets, types, s)
        uvars = {th: z3.Real('u_%s' % (th,)) for th in types}
        P = {j: S * xi[('real', j)] for j in J}
        v = {i: S * uvars[('src', i)] for i in I}
        f = {(i, j): (W + buyers[i][0]) * sig[(('src', i), ('real', j))] for i in I for (j, _, _) in buyers[i][1]}
        conds = []
        for i in I:
            tot = z3.Sum([f[(i, j)] for (j, _, _) in buyers[i][1]] + [z3.RealVal(0)])
            conds += [v[i] >= 0, tot <= buyers[i][0], z3.Or(v[i] == 0, tot == buyers[i][0])]
            for (j, a, b) in buyers[i][1]:
                conds += [v[i] >= a - b * P[j], z3.Or(f[(i, j)] == 0, v[i] == a - b * P[j])]
        for j in J:
            L = z3.Sum([f[(i, jj)] for i in I for (jj, _, _) in buyers[i][1] if jj == j] + [z3.RealVal(0)])
            conds += [P[j] >= 0, L <= goods[j], z3.Or(P[j] == 0, L == goods[j])]
        # source types put no mass on real targets that are not options
        for i in I:
            optg = {j for (j, _, _) in buyers[i][1]}
            conds += [sig[(('src', i), ('real', j))] == 0 for j in J if j not in optg]
        s.add(z3.Not(z3.And(conds)))
        r = s.check(); done += 1
        if r != z3.unsat:
            bad += 1
            if not control: print('L8 BAD', mk)
    return done, bad

if __name__ == '__main__':
    # artifact: results kept in variables for the exit status (same calls, same order, same output)
    print('Lemma 2 (k, inc==D_k, linear between integers, min gap, F(0)=0, ends):')
    rows = lemma2(4)
    for row in rows: print('  ', row)
    l5 = lemma5()
    print('Lemma 5: optima with T<Tmax among 300 random LPs (M = sum kappa + 1/97):', l5)
    l5c = lemma5(control=True)
    print('Lemma 5 control (M = sum kappa / 3): failures', l5c)
    l8 = lemma8()
    print('Lemma 8 (trials, bad):', l8)
    l8c = lemma8(control=True)
    print('Lemma 8 control, slopes 1/20..1/60 (trials, bad):', l8c)
    # artifact: exit status -- Lemma 2 rows all true with min gap >= 6; Lemma 5 and 8 no failures;
    # both controls caught (at least one failure)
    ok = all(r[1] and r[2] and r[3] >= 6 and r[4] and r[5] for r in rows) and len(rows) == 4
    ok = ok and l5 == 0 and l5c > 0 and l8[1] == 0 and l8c[1] > 0
    sys.exit(0 if ok else 1)
