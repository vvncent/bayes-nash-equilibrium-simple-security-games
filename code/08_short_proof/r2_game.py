# End-to-end: explicit one-resource Bayesian simple security game (Lemma 8 table), EVERY
# (type,target) pair encoded; check every BNE decodes to the run's answer.
import sys, os, random, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from r2lib import *

def build_game(inst, **kw):
    buyers, goods, opts, meta = build_market(inst, **kw)
    I = list(buyers); J = list(goods)
    W = 1 + sum(Fr(buyers[i]) for i in I) + max(Fr(goods[j]) for j in J)
    A = 1 + max(0, max(Fr(a) for (_, _, a, _) in opts))
    S = 1 + (len(I) + len(J)) * A
    targets = [('real', j) for j in J] + [('priv', i) for i in I] + [('out',), ('ctl',)]
    types = [('src', i) for i in I] + [('ded', j) for j in J] + [('ctl',)]
    weight = {}
    pay = {}  # (type,target) -> (u0, slope)
    for th in types:
        for k in targets: pay[(th, k)] = (Fr(-2), Fr(1))
    for i in I:
        th = ('src', i); weight[th] = W + buyers[i]
        pay[(th, ('priv', i))] = (A / S, Fr(1))
        pay[(th, ('out',))] = (Fr(0), Fr(1))
    for (i, j, a, b) in opts:
        pay[(('src', i), ('real', j))] = (Fr(a) / S, Fr(b))
    for j in J:
        th = ('ded', j); weight[th] = W - goods[j]
        pay[(th, ('real', j))] = (Fr(2), Fr(1))
    weight[('ctl',)] = W
    pay[(('ctl',), ('ctl',))] = (Fr(2), Fr(1))
    for key, (u0, sl) in pay.items(): assert sl >= 0  # legal: covered <= uncovered for attacker
    assert all(w > 0 for w in weight.values())
    return types, targets, weight, pay, meta, buyers

def bne_constraints(types, targets, weight, pay):
    R = lambda q: z3.RealVal(str(q))
    xi = {k: z3.Real(f'xi_{k}') for k in targets}
    sg = {(th, k): z3.Real(f's_{th}_{k}') for th in types for k in targets}
    u = {th: z3.Real(f'u_{th}') for th in types}
    L = z3.Real('L')
    cons = [z3.Sum(list(xi.values())) == 1] + [x >= 0 for x in xi.values()]
    for th in types:
        cons.append(z3.Sum([sg[(th, k)] for k in targets]) == 1)
        for k in targets:
            u0, sl = pay[(th, k)]
            U = R(u0) - R(sl) * xi[k]
            cons += [sg[(th, k)] >= 0, u[th] >= U, z3.Or(sg[(th, k)] == 0, u[th] == U)]
    for k in targets:
        lk = z3.Sum([R(weight[th]) * sg[(th, k)] for th in types])
        cons += [L >= lk, z3.Or(xi[k] == 0, lk == L)]
    return xi, sg, u, cons

if __name__ == '__main__':
    n = int(sys.argv[1]); cnt = int(sys.argv[2]); rng = random.Random(int(sys.argv[3]))
    neg = len(sys.argv) > 4 and sys.argv[4] == 'swap'
    insts = all_instances(n)
    if cnt < len(insts):
        # prefer discriminating ones: include both answers
        rng.shuffle(insts); insts = insts[:cnt]
    ok = bad = 0
    for idx, inst in enumerate(insts):
        t0 = time.time()
        types, targets, weight, pay, meta, buyers = build_game(inst, swap=neg)
        xi, sg, u, cons = bne_constraints(types, targets, weight, pay)
        V, o, s0, s1 = inst
        t = run(V, o, s0, s1); ey = 1 if t == YES else 0
        dec = z3.Sum([z3.RealVal(str(weight[('src', i)])) * sg[(('src', i), ('real', ('E',)))] for i in meta['yes_sinks']] or [z3.RealVal(0)])
        s = z3.Solver(); s.add(cons)
        ex = s.check() if not neg else None
        s.add(dec != ey)
        r = s.check()
        extra = ''
        if r == z3.sat: extra = f' dec={s.model().eval(dec)} expected={ey}'
        good = (r == z3.unsat and ex == z3.sat)
        if neg: good = (r == z3.sat)
        ok += good; bad += (not good)
        print(f'[{idx}] {" ".join(f"{v}:({s0[v]},{s1[v]})" for v in V)} run->{t} types={len(types)} targets={len(targets)} exist={ex} wrong-decode={r}{extra} {time.time()-t0:.1f}s', flush=True)
    print(('NEG swap: caught ' if neg else f'n={n}: OK ') + f'{ok}, other {bad}')
    # artifact: exit status -- swap control: caught on at least one instance; otherwise other 0
    sys.exit(0 if ((ok > 0) if neg else (bad == 0)) else 1)
