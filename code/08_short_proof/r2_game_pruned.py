# Same as r2_game.py, but pairs (type,target) with payoff -2 - xi are fixed to sigma = 0.
# Soundness (pure arithmetic, independent of the proof): such a pair pays <= -2, while every
# source type has o paying -xi_o >= -1 and every dedicated/control type has its own target paying
# 2 - xi >= 1; a strictly dominated pure strategy has probability 0 in every BNE.
import sys, os, random, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from r2lib import *
from r2_game import build_game

def bne_pruned(types, targets, weight, pay):
    R = lambda q: z3.RealVal(str(q))
    xi = {k: z3.Real(f'xi_{k}') for k in targets}
    sg = {}
    u = {th: z3.Real(f'u_{th}') for th in types}
    L = z3.Real('L')
    cons = [z3.Sum(list(xi.values())) == 1] + [x >= 0 for x in xi.values()]
    for th in types:
        live = []
        for k in targets:
            u0, sl = pay[(th, k)]
            U = R(u0) - R(sl) * xi[k]
            cons.append(u[th] >= U)
            if u0 == -2:
                continue
            sg[(th, k)] = z3.Real(f's_{th}_{k}'); live.append(sg[(th, k)])
            cons += [sg[(th, k)] >= 0, z3.Or(sg[(th, k)] == 0, u[th] == U)]
        cons.append(z3.Sum(live) == 1)
    for k in targets:
        terms = [R(weight[th]) * sg[(th, k)] for th in types if (th, k) in sg]
        lk = z3.Sum(terms) if terms else z3.RealVal(0)
        cons += [L >= lk, z3.Or(xi[k] == 0, lk == L)]
    return xi, sg, u, cons

n = int(sys.argv[1]); cnt = int(sys.argv[2]); rng = random.Random(int(sys.argv[3]))
neg = len(sys.argv) > 4 and sys.argv[4] == 'swap'
insts = all_instances(n); rng.shuffle(insts); insts = insts[:cnt]
ok = 0
for idx, inst in enumerate(insts):
    t0 = time.time()
    types, targets, weight, pay, meta, buyers = build_game(inst, swap=neg)
    # dominance sanity: every type has a non -2 option with payoff >= -1 always
    xi, sg, u, cons = bne_pruned(types, targets, weight, pay)
    V, o, s0, s1 = inst
    t = run(V, o, s0, s1); ey = 1 if t == YES else 0
    dec = z3.Sum([z3.RealVal(str(weight[('src', i)])) * sg[(('src', i), ('real', ('E',)))] for i in meta['yes_sinks']] or [z3.RealVal(0)])
    s = z3.Solver(); s.add(cons)
    ex = s.check() if not neg else None
    s.add(dec != ey); r = s.check()
    good = (r == z3.sat) if neg else (r == z3.unsat and ex == z3.sat); ok += good
    print(f'[{idx}] {" ".join(f"{v}:({s0[v]},{s1[v]})" for v in V)} run->{t} types={len(types)} targets={len(targets)} exist={ex} wrong-decode={r} {time.time()-t0:.1f}s', flush=True)
print(('NEG swap caught ' if neg else f'n={n} pruned: OK ') + f'{ok} of {len(insts)}')
# artifact: exit status -- swap control: caught on at least one instance; otherwise OK on all
sys.exit(0 if ((ok > 0) if neg else (ok == len(insts))) else 1)
