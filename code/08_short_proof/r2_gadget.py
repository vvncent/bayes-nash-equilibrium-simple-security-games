# Lemma 6 check: every optimum of G(c,x,M-P',M-eps-P'') has (A,B) = (hbar0(x), hbar1(x)).
# Optimality is encoded exactly by primal feasibility + dual feasibility + equal objectives.
import sys, os, random
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from r2lib import *

def gadget_check(m, c, x, Pa, Pb, eps=3, M=None):
    nodes, arcs = splitter(m)
    K = 2 ** (m + 1)
    if M is None: M = 2 * 3 ** (m + 1)
    incap = {u: 0 for u in nodes}
    for (t, h, cc, k) in arcs: incap[h] += cc
    mass = {u: (c if u == 's' else incap[u]) for u in nodes}
    fin = {('g', ei): arcs[ei][2] for ei in range(len(arcs))}
    fin[('p',)] = c - x
    opts = []
    for ei, (t, h, cc, k) in enumerate(arcs):
        opts.append((t, ('g', ei), 2 * M - k)); opts.append((h, ('g', ei), 2 * M))
    opts.append(('s', ('p',), 2 * M))
    opts.append(('a', 'pa', M - Pa)); opts.append(('b', 'pb', M - eps - Pb))
    R = lambda q: z3.RealVal(str(Fr(q)))
    s = z3.Solver()
    f = [z3.Real(f'f{i}') for i in range(len(opts))]
    vv = {u: z3.Real(f'v_{u}') for u in nodes}
    pi = {j: z3.Real(f'pi_{j}') for j in fin}
    for xx in f: s.add(xx >= 0)
    for u in nodes:
        s.add(vv[u] >= 0)
        s.add(z3.Sum([f[i] for i, o in enumerate(opts) if o[0] == u]) <= R(mass[u]))
    for j in fin:
        s.add(pi[j] >= 0)
        s.add(z3.Sum([f[i] for i, o in enumerate(opts) if o[1] == j]) <= R(fin[j]))
    for i, (u, j, a) in enumerate(opts):
        s.add(vv[u] + (pi[j] if j in fin else 0) >= R(a))
    prim = z3.Sum([R(a) * f[i] for i, (u, j, a) in enumerate(opts)])
    dual = z3.Sum([R(mass[u]) * vv[u] for u in nodes] + [R(fin[j]) * pi[j] for j in fin])
    s.add(prim == dual)
    A = f[len(opts) - 2]; B = f[len(opts) - 1]
    xm = min(Fr(x), K)
    eA, eB = h0(xm), h1(xm)
    r0 = s.check()
    assert r0 == z3.sat, 'no optimum?'
    mod = s.model()
    s.add(z3.Or(A != R(eA), B != R(eB)))
    r = s.check()
    info = None
    if r == z3.sat:
        mm = s.model(); info = (to_fr(mm.eval(A)), to_fr(mm.eval(B)), eA, eB)
    return r, info

if __name__ == '__main__':
    rng = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 1)
    tot = bad = 0
    for m in [1, 2, 3, 4, 5, 6]:
        K = 2 ** (m + 1)
        caps = [1 + 2 ** m, 1 + 2 ** m * 2 * m, 2 + 2 ** m * 3, K + 1]
        for c in caps:
            xs = set([Fr(0), Fr(K), Fr(c) - Fr(1, 97)])
            xs |= {Fr(j) for j in range(0, min(c, K + 3))}
            xs |= {Fr(2 * z + 1) + d for z in range(0, K // 2) for d in (Fr(1, 101), -Fr(1, 101))}
            xs |= {Fr(rng.randrange(0, 10 ** 6 * c), 10 ** 6) for _ in range(6)}
            xs = sorted(q for q in xs if 0 <= q < c)
            if m >= 5: xs = rng.sample(xs, min(len(xs), 14)) + [Fr(K), Fr(K) - Fr(1, 3), Fr(0)]
            xs = [q for q in xs if q < c]
            for x in xs:
                for (Pa, Pb) in [(0, 0), (0, 1), (1, 0), (1, 1), (Fr(rng.randrange(1, 99), 99), Fr(rng.randrange(1, 99), 99))]:
                    r, info = gadget_check(m, c, x, Pa, Pb)
                    tot += 1
                    if r != z3.unsat:
                        bad += 1; print('FAIL', m, c, x, Pa, Pb, r, info, flush=True)
        print(f'm={m} done, checks so far {tot}, failures {bad}', flush=True)
    # negative controls: each must produce a counterexample somewhere
    allcaught = True  # artifact: exit status
    print('--- negative controls (must FAIL) ---')
    for name, kw, Pa, Pb in [('eps=0,P\'=1,P\"=0 (theta=-1)', dict(eps=0), 1, 0),
                             ('eps=6,P\'=0,P\"=1 (theta=7)', dict(eps=6), 0, 1),
                             ('M=Sigma_kappa/3', dict(M=None), 0, 0)]:
        for m in [2, 3]:
            K = 2 ** (m + 1); c = 1 + 2 ** m * 2
            kk = dict(kw)
            if name.startswith('M='): kk['M'] = (2 * 3 ** (m + 1) - 6) // 3
            found = None
            for x in [Fr(j, 2) for j in range(0, 2 * K)] + [Fr(j) + Fr(1, 3) for j in range(K)]:
                if x >= c: continue
                r, info = gadget_check(m, c, x, Pa, Pb, **kk)
                if r == z3.sat: found = (x, info); break
            print(name, 'm=', m, 'counterexample:' if found else 'NOT CAUGHT', found, flush=True)
            allcaught &= found is not None  # artifact: exit status
    print('TOTAL', tot, 'FAILURES', bad)
    sys.exit(0 if (bad == 0 and allcaught) else 1)  # artifact: exit status
