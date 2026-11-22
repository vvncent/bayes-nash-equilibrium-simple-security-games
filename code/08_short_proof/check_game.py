# End-to-end: build the explicit one-resource Bayesian simple security game of section 6 from the
# market of section 5 and ask z3 for a BNE (Fact 0 conditions, ALL (type,target) pairs encoded) whose
# decoder value  sum_{yes-sinks} (W+mu_i) sigma_i(E)  differs from [run=yes] (and same for no).
# Also verifies Fact 0 is applied to a legal Conitzer instance (u2^0 >= u2^1, u1^0 <= u1^1, prior>0).
# usage: python -I check_game.py n [limit] [seed]
import sys, os, time, random
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from fractions import Fraction as Fr
import z3
from ref_lib import *

def build_game(mk):
    I = list(mk['buyers']); J = list(mk['goods'])
    mu = {i: Fr(mk['buyers'][i][0]) for i in I}
    W = 1 + sum(mu.values()) + max(Fr(c) for c in mk['goods'].values())
    A = 1 + max([Fr(0)] + [Fr(a) for i in I for (_, a, _) in mk["buyers"][i][1]])
    S = 1 + (len(I) + len(J)) * A
    targets = [('real', j) for j in J] + [('priv', i) for i in I] + [('out',), ('ctl',)]
    types = {}
    # type -> (weight, {target: (u0, slope)})
    for i in I:
        pay = {t: (Fr(-2), Fr(1)) for t in targets}
        for (j, a, b) in mk['buyers'][i][1]:
            pay[('real', j)] = (Fr(a) / S, Fr(b))
        pay[('priv', i)] = (A / S, Fr(1))
        pay[('out',)] = (Fr(0), Fr(1))
        types[('src', i)] = (W + mu[i], pay)
    for j in J:
        pay = {t: (Fr(-2), Fr(1)) for t in targets}
        pay[('real', j)] = (Fr(2), Fr(1))
        types[('ded', j)] = (W - Fr(mk['goods'][j]), pay)
    pay = {t: (Fr(-2), Fr(1)) for t in targets}
    pay[('ctl',)] = (Fr(2), Fr(1))
    types[('ctl',)] = (W, pay)
    for th, (w, pay) in types.items():
        assert w > 0
        for t, (u0, sl) in pay.items():
            assert sl >= 0  # u2^0 >= u2^1
    return targets, types, W

def bne(targets, types, s):
    xi = {t: z3.Real('xi_%s' % (t,)) for t in targets}
    s.add(z3.Sum(list(xi.values())) == 1)
    for t in targets: s.add(xi[t] >= 0, xi[t] <= 1)
    sig = {}
    load = {t: [] for t in targets}
    for th, (w, pay) in types.items():
        u = z3.Real('u_%s' % (th,))
        row = []
        for t in targets:
            g = z3.Real('s_%s_%s' % (th, t)); sig[(th, t)] = g
            U = pay[t][0] - pay[t][1] * xi[t]
            s.add(g >= 0, u >= U, z3.Or(g == 0, u == U))
            row.append(g); load[t].append(w * g)
        s.add(z3.Sum(row) == 1)
    L = z3.Real('L')
    for t in targets:
        lt = z3.Sum(load[t])
        s.add(L >= lt, z3.Or(xi[t] == 0, lt == L))
    return xi, sig

def check(n, s0, s1, o):
    ans = run(n, s0, s1, o)
    mk = build_market(n, s0, s1, o)
    targets, types, W = build_game(mk)
    s = z3.Solver()
    xi, sig = bne(targets, types, s)
    def dec(sinks):
        t = [(W + mk['buyers'][i][0]) * sig[(('src', i), ('real', ('E',)))] for i in sinks]
        return z3.Sum(t) if t else z3.RealVal(0)
    dy = dec(yes_sinks(n, s0, s1, mk)); dn = dec(no_sinks(n, s0, s1, mk))
    s.push(); ex = s.check(); s.pop()
    s.add(z3.Not(z3.And(dy == (1 if ans == YES else 0), dn == (1 if ans == NO else 0))))
    r = s.check()
    return ans, ex, r, len(types), len(targets)

if __name__ == '__main__':
    n = int(sys.argv[1]); limit = int(sys.argv[2]) if len(sys.argv) > 2 else None
    seed = int(sys.argv[3]) if len(sys.argv) > 3 else 0
    seen = {}
    for s0, s1, o in all_instances(n):
        q = preprocess(n, s0, s1, o)
        if q[0] != n: continue
        seen.setdefault(canon(*q), q)
    items = list(seen.values())
    if limit and limit < len(items):
        random.Random(seed).shuffle(items); items = items[:limit]
    bad = 0
    for q in items:
        t0 = time.time()
        ans, ex, r, nt, ng = check(*q)
        ok = ex == z3.sat and r == z3.unsat
        bad += not ok
        print(('OK ' if ok else 'BAD'), q, ans, 'exists', ex, 'violation', r, 'types', nt, 'targets', ng,
              'formula', 12 * n * n + 6 * n + 2, 12 * n * n + 6 * n + 3, '%.0fs' % (time.time() - t0), flush=True)
    print('n=%d instances %d bad %d' % (n, len(items), bad))
    sys.exit(0 if bad == 0 else 1)  # artifact: exit status
