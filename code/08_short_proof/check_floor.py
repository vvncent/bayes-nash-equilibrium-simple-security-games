# Lemma 1 / floor trick: exact z3 check over the piecewise-linear fixed-point system (FP).
# For every ARRIVAL instance with n <= N (origin 0 wlog; ALL instances, not only preprocessed):
#  Q1: exists fixed point violating Lemma 1's conclusion (y_{t*}=1, other 0, t* = run's terminal;
#      if the run never terminates, any fixed point is a violation)?
#  Q2: exists fixed point whose floor is not a fixed point with the same terminal inflows?
#  Q3 (non-vacuity): exists a fixed point with a non-integral coordinate?
# usage: python -I check_floor.py N [sample_n4]
import sys, random, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import z3
from ref_lib import run, all_instances, YES, NO

def encode(n, s0, s1, o):
    s = z3.Solver()
    z = [z3.Int('z%d' % u) for u in range(n)]
    r = [z3.Real('r%d' % u) for u in range(n)]
    x = [2 * z[u] + r[u] for u in range(n)]
    H = {}
    Hb = {}
    for u in range(n):
        s.add(z[u] >= 0, r[u] >= 0, r[u] < 2)
        H[(u, 0)] = z[u] + z3.If(r[u] < 1, r[u], 1)
        H[(u, 1)] = z[u] + z3.If(r[u] > 1, r[u] - 1, 0)
        fl = 2 * z[u] + z3.If(r[u] >= 1, 1, 0)       # floor(x_u)
        Hb[(u, 0)] = z[u] + z3.If(r[u] >= 1, 1, 0)    # h0(floor x_u)
        Hb[(u, 1)] = z[u] + 0                          # h1(floor x_u)
    succ = lambda u, i: s0[u] if i == 0 else s1[u]
    def inflow(w, HH):
        t = [HH[(u, i)] for u in range(n) for i in (0, 1) if succ(u, i) == w]
        return z3.Sum(t) if t else z3.IntVal(0)
    for v in range(n):
        s.add(x[v] == (1 if v == o else 0) + inflow(v, H))
    y = {t: inflow(t, H) for t in (YES, NO)}
    floor_ok = z3.And([2 * z[v] + z3.If(r[v] >= 1, 1, 0) == (1 if v == o else 0) + inflow(v, Hb) for v in range(n)]
                      + [inflow(t, Hb) == y[t] for t in (YES, NO)])
    return s, y, floor_ok, r

def check(n, s0, s1, o):
    ans = run(n, s0, s1, o)
    s, y, floor_ok, r = encode(n, s0, s1, o)
    res = {}
    s.push()
    if ans is None:
        pass
    else:
        oth = NO if ans == YES else YES
        s.add(z3.Not(z3.And(y[ans] == 1, y[oth] == 0)))
    res['Q1'] = s.check(); s.pop()
    s.push(); s.add(z3.Not(floor_ok)); res['Q2'] = s.check(); s.pop()
    s.push(); s.add(z3.Or([z3.And(ri != 0, ri != 1) for ri in r])); res['Q3'] = s.check(); s.pop()
    s.push(); res['exists'] = s.check(); s.pop()
    return ans, res

if __name__ == '__main__':
    N = int(sys.argv[1])
    sample4 = int(sys.argv[2]) if len(sys.argv) > 2 else 0
    jobs = []
    for n in range(1, N + 1):
        jobs += [(n, s0, s1, o) for s0, s1, o in all_instances(n)]
    if sample4:
        rng = random.Random(4)
        T = list(range(4)) + [YES, NO]
        for _ in range(sample4):
            jobs.append((4, [rng.choice(T) for _ in range(4)], [rng.choice(T) for _ in range(4)], 0))
    bad = 0; frac = 0; nonterm_fp = 0; cnt = 0
    for (n, s0, s1, o) in jobs:
        ans, res = check(n, s0, s1, o)
        cnt += 1
        if res['Q1'] != z3.unsat or res['Q2'] != z3.unsat:
            bad += 1
            print('VIOLATION', n, s0, s1, o, ans, res, flush=True)
        if res['Q3'] == z3.sat: frac += 1
        if ans is None and res['exists'] == z3.sat: nonterm_fp += 1
        if ans is not None and res['exists'] != z3.sat:
            print('NOTE: terminating run but no fixed point', n, s0, s1, o, flush=True)
    print('instances', cnt, 'violations', bad, 'with fractional fixed points', frac,
          'nonterminating-with-FP', nonterm_fp)
    sys.exit(0 if (bad == 0 and nonterm_fp == 0) else 1)  # artifact: exit status (README expected line)
