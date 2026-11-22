# Theorem 7: for preprocessed ARRIVAL instances, ask z3 whether the market of section 5 has an
# equilibrium (P,v,f) in which the load put on E by the yes-sinks is not [run=yes] or the load by the
# no-sinks is not [run=no].  unsat => every equilibrium decodes correctly.  Also checks an equilibrium
# exists (non-vacuity) and that every equilibrium has all port prices in [0,1].
# usage: python -I check_composed.py n [limit] [seed]     (n = number of switches before preprocessing)
import sys, os, time, random
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import z3
from ref_lib import *

def check(n, s0, s1, o, **kw):
    ans = run(n, s0, s1, o)
    assert ans in (YES, NO)
    mk = build_market(n, s0, s1, o, **kw)
    s = z3.Solver()
    P, V, F = eq_constraints(mk, s)
    def load(sinks):
        t = [F[(i, ('E',))] for i in sinks]
        return z3.Sum(t) if t else z3.RealVal(0)
    ly = load(yes_sinks(n, s0, s1, mk)); ln = load(no_sinks(n, s0, s1, mk))
    s.push(); ex = s.check(); s.pop()
    s.push()
    s.add(z3.Not(z3.And(ly == (1 if ans == YES else 0), ln == (1 if ans == NO else 0))))
    r = s.check()
    cex = None
    if r == z3.sat:
        md = s.model(); cex = (md.eval(ly), md.eval(ln))
    s.pop()
    s.push(); s.add(z3.Or([P[g] > 1 for g in mk['goods'] if g[0] in ('p', 'E')])); rp = s.check(); s.pop()
    return ans, ex, r, cex, rp

def degenerate_tags(n, s0, s1, o):
    t = set()
    for v in range(n):
        if s0[v] == v or s1[v] == v: t.add('selfloop')
        if s0[v] == s1[v]: t.add('a=b')
        if s0[v] == s1[v] and s0[v] in (YES, NO): t.add('both-same-terminal')
        if s0[v] == o or s1[v] == o: t.add('origin-in-edge')
    return t

if __name__ == '__main__':
    n = int(sys.argv[1])
    limit = int(sys.argv[2]) if len(sys.argv) > 2 else None
    seed = int(sys.argv[3]) if len(sys.argv) > 3 else 0
    ctrl = sys.argv[4] if len(sys.argv) > 4 else None
    seen = {}
    for s0, s1, o in all_instances(n):
        raw_del = None
        q = preprocess(n, s0, s1, o)
        key = canon(*q)
        if key not in seen:
            seen[key] = (q, set())
        if q[0] < n: seen[key][1].add('preproc-deleted')
    items = list(seen.values())
    if limit and limit < len(items):
        random.Random(seed).shuffle(items); items = items[:limit]
    sh = os.environ.get('SHARD')
    if sh:
        i, k = map(int, sh.split('/'))
        items = items[i::k]
    kw = {}
    if ctrl == 'eps0': kw = dict(eps=0)
    if ctrl == 'lamM': kw = dict(lam=1)
    tags = {}
    bad = 0; t0 = time.time()
    for (q, tg) in items:
        nn, s0, s1, o = q
        ans, ex, r, cex, rp = check(nn, s0, s1, o, **kw)
        for tt in degenerate_tags(nn, s0, s1, o) | tg:
            tags[tt] = tags.get(tt, 0) + 1
        if ex != z3.sat or r != z3.unsat or rp != z3.unsat:
            bad += 1
            print('BAD', q, ans, ex, r, cex, rp, flush=True)
    print('n=%d control=%s instances(canonical, preprocessed) %d bad %d tags %s  %.0fs' %
          (n, ctrl, len(items), bad, tags, time.time() - t0), flush=True)
    # artifact: exit status -- no control: bad 0; control eps0/lamM: caught (bad > 0)
    sys.exit(0 if ((bad > 0) if ctrl in ('eps0', 'lamM') else (bad == 0)) else 1)
