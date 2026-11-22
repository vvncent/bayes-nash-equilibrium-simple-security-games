# Theorem 7 check: in EVERY equilibrium of the composed market, the yes-sinks put load
# [run reaches yes] on E and the no-sinks [run reaches no].  Exact z3 (QF_LRA with disjunctions).
import sys, os, random, time, json
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from r2lib import *

def check(inst, want_existence=True, **kw):
    buyers, goods, opts, meta = build_market(inst, **kw)
    P, v, f, cons = market_eq_constraints(buyers, goods, opts)
    V, o, s0, s1 = inst
    t = run(V, o, s0, s1)
    ey, en = (1, 0) if t == YES else (0, 1)
    ly = z3.Sum([f[(i, ('E',))] for i in meta['yes_sinks']]) if meta['yes_sinks'] else z3.RealVal(0)
    ln = z3.Sum([f[(i, ('E',))] for i in meta['no_sinks']]) if meta['no_sinks'] else z3.RealVal(0)
    s = z3.Solver(); s.add(cons)
    ex = None
    if want_existence:
        ex = s.check()
    s.add(z3.Or(ly != ey, ln != en))
    r = s.check()
    cx = None
    if r == z3.sat:
        mm = s.model()
        cx = dict(ly=str(mm.eval(ly)), ln=str(mm.eval(ln)), expected=(ey, en),
                  xs={str(w): str(mm.eval(z3.Sum([f[(i, ('p', w))] for (i, j, a, b) in opts if j == ('p', w) and i[1] != 's'] or [z3.RealVal(0)]))) for w in V})
    return ex, r, cx, (len(buyers), len(goods), len(opts))

def fmt(inst):
    V, o, s0, s1 = inst
    return ' '.join(f'{v}:({s0[v]},{s1[v]})' for v in V)

if __name__ == '__main__':
    mode = sys.argv[1]
    if mode == 'all':
        n = int(sys.argv[2])
        insts = all_instances(n)
        if len(sys.argv) > 3:
            rng = random.Random(int(sys.argv[4])); insts = rng.sample(insts, int(sys.argv[3]))
    elif mode == 'rand':
        n = int(sys.argv[2]); cnt = int(sys.argv[3]); rng = random.Random(int(sys.argv[4]))
        insts = []
        while len(insts) < cnt:
            I = random_instance(n, rng)
            # prefer long runs / discriminating instances: require both terminals reachable
            insts.append(I)
    elif mode == 'neg':
        n = int(sys.argv[2]); cnt = int(sys.argv[3]); rng = random.Random(int(sys.argv[4]))
        kw = json.loads(sys.argv[5])
        if 'lamfac' in kw: kw['lamfac'] = Fr(kw['lamfac'])
        insts = all_instances(n)
        rng.shuffle(insts)
    kw = {} if mode != 'neg' else kw
    ok = bad = 0
    caught = 0
    for idx, I in enumerate(insts):
        if mode == 'neg' and idx >= cnt: break
        t0 = time.time()
        ex, r, cx, sz = check(I, want_existence=(mode != 'neg'), **kw)
        dt = time.time() - t0
        V, o, s0, s1 = I
        line = f'[{idx}] {fmt(I)} run->{run(V, o, s0, s1)} size(b,g,opt)={sz} exist={ex} wrong-decode={r} {dt:.1f}s'
        if mode == 'neg':
            if r == z3.sat: caught += 1; line += f' CAUGHT {cx}'
        else:
            if r == z3.unsat and ex == z3.sat: ok += 1
            else: bad += 1; line += f' FAIL {cx}'
        print(line, flush=True)
    if mode == 'neg':
        print(f'NEG {kw}: caught {caught} of {min(cnt, len(insts))}')
    else:
        print(f'n={n}: OK {ok}, FAIL {bad}')
    # artifact: exit status -- neg (control): caught on at least one instance; otherwise FAIL 0
    sys.exit(0 if ((caught > 0) if mode == 'neg' else (bad == 0 and ok > 0)) else 1)
