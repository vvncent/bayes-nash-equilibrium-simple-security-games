# harder instance families for Theorem 7: longest runs among random samples, and high-indegree hubs
import sys, os, random, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from r2lib import *
from r2_market import check, fmt

def runlen(I):
    V, o, s0, s1 = I
    cur = {v: 0 for v in V}; v = o; k = 0
    while v in cur:
        w = s0[v] if cur[v] == 0 else s1[v]; cur[v] ^= 1; v = w; k += 1
    return k

n = int(sys.argv[1]); cnt = int(sys.argv[2]); rng = random.Random(int(sys.argv[3]))
pool = {}
for _ in range(20000):
    I = random_instance(n, rng)
    pool[fmt(I)] = I
L = sorted(pool.values(), key=lambda I: -runlen(I))
chosen = L[:cnt]
# hubs: every vertex sends one edge to vertex hub (indegree ~ n), other edge random; terminals far
hubs = [I for I in pool.values() if max(sum(1 for v in I[0] for s in (I[2][v], I[3][v]) if s == w) for w in I[0]) >= n + 1]
chosen += hubs[:cnt // 2]
# both successors equal / self-loops at origin
chosen += [I for I in pool.values() if I[2][0] == 0 and I[1] == 0][:3]
ok = bad = 0
for idx, I in enumerate(chosen):
    t0 = time.time()
    ex, r, cx, sz = check(I)
    V, o, s0, s1 = I
    good = (ex == z3.sat and r == z3.unsat); ok += good; bad += not good
    print(f'[{idx}] {fmt(I)} runlen={runlen(I)} run->{run(V,o,s0,s1)} exist={ex} wrong-decode={r} {time.time()-t0:.1f}s' + ('' if good else f' FAIL {cx}'), flush=True)
print(f'n={n} hard: OK {ok}, FAIL {bad}')
sys.exit(0 if bad == 0 else 1)  # artifact: exit status
