# Theorem 7 on random preprocessed n=4 instances (n'=4 kept), half chosen with long runs.
# usage: SHARD=i/k python -I check_composed_n4.py count seed
import sys, os, random, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import z3
from ref_lib import *
from check_composed import check, degenerate_tags

def runlen(n, s0, s1, o):
    sw = [0] * n; cur = o; k = 0
    while cur not in (YES, NO):
        nxt = s0[cur] if sw[cur] == 0 else s1[cur]; sw[cur] ^= 1; cur = nxt; k += 1
    return k

if __name__ == '__main__':
    cnt = int(sys.argv[1]); seed = int(sys.argv[2])
    rng = random.Random(seed); T = list(range(4)) + [YES, NO]
    pool = []
    seen = set()
    while len(pool) < 4000:
        s0 = [rng.choice(T) for _ in range(4)]; s1 = [rng.choice(T) for _ in range(4)]
        q = preprocess(4, s0, s1, 0)
        if q[0] != 4: continue
        key = canon(*q)
        if key in seen: continue
        seen.add(key); pool.append(q)
    pool.sort(key=lambda q: -runlen(*q))
    items = pool[:cnt // 2] + rng.sample(pool[cnt // 2:], cnt - cnt // 2)
    sh = os.environ.get('SHARD')
    if sh:
        i, k = map(int, sh.split('/')); items = items[i::k]
    bad = 0; t0 = time.time()
    for q in items:
        ans, ex, r, cex, rp = check(*q)
        ok = ex == z3.sat and r == z3.unsat and rp == z3.unsat
        bad += not ok
        print('OK ' if ok else 'BAD', q, ans, 'runlen', runlen(*q), sorted(degenerate_tags(*q)), ex, r, cex, rp, flush=True)
    print('n=4 instances %d bad %d %.0fs' % (len(items), bad, time.time() - t0))
    sys.exit(0 if bad == 0 else 1)  # artifact: exit status
