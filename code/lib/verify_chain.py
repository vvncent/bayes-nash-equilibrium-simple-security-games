"""Baseline family: the threshold chain G_K (K unit buyers + 1 slack buyer + input good; size K+2).
Reproduce: $PY -I verify_chain.py
Certifies S1 and S2 (switchcheck.check) exactly for K = 2,4,8,16,32 with box U = 1."""
import sys, os, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from fractions import Fraction as F
from switchcheck import check, size, bits

def chain(K, Ms=None):
    lam = 2 * K + 2
    Ms = 2 * K if Ms is None else Ms
    buyers = []
    for k in range(1, K + 1):
        o = "a" if k % 2 == 1 else "b"
        buyers.append((1, {"p": (2 * k + 1, lam), o: (2, 1)}))
    buyers.append((Ms, {"p": (2 * K + 1, lam)}))
    return {"cp": K + Ms, "goods": {}, "buyers": buyers}

if __name__ == "__main__":
    print("K  size  bits  certified  seconds")
    allok = True
    for K in [2, 4, 8, 16, 32]:
        g = chain(K); t = time.time()
        ok, res = check(g, K, 1)
        allok &= ok
        print(K, size(g), bits(g), ok, round(time.time() - t, 1))
    print("ALL CERTIFIED" if allok else "FAILURE")
