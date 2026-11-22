"""Run the exact Algorithm 1 on G_n of scaling/findings.md Theorem 1 (built read-only by
its experiments/game.py) and count successful Algorithm 3 calls."""
from fractions import Fraction as F
import sys
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
sys.path.insert(1, str(Path(__file__).resolve().parent.parent / "lib"))  # artifact: shared modules in lib/
EXP = str(Path(__file__).resolve().parent.parent / "lib")  # artifact: scaling game.py/mcf.py copied to lib/
sys.path.insert(1, EXP)
from lck_alg import Rule, algorithm1, Stuck  # noqa: E402
from security import SecurityGame, is_bne_security  # noqa: E402
from run_family_a import RULES  # noqa: E402
import game as scaling_game  # noqa: E402


def family_b(n):
    G = scaling_game.Gn(n)
    m = G.V
    uu = [list(row) for row in G.a]
    uc = [[G.a[k][u] - G.b[k][u] for u in range(m)] for k in range(len(G.p))]
    S = SecurityGame(G.r, G.p, uu, uc, [F(0)] * m, list(G.d))
    return S, G


def run(n, rname, seed=0):
    S, G = family_b(n)
    CE = S.to_ce()
    rule = Rule(seed=seed, **RULES[rname])
    t0 = time.time()
    x0, x, stats, log = algorithm1(CE, rule)
    attack = [[x[i][t] / S.prior[i] for t in range(S.m)] for i in range(S.n)]
    bne = is_bne_security(S, x0, attack)
    # special-pair mass seen along successful calls (fixed within a call)
    return dict(n=n, rule=rname, seed=seed, bne=bne, succ=stats['alg3_success'], fail=stats['alg3_fail'],
                bound=2 ** n, cancels=stats['cancel'], secs=round(time.time() - t0, 1), types=S.n, targets=S.m)


if __name__ == '__main__':
    ns = [int(a) for a in sys.argv[1].split(',')]
    rules = sys.argv[2].split(',') if len(sys.argv) > 2 else list(RULES)
    allok = True  # artifact: exit status
    for n in ns:
        for r in rules:
            try:
                res = run(n, r)
                print(res, flush=True)
                allok &= res['bne'] is True and res['succ'] >= res['bound']  # artifact: exit status (>= 2^n, exact BNE)
            except Stuck as e:
                print(dict(n=n, rule=r, stuck=str(e)), flush=True)
                allok = False  # artifact: exit status
    sys.exit(0 if allok else 1)  # artifact: exit status
