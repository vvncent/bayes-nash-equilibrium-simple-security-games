"""Run Algorithm 1 on random small Bayesian security games under several tie-breaking
rules and check the output exactly with an independent Bayes-Nash test."""
import random
import sys
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
sys.path.insert(1, str(Path(__file__).resolve().parent.parent / "lib"))  # artifact: shared modules in lib/
from lck_alg import Rule, algorithm1, Stuck
from security import random_security_game, is_bne_security

RULES = [
    dict(init='asc', flow='cancel', alg3='asc', maxflow='asc', cycle='asc'),
    dict(init='desc', flow='ssp', alg3='desc', maxflow='desc', cycle='desc'),
    dict(init='rand', flow='cancel', alg3='rand', maxflow='rand', cycle='rand'),
    dict(init='rand', flow='ssp', alg3='rand', maxflow='rand', cycle='rand'),
]


def main(count=40, seed=1):
    rng = random.Random(seed)
    ok = bad = stuck = 0
    t0 = time.time()
    for g in range(count):
        n, m = rng.randint(1, 4), rng.randint(2, 5)
        R = 3 if g % 2 else 10  # narrow payoff ranges create ties
        S = random_security_game(rng, n, m, R)
        for k, rd in enumerate(RULES):
            G = S.to_ce()
            rule = Rule(seed=1000 * g + k, **rd)
            try:
                x0, x, stats, log = algorithm1(G, rule)
            except Stuck as e:
                stuck += 1
                print(f"game {g} rule {k}: STUCK {e}")
                continue
            attack = [[x[i][t] / S.prior[i] for t in range(S.m)] for i in range(S.n)]
            good = is_bne_security(S, x0, attack)
            ok += good
            bad += not good
            print(f"game {g} n={n} m={m} rd={S.rd} rule {k}: BNE={good} succ3={stats['alg3_success']} "
                  f"fail3={stats['alg3_fail']} cancels={stats['cancel']}")
    print(f"SUMMARY ok={ok} bad={bad} stuck={stuck} runs={count * len(RULES)} time={time.time() - t0:.1f}s")
    return bad == 0 and stuck == 0 and ok == count * len(RULES)  # artifact: exit status


if __name__ == '__main__':
    sys.exit(0 if main(int(sys.argv[1]) if len(sys.argv) > 1 else 40) else 1)  # artifact: exit status
