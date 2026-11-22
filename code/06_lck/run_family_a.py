"""Run the exact Algorithm 1 on family (a) of round2/lck-security-path.md and count
successful Algorithm 3 calls, under several tie-breaking rules."""
from fractions import Fraction as F
import importlib.util
import sys
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
sys.path.insert(1, str(Path(__file__).resolve().parent.parent / "lib"))  # artifact: shared modules in lib/
from lck_alg import Rule, algorithm1, Stuck  # noqa: E402
from security import SecurityGame, is_bne_security  # noqa: E402

BUILDER = Path(__file__).resolve().parent.parent / "lib" / "auction_levels_check.py"  # artifact: was absolute path


def load_builder():
    spec = importlib.util.spec_from_file_location("auction_levels_readonly", BUILDER)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod.build_market


def signals(depth, domain, terminal):  # same recurrence as check_lck_security_path.py
    low, high = terminal, 2 * terminal
    outputs = [low, high]
    for level in range(1, depth + 1):
        shift = domain / 2 ** (level + 1)
        upper, lower = max(low, high) - shift, min(low, high) + shift
        outputs.extend((upper, lower))
        low, high = lower, upper
    return outputs


def family_a(build_market, h):
    goods = 2 * h + 2
    domain = F(1, 4 * goods)
    demands, supplies, values, slopes, output, special = build_market(h, domain)
    masses = [dm // 2 for dm in demands[:-1]]
    weights = [c // 2 for c in supplies]
    values, slopes = values[:-1], slopes[:-1]
    assert len(masses) == 5 * h + 2 and len(weights) == goods and sum(masses) == sum(weights)
    M = sum(masses)
    prior = [F(mm, M) for mm in masses]
    uu = [list(row) for row in values]
    uc = [[v - s for v, s in zip(row, srow)] for row, srow in zip(values, slopes)]
    ddu = [F(0)] * goods
    ddc = [F(M, c) for c in weights]
    return SecurityGame(1, prior, uu, uc, ddu, ddc), domain, output


RULES = {
    'R1': dict(init='asc', flow='cancel', alg3='asc', maxflow='asc', cycle='asc'),
    'R2': dict(init='desc', flow='ssp', alg3='desc', maxflow='desc', cycle='desc'),
    'R3': dict(init='rand', flow='cancel', alg3='rand', maxflow='rand', cycle='rand'),
    'R4': dict(init='rand', flow='ssp', alg3='rand', maxflow='rand', cycle='rand'),
}


def run(h, rname, seed=0, check_every=True):
    build_market = load_builder()
    S, domain, output = family_a(build_market, h)
    G = S.to_ce()
    rule = Rule(seed=seed, **RULES[rname])
    t0 = time.time()
    x0, x, stats, log = algorithm1(G, rule, check_every=check_every)
    attack = [[x[i][t] / S.prior[i] for t in range(S.m)] for i in range(S.n)]
    bne = is_bne_security(S, x0, attack)
    cut = F(3, 8)
    below = sum(1 for e in log if e['budget_before'] < cut)
    # compare the path with the claimed unique coverage P(y) at every call endpoint with budget <= 3/8
    off = signals(h, domain, F(0))
    mism = 0
    for e in log:
        for key in ('x0_before', 'x0_after'):
            b = sum(e[key])
            if b <= cut:
                y = b / (3 * (h + 1))
                P = [v - o for v, o in zip(signals(h, domain, y), off)]
                mism += P != e[key]
    return dict(h=h, rule=rname, seed=seed, bne=bne, succ=stats['alg3_success'], fail=stats['alg3_fail'],
                below=below, bound=2 ** (h - 1), path_mismatch=mism, cancels=stats['cancel'],
                secs=round(time.time() - t0, 1), types=S.n, targets=S.m)


if __name__ == '__main__':
    hs = [int(a) for a in sys.argv[1].split(',')]
    rules = sys.argv[2].split(',') if len(sys.argv) > 2 else list(RULES)
    seeds = [int(a) for a in sys.argv[3].split(',')] if len(sys.argv) > 3 else [0]
    check = (sys.argv[4] != 'nocheck') if len(sys.argv) > 4 else True
    allok = True  # artifact: exit status
    for h in hs:
        for r in rules:
            for sd in (seeds if RULES[r]['init'] == 'rand' else [0]):
                try:
                    res = run(h, r, sd, check)
                    print(res, flush=True)
                    # artifact: exit status -- exact BNE, exactly 2^(h-1) successful calls, no path mismatch
                    allok &= res['bne'] is True and res['succ'] == res['bound'] and res['path_mismatch'] == 0
                except Stuck as e:
                    print(dict(h=h, rule=r, seed=sd, stuck=str(e)), flush=True)
                    allok = False  # artifact: exit status
    sys.exit(0 if allok else 1)  # artifact: exit status
