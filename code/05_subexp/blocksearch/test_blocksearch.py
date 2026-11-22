"""Tests of the block search of blocksearch.py (book Ch. 5, Sec. sec:subexp) with block size k >= 2.

Usage (from the artifact root):  $PY -I -B 05_subexp/blocksearch/test_blocksearch.py MODE
  MODE = k2        primitives self-tests, deep-point stress (k=1,2), abstract maps k=2 (d=2..6),
                   games k=2 (n=2,3) and the k=1 baseline on games (n=2)
         k3        deep-point stress (k=3), abstract maps k=3 (d=2..6), games k=3 (n=2..5)
         controls  negative controls (must be caught): non-contraction (delta<=0 and an expanding
                   map), wrong cut orientation, too-coarse tail tolerance, too-coarse root tolerance
         quick     a <=60 s subset of k2 and k3 and the controls
Exit status: 0 iff every check passes (for `controls`: iff every control is caught).

Every game instance: toy threshold g (default 1/2; the book's g = 1/(4Q) would make delta about
10^-100 and the search infeasible); the book's constants are computed from g exactly, and z3 proves
the (1-delta) l1 contraction inequality for those constants on that instance (unsat of a violating
pair) BEFORE the search is run.  z3 also gives the fixed point and proves it unique.  D = the largest
denominator of z3's fixed point (an instance-specific valid denominator bound; the book's
D = (MH)^M is far larger).  Root tau = 2^-B <= delta/(8D^2).  The reconstructed point must equal
z3's fixed point exactly, and decode (Lemma ueopl-decoding) to a feasible pattern LP whose exact
solution satisfies every BNE condition of Lemma cutoff(b).  If the pattern LP is infeasible at
the toy g, g is divided by 4 and the instance is redone (reported).
"""
import os
import random
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from blocksearch import (Fr, Config, CheckFailure, Game, PLMap, make_abstract, random_game,  # noqa: E402
                         z3_fixed_point, z3_contraction, solve_exact, selftest_depth, selftest_halfspace,
                         selftest_cut, depth_count, marginal_quantile, union_size, cut_boxes, box_size,
                         product, l1, sub, root_tau, FrB)

T0 = time.time()
FAIL = []
TOTALS = dict(deep_calls=0, deep_median=0, deep_grid=0, deep_exhaustive=0, deep_audits=0,
              protected_checks=0, protected_cut=0, calls=0, tests=0)
MIN_DEPTH = {}       # k -> smallest depth of a used deep point, as a fraction
COUNTS = {}          # (kind, dim, k) -> number of passing instances


def say(*a):
    print(*a, flush=True)


def fmt(x):
    return f"{float(x):.4f}"


def accumulate(st, k):
    for key in TOTALS:
        TOTALS[key] += st[key]
    if st["deep_calls"]:
        MIN_DEPTH[k] = min(MIN_DEPTH.get(k, Fr(1)), st["deep_min_depth_used"])


def run_abstract(seed, d, k, delta, density=1.0, unit=4, label=""):
    rng = random.Random(seed)
    G = make_abstract(rng, d, delta, density=density, unit=unit)
    t = time.time()
    tag = f"abstract d={d} k={k} delta={delta} seed={seed}"
    try:
        con, _ = z3_contraction(G) if d <= 4 else ("skipped(d>4; contraction holds by construction)", None)
        if con == "sat":
            raise CheckFailure("contraction premise violated")
        xs, uniq = z3_fixed_point(G)
        if uniq != "unsat":
            raise CheckFailure(f"z3 uniqueness: {uniq}")
        D = max(x.denominator for x in xs)
        rec, info = solve_exact(G, k, D)
        st = info["stats"]
        if rec != xs:
            raise CheckFailure(f"reconstruction {rec} != z3 {xs}")
        accumulate(st, min(k, d))
        COUNTS[("abstract", d, k)] = COUNTS.get(("abstract", d, k), 0) + 1
        say(f"PASS {tag} D={D} tau=2^-{info['tau'].denominator.bit_length() - 1} contraction={con} "
            f"calls={st['calls']} tests={st['tests']} max_tests/call={st['max_tests']} max_beta={st['max_beta']} "
            f"max_boxes={st['max_boxes']} protected_checks={st['protected_checks']} cut=0 "
            f"deep(median/grid/exh)={st['deep_median']}/{st['deep_grid']}/{st['deep_exhaustive']} "
            f"min_depth={fmt(st['deep_min_depth_used'])} audits={st['deep_audits']} "
            f"max ||y-y(c)||/(dt/16)={fmt(st['tail_err_max_ratio'])} max ||h-T(c)||/e={fmt(st['h_err_max_ratio'])} "
            f"{time.time() - t:.1f}s")
    except CheckFailure as ex:
        FAIL.append((tag, str(ex)))
        say(f"FAIL {tag}: {ex}")


def run_game(seed, n, m, k, r=None, g=Fr(1, 2)):
    rng = random.Random(seed)
    a, b, d, p, r = random_game(rng, n, m, r)
    tag = f"game n={n} m={m} r={r} k={k} seed={seed}"
    t = time.time()
    try:
        for attempt in range(6):
            gm = Game(a, b, d, p, r, g)
            G = gm.map
            con, wit = z3_contraction(G)
            if con != "unsat":
                raise CheckFailure(f"contraction premise at g={g}: z3 {con}")
            xs, uniq = z3_fixed_point(G)
            if uniq != "unsat":
                raise CheckFailure(f"z3 uniqueness: {uniq}")
            chk, bne = gm.decode(xs)
            if chk["pattern LP feasible"]:
                break
            say(f"  note {tag}: pattern LP infeasible at toy g={g}; retry with g/4")
            g = g / 4
        bad = [key for key, v in chk.items() if not v]
        if bad:
            raise CheckFailure(f"decoding checks failed at g={g}: {bad}")
        D = max(x.denominator for x in xs)
        rec, info = solve_exact(G, k, D)
        st = info["stats"]
        if rec != xs:
            raise CheckFailure(f"reconstruction != z3 fixed point")
        chk2, bne2 = gm.decode(rec)        # decode the algorithm's own output
        if not all(chk2.values()):
            raise CheckFailure(f"decoding of the returned point failed: {[k_ for k_, v in chk2.items() if not v]}")
        accumulate(st, min(k, n + 1))
        COUNTS[("game", n, k)] = COUNTS.get(("game", n, k), 0) + 1
        aux = {}
        gm.circuit(rec, FrB, aux)
        zs = "".join("0" if t_ == 0 else "1" if t_ == 1 else "f" for t_ in aux["T"])
        say(f"PASS {tag} g={g} delta~{fmt(G.delta * 10**6)}e-6 D~2^{D.bit_length()} contraction=unsat unique=unsat "
            f"labels={zs} BNE=exact calls={st['calls']} tests={st['tests']} max_tests/call={st['max_tests']} "
            f"max_beta={st['max_beta']} max_boxes={st['max_boxes']} protected_checks={st['protected_checks']} cut=0 "
            f"deep(median/grid/exh)={st['deep_median']}/{st['deep_grid']}/{st['deep_exhaustive']} "
            f"min_depth={fmt(st['deep_min_depth_used'])} max ||h-T(c)||/e={fmt(st['h_err_max_ratio'])} "
            f"piece_fallback_z3={st['piece_fallback_z3']} {time.time() - t:.1f}s")
    except CheckFailure as ex:
        FAIL.append((tag, str(ex)))
        say(f"FAIL {tag}: {ex}")


def random_union(rng, k, N, ncuts):
    """candidate unions as the search produces them: [0,N]^k cut by random l1 halfspaces."""
    boxes = [tuple((0, N) for _ in range(k))]
    for _ in range(ncuts):
        w = [rng.randint(0, N) for _ in range(k)]
        v = [Fr(rng.randint(-5, 5), rng.randint(1, 4)) for _ in range(k)]
        if not any(v):
            continue
        nb, _ = cut_boxes(boxes, w, v)
        if nb:
            boxes = nb
    return boxes


def deep_stress(k, trials, seed):
    """the deep-lattice-point lemma's conclusion on random unions of boxes: the deepest integer
    point of the bounding box (exhaustive) has depth >= 1/(2(k+1)); also report the median."""
    rng = random.Random(seed)
    need = Fr(1, 2 * (k + 1))
    worst_max, worst_med, nfail, medfail = Fr(1), Fr(1), 0, 0
    for _ in range(trials):
        N = rng.choice([4, 6, 8, 11]) if k == 3 else rng.choice([6, 10, 15, 24])
        if rng.random() < 0.35:
            boxes = random_union(rng, k, N, rng.randint(1, 6))
        elif rng.random() < 0.6:   # sparse point clouds (singleton boxes): the centerpoint regime
            pts = {tuple(rng.randint(0, N) for _ in range(k)) for _ in range(rng.randint(1, 9))}
            if rng.random() < 0.5:     # clustered near the coordinate axes through a common point
                c0 = [rng.randint(0, N) for _ in range(k)]
                pts = set()
                for _ in range(rng.randint(2, 9)):
                    i = rng.randrange(k)
                    q = list(c0)
                    q[i] = rng.randint(0, N)
                    for j in range(k):
                        if j != i and rng.random() < 0.3:
                            q[j] = rng.randint(0, N)
                    pts.add(tuple(q))
            boxes = [tuple((t, t) for t in q) for q in pts]
        else:     # random disjoint boxes (incl. lower-dimensional ones)
            boxes = []
            for _ in range(rng.randint(1, 5)):
                bx = []
                for _ in range(k):
                    lo = rng.randint(0, N)
                    bx.append((lo, min(N, lo + rng.choice([0, 0, 1, 2, 4]))))
                bx = tuple(bx)
                if all(any(bx[i][1] < c[i][0] or c[i][1] < bx[i][0] for i in range(k)) for c in boxes):
                    boxes.append(bx)
        tot = union_size(boxes)
        bbox = [(min(b_[i][0] for b_ in boxes), max(b_[i][1] for b_ in boxes)) for i in range(k)]
        mx = max(depth_count(boxes, list(w)) for w in product(*[range(lo, hi + 1) for lo, hi in bbox]))
        med = [marginal_quantile(boxes, i, Fr(1, 2)) for i in range(k)]
        md = Fr(depth_count(boxes, med), tot)
        worst_max = min(worst_max, Fr(mx, tot))
        worst_med = min(worst_med, md)
        nfail += Fr(mx, tot) < need
        medfail += md < need
    tag = f"deep-point stress k={k}: {trials} unions"
    line = (f"{tag}, min over unions of max depth = {worst_max} ({fmt(worst_max)}) vs 1/(2(k+1)) = {need}; "
            f"unions without a deep point: {nfail}; median depth min {fmt(worst_med)} (median below bound: {medfail})")
    if nfail:
        FAIL.append((tag, line))
        say("FAIL " + line)
    else:
        say("PASS " + line)


def primitives(rng):
    for name, fn, arg in [("sign formula vs definition", selftest_halfspace, 5000),
                          ("depth formula vs all integer v in [-4,4]^k", selftest_depth, 300),
                          ("box cut vs pointwise removal", selftest_cut, 300)]:
        bad = fn(rng, arg)
        (FAIL.append((name, bad)) if bad else None)
        say(f"{'PASS' if not bad else 'FAIL'} primitive: {name}: {bad} mismatches in {arg} trials")


# ---------------------------------------------------------------------------------------------- controls


def expanding_map():
    """F(x) = (clip01(2x1 - 1/3), clip01(2x2 - 1/3)): l1-expanding, fixed points {0,1/3,1}^2."""
    def circuit(x, B):
        return [B.min(B.K(Fr(1)), B.max(B.K(Fr(0)), x[i] * B.K(Fr(2)) - B.K(Fr(1, 3)))) for i in range(2)]
    return circuit


def controls(sizes="full"):
    caught, total = 0, 0

    def report(name, ok, detail):
        nonlocal caught, total
        total += 1
        caught += ok
        say(f"{'CAUGHT' if ok else 'NOT CAUGHT'} control {name}: {detail}")
        if not ok:
            FAIL.append((name, detail))

    # (1a) delta <= 0
    G0 = PLMap(2, Fr(0), expanding_map(), "delta=0")
    try:
        solve_exact(G0, 2, 3)
        report("delta=0", False, "algorithm ran with delta=0")
    except CheckFailure as ex:
        report("delta=0", True, f"refused: {ex}")
    # (1b) expanding map with a claimed delta = 1/4
    G1 = PLMap(2, Fr(1, 4), expanding_map(), "expanding")
    con, wit = z3_contraction(G1)
    _, uniq = z3_fixed_point(G1)
    try:
        rec, info = solve_exact(G1, 2, 3, cfg=Config(2, xstar_top=[Fr(1, 3), Fr(1, 3)]))
        res = f"search finished, returned {rec}"
        hit = False
    except CheckFailure as ex:
        res, hit = f"search check failed: {ex}", True
    report("non-contraction (expanding, claimed delta=1/4)", con == "sat" and uniq == "sat" and hit,
           f"z3 contraction premise {con} (witness pair {wit}), z3 second fixed point {uniq}, {res}")
    # (2) wrong cut orientation
    seeds = [(d, k, s) for d, k, s in [(2, 2, 101), (3, 2, 102), (3, 3, 103), (4, 2, 104), (4, 3, 105)]]
    if sizes == "quick":
        seeds = seeds[:3]
    hits = []
    for d, k, s in seeds:
        G = make_abstract(random.Random(s), d, Fr(1, 2))
        xs, _ = z3_fixed_point(G)
        D = max(x.denominator for x in xs)
        try:
            rec, info = solve_exact(G, k, D, cfg=Config(k, flip=True, xstar_top=xs))
            hits.append(f"d={d},k={k}: not caught (rec==z3: {rec == xs})")
        except CheckFailure as ex:
            hits.append(f"d={d},k={k}: {str(ex)[:70]}")
    nh = sum("not caught" not in h for h in hits)
    report("wrong cut orientation H(c,h-c)", nh == len(hits), f"{nh}/{len(hits)} caught; " + " | ".join(hits))
    # (3a) too-coarse tail tolerance theta = tau (instead of delta^2 tau/16), on games (delta ~ 1e-5)
    hits = []
    gseeds = [(2, 2, 2, 201), (2, 3, 2, 202), (3, 2, 3, 203)] if sizes != "quick" else []
    for n, m, k, s in gseeds:
        a, b, d, p, r = random_game(random.Random(s), n, m)
        G = Game(a, b, d, p, r, Fr(1, 2)).map
        xs, _ = z3_fixed_point(G)
        D = max(x.denominator for x in xs)
        try:
            rec, info = solve_exact(G, k, D, cfg=Config(k, theta_factor=Fr(1)))
            hits.append(f"game n={n},k={k}: not caught (rec==z3: {rec == xs})")
        except CheckFailure as ex:
            hits.append(f"game n={n},k={k}: {str(ex)[:60]}")
        # downstream effect, hypothesis checks off: theta = tau (informational) and
        # theta = 2^40 tau/delta^2 (must end in a protected-point cut or a wrong result)
        for lab, fac in (("theta=tau", Fr(1)), ("theta=2^40 tau/delta^2", Fr(2) ** 40 / G.delta ** 2)):
            try:
                rec, info = solve_exact(G, k, D, cfg=Config(k, theta_factor=fac, strict_hyp=False, xstar_top=xs))
                hits[-1] += (f" [{lab}, hypothesis checks off: {info['stats'].get('hyp_viol', 0)} violations, "
                             f"result {'==' if rec == xs else '!='} z3]")
                if lab != "theta=tau" and rec == xs:
                    hits[-1] += " DOWNSTREAM not caught"
            except CheckFailure as ex:
                hits[-1] += f" [{lab}, hypothesis checks off: {str(ex)[:45]}]"
    nh = sum("not caught" not in h for h in hits)
    if gseeds:
        report("too-coarse tail tolerance (theta=tau: hypothesis; theta=2^40 tau/delta^2: downstream)", nh == len(hits), f"{nh}/{len(hits)} caught; " + " | ".join(hits))
    # (3b) too-coarse root tolerance: tau chosen for D=2 instead of the true denominator bound
    hits = []
    for d, k, s in [(2, 2, 301), (3, 3, 302), (4, 2, 303)]:
        G = make_abstract(random.Random(s), d, Fr(1, 2))
        xs, _ = z3_fixed_point(G)
        D = max(x.denominator for x in xs)
        tau, _ = root_tau(G.delta, 2)
        rec, info = solve_exact(G, k, D, tau=tau)
        hits.append(f"d={d},k={k},D={D}: rec {'==' if rec == xs else '!='} z3")
    nh = sum("!=" in h for h in hits)
    report("too-coarse root tolerance (tau for D=2)", nh == len(hits), f"{nh}/{len(hits)} caught; " + " | ".join(hits))
    return caught, total


# ---------------------------------------------------------------------------------------------- plans


def plan_k2(quick=False):
    primitives(random.Random(5))
    deep_stress(1, 60 if quick else 300, 11)
    deep_stress(2, 60 if quick else 400, 12)
    ab = [(2, 0.5, 1.0), (3, 0.5, 1.0), (4, 0.5, 0.6), (5, 0.5, 0.4), (6, 0.5, 0.3)]
    reps = 1 if quick else 4
    for d, dl, dens in ab:
        if quick and d > 4:
            continue
        for rep in range(reps):
            for delta in ([Fr(1, 2)] if (d >= 5 or quick) else [Fr(1, 2), Fr(1, 8)]):
                run_abstract(1000 * d + rep, d, 2, delta, density=dens)
    games = [(2, 2, 1001), (2, 3, 1002), (2, 2, 1003), (2, 3, 1004), (2, 1, 1005), (2, 2, 1006),
             (3, 2, 1011), (3, 3, 1012), (3, 2, 1013)]
    if quick:
        games = []          # games with k=2 take 15-120 s each; they run in the full k2 check
    for n, m, s in games:
        run_game(s, n, m, 2, r=None if n == 2 else 1 + (s % 2))
    if not quick:
        for n, m, s in [(2, 2, 1102)]:   # seed with D ~ 2^24 (seed 1101: D ~ 2^65, about 1 h with k=1)
            run_game(s, n, m, 1)          # the block-size-one baseline (3 nested levels)


def plan_k3(quick=False):
    deep_stress(3, 60 if quick else 300, 13)
    ab = [(2, 1.0), (3, 1.0), (4, 0.6), (5, 0.4), (6, 0.3)]
    reps = 1 if quick else 4
    for d, dens in ab:
        if quick and d > 4:
            continue
        for rep in range(reps):
            for delta in ([Fr(1, 2)] if quick else [Fr(1, 2), Fr(1, 8)]):
                run_abstract(2000 * d + rep, d, 3, delta, density=dens)
    games = [(2, 2, 2001), (2, 3, 2002), (2, 2, 2003), (3, 2, 2011), (3, 3, 2012), (4, 2, 2021), (4, 2, 2022),
             (5, 2, 2031)]
    if quick:
        games = games[:2]
    for n, m, s in games:
        run_game(s, n, m, 3, r=None if n == 2 else 1 + (s % (n - 1)))


def summary(mode):
    say("instances passed by (kind, n or d, k): " + ", ".join(f"{k_[0]} {'n' if k_[0] == 'game' else 'd'}={k_[1]} k={k_[2]}: {v}"
                                                         for k_, v in sorted(COUNTS.items())))
    say(f"deep points: {TOTALS['deep_calls']} searched, median {TOTALS['deep_median']}, grid {TOTALS['deep_grid']}, "
        f"exhaustive {TOTALS['deep_exhaustive']}, exhaustive bbox audits {TOTALS['deep_audits']}; smallest depth used "
        + ", ".join(f"k={k_}: {fmt(v)} (bound {fmt(Fr(1, 2 * (k_ + 1)))})" for k_, v in sorted(MIN_DEPTH.items())))
    say(f"recursion: {TOTALS['calls']} calls, {TOTALS['tests']} tests, protected point checked against "
        f"{TOTALS['protected_checks']} cuts, cut {TOTALS['protected_cut']} times")
    n_inst = sum(COUNTS.values())
    if FAIL:
        say(f"blocksearch {mode}: FAIL ({len(FAIL)} failures: {FAIL[:3]}) {time.time() - T0:.0f}s")
        return 1
    say(f"blocksearch {mode}: ALL PASS ({n_inst} instances, all equal to z3's unique fixed point; "
        f"games decode to exact BNE) {time.time() - T0:.0f}s")
    return 0


if __name__ == "__main__":
    mode = sys.argv[1] if len(sys.argv) > 1 else "quick"
    if mode == "k2":
        plan_k2()
        sys.exit(summary("k2"))
    if mode == "k3":
        plan_k3()
        sys.exit(summary("k3"))
    if mode == "controls":
        c, t = controls()
        say(f"blocksearch controls: {c}/{t} caught {time.time() - T0:.0f}s")
        sys.exit(0 if c == t else 1)
    if mode == "quick":
        plan_k2(quick=True)
        plan_k3(quick=True)
        c, t = controls("quick")
        say(f"controls: {c}/{t} caught")
        if c != t:
            FAIL.append(("controls", f"{c}/{t}"))
        sys.exit(summary("quick"))
    sys.exit(f"unknown mode {mode}")
