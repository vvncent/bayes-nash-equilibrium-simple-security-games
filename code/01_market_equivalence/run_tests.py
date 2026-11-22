"""Run the game -> market procedure of matching.typ on required and random games.
Usage: $PY -I -B run_tests.py [n_random] [seed]"""
import sys, time, random
from fractions import Fraction as Fr
import os as _os, sys as _sys; _HERE = _os.path.dirname(_os.path.abspath(__file__)); _sys.path[:0] = [_HERE, _os.path.join(_HERE, "..", "lib")]  # artifact: path bootstrap (relative to this file)
from core import Game, M1Oracle, check_bne, check_box, loads
from procedure import solve_game, narrow_and_repair

F = Fr


def three_target():
    return Game(p=[F(4, 7), F(2, 7), F(1, 7)],
                a=[[F(4, 3), F(4, 3), F(-2)], [F(1), F(7, 6), F(4, 3)], [F(-2), F(-2), F(4, 3)]],
                b=[[F(2), F(1), F(1)], [F(1), F(1), F(1)], [F(1), F(1), F(1)]],
                d=[F(1), F(2, 3), F(1)], r=1)


def two_target():
    return Game(p=[F(1)], a=[[F(2), F(2)]], b=[[F(1), F(1)]], d=[F(1), F(1)], r=1)


def rand_game(rng):
    m = rng.randint(1, 3)
    n = rng.randint(2, 3)
    w = [rng.randint(1, 4) for _ in range(m)]
    p = [F(q, sum(w)) for q in w]
    a = [[F(rng.randint(-6, 6), rng.randint(1, 3)) for _ in range(n)] for _ in range(m)]
    b = [[F(rng.randint(1, 6), rng.randint(1, 3)) for _ in range(n)] for _ in range(m)]
    d = [F(rng.randint(1, 5), rng.randint(1, 3)) for _ in range(n)]
    return Game(p, a, b, d, rng.randint(1, n - 1))


def run(G, mode, seed, label, canon=True):
    t0 = time.time()
    orc = M1Oracle(mode, seed)
    x, f, st = solve_game(G, orc, canon)
    ok, why = check_bne(G, x, f)
    mb = st.get("maxbits", [])
    print(f"{label:28s} mode={mode:8s} seed={seed} BNE={ok} ({why}) exit={st['exit']} "
          f"oracle_calls={orc.calls} bisect={st.get('bisect_steps')}/{st.get('bisect_bound')} "
          f"narrow={st.get('narrow_calls')} lam0={st.get('lam0')} "
          f"endpoint_bits_max={max(mb) if mb else None} t={time.time()-t0:.1f}s x={[str(q) for q in x]}",
          flush=True)
    assert ok, why
    return st


def three_target_from_audit_bracket(mode, seed):
    """Start §5 from the audit's L, H at lambda = 2/7 (the off-chord case)."""
    G = three_target()
    L = [F(0), F(0), F(1, 6)]
    H = [F(1, 3), F(2, 3), F(2, 3)]
    fL = [[F(2, 7), F(2, 7), F(0)], [F(0), F(1, 7), F(1, 7)], [F(0), F(0), F(1, 7)]]
    fH = [[F(1, 7), F(3, 7), F(0)], [F(1, 7), F(0), F(1, 7)], [F(0), F(0), F(1, 7)]]
    lam = F(2, 7)
    c = [lam / dj for dj in G.d]
    one, zero = [F(1)] * 3, [F(0)] * 3
    assert check_box(G, c, zero, one, L, fL)[0] and check_box(G, c, zero, one, H, fH)[0]
    # The audit's interpolation (5/27, 10/27, 4/9) supports no equilibrium attack: confirm the common
    # support transport LP on the chord fails, i.e. naive interpolation is not a valid repair here.
    orc = M1Oracle(mode, seed)
    st = {}
    x, f = narrow_and_repair(G, orc, lam, L, fL, H, fH, st)
    ok, why = check_bne(G, x, f)
    print(f"{'three-target audit bracket':28s} mode={mode:8s} seed={seed} BNE={ok} exit={st['exit']} "
          f"calls={orc.calls} x={[str(q) for q in x]} w={[str(q) for q in loads(G, f)]}", flush=True)
    assert ok, why


if __name__ == "__main__":
    nr = int(sys.argv[1]) if len(sys.argv) > 1 else 6
    seed = int(sys.argv[2]) if len(sys.argv) > 2 else 1
    for mode in ("opt", "interior", "plain"):
        three_target_from_audit_bracket(mode, 3)
    for mode in ("opt", "interior"):
        run(three_target(), mode, 5, "three-target full")
        run(two_target(), mode, 5, "two-target full")
    rng = random.Random(seed)
    for t in range(nr):
        G = rand_game(rng)
        run(G, ["opt", "interior", "plain"][t % 3], t, f"random#{t} m={G.m} n={G.n} r={G.r}")
    print("ALL OK")
