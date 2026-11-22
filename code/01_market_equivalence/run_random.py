"""Random games, all three oracle modes, with and without §5 canonicalization.
Usage: $PY -I -B run_random.py N seed canon(1|0)"""
import sys, os, time, random
import os as _os, sys as _sys; _HERE = _os.path.dirname(_os.path.abspath(__file__)); _sys.path[:0] = [_HERE, _os.path.join(_HERE, "..", "lib")]  # artifact: path bootstrap (relative to this file)
from fractions import Fraction as Fr
from core import Game, M1Oracle, check_bne, check_box, loads
from procedure import solve_game, locate_cutoff, narrow_and_repair
from run_tests import rand_game, three_target

N = int(sys.argv[1]); seed = int(sys.argv[2]); canon = sys.argv[3] == "1"
rng = random.Random(seed)
exits = {}
t0 = time.time()
for t in range(N):
    G = rand_game(rng)
    mode = ["opt", "interior", "plain"][t % 3]
    orc = M1Oracle(mode, seed * 1000 + t)
    x, f, st = solve_game(G, orc, canon)
    ok, why = check_bne(G, x, f)
    assert ok, (t, why)
    exits[st["exit"]] = exits.get(st["exit"], 0) + 1
    mb = st.get("maxbits") or [0]
    if st["exit"] != "bisection-hit":
        print(f"#{t} m={G.m} n={G.n} r={G.r} {mode} exit={st['exit']} calls={orc.calls} "
              f"bisect={st.get('bisect_steps')} narrow={st.get('narrow_calls')} lam0={st.get('lam0')} "
              f"endpoint_bits_max={max(mb)} x={[str(q) for q in x]}", flush=True)
# required test with non-canonical endpoints and several oracle seeds
for sd in range(4):
    G = three_target()
    orc = M1Oracle(["opt", "interior", "plain", "interior"][sd], 77 + sd)
    x, f, st = solve_game(G, orc, canon)
    ok, why = check_bne(G, x, f)
    assert ok, why
    print(f"three-target full seed={sd} exit={st['exit']} x={[str(q) for q in x]} "
          f"bits_max={max(st.get('maxbits') or [0])}", flush=True)
print("exits", exits, f"canon={canon} N={N} all BNE verified, {time.time()-t0:.0f}s")
