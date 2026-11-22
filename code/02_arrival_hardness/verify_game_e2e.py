"""End-to-end check on the ACTUAL Bayesian security game (one resource) built from the composed
two-copy ARRIVAL market. z3 (exact LRA) proves that EVERY Bayes-Nash equilibrium of the game puts
unnormalised attack mass exactly 1 on the run's terminal target and 0 on the other.
Default mode `pruned` drops unlisted pairs after z3 proves no BNE uses them (unlisted_never_used); mode `full` encodes every pair.
Usage: verify_game_e2e.py n count [eps] [term_cap]
  eps=3 correct gadget (expect OK). Negative controls (expect CAUGHT): 'swap' = +3 penalty on port a
  (b-first switch), eps=-3 (port b margin M+3 exceeds slack margin M+1: phantom flow), eps=7.
Reproduce: $PY -I -B verify_game_e2e.py 2 4   (then with eps -3 for the negative control)
  optional args: term_cap (S3 or a number), mode (pruned [default: unlisted pairs proved unusable by
  per-type z3 lemma L1, then fixed to 0] or full), first (offset into the instance list)
"""
import os, sys, time
import os as _os, sys as _sys  # artifact: path bootstrap (relative to this file)
_HERE = _os.path.dirname(_os.path.abspath(__file__))
_sys.path[:0] = [_HERE, _os.path.join(_HERE, "..", "lib")]
import z3
from referee_lib import discriminating, compose, market_to_game, game_bne, game_bne_pruned, unlisted_never_used, game_terminal_inflow, run_arrival

n, count = int(sys.argv[1]), int(sys.argv[2])
swap = len(sys.argv) > 3 and sys.argv[3] == "swap"
eps = 3 if swap else (int(sys.argv[3]) if len(sys.argv) > 3 else 3)
tc = sys.argv[4] if len(sys.argv) > 4 else "S3"
mode = sys.argv[5] if len(sys.argv) > 5 else "pruned"  # "full": encode every pair with complementarity
first = int(sys.argv[6]) if len(sys.argv) > 6 else 0
inst = discriminating(n)[first:]
# pick a spread: longest, plus ones with self-loops
chosen, seen = [], set()
for st, succ, want in inst:
    key = any(v in succ[v] for v in range(n))
    if len(chosen) < count and (len(chosen) % 2 == 0 or key):
        chosen.append((st, succ, want))
for st, succ, want in inst:
    if len(chosen) >= count:
        break
    if (st, succ, want) not in chosen:
        chosen.append((st, succ, want))
print(f"n={n}: {len(inst)} discriminating instances; checking {len(chosen)}; eps={eps}; swap={swap}; term_cap={tc}")
allok = True
control = swap or eps != 3  # artifact: exit status (docstring: eps=3 correct, swap / other eps = controls)
caught_all = True  # artifact: exit status
for st, succ, want in chosen:
    t0 = time.time()
    other = "no" if want == "yes" else "yes"
    gb = compose(succ, 0, n, eps=eps, term_cap=tc, swap=swap)
    game = market_to_game(*gb)
    s = z3.Solver()
    if mode == "full":
        x, sig, tot = game_bne(game, s)
    else:
        x, sig, tot = game_bne_pruned(game, s, unlisted_never_used(game))
    yin = game_terminal_inflow(game, gb, sig, tot, want)
    oin = game_terminal_inflow(game, gb, sig, tot, other)
    ex = s.check()
    s.push(); s.add(z3.Or(yin != 1, oin != 0)); wrong = s.check(); s.pop()
    ok = ex == z3.sat and wrong == z3.unsat
    allok &= ok
    caught_all &= not ok  # artifact: exit status (control: every instance CAUGHT/FAIL)
    extra = ""
    if wrong == z3.sat:
        s.add(z3.Or(yin != 1, oin != 0)); s.check(); mdl = s.model()
        extra = f" witness: in({want})={mdl.eval(yin)}, in({other})={mdl.eval(oin)}"
    print(f"succ={succ} run->{want} ({st} steps) | types={len(game['types'])} targets={len(game['targets'])} "
          f"| BNE exists: {ex}; some BNE decodes wrongly: {wrong} | {'OK' if ok else 'CAUGHT/FAIL'}{extra} "
          f"({time.time()-t0:.0f}s)", flush=True)
print("ALL OK" if allok else "NOT ALL OK")
sys.exit(0 if (caught_all if control else allok) else 1)  # artifact: exit status
