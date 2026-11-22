#!/usr/bin/env bash
# run_quick.sh: the fast checks (all chapters)
# 56 checks; sum of per-check runtimes measured under heavy machine load ~577 s (~9 min); per-line numbers are those runtimes.
# End-to-end on a quiet machine: 138 s for the first 36 (chapters 01-07); see README.md for the full quick run.
# Usage: PY=/path/to/python3.12 ./run_quick.sh   (run from anywhere; logs go to <folder>/logs/<script>_<n>.log)
set -u
TAG=run_quick
cd "$(dirname "$0")"
PY="${PY:-python3}"
fail=0; n=0
run() {  # run <folder> <approx seconds> <command...>
  local folder=$1 approx=$2; shift 2; n=$((n+1))
  local log="$folder/logs/${TAG}_$n.log"; local t0=$SECONDS
  echo "[$n] ($folder, ~${approx}s) $*"
  "$@" > "$log" 2>&1; local rc=$?
  echo "    rc=$rc $((SECONDS-t0))s | $(tail -n 1 "$log" | cut -c1-160)"
  [ $rc -eq 0 ] || fail=$((fail+1))
}

run 01_market_equivalence 7 "$PY" -I -B 01_market_equivalence/run_tests.py 6 1
run 01_market_equivalence 1 "$PY" -I -B 01_market_equivalence/check_audit_cases.py
run 01_market_equivalence 1 "$PY" -I -B 01_market_equivalence/check_balanced.py 80 3
run 01_market_equivalence 1 "$PY" -I -B 01_market_equivalence/slope_below_one.py
run 01_market_equivalence 1 "$PY" -I -B 01_market_equivalence/game_check_reduced.py n1
run 01_market_equivalence 3 "$PY" -I -B 01_market_equivalence/game_check_reduced.py n2
run 01_market_equivalence 46 "$PY" -I -B 01_market_equivalence/run_random.py 60 7 1
run 01_market_equivalence 48 "$PY" -I -B 01_market_equivalence/game_check.py n1
run 01_market_equivalence/adversarial 24 "$PY" -I -B 01_market_equivalence/adversarial/test_adversarial.py quick 6
run 02_arrival_hardness 6 "$PY" -I -B 02_arrival_hardness/ds_twocopy.py
run 02_arrival_hardness 2 "$PY" -I -B 02_arrival_hardness/incr_check.py 5
run 02_arrival_hardness 1 "$PY" -I -B 02_arrival_hardness/verify_gadget_allK.py
run 02_arrival_hardness 3 "$PY" -I -B 02_arrival_hardness/run_twocopy_gadget.py 3
run 02_arrival_hardness 1 "$PY" -I -B 02_arrival_hardness/nocreation.py
run 02_arrival_hardness 1 "$PY" -I -B 02_arrival_hardness/nocreation_control.py
run 02_arrival_hardness 3 "$PY" -I -B 02_arrival_hardness/composed_driver2.py 2 6
run 02_arrival_hardness 28 "$PY" -I -B 02_arrival_hardness/composed_random.py 3 40 11
run 02_arrival_hardness 23 "$PY" -I -B 02_arrival_hardness/verify_market_e2e.py 3 20
run 02_arrival_hardness 33 "$PY" -I -B 02_arrival_hardness/gadget_cp.py 02_arrival_hardness/out/gadget_cp_m1-3.jsonl 4 1 2 3
run 02_arrival_hardness 1 "$PY" -I -B 02_arrival_hardness/verify_bits.py 7
run 03_plcp 34 "$PY" -I -B 03_plcp/check_plcp.py
run 03_plcp 1 "$PY" -I -B 03_plcp/check_q0.py
run 03_plcp 1 "$PY" -I -B 03_plcp/check_lemke_rays.py
run 03_plcp 8 "$PY" -I -B 03_plcp/e2e.py n1 cert
run 03_plcp 20 "$PY" -I -B 03_plcp/side_checks.py
run 03_plcp 1 "$PY" -I -B 03_plcp/sizes.py
run 04_ueopl 1 "$PY" -I -B 04_ueopl/teeth_s_column.py
run 04_ueopl 41 "$PY" -I -B 04_ueopl/check_l1_contraction.py
run 05_subexp 38 "$PY" -I -B 05_subexp/check_sec6.py
run 06_lck 21 "$PY" -I -B 06_lck/check_lck_security_path.py --depth 5
run 06_lck 1 "$PY" -I -B 06_lck/check_lck_security_path.py --endpoint 21
run 06_lck 1 "$PY" -I -B 06_lck/validate.py 40
run 06_lck 2 "$PY" -I -B 06_lck/run_family_a.py 1,2,3,4 R1,R2,R3,R4 0,1
run 06_lck 12 "$PY" -I -B 06_lck/run_family_b.py 1,2,3,4,5
run 06_lck 1 "$PY" -I -B 06_lck/run_mcf.py 8
run 06_lck 16 "$PY" -I -B 06_lck/verify_theorem1.py 40 10 2
run 07_direct_lcp 1 "$PY" -I -B 07_direct_lcp/check_direct_game.py
run 07_direct_lcp 3 "$PY" -I -B 07_direct_lcp/check_review.py

# 08_short_proof (Appendix C)
run 08_short_proof 4 "$PY" -I -B 08_short_proof/check_gadget.py 6
run 08_short_proof 1 "$PY" -I -B 08_short_proof/check_gadget.py 3 smallM
run 08_short_proof 1 "$PY" -I -B 08_short_proof/check_gadget.py 3 eps1
run 08_short_proof 1 "$PY" -I -B 08_short_proof/check_gadget.py 3 eps55
run 08_short_proof 1 "$PY" -I -B 08_short_proof/check_gadget.py 3 Pbox2
run 08_short_proof 3 "$PY" -I -B 08_short_proof/check_lemmas.py
run 08_short_proof 1 "$PY" -I -B 08_short_proof/check_floor.py 2
run 08_short_proof 1 "$PY" -I -B 08_short_proof/check_composed.py 1
run 08_short_proof 19 "$PY" -I -B 08_short_proof/check_composed.py 2
run 08_short_proof 5 "$PY" -I -B 08_short_proof/check_game.py 1
run 08_short_proof 1 "$PY" -I -B 08_short_proof/r2_market.py all 1
run 08_short_proof 15 "$PY" -I -B 08_short_proof/r2_market.py all 2
run 08_short_proof 10 "$PY" -I -B 08_short_proof/r2_market.py rand 3 30 11
run 08_short_proof 8 "$PY" -I -B 08_short_proof/r2_market.py rand 4 6 12
run 08_short_proof 9 "$PY" -I -B 08_short_proof/r2_market.py rand 5 4 13
run 08_short_proof 9 "$PY" -I -B 08_short_proof/r2_market.py neg 2 216 0 '{"swap":true}'
run 08_short_proof 39 "$PY" -I -B 08_short_proof/r2_game.py 1 8 0

# 05_subexp/blocksearch (added 2026-11-22): exact block search with block size k>=2
run 05_subexp/blocksearch 13 "$PY" -I -B 05_subexp/blocksearch/test_blocksearch.py quick

echo "done: $n checks, $fail with nonzero exit status (compare each final line with README.md)"
exit $fail
