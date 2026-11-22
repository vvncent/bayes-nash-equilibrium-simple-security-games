#!/usr/bin/env bash
# run_full.sh: every included check, including the slow ones
# 124 checks in 135 commands (08.composed_n3 has 10 shards, 08.composed_n4 has 3); sum of per-check runtimes measured
# under load ~23,050 s (~6.4 h); per-line numbers are those runtimes (02.eh_batch_n5/n6: estimates from the original runs).
# Expect about 4-7 h. Negative controls print NOT OK / caught by design; see README.md.
# Usage: PY=/path/to/python3.12 ./run_full.sh   (run from anywhere; logs go to <folder>/logs/<script>_<n>.log)
set -u
TAG=run_full
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
run 01_market_equivalence 48 "$PY" -I -B 01_market_equivalence/run_random.py 60 8 0
run 01_market_equivalence 178 "$PY" -I -B 01_market_equivalence/run_random.py 150 21 1
run 01_market_equivalence 281 "$PY" -I -B 01_market_equivalence/run_random.py 150 22 0
run 01_market_equivalence 84 "$PY" -I -B 01_market_equivalence/check_degenerate.py 8 5
run 01_market_equivalence 244 "$PY" -I -B 01_market_equivalence/check_degenerate.py 16 9
run 01_market_equivalence 68 "$PY" -I -B 01_market_equivalence/game_check.py n1 1
run 01_market_equivalence 96 "$PY" -I -B 01_market_equivalence/game_check.py n1 0 -3
run 01_market_equivalence 445 "$PY" -I -B 01_market_equivalence/batch_reduced.py 2
run 01_market_equivalence 640 "$PY" -I -B 01_market_equivalence/batch_reduced.py 3 8 7
run 01_market_equivalence/adversarial 24 "$PY" -I -B 01_market_equivalence/adversarial/test_adversarial.py quick 6
run 01_market_equivalence/adversarial 2543 "$PY" -I -B 01_market_equivalence/adversarial/test_adversarial.py main 1 10 1 1800
run 01_market_equivalence/adversarial 130 "$PY" -I -B 01_market_equivalence/adversarial/test_adversarial.py games 1 identical#2 identical#45 ties#31
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
run 02_arrival_hardness 564 "$PY" -I -B 02_arrival_hardness/twocopy_controls.py 4 5 6 7
run 02_arrival_hardness 870 "$PY" -I -B 02_arrival_hardness/gadget_cp.py 02_arrival_hardness/out/gadget_cp_m4-6.jsonl 6 4 5 6
run 02_arrival_hardness 329 "$PY" -I -B 02_arrival_hardness/composed_driver2.py 3 40
run 02_arrival_hardness 153 "$PY" -I -B 02_arrival_hardness/composed_driver2.py 4 15
run 02_arrival_hardness 23 "$PY" -I -B 02_arrival_hardness/composed_random.py 4 15 12
run 02_arrival_hardness 47 "$PY" -I -B 02_arrival_hardness/verify_market_e2e.py 4 12
run 02_arrival_hardness 354 "$PY" -I -B 02_arrival_hardness/verify_game_e2e.py 2 8
run 02_arrival_hardness 418 "$PY" -I -B 02_arrival_hardness/verify_game_e2e.py 2 8 swap
run 02_arrival_hardness 181 "$PY" -I -B 02_arrival_hardness/verify_game_e2e.py 2 8 -3
run 02_arrival_hardness 879 "$PY" -I -B 02_arrival_hardness/verify_game_e2e.py 3 1
run 02_arrival_hardness 427 "$PY" -I -B 02_arrival_hardness/verify_game_e2e.py 3 1 swap
run 03_plcp 34 "$PY" -I -B 03_plcp/check_plcp.py
run 03_plcp 1 "$PY" -I -B 03_plcp/check_q0.py
run 03_plcp 1 "$PY" -I -B 03_plcp/check_lemke_rays.py
run 03_plcp 8 "$PY" -I -B 03_plcp/e2e.py n1 cert
run 03_plcp 20 "$PY" -I -B 03_plcp/side_checks.py
run 03_plcp 1 "$PY" -I -B 03_plcp/sizes.py
run 04_ueopl 1 "$PY" -I -B 04_ueopl/teeth_s_column.py
run 04_ueopl 41 "$PY" -I -B 04_ueopl/check_l1_contraction.py
run 04_ueopl 79 "$PY" -I -B 04_ueopl/check.py 1 3 full
run 04_ueopl 71 "$PY" -I -B 04_ueopl/check.py 2 3 full
run 04_ueopl 190 "$PY" -I -B 04_ueopl/check.py 3 3 full
run 04_ueopl 50 "$PY" -I -B 04_ueopl/check.py 4 4 full
run 04_ueopl 200 "$PY" -I -B 04_ueopl/check.py 5 4 full
run 04_ueopl 268 "$PY" -I -B 04_ueopl/check.py 6 4 full
run 04_ueopl 69 "$PY" -I -B 04_ueopl/check.py 7 4 full
run 04_ueopl 317 "$PY" -I -B 04_ueopl/sanity.py
run 05_subexp 38 "$PY" -I -B 05_subexp/check_sec6.py
run 05_subexp 144 "$PY" -I -B 05_subexp/check_thm1.py
run 06_lck 21 "$PY" -I -B 06_lck/check_lck_security_path.py --depth 5
run 06_lck 1 "$PY" -I -B 06_lck/check_lck_security_path.py --endpoint 21
run 06_lck 1 "$PY" -I -B 06_lck/validate.py 40
run 06_lck 2 "$PY" -I -B 06_lck/run_family_a.py 1,2,3,4 R1,R2,R3,R4 0,1
run 06_lck 12 "$PY" -I -B 06_lck/run_family_b.py 1,2,3,4,5
run 06_lck 1 "$PY" -I -B 06_lck/run_mcf.py 8
run 06_lck 16 "$PY" -I -B 06_lck/verify_theorem1.py 40 10 2
run 06_lck 44 "$PY" -I -B 06_lck/run_family_a.py 5,6,7,8 R1,R2,R3,R4 0
run 06_lck 726 "$PY" -I -B 06_lck/run_family_a.py 9,10,11 R1,R2 0
run 06_lck 26 "$PY" -I -B 06_lck/verify_theorem1.py 1 1 3
run 06_lck 256 "$PY" -I -B 06_lck/bisect_solver.py 10 20 40 60
run 07_direct_lcp 1 "$PY" -I -B 07_direct_lcp/check_direct_game.py
run 07_direct_lcp 3 "$PY" -I -B 07_direct_lcp/check_review.py

# 02 error hunt (original construction) and 08_short_proof (Appendix C)
run 08_short_proof 4 "$PY" -I -B 08_short_proof/check_gadget.py 6
run 08_short_proof 1 "$PY" -I -B 08_short_proof/check_gadget.py 3 smallM
run 08_short_proof 1 "$PY" -I -B 08_short_proof/check_gadget.py 3 eps1
run 08_short_proof 1 "$PY" -I -B 08_short_proof/check_gadget.py 3 eps55
run 08_short_proof 1 "$PY" -I -B 08_short_proof/check_gadget.py 3 Pbox2
run 08_short_proof 3 "$PY" -I -B 08_short_proof/check_lemmas.py
run 08_short_proof 1 "$PY" -I -B 08_short_proof/check_floor.py 2
run 08_short_proof 66 "$PY" -I -B 08_short_proof/check_floor.py 3 3000
run 08_short_proof 1 "$PY" -I -B 08_short_proof/check_composed.py 1
run 08_short_proof 19 "$PY" -I -B 08_short_proof/check_composed.py 2
run 08_short_proof 17 "$PY" -I -B 08_short_proof/check_composed.py 2 0 0 eps0
run 08_short_proof 9 "$PY" -I -B 08_short_proof/check_composed.py 2 0 0 lamM
run 08_short_proof 309 env SHARD=0/10 "$PY" -I -B 08_short_proof/check_composed.py 3
run 08_short_proof 330 env SHARD=1/10 "$PY" -I -B 08_short_proof/check_composed.py 3
run 08_short_proof 334 env SHARD=2/10 "$PY" -I -B 08_short_proof/check_composed.py 3
run 08_short_proof 346 env SHARD=3/10 "$PY" -I -B 08_short_proof/check_composed.py 3
run 08_short_proof 336 env SHARD=4/10 "$PY" -I -B 08_short_proof/check_composed.py 3
run 08_short_proof 314 env SHARD=5/10 "$PY" -I -B 08_short_proof/check_composed.py 3
run 08_short_proof 334 env SHARD=6/10 "$PY" -I -B 08_short_proof/check_composed.py 3
run 08_short_proof 341 env SHARD=7/10 "$PY" -I -B 08_short_proof/check_composed.py 3
run 08_short_proof 342 env SHARD=8/10 "$PY" -I -B 08_short_proof/check_composed.py 3
run 08_short_proof 325 env SHARD=9/10 "$PY" -I -B 08_short_proof/check_composed.py 3
run 08_short_proof 36 env SHARD=0/3 "$PY" -I -B 08_short_proof/check_composed_n4.py 24 44
run 08_short_proof 36 env SHARD=1/3 "$PY" -I -B 08_short_proof/check_composed_n4.py 24 44
run 08_short_proof 52 env SHARD=2/3 "$PY" -I -B 08_short_proof/check_composed_n4.py 24 44
run 08_short_proof 5 "$PY" -I -B 08_short_proof/check_game.py 1
run 08_short_proof 278 "$PY" -I -B 08_short_proof/check_game.py 2 6 1
run 08_short_proof 198 "$PY" -I -B 08_short_proof/r2_gadget.py
run 08_short_proof 1 "$PY" -I -B 08_short_proof/r2_market.py all 1
run 08_short_proof 15 "$PY" -I -B 08_short_proof/r2_market.py all 2
run 08_short_proof 10 "$PY" -I -B 08_short_proof/r2_market.py rand 3 30 11
run 08_short_proof 115 "$PY" -I -B 08_short_proof/r2_market.py rand 3 300 31
run 08_short_proof 8 "$PY" -I -B 08_short_proof/r2_market.py rand 4 6 12
run 08_short_proof 130 "$PY" -I -B 08_short_proof/r2_market.py rand 4 60 41
run 08_short_proof 9 "$PY" -I -B 08_short_proof/r2_market.py rand 5 4 13
run 08_short_proof 153 "$PY" -I -B 08_short_proof/r2_market_hard.py 4 20 21
run 08_short_proof 657 "$PY" -I -B 08_short_proof/r2_market_hard.py 5 16 22
run 08_short_proof 9 "$PY" -I -B 08_short_proof/r2_market.py neg 2 216 0 '{"swap":true}'
run 08_short_proof 10 "$PY" -I -B 08_short_proof/r2_market.py neg 2 216 0 '{"lamfac":"1/4"}'
run 08_short_proof 10 "$PY" -I -B 08_short_proof/r2_market.py neg 2 216 0 '{"eps":0}'
run 08_short_proof 19 "$PY" -I -B 08_short_proof/r2_market.py neg 3 600 5 '{"m":1}'
run 08_short_proof 39 "$PY" -I -B 08_short_proof/r2_game.py 1 8 0
run 08_short_proof 9 "$PY" -I -B 08_short_proof/r2_game.py 1 8 0 swap
run 08_short_proof 64 "$PY" -I -B 08_short_proof/r2_game_pruned.py 2 12 3
run 08_short_proof 808 "$PY" -I -B 08_short_proof/r2_game_pruned.py 2 216 4
run 08_short_proof 85 "$PY" -I -B 08_short_proof/r2_game_pruned.py 2 40 9 swap
run 08_short_proof 823 "$PY" -I -B 08_short_proof/r2_game.py 2 1 3
run 02_arrival_hardness 800 "$PY" -I -B 02_arrival_hardness/composed_batch.py 5 24 11
run 02_arrival_hardness 1700 "$PY" -I -B 02_arrival_hardness/composed_batch.py 6 10 12
run 02_arrival_hardness 21 "$PY" -I -B 02_arrival_hardness/composed_n56.py n5_selfloop_chain
run 02_arrival_hardness 61 "$PY" -I -B 02_arrival_hardness/composed_n56.py n5_coincident
run 02_arrival_hardness 4 "$PY" -I -B 02_arrival_hardness/composed_n56.py n5_bothterm_same
run 02_arrival_hardness 41 "$PY" -I -B 02_arrival_hardness/composed_n56.py n5_counter
run 02_arrival_hardness 15 "$PY" -I -B 02_arrival_hardness/composed_n56.py n5_unreach_cycle
run 02_arrival_hardness 8 "$PY" -I -B 02_arrival_hardness/composed_n56.py n5_deleted
run 02_arrival_hardness 71 "$PY" -I -B 02_arrival_hardness/composed_n56.py n6_counter
run 02_arrival_hardness 80 "$PY" -I -B 02_arrival_hardness/composed_n56.py n6_mixed
run 02_arrival_hardness 1 "$PY" -I -B 02_arrival_hardness/composed_n56.py n2_fig swap
run 02_arrival_hardness 1 "$PY" -I -B 02_arrival_hardness/composed_n56.py n3_t swap
run 02_arrival_hardness 1 "$PY" -I -B 02_arrival_hardness/verify_bits.py 7

# 05_subexp/blocksearch (added 2026-11-22): exact block search with block size k>=2
run 05_subexp/blocksearch 303 "$PY" -I -B 05_subexp/blocksearch/test_blocksearch.py k2
run 05_subexp/blocksearch 994 "$PY" -I -B 05_subexp/blocksearch/test_blocksearch.py k3
run 05_subexp/blocksearch 50 "$PY" -I -B 05_subexp/blocksearch/test_blocksearch.py controls

echo "done: $n checks, $fail with nonzero exit status (compare each final line with README.md)"
exit $fail
