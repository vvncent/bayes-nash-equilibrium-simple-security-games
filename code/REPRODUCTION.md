# REPRODUCTION

Every included check was re-run; two long batches only on their first instance. The runs were made
from the artifact root with `$PY -I -B ...` (CPython 3.12.11, z3-solver 5.4.1.0, numpy 2.4.2 / scipy 1.17.1
for the one MILP cross-check), on a 14-core laptop, on 2026-11-22. Full outputs of these runs are in `<folder>/logs/`. "identical" means the artifact log equals
the original log line by line after removing timing fields. The original logs are not shipped. Runtimes are wall-clock; most chapter runs
were made while the machine was heavily loaded by other jobs (load average up to about 330), so they are
upper bounds. `run_quick.sh` was afterwards run end to end on a quiet machine, then 36 checks (chapters 01-07), all exit 0, all
final lines as expected, **138 s in total**. The sum of the measured runtimes of all checks in
`run_full.sh` is about **19,000 s (about 5.3 h)** under load (about 23,050 s with the block-search and adversarial-oracle checks added later); on a quiet machine expect roughly half.

## Summary

| folder | checks included | reproduced | not reproduced / notes |
|---|---|---|---|
| 01_market_equivalence | 20 | 20 | none (01.adv_main was recorded with the oracles before the z3 bound fix and lost 3 runs to a kill by the testing agent; those 3 games are rerun as 01.adv_games, see "01.adv_* (added 2026-11-22)") |
| 02_arrival_hardness | 34 | 32 in full, 2 on their first instance only | none (C1-C6 witness points differ, verdicts identical; see 3 below); the two error-hunt batches `02.eh_batch_n5/n6` were rerun on their first instance only (see 8 below) |
| 03_plcp | 6 | 6 | none |
| 04_ueopl | 10 | 10 | **two timing-sensitive z3 searches** (below) |
| 05_subexp | 6 | 6 | none (4 block-search checks added later; see the blocksearch section) |
| 06_lck | 11 | 11 | none |
| 07_direct_lcp | 2 | 2 | none |
| 08_short_proof | 36 | 36 | none |
| **total** | **125** (124 in `run_full.sh`; `05.blocksearch_quick` is a quick subset) | | |

Checks that are negative controls (eps=-3, `swap`, eps=0, eps=7, mutated constants, ...) count as
reproduced when they are *caught*, as in the original runs; their scripts then print `NOT OK`,
`NOT ALL OK`, `caught` or `FAIL` by design.

### Non-reproductions and caveats (read these first)

1. **UEOPL contraction search, timeout-dependent (04_ueopl, `check.py` seeds 3 and 4).** The script gives
   the true-constant contraction-violation search a fixed 180 s z3 timeout (not changed). Under heavy load
   seed 4 game 1 returned `unknown` twice where the original log has `unsat`; a rerun on a quiet machine
   reproduced the original log exactly. Conversely, seed 3 game 1, recorded (and reported in the book) as
   the one `unknown`, reproduced as `unknown` under load but returned `unsat` on a quiet machine. No run
   found a violating pair. The book's count "30 unsat, 1 unknown" is therefore machine-dependent.
   The checker can exit successfully after an `unknown` result. Inspect the per-search verdicts in the logs
   to distinguish a timeout from a completed search that returned `unsat`.
2. **UEOPL digit range (04_ueopl).** The published book reports 11 to 44 decimal digits for `Q`. The logs
   show `log10(Q)~` values of 11 to 44, which the checker computes as the decimal digit count minus one.
   The 25 random games therefore have `Q` values of 12 to 45 decimal digits.
3. **C1-C6 boundary witnesses (02_arrival_hardness, `gadget_cp.py`):** all 216 configuration verdicts and
   piece counts are identical to the original results; for some failing configurations z3 returns a
   different witness point than in the original run. Every witness is re-verified in exact arithmetic by
   the script as an equilibrium that violates S1/S2.
4. **Reduced / partial instances.** No check was run on a reduced instance except where the original run
   itself was partial: the game-level n=3 check runs the one instance (the longest, 7-step run) that the
   original run finished, via the count argument `3 1`.
5. **Not claimed in the book and not run:** the P-LCP end-to-end runs for n=2 and n=3 (did not finish in 30
   minutes originally); the full (unreduced) n=2 game encoding (never finished originally).
6. **Not located:** the command of the "later exact rerun of 254 ordered equilibria through n=7" (06);
   these equilibria are a subset of the 2,046 forced equilibria checked by `verify_theorem1.py 40 10 2`,
   which was rerun and passed.
7. Eleven cited checks had no saved original output, so the expected result comes from the report or the
   book text: 01 `check_audit_cases.py`, `check_balanced.py`, `game_check.py n1`; 02 `ds_twocopy.py`,
   `incr_check.py`, `composed_driver2.py`, `composed_random.py`; 03 `sizes.py`; 04 `teeth_s_column.py`;
   06 the two `check_lck_security_path.py` runs. All agree with the reported numbers.
8. **Added later (same day): 02 error hunt and 08_short_proof.** Afterwards `run_quick.sh` (then 53 checks; 54 after `02.verify_bits` was added) was run end to end: all exit 0, all final lines as expected. All 36 `08.*` checks and all `02.eh_*` checks except the two
   batches were rerun in full from the artifact (up to 12 at once, so runtimes are upper bounds; the 10 shards of
   `08.composed_n3` ran in parallel, each 5-6 min against about 15 min originally). `02.eh_batch_n5` (24 instances) and
   `02.eh_batch_n6` (10 instances) take 2-16 min per instance; only their first instance was rerun
   (`composed_batch.py 5 1 11 1`, `composed_batch.py 6 1 12 1`); its output line is identical to the original line for that
   instance. Original full results: `n=5 count=24 seed=11: ALL OK` (24/24 `exists=sat wrong=unsat notFP=unsat`, runs of
   10-18 steps, 63-471 s per instance) and `n=6 count=10 seed=12: ALL OK` (10/10, runs of 12-37 steps, 445-986 s per instance).
   Five checks had no saved original log; their counts come from the referee or error-hunt reports and agree: `08.floor_n2`,
   `08.composed_n1` (reduced instances), `08.composed_n2_eps0` (48 bad), `08.composed_n2_lamM` (224 bad), `02.eh_swap_n2/n3` (caught).


## 01_market_equivalence/ -- Ch. 3: security game <-> affine matching market

Expected outputs come from the original run logs, where they exist, and otherwise from the review reports. "identical" means the full log matches the original log line by line once timing fields are removed.

| check id | command | actual output tail | runtime | expected (source) | result |
|---|---|---|---|---|---|
| 01.run_tests | `$PY -I -B 01_market_equivalence/run_tests.py 6 1` | `ALL OK` | 7 s | original run_tests.log (identical apart from timings) | PASS |
| 01.audit_cases | `$PY -I -B 01_market_equivalence/check_audit_cases.py` | `two-target from audit bracket: plain ['1/2', '1/2'] hit` / `audit cases OK` | <1 s | matching review: interpolated point unsat; two-target gives (1/2,1/2). No original log was saved | PASS |
| 01.rand_canon60 | `$PY -I -B 01_market_equivalence/run_random.py 60 7 1` | `exits {'repair': 28, 'bisection-hit': 32} canon=True N=60 all BNE verified, 46s` | 46 s | original rand_canon.log (identical apart from timings) | PASS |
| 01.rand_nocanon60 | `$PY -I -B 01_market_equivalence/run_random.py 60 8 0` | `exits {'bisection-hit': 31, 'repair': 28, 'hit': 1} canon=False N=60 all BNE verified, 48s` | 48 s | original rand_nocanon.log (identical) | PASS |
| 01.rand_canon150 | `$PY -I -B 01_market_equivalence/run_random.py 150 21 1` | `exits {'repair': 66, 'bisection-hit': 79, 'hit': 5} canon=True N=150 all BNE verified, 178s` | 178 s | original rand_canon_150.log (identical) | PASS |
| 01.rand_nocanon150 | `$PY -I -B 01_market_equivalence/run_random.py 150 22 0` | `exits {'bisection-hit': 69, 'repair': 77, 'hit': 4} canon=False N=150 all BNE verified, 281s` | 281 s | original rand_nocanon_150.log (identical) | PASS |
| 01.degen8 | `$PY -I -B 01_market_equivalence/check_degenerate.py 8 5` | `#7 m=1 n=3 r=2 zero_b=0 zero_d=2 eps_bits=46 calls=698 exit=hit original BNE=True x=['1', '1', '0']` / `degenerate decoding OK` | 84 s | original degen.log (identical) | PASS |
| 01.degen16 | `$PY -I -B 01_market_equivalence/check_degenerate.py 16 9` | `#15 m=2 n=2 r=1 ... exit=repair original BNE=True x=[2/3, 1/3]` / `degenerate decoding OK` | 244 s | original degen16.log (identical) | PASS |
| 01.balanced | `$PY -I -B 01_market_equivalence/check_balanced.py 80 3` | `balanced anchor decode OK on 80 markets (39 equilibria with positive dummy utility)` | 1 s | matching review item 14: 80 markets, 39 with positive dummy utility. No original log was saved | PASS |
| 01.slope_below_one | `$PY -I -B 01_market_equivalence/slope_below_one.py` | `BNE exists: sat; witness x=['80/101', '21/101', '0', '0']` / `some BNE fails the M1 decoding: sat` / `market equilibrium with P != 100: unsat` / `market equilibrium exists: sat` | <1 s | embedding review E3: U=12, A=2, S=5, BNE x=(80/101,21/101,0,0), fails the decoding, no equilibrium with P different from 100 | PASS |
| 01.embed_n1_reduced | `$PY -I -B 01_market_equivalence/game_check_reduced.py n1` | `Q1 ... sat` / `Q2 ... unsat` / `Q3 ... unsat` | 1 s | original n1_reduced.log (identical) | PASS |
| 01.embed_n1_full | `$PY -I -B 01_market_equivalence/game_check.py n1` | `Q2 ... unsat (24.2s)` / `Q3 ... unsat (22.1s)` / `RESULT: OK` | 48 s | embedding review table: full, unnormalized, sat/unsat/unsat, 26 s. No original log was saved | PASS |
| 01.embed_n1_full_normalized | `$PY -I -B 01_market_equivalence/game_check.py n1 1` | `Q3 ... unsat` / `RESULT: OK` | 68 s | original n1_normalized.log (identical) | PASS |
| 01.embed_n1_control | `$PY -I -B 01_market_equivalence/game_check.py n1 0 -3` | `Q2 ... sat (28.0s) \| counterexample inflow(yes)=0, inflow(no)=2` / `Q3 ... unsat` / `RESULT: NOT OK` | 96 s | original n1_control_swapped.log (identical); the control is meant to be caught | PASS (control caught) |
| 01.embed_n2_reduced | `$PY -I -B 01_market_equivalence/game_check_reduced.py n2` | `Q1 ... sat` / `Q2 ... unsat` / `Q3 ... unsat` | 3 s | original n2_reduced.log (identical) | PASS |
| 01.batch_n2 | `$PY -I -B 01_market_equivalence/batch_reduced.py 2` | `56 instances; all OK: True; swapped control caught on 56/56` | 445 s | original batch_n2.log (identical apart from timings) | PASS |
| 01.batch_n3 | `$PY -I -B 01_market_equivalence/batch_reduced.py 3 8 7` | `8 instances; all OK: True; swapped control caught on 8/8` | 640 s | original batch_n3.log: `8 instances; all OK: True; swapped control caught on 8/8` | PASS (identical apart from timings) |
| 01.adv_quick | `$PY -I -B 01_market_equivalence/adversarial/test_adversarial.py quick 6` | `quick: 70 runs (13 games x 5 oracles + 5 audit-bracket), failures=0, timeouts=0, controls all caught, 24s` | 24 s | new check (logs/quick.log) | PASS |
| 01.adv_main | `$PY -I -B 01_market_equivalence/adversarial/test_adversarial.py main 1 10 1 1800` | `main_s1: 5135 runs (1026 games x 5 oracles + 5 audit-bracket), failures=3, timeouts=0, controls all caught, 2543s` (`rc=1`) | 2,543 s | new check (logs/prefix_main_s1.log, prefix_runs_main_s1.jsonl, prefix_controls_main_s1.jsonl); the 3 "failures" are `worker died`: killed by the testing agent, see below | PASS for 5,132 runs; 3 runs completed by 01.adv_games |
| 01.adv_games | `$PY -I -B 01_market_equivalence/adversarial/test_adversarial.py games 1 identical#2 identical#45 ties#31` | `games_s1: 15 runs (3 games x 5 oracles + 0 audit-bracket), failures=0, timeouts=0, controls all caught, 130s` | 130 s | new check (logs/games_s1.log, runs_games_s1.jsonl) | PASS |

- How the two N=60 runs were identified: the review's reproduce block lists only the N=150 runs. The seeds of the two N=60 logs (7 with canonicalization on, 8 with it off) were found by regenerating the random games for candidate seeds and matching the (m,n,r) of the logged instances. With those seeds the reruns match the logs exactly. 60+60+150+150 = 420 games, as the book states.
- In the book, the 24/25 full-encoding checks are the two `game_check.py n1` runs (unnormalized weights and true probabilities).


## 02_arrival_hardness/ -- Ch. 4: ARRIVAL-hardness of exact BNE

| check id | command | actual output tail | runtime | expected (source) | result |
|---|---|---|---|---|---|
| 02.ds_twocopy | `$PY -I -B 02_arrival_hardness/ds_twocopy.py` | `G_6: 64 increments, strictly increasing=True, min gap=6` ... `two-copy m=5 K=64 eps=3: PASS` | 6 s | design note: increments checked for m<=6; no saved log | PASS |
| 02.incr_check | `... incr_check.py 5` | `m=5: LP increments == recursion: True; linear between integers: True; min gap 6; max increment 486` / `ALL OK` | 2 s | gadget referee report: m=1..5, min gap 6, max 2*3^m; no saved log | PASS |
| 02.gadget_allK | `... verify_gadget_allK.py` | `(2) m=1..20: ... True` / `(3) m=3 K=16: equilibrium violating Step-1 structure: unsat` / `ALL OK` | 1 s | referee checkpoint: `ALL OK` | PASS |
| 02.twocopy_gadget | `... run_twocopy_gadget.py 3` | `1 4 18 282 True []` / `2 8 30 564 True []` / `3 16 42 978 True []` | 3 s | design note: certified K=4,8,16; bits 282, 564, 978 | PASS |
| 02.twocopy_controls | `... twocopy_controls.py 4 5 6 7` | controls eps=0, eps=7, w=4: `certified=False`; `m=4..7 ... certified=True`; bits 1428, 2042, 2660, 3474; 90 agents at K=256 | 564 s (orig. about 2 min) | design note and book: controls rejected, K up to 256 certified, bits as listed | PASS |
| 02.gadget_cp_m1-3 | `... gadget_cp.py ... 4 1 2 3` | 54 PASS / 54 FAIL; per-configuration verdicts and counts (pieces, bad, violating, vacuous) identical to the original results_m1-3.jsonl | 33 s | original results_m1-3.jsonl; book: 18 in-condition configurations per m pass, eps in {1,5}, H=0, c_p<=K fail | PASS (witness points differ: z3 picks other models; every new witness re-verified exactly as an equilibrium violating S1/S2) |
| 02.gadget_cp_m4-6 | `... gadget_cp.py ... 6 4 5 6` | 54 PASS / 54 FAIL; verdicts and counts identical to results_m4-6.jsonl | 870 s | original results_m4-6.jsonl | PASS (same note on witnesses) |
| 02.driver2_n2 | `... composed_driver2.py 2 6` | 6/6 `eps=3: OK`, 6/6 `eps=-3: caught`; final line as expected | 3 s | design note: n=2 6 longest, correct OK, eps=-3 caught on every instance, eps=0 caught on most; no saved log | PASS |
| 02.driver2_n3 | `... composed_driver2.py 3 40` | 40/40 OK, 40/40 eps=-3 caught (eps=0 caught 20/40); runs up to 7 steps | 329 s | same | PASS |
| 02.driver2_n4 | `... composed_driver2.py 4 15` | 15/15 OK, 15/15 eps=-3 caught (eps=0 caught 12/15); runs up to 15 steps | 153 s | same; "runs up to 15 steps" | PASS |
| 02.random_n3 | `... composed_random.py 3 40 11` | `n=3: 40 random discriminating instances; correct gadget OK on all: True; swapped gadget caught on all: True (27s)` | 28 s | design note | PASS |
| 02.random_n4 | `... composed_random.py 4 15 12` | `n=4: 15 random discriminating instances; correct gadget OK on all: True; swapped gadget caught on all: True (23s)` | 23 s | design note | PASS |
| 02.market_e2e_n3 | `... verify_market_e2e.py 3 20` | `n=3: 20 of 3418 discriminating instances; correct OK on all: True; swap caught on all: True` | 23 s | original log_market_n3.txt (identical apart from timings) | PASS |
| 02.market_e2e_n4 | `... verify_market_e2e.py 4 12` | `n=4: 12 of 370056 discriminating instances; correct OK on all: True; swap caught on all: True` | 47 s | original log_market_n4.txt (identical apart from timings) | PASS |
| 02.game_e2e_n2 | `... verify_game_e2e.py 2 8` | 8 x `BNE exists: sat; some BNE decodes wrongly: unsat \| OK` / `ALL OK` | 354 s | original log_e2e_n2_eps3.txt: identical apart from timings and a header line that now also prints `swap=False` | PASS |
| 02.game_e2e_n2_swap | `... verify_game_e2e.py 2 8 swap` | 8 x `CAUGHT/FAIL witness: in(run's terminal)=0, in(other)=1` / `NOT ALL OK` | 418 s | original log_e2e_n2_swap.txt (identical apart from timings) | PASS (control caught) |
| 02.game_e2e_n2_epsm3 | `... verify_game_e2e.py 2 8 -3` | 8 x `CAUGHT/FAIL` (inflows 2 and 4) / `NOT ALL OK` | 181 s | original log_e2e_n2_epsm3.txt (identical apart from timings and header) | PASS (control caught) |
| 02.game_e2e_n3 | `... verify_game_e2e.py 3 1` | `succ=[(0, 1), (0, 2), ('yes', 'no')] run->yes (7 steps) \| types=132 targets=133 \| BNE exists: sat; some BNE decodes wrongly: unsat \| OK (878s)` / `ALL OK` | 879 s | original log_e2e_n3_eps3.txt: same instance OK in 1196 s | PASS |
| 02.game_e2e_n3_swap | `... verify_game_e2e.py 3 1 swap` | `... BNE exists: sat; some BNE decodes wrongly: sat \| CAUGHT/FAIL witness: in(yes)=0, in(no)=1 (427s)` / `NOT ALL OK` | 427 s | original log_e2e_n3_swap.txt (identical apart from timing and header) | PASS (control caught) |
| 02.eh_batch_n5 | `$PY -I -B 02_arrival_hardness/composed_batch.py 5 24 11` | `succ={0: (4, 4), 1: (3, 'no'), 2: (3, 'yes'), 3: (1, 0), 4: (3, 2)} run->no 10 steps kept=5 \| exists=sat wrong=unsat notFP=unsat \| OK (<t>)` | 108 s | errorhunt/logs/batch_n5.txt | PASS (first instance rerun, `composed_batch.py 5 1 11 1`: its line is identical to the original's line for that instance up to timing) |
| 02.eh_batch_n6 | `$PY -I -B 02_arrival_hardness/composed_batch.py 6 10 12` | `succ={0: (2, 'yes'), 1: (4, 3), 2: (1, 'no'), 3: (1, 2), 4: (4, 1), 5: (2, 'yes')} run->no 13 steps kept=6 \| exists=sat wrong=unsat notFP=unsat \| OK (<t>)` | 194 s | errorhunt/logs/batch_n6.txt | PASS (first instance rerun, `composed_batch.py 6 1 12 1`: its line is identical to the original's line for that instance up to timing) |
| 02.eh_n5_selfloop_chain | `$PY -I -B 02_arrival_hardness/composed_n56.py n5_selfloop_chain` | `OK` | 21 s | errorhunt/logs/n5_selfloop_chain.txt | PASS (identical up to timings) |
| 02.eh_n5_coincident | `$PY -I -B 02_arrival_hardness/composed_n56.py n5_coincident` | `OK` | 61 s | errorhunt/logs/n5_coincident.txt | PASS (identical up to timings) |
| 02.eh_n5_bothterm_same | `$PY -I -B 02_arrival_hardness/composed_n56.py n5_bothterm_same` | `OK` | 4 s | errorhunt/logs/n5_bothterm_same.txt | PASS (identical up to timings) |
| 02.eh_n5_counter | `$PY -I -B 02_arrival_hardness/composed_n56.py n5_counter` | `OK` | 41 s | errorhunt/logs/n5_counter.txt | PASS (identical up to timings) |
| 02.eh_n5_unreach_cycle | `$PY -I -B 02_arrival_hardness/composed_n56.py n5_unreach_cycle` | `OK` | 15 s | errorhunt/logs/n5_unreach_cycle.txt | PASS (identical up to timings) |
| 02.eh_n5_deleted | `$PY -I -B 02_arrival_hardness/composed_n56.py n5_deleted` | `OK` | 8 s | errorhunt/logs/n5_deleted.txt | PASS (identical up to timings) |
| 02.eh_n6_counter | `$PY -I -B 02_arrival_hardness/composed_n56.py n6_counter` | `OK` | 71 s | errorhunt/logs/n6_counter.txt | PASS (identical up to timings) |
| 02.eh_n6_mixed | `$PY -I -B 02_arrival_hardness/composed_n56.py n6_mixed` | `OK` | 80 s | errorhunt/logs/n6_mixed.txt | PASS (identical up to timings) |
| 02.eh_swap_n2 | `$PY -I -B 02_arrival_hardness/composed_n56.py n2_fig swap` | `OK` | 1 s | (no original log; error-hunt report: caught) | PASS (count/verdict as reported) |
| 02.eh_swap_n3 | `$PY -I -B 02_arrival_hardness/composed_n56.py n3_t swap` | `OK` | 0 s | (no original log; error-hunt report: caught) | PASS (count/verdict as reported) |

- The original game-level n=3 run queued 3 instances (`3 3`) and finished only the first (longest) one; the artifact runs `3 1` (count argument only), i.e. exactly the instance the book reports. The n=3 swap control was rerun the same way (`3 1 swap`).
- The book's eps=-3 "wrong-order switch" in the market-level rows is, as the P-LCP review notes, a broken gadget rather than a clean swap; the clean swap control is the one in verify_market_e2e.py / verify_game_e2e.py (`swap`), which is caught on every instance.


## 03_plcp/ -- Sec. 5.1: market (M1) -> P-matrix LCP, and ARRIVAL -> P-LCP

| check id | command | actual output tail | runtime | expected (book/log) | result |
|---|---|---|---|---|---|
| plcp-check | `$PY -I -B 03_plcp/check_plcp.py` | `random: 60 markets (ties, balances, negative intercepts, sparse edges): all checks pass` / `large: 8 markets up to N=19, eps up to 828 bits: unique P-LCP solution and exact decode` / `ALL CHECKS PASSED` | 34.1 s | original log: identical 10 output lines ending `ALL CHECKS PASSED` (29.9 s); book: 6 hand-built + 60 random, N<=19, eps 16--828 bits, negative control | PASS (output identical to original log) |
| plcp-q0 | `$PY -I -B 03_plcp/check_q0.py` | `Q0 recipe: 40 random markets with zero margins, restored point solves LCP(q, M) exactly` | 0.2 s | original log identical; book: 40 random zero-margin markets | PASS |
| plcp-lemke-rays | `$PY -I -B 03_plcp/check_lemke_rays.py` | `slopes below and above one: all-cover bound violations unsat, four quotas and P-LCP decode verified by both LPs` / `Zero-margin lift and homogeneous direction sat, both negative margins infeasible` | 0.9 s | referee rerun log identical (4 lines); book: three markets, two split-LP implementations, boundary cases | PASS |
| plcp-e2e-n1 | `$PY -I -B 03_plcp/e2e.py n1 cert` | `RESULT n=1 ... geps=3 ... delta_bits=676 ... plcp_verified=True ... load_yes=1 / load_no=0 ... decoded=yes ... run=yes ... ok=True` / `RESULT n=1 ... geps=-3 ... delta_bits=659 ... load_yes=0 / load_no=2 ... decoded=none (yes=0, no=2) ... ok=True` | 8.1 s | original log identical apart from wall-clock timing fields; book: 49-dim, 676-bit eps, certified basis, loads the run's terminal; eps=-3 control loads no=2, yes=0 | PASS |
| plcp-e2e-side | `$PY -I -B 03_plcp/side_checks.py` | `RESULT n=1 ... delta_bits=1 ... decode=unsat ... why=system (1) infeasible` (same for delta_bits=2, 5) | 20.2 s | original log identical apart from timing fields; book: eps in {1,1/2,1/16} makes decoding LP infeasible | PASS |
| plcp-e2e-sizes | `$PY -I -B 03_plcp/sizes.py` | `n=2 geps=3 discriminating=56 N=146 ... delta_bits=2482` / `n=3 geps=3 discriminating=3418 N=299 ... delta_bits=6096` / `n=4 ... delta_bits=12026` | 0.4 s | no saved log; values match the e2e report and the book (146-dim, 2,482-bit; n=3 299-dim) | PASS |

- All six included checks reproduced; outputs were byte-identical to the original logs after removing wall-clock timing fields. No failures.
- Runs were made concurrently with other chapters' checks on a 14-core machine; runtimes are wall clock under that load.
- End-to-end n=2 (146-dim, 2,482-bit eps) and n=3 were NOT run: in the original they did not finish within 30 minutes per instance and the book claims nothing beyond n=1. The `e2e.py n2` / `e2e.py n3` modes are present in the copied file but are not part of the quick or full runs.


## 04_ueopl/ -- Sec. 5.3-5.4: UEOPL membership via one l1 contraction

| check id | command | actual output tail | runtime | expected (book / original log) | result |
|---|---|---|---|---|---|
| ueopl_seed1 | `$PY -I -B 04_ueopl/check.py 1 3 full` | all result lines identical to the original run_seed1.log | 79 s | original run_seed1.log | PASS (identical except timing lines) |
| ueopl_seed2 | `$PY -I -B 04_ueopl/check.py 2 3 full` | identical to run_seed2.log | 71 s | run_seed2.log | PASS |
| ueopl_seed3 | `$PY -I -B 04_ueopl/check.py 3 3 full` | run 1 (machine loaded): identical to run_seed3.log, including game 1 `z3 contraction-violation search (true constants): unknown`. Run 2 (quiet machine, logs/ueopl_seed3_rerun_idle.log): game 1 gives `unsat`, all other lines identical | 235 s; 190 s | run_seed3.log; book: "one timeout" | PASS on run 1 (the reported timeout reproduces); **TIMING-SENSITIVE**: on a quiet machine the search finishes within the script's 180 s z3 timeout and returns `unsat`, which is stronger than, but differs from, the recorded `unknown` |
| ueopl_seed4 | `$PY -I -B 04_ueopl/check.py 4 4 full` | runs 1-2 (machine loaded, load average about 330): game 1 `z3 contraction-violation search (true constants): unknown`. Run 3 (quiet machine, logs/ueopl_seed4_rerun_idle.log): every line identical to run_seed4.log, including `unsat` | 236 s, 230 s; 50 s | run_seed4.log | PASS on the quiet-machine rerun; **TIMING-SENSITIVE**: under heavy load the search hit the 180 s z3 timeout and returned `unknown` (not a failure of the bound, but not the recorded answer) |
| ueopl_seed5 | `$PY -I -B 04_ueopl/check.py 5 4 full` | identical to run_seed5.log | 200 s | run_seed5.log | PASS |
| ueopl_seed6 | `$PY -I -B 04_ueopl/check.py 6 4 full` | identical to run_seed6.log | 268 s | run_seed6.log | PASS |
| ueopl_seed7 | `$PY -I -B 04_ueopl/check.py 7 4 full` | identical to run_seed7.log | 69 s | run_seed7.log | PASS |
| ueopl_sanity | `$PY -I -B 04_ueopl/sanity.py` | `teeth: factor (1-delta) -> unsat (should be unsat)` / `teeth: mutated eta = 3 tau/B -> sat, ratio 36210294528322517858048000/27157744269216035866974163 (expect sat)` / `teeth: mutated eta with s-column sum 0.677 -> unsat, ratio None (expect sat if > 1)` | 317 s | sanity.log: identical apart from per-game timings | PASS |
| ueopl_teeth_s_column | `$PY -I -B 04_ueopl/teeth_s_column.py` | `mutated s-column sum 7.93 -> z3 sat, exact ratio of witness 34858.../21461... (> 1-delta, caught)` | <1 s | book item 3 ("shrinking the d'_j ... yields a violating pair"); no original log saved | PASS (vs. the book's claim) |
| ueopl_l1_contraction | `$PY -I -B 04_ueopl/check_l1_contraction.py` | `Part C PASS: reproduces J v = (4+1/24, 2-1/24, -3, -3) and l2 growth` / `OVERALL PASS` | 41 s | original logs/check_l1_contraction.log: byte-identical | PASS |

Aggregate over the artifact runs (seeds 1-7 + sanity): 18 gap-test games, 1,800 patterns, 82 with t*=0, smallest positive t*=4/147, bad=[] everywhere; 1,740 Jacobian pieces, 0 failures; fixed point found and second fixed point unsat on all 33; g=1/10 searches unsat on all 31; residual/g maxima 0.0625 (budget), 0.125 (best response), 0.0625 (cutoff); delta 157-812 bits. All match the book. True-constant searches: book 30 unsat + 1 unknown; artifact loaded-machine runs 29 unsat + 2 unknown; with the quiet-machine reruns of seeds 3 and 4, 31 unsat + 0 unknown (see the timing note below).

- **Timing-sensitive searches (seeds 3 and 4, game 1 each).** `check.py` gives the true-constant contraction search a fixed 180 s z3 wall-clock timeout (unchanged here). Its answer therefore depends on machine load: under heavy load seed 4 returned `unknown` where the original log has `unsat`; on a quiet machine seed 4 reproduces `unsat` exactly, and seed 3 returns `unsat` where the original log (and the book's "one timeout") has `unknown`. Across the runs, every completed search returned `unsat`; none found a violating pair.
- In the 25 shipped random-game logs, `log10(Q)~` ranges from 11 to 44 (two games at 40, one at 44), so `Q` has 12 to 45 decimal digits. The delta bit range is 157-812.
- Runtimes are inflated by load. The original runs took 21-211 s per seed, about 11 minutes for all seven.


## 05_subexp/ -- Sec. 5.5: subexponential algorithm

| check id | command | actual output tail | runtime | expected (book / original log) | result |
|---|---|---|---|---|---|
| subexp_thm1 | `$PY -I -B 05_subexp/check_thm1.py` | `continued-fraction recovery failures: 0` / `pipeline d=2 exact recoveries: 12 {...'z_removed': 0}` / `pipeline d=3 exact recoveries: 3 {'calls': 6077, 'tests': 544970, 'max_tests': 94, 'z_removed': 0}` | 144 s | book Ch. 5 "Computer checks" (no mismatch in 20,000; 0 of 349,550; 0 failures; 12/12, 3/3); original output check_thm1.out: all 5 lines identical | PASS (output byte-identical to the original output) |
| subexp_sec6 | `$PY -I -B 05_subexp/check_sec6.py` | `(3, 'unsat', 0.9999932258014852, True, {})` / `(4, 'unsat', 0.9999937727500672, True, {})` / `(5, 'unsat', 0.9999976784663589, True, {})` | 38 s | book: z3 proved no violating pair on 6 games, all fixed-point properties confirmed; original check_sec6.out: 6 identical tuples | PASS (byte-identical) |

- No failures or non-reproductions in this folder.
- Runtimes were measured while the machine was heavily loaded (load average about 300 on 14 cores, other checks running in parallel); expect them to be shorter on an idle machine.


## 06_lck/ -- Ch. 6: lower bounds for the Li-Conitzer-Korzhyk algorithm

| check id | command | actual output tail | runtime | expected (book/log) | result |
|---|---|---|---|---|---|
| lck_uniqueness_depth5 | `06_lck/check_lck_security_path.py --depth 5` | `Depth 5: 27 types, 12 targets, 33 unique intermediate coverages, 16 affine pieces, integer-budget equilibrium verified.` (depths 1–5: 3+5+9+17+33 = 67 budgets, 1/2/4/8/16 pieces) | 21 s | book: 67 budgets in five games, only coverage P(y); slopes 1 and 2 alternate (asserted in script); budget-1 equilibria verified (no saved original log; book/source note give the counts) | PASS |
| lck_endpoint_h21 | `06_lck/check_lck_security_path.py --endpoint 21` | `Direct endpoint verified for depth 21, 107 types and 44 targets. Published path bound: 1,048,576 successful updates.` | <1 s | book: h=21, 44 targets, 107 types, >= 2^20 calls | PASS |
| lck_validate | `06_lck/validate.py 40` | `SUMMARY ok=160 bad=0 stuck=0 runs=160 time=0.5s` | <1 s | original validate.log: identical except timing (all 161 lines) | PASS |
| lck_family_a_small | `06_lck/run_family_a.py 1,2,3,4 R1,R2,R3,R4 0,1` | `{'h': 4, 'rule': 'R4', 'seed': 1, 'bne': True, 'succ': 8, 'fail': 6, 'below': 8, 'bound': 8, 'path_mismatch': 0, ...}` | 2 s | original family_a_small.log: identical except `secs` (24 lines) | PASS |
| lck_family_a_mid | `06_lck/run_family_a.py 5,6,7,8 R1,R2,R3,R4 0` | `{'h': 8, 'rule': 'R4', 'seed': 0, 'bne': True, 'succ': 128, 'fail': 7, 'below': 128, 'bound': 128, 'path_mismatch': 0, ...}` | 44 s | original family_a_mid.log: identical except `secs` (16 lines) | PASS |
| lck_family_a_large | `06_lck/run_family_a.py 9,10,11 R1,R2 0` | `{'h': 11, 'rule': 'R1', ... 'succ': 1024, 'fail': 1, ...}` / `{'h': 11, 'rule': 'R2', 'seed': 0, 'bne': True, 'succ': 1024, 'fail': 23, 'below': 1024, 'bound': 1024, 'path_mismatch': 0, 'cancels': 0, 'secs': 374.5, ...}` | 726 s (full instance; slow only because of machine load) | original family_a_large.log: identical except `secs` (6 lines); book: 1024 successful calls for R1 and R2 at h=11, failed calls 1 (R1) and 2h+1=23 (R2) | PASS |
| lck_family_b | `06_lck/run_family_b.py 1,2,3,4,5` | `{'n': 5, 'rule': 'R4', 'seed': 0, 'bne': True, 'succ': 143, 'fail': 20, 'bound': 32, 'cancels': 0, ...}` | 12 s | original family_b.log identical except `secs`; book table: 6/5/21/7 ... 86/85/139/143 | PASS |
| lck_ds_gadget | `06_lck/run_mcf.py 8` | `n=8: nodes=18 arcs=33 SSP iterations=256 path costs 0..2^n-1: True, unit augmentations: True, recursive flows optimal with cost v(v-1)/2: True` | <1 s | original results/ds_gadget.txt identical | PASS |
| lck_gn_theorem | `06_lck/verify_theorem1.py 40 10 2` | `n=1..40: all inequalities hold exactly ... True`; `n=10: 1024 equilibria exact-verified=True, budgets strictly monotone=True ...`; `n=2: max \|extreme return mass - (j+1)/Kappa\| over j = 1.11e-16` | 16 s | original results/theorem1.txt identical (except timings and stderr HiGHS warnings); 2+4+...+1024 = 2046 equilibria | PASS |
| lck_gn_milp_n3 | `06_lck/verify_theorem1.py 1 1 3` | `n=3: max \|extreme return mass - (j+1)/Kappa\| over j = 3.89e-16  (21.3s)` | 26 s | original: `n=3 worst 3.89e-16` (results/theorem1.txt, separate run) | PASS |
| lck_gn_bisection | `06_lck/bisect_solver.py 10 20 40 60` | n=10/20/40/60: exact equilibrium True, oracle calls 32/53/97/137 (mid-window 30/55/97/138) | 256 s | original results/bisect_solver.txt: identical lines for n=10,20,40,60 except timings; book: 32, 53, 97, 137 | PASS |

All 11 checks reproduced their originally reported result; no failures.


## 07_direct_lcp/ -- Sec. 5.2: direct P0 / P-matrix LCP formulation of the game

| check id | command | actual output tail | runtime | expected (source) | result |
|---|---|---|---|---|---|
| 07-source | `$PY -I -B 07_direct_lcp/check_direct_game.py` | `2 by 3 game with gains [2, 3, 5]: 1869 zero, 1134 positive, 494 positive with budget column` / `2 by 3 game with gains [0, Fraction(17, 12), Fraction(2, 29)]: 2340 zero, 663 positive, 359 positive with budget column` / four `1/epsilon uses {56,113,958,170} bits; ...` lines / `All direct-game checks passed.` | 1 s | book 07 "Computer checks" item 1 (3,003 pairs, 1,134/663 positive, 494/359 with budget column, 56-958 bits); recorded run output in the producing run's audit log (identical four 1/epsilon lines and final line) | PASS |
| 07-referee | `$PY -I -B 07_direct_lcp/check_review.py` | `minors 27904 12000` / `formulation 15 negative-control-rejected` / `decoder 3` / `boundary-and-zero-prior` / `PASS` | 3 s | referee report output block (identical five lines); book 07 item 2 | PASS |

Both outputs are line-for-line identical to the recorded outputs. No failures.


## 08_short_proof/ -- Appendix C: shorter proof of ARRIVAL-hardness (two referees)

Expected outputs come from the referees' logs (`simplify/referee/log_*.txt`, `simplify/referee2/log_*.txt`). "identical up to
timings" means the artifact log equals the original line by line after removing timing fields (and, for `check_composed.py`,
after sorting the printed tag dictionaries, whose key order depends on hash randomization).

| check id | command | actual output tail | runtime | expected (source) | result |
|---|---|---|---|---|---|
| 08.gadget | `$PY -I -B 08_short_proof/check_gadget.py 6` | `m=6 M=4374 eps=3 control=None : violation query unsat   sanity ['sat', 'sat', 'sat', 'sat', 'sat']  (2.2s)` | 4 s | referee/log_gadget.txt (control=None lines) | PASS (identical up to timings) |
| 08.gadget_smallM | `$PY -I -B 08_short_proof/check_gadget.py 3 smallM` | `m=3 M=40 eps=3 control=smallM : violation query sat CEX c=33/2 x=65/4 P1=1 P2=1 A=5 B=19/4  sanity ['sat', 'sat', 'sat', 'sat', 'sat']  (0.1s)` | 0 s | referee/log_gadget.txt | PASS (identical up to timings) |
| 08.gadget_eps1 | `$PY -I -B 08_short_proof/check_gadget.py 3 eps1` | `m=3 M=162 eps=1 control=eps1 : violation query sat CEX c=7/2 x=3 P1=1 P2=0 A=1 B=2  sanity ['sat', 'sat', 'sat', 'sat', 'sat']  (0.1s)` | 1 s | referee/log_gadget.txt | PASS (identical up to timings) |
| 08.gadget_eps55 | `$PY -I -B 08_short_proof/check_gadget.py 3 eps55` | `m=3 M=162 eps=5.5 control=eps55 : violation query sat CEX c=13 x=155/12 P1=1/4 P2=1 A=7 B=71/12  sanity ['sat', 'sat', 'sat', 'sat', 'sat']  (0.1s)` | 0 s | referee/log_gadget.txt | PASS (identical up to timings) |
| 08.gadget_Pbox2 | `$PY -I -B 08_short_proof/check_gadget.py 3 Pbox2` | `m=3 M=162 eps=3 control=Pbox2 : violation query unsat   sanity ['sat', 'sat', 'sat', 'sat', 'sat']  (0.1s)` | 0 s | referee/log_gadget.txt | PASS (identical up to timings) |
| 08.lemmas | `$PY -I -B 08_short_proof/check_lemmas.py` | `Lemma 8 control, slopes 1/20..1/60 (trials, bad): (60, 27)` | 3 s | referee/log_lemmas.txt | PASS (identical up to timings) |
| 08.floor_n2 | `$PY -I -B 08_short_proof/check_floor.py 2` | `instances 265 violations 0 with fractional fixed points 146 nonterminating-with-FP 0` | 0 s | (no original log; reduced instance of 08.floor) | PASS (count/verdict as reported) |
| 08.floor | `$PY -I -B 08_short_proof/check_floor.py 3 3000` | `instances 18890 violations 0 with fractional fixed points 11849 nonterminating-with-FP 0` | 66 s | referee/log_floor.txt | PASS (identical up to timings) |
| 08.composed_n1 | `$PY -I -B 08_short_proof/check_composed.py 1` | `n=1 control=None instances(canonical, preprocessed) 8 bad 0 tags {'both-same-terminal': 2, 'a=b': 2, 'origin-in-edge': 4, 'selfloop': 4}  0s` | 0 s | (no original log; reduced instance of 08.composed_n2) | PASS (count/verdict as reported) |
| 08.composed_n2 | `$PY -I -B 08_short_proof/check_composed.py 2` | `n=2 control=None instances(canonical, preprocessed) 224 bad 0 tags {'both-same-terminal': 58, 'preproc-deleted': 8, 'a=b': 78, 'selfloop': 140, 'origin-in-edge'` | 19 s | referee/log_composed_n2.txt | PASS (identical up to timings) |
| 08.composed_n2_eps0 | `$PY -I -B 08_short_proof/check_composed.py 2 0 0 eps0` | `n=2 control=eps0 instances(canonical, preprocessed) 224 bad 48 tags {'a=b': 78, 'preproc-deleted': 8, 'both-same-terminal': 58, 'selfloop': 140, 'origin-in-edge` | 17 s | (no original log; count 48 from referee report) | PASS (count/verdict as reported) |
| 08.composed_n2_lamM | `$PY -I -B 08_short_proof/check_composed.py 2 0 0 lamM` | `n=2 control=lamM instances(canonical, preprocessed) 224 bad 224 tags {'a=b': 78, 'preproc-deleted': 8, 'both-same-terminal': 58, 'selfloop': 140, 'origin-in-edg` | 9 s | (no original log; count 224 from referee report) | PASS (count/verdict as reported) |
| 08.composed_n3 | `SHARD=<i>/10 $PY -I -B 08_short_proof/check_composed.py 3` | shard 0: `n=3 control=None instances(canonical, preprocessed) 675 bad 0 tags {'preproc-deleted': 25, 'a=b': 263, 'both-same-terminal': 165, 'origin-in-edge': 50` | 309-346 s per shard | referee/log_composed_n3_shard0..9.txt | PASS (all 10 shard logs identical up to timings and tag-dict order) |
| 08.composed_n4 | `SHARD=<i>/3 $PY -I -B 08_short_proof/check_composed_n4.py 24 44` | shard 0: `n=4 instances 8 bad 0 36s` | 36-52 s per shard | referee/log_composed_n4_shard0..2.txt | PASS (all 3 shard logs identical up to timings and tag-dict order) |
| 08.game_n1 | `$PY -I -B 08_short_proof/check_game.py 1` | `n=1 instances 8 bad 0` | 5 s | referee/log_game_n1.txt | PASS (identical up to timings) |
| 08.game_n2 | `$PY -I -B 08_short_proof/check_game.py 2 6 1` | `n=2 instances 6 bad 0` | 278 s | referee/log_game_n2.txt | PASS (identical up to timings) |
| 08.r2_gadget | `$PY -I -B 08_short_proof/r2_gadget.py` | `TOTAL 3490 FAILURES 0` | 198 s | referee2/log_gadget.txt | PASS (identical up to timings) |
| 08.r2_market_n1 | `$PY -I -B 08_short_proof/r2_market.py all 1` | `n=1: OK 8, FAIL 0` | 0 s | referee2/log_market_n1.txt | PASS (identical up to timings) |
| 08.r2_market_n2 | `$PY -I -B 08_short_proof/r2_market.py all 2` | `n=2: OK 216, FAIL 0` | 15 s | referee2/log_market_n2.txt | PASS (identical up to timings) |
| 08.r2_market_n3 | `$PY -I -B 08_short_proof/r2_market.py rand 3 30 11` | `n=3: OK 30, FAIL 0` | 10 s | referee2/log_market_n3.txt | PASS (identical up to timings) |
| 08.r2_market_n3_300 | `$PY -I -B 08_short_proof/r2_market.py rand 3 300 31` | `n=3: OK 300, FAIL 0` | 115 s | referee2/log_market_n3_300.txt | PASS (identical up to timings) |
| 08.r2_market_n4 | `$PY -I -B 08_short_proof/r2_market.py rand 4 6 12` | `n=4: OK 6, FAIL 0` | 8 s | referee2/log_market_n4.txt | PASS (identical up to timings) |
| 08.r2_market_n4_60 | `$PY -I -B 08_short_proof/r2_market.py rand 4 60 41` | `n=4: OK 60, FAIL 0` | 130 s | referee2/log_market_n4_60.txt | PASS (identical up to timings) |
| 08.r2_market_n5 | `$PY -I -B 08_short_proof/r2_market.py rand 5 4 13` | `n=5: OK 4, FAIL 0` | 9 s | referee2/log_market_n5.txt | PASS (identical up to timings) |
| 08.r2_market_hard_n4 | `$PY -I -B 08_short_proof/r2_market_hard.py 4 20 21` | `n=4 hard: OK 33, FAIL 0` | 153 s | referee2/log_market_hard_n4.txt | PASS (identical up to timings) |
| 08.r2_market_hard_n5 | `$PY -I -B 08_short_proof/r2_market_hard.py 5 16 22` | `n=5 hard: OK 27, FAIL 0` | 657 s | referee2/log_market_hard_n5.txt | PASS (identical up to timings) |
| 08.r2_neg_n2_swap | `$PY -I -B 08_short_proof/r2_market.py neg 2 216 0 '{"swap":true}'` | `NEG {'swap': True}: caught 56 of 216` | 9 s | referee2/log_market_neg_n2.txt | PASS (identical up to timings) |
| 08.r2_neg_n2_lam1_4 | `$PY -I -B 08_short_proof/r2_market.py neg 2 216 0 '{"lamfac":"1/4"}'` | `NEG {'lamfac': Fraction(1, 4)}: caught 10 of 216` | 10 s | referee2/log_market_neg_n2.txt | PASS (identical up to timings) |
| 08.r2_neg_n2_eps0 | `$PY -I -B 08_short_proof/r2_market.py neg 2 216 0 '{"eps":0}'` | `NEG {'eps': 0}: caught 46 of 216` | 10 s | referee2/log_market_neg_n2.txt | PASS (identical up to timings) |
| 08.r2_neg_n3_m1 | `$PY -I -B 08_short_proof/r2_market.py neg 3 600 5 '{"m":1}'` | `NEG {'m': 1}: caught 1 of 600` | 19 s | referee2/log_market_neg_n3_m1.txt | PASS (identical up to timings) |
| 08.r2_game_n1 | `$PY -I -B 08_short_proof/r2_game.py 1 8 0` | `n=1: OK 8, other 0` | 39 s | referee2/log_game_n1.txt | PASS (identical up to timings) |
| 08.r2_game_n1_swap | `$PY -I -B 08_short_proof/r2_game.py 1 8 0 swap` | `NEG swap: caught 2, other 6` | 9 s | referee2/log_game_n1_neg_swap.txt | PASS (identical up to timings) |
| 08.r2_game_n2_pruned | `$PY -I -B 08_short_proof/r2_game_pruned.py 2 12 3` | `n=2 pruned: OK 12 of 12` | 64 s | referee2/log_game_n2_pruned.txt | PASS (identical up to timings) |
| 08.r2_game_n2_pruned_all | `$PY -I -B 08_short_proof/r2_game_pruned.py 2 216 4` | `n=2 pruned: OK 216 of 216` | 808 s | referee2/log_game_n2_pruned_all.txt | PASS (identical up to timings) |
| 08.r2_game_n2_pruned_swap | `$PY -I -B 08_short_proof/r2_game_pruned.py 2 40 9 swap` | `NEG swap caught 11 of 40` | 85 s | referee2/log_game_n2_pruned_negswap.txt | PASS (identical up to timings) |
| 08.r2_game_n2_full | `$PY -I -B 08_short_proof/r2_game.py 2 1 3` | `n=2: OK 1, other 0` | 823 s | referee2/log_game_n2.txt | PASS (instance line identical up to timing; the original log stops before the summary line) |


# Not included


### 01_market_equivalence

- `game_check.py n2` (the full, unreduced n=2 encoding, log n2_unnormalized.log). The book does not cite it: the book reports full encodings only for the 24/25 games. The original run took 1,917 s for Q1 and 8,210 s for Q2 and never logged Q3, so it did not finish. Not run.
- `run1.log` of the game-to-market referee. This is an earlier, smaller invocation of run_tests.py that `run_tests.py 6 1` supersedes. Not a separate check.


### 02_arrival_hardness

- composed_ct.py and coincident.py (Thm compose referee) (C_T = 3/2 composition and coincident ports): referee checks of an alternative sizing, not cited in the book's check lists.
- verify_termcap.py (independent referee of the chain): the terminal-capacity probe; not cited as a check in the book. (verify_bits.py is the cited check `02.verify_bits`, below.)
- verify_lemmas.py, verify_noreuse.py (switch-gadget design run): checks of the earlier chain gadget, superseded by the two-copy gadget; not cited. (verify_chain.py is copied to lib/ only because nocreation.py imports it.)
- the other error-hunt scripts (gadget_stress.py, gadget_bigcp.py, gadget_ctrl.py, embed_random.py, longrun.py, constants_check.py: gadget m<=11, 300 random embeddings, 4 longest n=5 runs, constants m<=80): not cited in Appendix A. The error hunt's composed-market checks (composed_batch.py, composed_n56.py) are now included as `02.eh_*`.
- audit.py of the third review round for article 02: a later audit of the article text (reads the .tex); not cited.
- verify_game_e2e.py `2 8 7` (eps=7 game-level run): reported by the referee as "not caught" and not a must-fail control; not cited.


### 03_plcp

- `e2e.py n2 [start count]`, `e2e.py n3 [count]` modes: not finished in the original (empty logs n2_*.log, n3.log, n2b_first.log); no result is claimed in the book.
- `e2e.py n1 z3` (direct z3 solve, original log n1.log): crashed in the original on converting a 6,919-digit value (int string limit); not a cited result.
- Other scripts of the checker's origin run directory (other worker folders, t1_*.py ... t5, tests): not cited by the book; only the modules imported by check_lemke_rays.py were copied to lib/.


### 04_ueopl

- audit.py of the third review round for article 04: a later audit that reads the article .tex by absolute path; its results are not cited in the book's "Computer checks" or appA-status.
- The "companion" six-game g=1/2 check is included once, as 05_subexp/check_sec6.py.


### 05_subexp

- audit_05_subexp.py, exact_geometry_checks.py, line_extract.py: a later audit of the article text (they read the .tex by absolute path; the numbers they report, e.g. 2,000 projections and 9,846 halfspace cases, are not cited in the book's "Computer checks" or appA-status). Not cited.
- test_glm_lemma.py: Lemma sx-deep is tagged "cited" (statement checked against the source text); the book cites no computer check for it.


### 06_lck

- "A later exact rerun verified 254 ordered equilibria through n=7" (book, Thm artlck:thm:gn): its exact command was not found in the logs (the closest recorded command is `verify_theorem1.py 12 5 0`). The 254 = 2+4+...+128 equilibria for n<=7 are a subset of lck_gn_theorem (n<=10), which was rerun and passed.
- auction-levels-check.py as a standalone check (its `__main__` loads a capacity-scaling auction from another run directory): not cited by the book for this chapter; only its `build_market` builder is used (copied to lib/).
- Other scaling-family scripts (capscale.py as a check, approx_support.py, slope_homotopy.py, dard_*.py, game_one_column.py, game.py `__main__`): not cited in the ch. 6 Status/Computer checks.


### 07_direct_lcp

- None for this chapter: the book cites exactly these two scripts. The other scripts in the producing run's directory (check_block_recognition.py, check_market.py, stoch_*.py, test_signed_k_*_tmp.py, ...) are exploratory and are not cited by the 07 article.


### 08_short_proof

- The author's own checks of the shorter proof (`simplify/simple/verify_*.py`, `simple_lib.py`): Appendix C cites the referees' checks only; `simple_lib.py` imports `referee_lib` by absolute path.
- Referee 2's market-level controls that were *not* caught (`m=1`, `lamfac=1`, `capplus=0`, `eps=6` at n=2, each "caught 0 of 216" in log_market_neg_n2.txt): informational probes, not must-fail controls; not cited.
- Referee 1's n=3 composed check is included as 10 shards (`08.composed_n3`), exactly as originally run.

### 02.verify_bits (added at wrap-up)
Command: `$PY -I -B 02_arrival_hardness/verify_bits.py 7`, 1.2 s. Output rows n=5,6,7 identical to the original log (n=7: 2,570,302 total bits, largest number 81 bits). PASS.

### 01.adv_* (added 2026-11-22): adversarial oracles for the game-to-market reduction
Results. 1,026 games x 5 oracles = 5,130 runs plus the audit bracket (Ex. mk-interp) x 5. Every oracle
answer was verified as an exact (M1) equilibrium of its query, and every output was an exact BNE of the
original game under two independent checkers (attacker best responses, defender cutoff condition, the
top-r optimality of the defender, realization as a mixture of r-sets), whichever equilibrium the oracle
returned. The only exceptions are 3 runs killed by the testing agent (below), which were rerun: 15 of 15 runs
are exact BNE. The audit bracket gives x=(1/6,1/3,1/2) with every oracle.
Size claims (Lemmas mk-bisect, mk-narrow, mk-bits): the number of oracle calls was at most 0.96 of the exact
bound 1+ceil(log2(D Q1^2)) + n ceil(log_{3/2} 4nQ2) in every run. Maxima: 1,967 calls (2 types x 3 targets
with zero slopes/gains, 1/eps = 83 bits); 1,325 calls for positive data (5 x 4); 1,306 calls at 5 x 6. The
largest number in any query had 1,709 bits, in any answer 1,711 bits; at most 2 log2 Q1 + 77 bits in every
run. That is the dyadic bisection midpoint: query size follows the number of bisection steps, as the proof
says, and does not compound across calls. The slowest single oracle call took 0.85 s.
Controls (22 games x 3 oracles, 01.adv_main): the corrupted oracle (raise a used price by 1/3, answer for
doubled capacities, halve the flows) was flagged by the verifier and stopped the procedure in 66/66 runs.
With the pin removed from the narrowing query, the procedure stalled in 69/69 runs (the oracle can return
an endpoint). With the Lemma mk-pin patch removed it output a non-BNE in 18/69 runs: only on the 4 pin
witnesses, which a search over 300 small random games found. On generic games the raw sub-box flow is
already a full-box flow. With the budget repair removed it output a non-BNE in 57/69 runs (endpoint) and in
6/69 runs (chord interpolation, including the audit bracket).
The stall, the fix and the kill. In the first attempt and in the recorded run, randomized-oracle
runs on games with identical types or many ties stopped inside a single z3 `Optimize.check()`. The stack
samples (logs/main_s1_killed_straggler_sample.txt, logs/stuck_sample_pid*.txt) show
`opt::optsmt::prove_unbounded_above` / `opt::curve_certificate::certify` with nlsat/nla frames. A random
objective is unbounded on the LP relaxation until the "price 0 or column full" disjunctions are decided.
The procedure was waiting on the test oracle; its own steps were not involved. The first attempt was
killed after 60 min without results (logs/main_s1_killed.log). That is why the pool is now inspectable:
progress log, live status files, records written as runs finish, a per-run time limit. In the recorded run
the 3 stuck runs were killed by the testing agent itself, through an over-broad `pkill` that matched all
`multiprocessing.spawn` processes of the user. Fix, in the committed oracle code: the encoding adds the
bounds that every equilibrium satisfies (P_j <= max(0, max_i a_ij/b_ij), v_i <= max(0, max_j a_ij),
f_ij <= p_i), and every z3 optimization has a 20 s limit, falling back to a re-randomized objective or a
plain z3 equilibrium (counted in the record field `fallbacks`; one fallback in 01.adv_games). The equilibrium
set does not change, and answers are still verified exactly. 01.adv_main was recorded with the oracle code
before this fix (the procedure and checkers are identical). A full rerun with the committed code was
started and stopped at the user's request (logs/aborted_rerun_*: 440 runs, all exact BNE).
Interpretation points: the dyadic pin t is the smallest multiple of the largest power of 2 that is at most
eta/4, at or above the lower end of the middle third. Lemma mk-degenerate is used only when some slope or
gain is 0. The decode LP takes the support of the perturbed BNE as the pattern. Zero-prior types and
r in {0, n} were not generated (Game requires p_i > 0 and 0 < r < n); tiny priors (down to 1e-6) stand in.

### Exit status (added 2026-11-22)
Every check now exits nonzero when its expected result fails, and a negative control exits 0 only when it is
caught (see MANIFEST.md, "exit-status lines"; no computation or printed output changed). Afterwards
`PY=... ./run_quick.sh` was run end to end on 2026-11-22 (13:15-13:21 UTC): **54 checks, all exit 0
(`done: 54 checks, 0 with nonzero exit status`), 326 s in total**; every final line as listed in README.md.
Failure detection was tested with two runs that must fail (not part of the run scripts, nothing was changed
for them): `game_check_reduced.py n1 -3` (swapped gadget given to the non-control check: Q2 sat) exits 1, and
`r2_market.py neg 1 8 0 '{}'` (a "control" with no modification: caught 0 of 8) exits 1.

### 05_subexp/blocksearch (added 2026-11-22): block search with block size k >= 2

New checks written for the artifact; there is no earlier output to compare against. They were run on
2026-11-22 from the artifact root with `$PY -I -B ...` (CPython 3.12.11, z3 5.4.1). k2 and k3 ran in
parallel with each other, and other jobs were also running. Logs:
`05_subexp/blocksearch/logs/blocksearch_{k2,k3,controls,quick}.log`.

| check id | command | actual final line | runtime | result |
|---|---|---|---|---|
| 05.blocksearch_k2 | `$PY -I -B 05_subexp/blocksearch/test_blocksearch.py k2` | `blocksearch k2: ALL PASS (42 instances, all equal to z3's unique fixed point; games decode to exact BNE) 303s` | 303 s | PASS (exit 0) |
| 05.blocksearch_k3 | `$PY -I -B 05_subexp/blocksearch/test_blocksearch.py k3` | `blocksearch k3: ALL PASS (48 instances, all equal to z3's unique fixed point; games decode to exact BNE) 994s` | 994 s | PASS (exit 0) |
| 05.blocksearch_controls | `$PY -I -B 05_subexp/blocksearch/test_blocksearch.py controls` | `blocksearch controls: 5/5 caught 50s` | 50 s | PASS (all controls caught, exit 0) |
| 05.blocksearch_quick | `$PY -I -B 05_subexp/blocksearch/test_blocksearch.py quick` | `blocksearch quick: ALL PASS (8 instances, all equal to z3's unique fixed point; games decode to exact BNE) 9s` | 10 s | PASS (exit 0) |

**Instances (all passed).**
- Abstract max/clip l1 contractions:
  - k=2: d=2, 3, 4 with 8 each (delta 1/2 and 1/8), d=5 and 6 with 4 each (delta 1/2).
  - k=3: d=2..6 with 8 each.
- Games, m = 1..3 types, a zero slope and a zero gain in every game, r=1 and r=2,3,4:
  - k=1: n=2 (1 game).
  - k=2: n=2 (6), n=3 (3).
  - k=3: n=2 (3), n=3 (2), n=4 (2), n=5 (1).

**Results.**
- Every returned point equals z3's fixed point, and z3 proves that point unique.
- In every game, z3 proved the (1-delta) l1 contraction inequality at the toy g = 1/2 (`unsat`). No
  pattern LP was infeasible, so no g retry was needed.
- Every game decodes to a feasible pattern LP whose exact solution satisfies all BNE conditions. All
  residual bounds of Lemma ueopl-decoding held.

**Totals over k2 and k3.**
- 19,601 recursion calls and 2,747,908 tests.
- The protected grid point was checked against 2,728,307 cuts and was never cut.
- Every return had residual <= tau and ||u-u*|| <= tau/delta.
- Every test satisfied ||y-y(c)|| <= delta tau/16 and ||h-T(c)|| <= e.
- Every cut removed >= 1/(2(k+1)) of the candidates.

**Deep point.** A point of depth >= 1/(2(k+1)) existed every time: 2,747,908 searches, plus 2,480
exhaustive audits of the whole bounding box when it was small, plus 1,000 random unions.
- The coordinatewise median always qualified; the grid and exhaustive fallbacks were never needed.
- Smallest depth used: 1/2 for k=1 and k=2, and 0.419 for k=3 (bound 1/8).
- In 2D a generic l1 halfspace is a coordinate halfspace, so for k=2 the median is 1/2-deep and the
  candidates stay one box.
- For k=3 the unions grew to 20 boxes. On sparse point clouds the deepest point reached 2/5 and the
  median 1/4.

**Controls (all caught).**
- delta=0 is refused.
- Expanding map: z3 finds a violating pair and a second fixed point, and the protected point is cut at
  test 1.
- Wrong orientation: 5/5 caught (protected point cut, or the candidates emptied in a tail call).
- Coarse tail tolerance theta=tau: the hypothesis check fires on 3/3 games. With that check off, the
  final answer was still correct (tails are far more accurate than required). At theta = 2^40
  tau/delta^2 the protected point is cut on 3/3.
- Coarse root tolerance (D=2): 3/3 wrong reconstructions.

**Interpretation and caveats.**
1. g is a toy value, verified per instance by z3.
2. D is the largest true denominator, not the book's (MH)^M.
3. The deep point is found by brute-force search, not GLM's construction.
4. For abstract maps with d=5,6 the contraction is by construction (column sums <= 1-delta on every
   piece), not z3-checked.
5. The k=1 game uses seed 1102 (D ~ 2^24). Seed 1101 (D ~ 2^65) would take about an hour with three
   nested median searches and was stopped.
6. k=2 games with n >= 4 and k=1 games with n >= 3 need three or more nested levels at beta ~ 200-300;
   these were not run.

### Final quick run (2026-11-22, after all additions)
`PY=... ./run_quick.sh`, run end to end from the assembled `submission/code/`: **56 checks, all exit 0** (`done: 56 checks, 0 with nonzero exit status`), **258 s in total**, final lines as listed in README.md. Its logs were not kept in the shipped folder.
