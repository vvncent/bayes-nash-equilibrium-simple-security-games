# Verification artifact: Bayes-Nash equilibrium in Bayesian simple security games

This package collects, in one place and with relative imports only, the computer checks that the book's
"Computer checks" / "Status" passages and the verification-status appendix (Appendix A) of `main.pdf`
cite, including the checks of the shorter ARRIVAL-hardness proof of
Appendix C (folder `08_short_proof/`). Every check here was copied from the script that produced the
reported result and changed only in paths/imports (and, where noted, an output path or argument default),
plus exit-status lines: every check exits nonzero when its expected result fails, and a negative control exits
0 only when it is caught (see MANIFEST.md).
Exploratory scripts that the book does not cite are not included; see REPRODUCTION.md, "Not included".

* `MANIFEST.md` -- every file: original path, sha256 of the original, modifications made.
* `REPRODUCTION.md` -- the result of re-running every included check from this folder, compared with the
  output recorded in the book or the original logs (PASS / FAIL / timing notes).
* `run_quick.sh` -- the fast subset (a few minutes in total); `run_full.sh` -- every check (several hours).

What the checks are: exact rational arithmetic (Python `fractions`) and the SMT solver z3 over linear real
arithmetic with rational inputs, one disjunction per complementarity condition, so an `unsat` answer covers
every equilibrium of the finite instance at once. Exceptions are stated per check (one floating-point MILP
cross-check in 06_lck). The checks cover small instances only; for general sizes the results rest on the
proofs in the book.

## Setup

```
python3.12 -m venv .venv && .venv/bin/pip install -r requirements.txt
export PY=$PWD/.venv/bin/python
./run_quick.sh            # or ./run_full.sh
```

All commands below are run **from the artifact root** as `$PY -I -B <folder>/<script> [args]`
(`-I`: isolated mode, `-B`: no `__pycache__`). Reproduced with CPython 3.12.11 and z3-solver 5.4.1.0
(see requirements.txt).

## Layout

```
lib/            shared builders, imported by the checks through a path computed relative to each script
  switchcheck.py        exact z3 verifier of switch gadgets in the market (M1) (S1/S2 over all chambers)
  ds_twosink.py         Disser-Skutella counting network, exact integer successive-shortest-path min-cost flow
  twocopy_gadget.py     the two-copy switch gadget as an (M1) market gadget (also a check: S1+S2 for small K)
  composed_check.py     ARRIVAL runner + composition of gadgets into one (M1) market + z3 equilibrium encoding
  referee_lib.py        independent re-implementation of composition, market-to-game embedding and BNE encoding
  verify_chain.py       the earlier chain gadget (used by the no-mass-creation check)
  core.py, procedure.py game, box, (M1) z3 oracle, exact BNE checker; game-to-market procedure (bisection, pinning, repair LP)
  lp_market.py, ratlp.py, splitcore.py, exactlp.py   exact LP helpers of the original P-LCP audit checker
  lck_alg.py, security.py                            exact Li-Conitzer-Korzhyk Algorithms 1-4; security-game BNE checker
  auction_levels_check.py                            builder of the hard family Gamma_h
  game.py, mcf.py, capscale.py                       the family G_n, exact min-cost flow, capacity scaling
01_market_equivalence/ ... 07_direct_lcp/   one folder per article; logs/ = output of the artifact runs; out/ = files written by checks
08_short_proof/  checks of Appendix C (shorter ARRIVAL-hardness proof) by its two referees; their builders
                 ref_lib.py (referee 1) and r2lib.py (referee 2) live in this folder, next to the checks that import them
```

Each chapter script starts with a three-line bootstrap that puts its own folder and `../lib` on
`sys.path`; there are no absolute paths in the code. A check that is also a shared module lives in `lib/`
and is started through a launcher `run_<module>.py` in its chapter folder.

## The checks

Columns: check id; the book result it supports and what it verifies; command (from the artifact root);
the expected final output line (from the original log or, if none was saved, from the book/report; `<t>`
stands for a timing); runtime measured in the artifact run (the machine was often heavily loaded by other
jobs, so these are upper bounds; original runtimes are given where they differ a lot); whether it is in
`run_quick.sh`. **Original source path:** for each check, the script file named in the command is listed in
`MANIFEST.md` with its original path and hash (provenance is kept only there).


## 01_market_equivalence/ -- Ch. 3: security game <-> affine matching market

All commands run from the artifact root with `$PY -I -B`. Runtimes were measured with up to three checks running at once on a shared 14-core machine (other chapters were running at the same time), so a check run alone takes less.

| check id | book result: what it verifies | command | expected final output line | measured runtime | quick/full |
|---|---|---|---|---|---|
| 01.run_tests | Ex. mk-interp, Prop. mk-g2m: the game-to-market procedure (z3 as the (M1) oracle) run from the audit bracket (25 pinned calls) and from scratch returns x=(1/6,1/3,1/2); two-target example; 6 random games; every output is an exact BNE | `$PY -I -B 01_market_equivalence/run_tests.py 6 1` | `ALL OK` | 7 s | quick |
| 01.audit_cases | Ex. mk-interp: z3 shows the interpolated point (5/27,10/27,4/9) admits no BNE flow at any cutoff; the two-target bracket is repaired to (1/2,1/2) | `$PY -I -B 01_market_equivalence/check_audit_cases.py` | `audit cases OK` | <1 s | quick |
| 01.rand_canon60 | Lemmas mk-box-cutoff..mk-pin, Prop. mk-g2m: 60 random games (at most 3 types and 3 targets), canonicalization on, three oracle modes; every output is an exact BNE (part of the book's 420) | `$PY -I -B 01_market_equivalence/run_random.py 60 7 1` | `exits {'repair': 28, 'bisection-hit': 32} canon=True N=60 all BNE verified, <t>s` | 46 s | quick |
| 01.rand_nocanon60 | same, 60 games, canonicalization off | `$PY -I -B 01_market_equivalence/run_random.py 60 8 0` | `exits {'bisection-hit': 31, 'repair': 28, 'hit': 1} canon=False N=60 all BNE verified, <t>s` | 48 s | full |
| 01.rand_canon150 | same, 150 games, canonicalization on | `$PY -I -B 01_market_equivalence/run_random.py 150 21 1` | `exits {'repair': 66, 'bisection-hit': 79, 'hit': 5} canon=True N=150 all BNE verified, <t>s` | 178 s | full |
| 01.rand_nocanon150 | same, 150 games, canonicalization off | `$PY -I -B 01_market_equivalence/run_random.py 150 22 0` | `exits {'bisection-hit': 69, 'repair': 77, 'hit': 4} canon=False N=150 all BNE verified, <t>s` | 281 s | full |
| 01.degen8 | Lemma mk-degenerate: 8 random games with zero slopes and gains, solved through the perturbation; each decoded result is an exact BNE of the original game | `$PY -I -B 01_market_equivalence/check_degenerate.py 8 5` | `degenerate decoding OK` | 84 s | full |
| 01.degen16 | Lemma mk-degenerate: 16 more such games (24 in total with degen8) | `$PY -I -B 01_market_equivalence/check_degenerate.py 16 9` | `degenerate decoding OK` | 244 s | full |
| 01.balanced | Balanced anchored market (Appendix B, ch. 3 notes): on 80 random markets every equilibrium decodes to an (M1) equilibrium; 39 have positive dummy utility | `$PY -I -B 01_market_equivalence/check_balanced.py 80 3` | `balanced anchor decode OK on 80 markets (39 equilibria with positive dummy utility)` | 1 s | quick |
| 01.slope_below_one | Prop. mk-below-one: with slope 1/100 the constructed game has a BNE (x=(80/101,21/101,0,0)) that does not decode, and the market has no equilibrium with P different from 100 | `$PY -I -B 01_market_equivalence/slope_below_one.py` | `market equilibrium exists: sat` | <1 s | quick |
| 01.embed_n1_reduced | Thm. mk-embed / Thm. A: n=1 instance (24 types, 25 targets), reduced encoding: a BNE exists (Q1 sat), no BNE decodes wrongly (Q2 unsat), none violates an intermediate claim (Q3 unsat) | `$PY -I -B 01_market_equivalence/game_check_reduced.py n1` | `Q3 some BNE fails the M1 decoding or the doc's lemmas: unsat (<t>s)` | 1 s | quick |
| 01.embed_n1_full | Thm. mk-embed: same n=1 instance, full encoding (every type x target pair), unnormalized weights | `$PY -I -B 01_market_equivalence/game_check.py n1` | `RESULT: OK` | 48 s | quick |
| 01.embed_n1_full_normalized | Thm. mk-embed: same, full encoding with the true probabilities | `$PY -I -B 01_market_equivalence/game_check.py n1 1` | `RESULT: OK` | 68 s | full |
| 01.embed_n1_control | Thm. mk-embed negative control: swapped gadget (eps=-3); Q2 must be sat (a BNE loads the wrong terminal), Q3 unsat. The script prints NOT OK, which is the expected outcome for a control | `$PY -I -B 01_market_equivalence/game_check.py n1 0 -3` | `RESULT: NOT OK` | 96 s | full |
| 01.embed_n2_reduced | Thm. mk-embed / Thm. A: n=2 instance (66 types, 67 targets), reduced encoding, Q1 sat, Q2 unsat, Q3 unsat | `$PY -I -B 01_market_equivalence/game_check_reduced.py n2` | `Q3 some BNE fails the M1 decoding or the doc's lemmas: unsat (<t>s)` | 3 s | quick |
| 01.batch_n2 | Thm. mk-embed / Thm. A: all 56 discriminating n=2 instances (66 types, 67 targets), reduced encoding, plus the swapped-gadget control on each | `$PY -I -B 01_market_equivalence/batch_reduced.py 2` | `56 instances; all OK: True; swapped control caught on 56/56` | 445 s | full |
| 01.batch_n3 | Thm. mk-embed / Thm. A: 8 random discriminating n=3 instances (132 types, 133 targets), reduced encoding, plus controls | `$PY -I -B 01_market_equivalence/batch_reduced.py 3 8 7` | `8 instances; all OK: True; swapped control caught on 8/8` | 640 s | full |
| 01.adv_quick | Prop. mk-g2m / Thm. mk-main(b), adversarial oracles: 13 small games (audit cases, one pin witness, 10 random/structured incl. one with a zero slope or gain) x 5 oracles (z3 default; lexicographically smallest and largest prices; random vertex / relative-interior point; maximally degenerate), the audit bracket x 5 oracles, and the negative controls (corrupted oracle x3, pinning removed (no pin / no patch), budget repair removed (endpoint / chord interpolation)); every oracle answer verified as an exact (M1) equilibrium, every output an exact BNE of the original game | `$PY -I -B 01_market_equivalence/adversarial/test_adversarial.py quick 6` | `quick: 70 runs (13 games x 5 oracles + 5 audit-bracket), failures=0, timeouts=0, controls all caught, <t>s` | 24 s | quick |
| 01.adv_main | same, 1,026 games (2 audit cases, 4 pin witnesses, 420 random positive games up to 5 types x 6 targets, 30 at 4-5 x 5-6, 150 with exact ties, 120 near-degenerate, 120 with zero slopes/gains through Lemma mk-degenerate, 60 identical types, 60 one dominant target, 60 tiny priors), r = 1..n-1, x 5 oracles = 5,130 runs + audit bracket x 5; records call counts (checked against the bound of Lemmas mk-bisect + mk-narrow) and the bit length of every query and answer; controls on 22 games x 3 oracles | `$PY -I -B 01_market_equivalence/adversarial/test_adversarial.py main 1 10 1 1800` | recorded run (oracles before the z3 bound fix, see REPRODUCTION.md): `main_s1: 5135 runs (1026 games x 5 oracles + 5 audit-bracket), failures=3, timeouts=0, controls all caught, 2543s`, the 3 being runs killed by the testing agent, rerun as 01.adv_games; a rerun with the committed oracle code should print failures=0 | 2,543 s (10 workers) | full |
| 01.adv_games | the 3 runs of 01.adv_main lost to a kill by the testing agent (`identical#2`, `identical#45`, `ties#31`, all with the random oracle), rerun with all 5 oracles and the committed oracle code | `$PY -I -B 01_market_equivalence/adversarial/test_adversarial.py games 1 identical#2 identical#45 ties#31` | `games_s1: 15 runs (3 games x 5 oracles + 0 audit-bracket), failures=0, timeouts=0, controls all caught, <t>s` | 130 s | full |

`adversarial/test_adversarial.py` imports `lib/core.py`, `lib/procedure.py`, `check_degenerate.py` (Q3, decode) and `run_tests.py` (audit games) read-only and replaces only the (M1) oracle. Exit status: 0 = all runs exact BNE and all controls caught; 1 = a failure or an uncaught control; 2 = no failure but some runs hit the per-run time limit (unverified). While it runs it writes `adversarial/logs/progress_<tag>.log` (START/DONE/TIMEOUT per run, a heartbeat every 60 s with each running task's phase and the age of its current oracle call), `logs/live_<tag>/w<k>.json`, and `logs/runs_<tag>.jsonl` (one record per run, written as it finishes; failures carry the full game data).

Shared modules: `lib/core.py` (game, box, (M1) z3 oracle, exact BNE checker) and `lib/procedure.py` (bisection, pinning, canonicalization, repair LP). The embedding checks use `lib/composed_check.py`, `lib/twocopy_gadget.py` and `lib/switchcheck.py`. `game_check.py` builds the game (types and targets) from a composed market and is imported by the other embedding checks.


## 02_arrival_hardness/ -- Ch. 4: ARRIVAL-hardness of exact BNE

| check id | book result: what it verifies | command | expected final output line | measured runtime | quick/full |
|---|---|---|---|---|---|
| 02.ds_twocopy | Lemmas incr, alt: G_m increments strictly increasing with min gap 6 (m<=6, exact successive shortest paths); two-copy flow-level split alternates a,b,a,b for K up to 64 | `$PY -I -B 02_arrival_hardness/ds_twocopy.py` | `two-copy m=5 K=64 eps=3: PASS; min kink=3; arcs=42; nodes=23` | 6 s | quick |
| 02.incr_check | Lemma incr: exact LP values F_m(y) (z3 Optimize) equal the proved recursion, linear between integers, min gap 6, max increment 2*3^m, m=1..5 | `$PY -I -B 02_arrival_hardness/incr_check.py 5` | `ALL OK` | 2 s | quick |
| 02.gadget_allK | Lemmas incr, alt and Lemma lp (Step 1): recursion = direct SSP for m<=6; recursion properties for m<=20; LP structure of every gadget equilibrium (z3, m<=3) | `$PY -I -B 02_arrival_hardness/verify_gadget_allK.py` | `ALL OK` | 1 s | quick |
| 02.twocopy_gadget | Thm gadget (S1, S2): exact certification over all equilibria and all policy chambers, K=4,8,16 | `$PY -I -B 02_arrival_hardness/run_twocopy_gadget.py 3` | `3 16 42 978 True []` | 3 s | quick |
| 02.twocopy_controls | Thm gadget: controls eps=0, eps=7, box 4 rejected; S1+S2 certified for K=32,64,128,256 | `$PY -I -B 02_arrival_hardness/twocopy_controls.py 4 5 6 7` | `m=7 K=256 agents=90 bits=3474 certified=True (<t>s); chain(K) would need 258 agents` | 564 s | full |
| 02.verify_bits | Sizes (Section 4.4): bit size of the reduction on the chain instance (succ0(v)=v+1, succ1(v)=0, origin 0), n=1..7; n=7 game has 2,570,302 bits (about 2.6 Mbit); bit sizes for n=1..7 (ratio to n^5 printed) | `$PY -I -B 02_arrival_hardness/verify_bits.py 7` | last row `7 \|   220   415 \|    24359 (  23) \|   636   637 \|      2570302 (   81) \| 152.9` | 1 s | quick |
| 02.gadget_cp_m1-3 | Thm gadget, conditions C1-C6: for m=1..3, all 18 in-condition configurations per m pass; eps in {1,5} and H=0 violate S1 (re-verified witnesses); c_p<=K fails only the checker's stronger test P_p <= Pbar, as the Sharpness paragraph of Ch. 4 says | `$PY -I -B 02_arrival_hardness/gadget_cp.py 02_arrival_hardness/out/gadget_cp_m1-3.jsonl 4 1 2 3` | 108 lines, 54 `PASS` and 54 `FAIL` (order varies, parallel workers) | 33 s | quick |
| 02.gadget_cp_m4-6 | same, m=4..6 | `$PY -I -B 02_arrival_hardness/gadget_cp.py 02_arrival_hardness/out/gadget_cp_m4-6.jsonl 6 4 5 6` | 108 lines, 54 `PASS` and 54 `FAIL` | 870 s (6 workers) | full |
| 02.driver2_n2 | Thm compose (market level): 6 longest discriminating n=2 instances; every equilibrium loads the run's terminal 1, the other 0; eps=-3 gadget caught | `$PY -I -B 02_arrival_hardness/composed_driver2.py 2 6` | `correct gadget all OK: True; swapped gadget all OK (should be False): False; tied gadget all OK: False` | 3 s | quick |
| 02.driver2_n3 | Thm compose: 40 longest discriminating n=3 instances | `$PY -I -B 02_arrival_hardness/composed_driver2.py 3 40` | same line as above | 329 s | full |
| 02.driver2_n4 | Thm compose: 15 longest discriminating n=4 instances (runs up to 15 steps) | `$PY -I -B 02_arrival_hardness/composed_driver2.py 4 15` | same line as above | 153 s | full |
| 02.random_n3 | Thm compose: 40 random discriminating n=3 instances | `$PY -I -B 02_arrival_hardness/composed_random.py 3 40 11` | `n=3: 40 random discriminating instances; correct gadget OK on all: True; swapped gadget caught on all: True (<t>s)` | 28 s | quick |
| 02.random_n4 | Thm compose: 15 random discriminating n=4 instances | `$PY -I -B 02_arrival_hardness/composed_random.py 4 15 12` | `n=4: 15 random discriminating instances; correct gadget OK on all: True; swapped gadget caught on all: True (<t>s)` | 23 s | full |
| 02.market_e2e_n3 | Thm compose, independent re-implementation: 20 n=3 instances; correct gadget OK, wrong-order (swap) switch caught | `$PY -I -B 02_arrival_hardness/verify_market_e2e.py 3 20` | `n=3: 20 of 3418 discriminating instances; correct OK on all: True; swap caught on all: True (<t>s)` | 23 s | quick |
| 02.market_e2e_n4 | same, 12 n=4 instances | `$PY -I -B 02_arrival_hardness/verify_market_e2e.py 4 12` | `n=4: 12 of 370056 discriminating instances; correct OK on all: True; swap caught on all: True (<t>s)` | 47 s | full |
| 02.game_e2e_n2 | Thm A / Cor A, independent chain on the actual game: 8 n=2 instances (66 types, 67 targets): a BNE exists and no BNE decodes wrongly | `$PY -I -B 02_arrival_hardness/verify_game_e2e.py 2 8` | `ALL OK` | 354 s | full |
| 02.game_e2e_n2_swap | Thm A control: wrong-order switch caught on 8/8 | `$PY -I -B 02_arrival_hardness/verify_game_e2e.py 2 8 swap` | `NOT ALL OK` (every instance `CAUGHT/FAIL`, as intended for a control) | 418 s | full |
| 02.game_e2e_n2_epsm3 | Thm A control: eps=-3 gadget caught on 8/8 | `$PY -I -B 02_arrival_hardness/verify_game_e2e.py 2 8 -3` | `NOT ALL OK` (every instance `CAUGHT/FAIL`) | 181 s | full |
| 02.game_e2e_n3 | Thm A: the longest n=3 instance (7-step run, 132 types, 133 targets) | `$PY -I -B 02_arrival_hardness/verify_game_e2e.py 3 1` | `succ=[(0, 1), (0, 2), ('yes', 'no')] run->yes (7 steps) \| types=132 targets=133 \| BNE exists: sat; some BNE decodes wrongly: unsat \| OK (<t>s)`, then `ALL OK` | 879 s | full |
| 02.game_e2e_n3_swap | Thm A control: wrong-order switch caught on the longest n=3 instance | `$PY -I -B 02_arrival_hardness/verify_game_e2e.py 3 1 swap` | `NOT ALL OK` (instance `CAUGHT/FAIL witness: in(yes)=0, in(no)=1`) | 427 s | full |
| 02.nocreation | Remark ar-smallterm: "no mass creation" (A+B<=x at all port prices >=0) for small gadgets | `$PY -I -B 02_arrival_hardness/nocreation.py` | `ALL OK` | <1 s | quick |
| 02.nocreation_control | Remark ar-smallterm control: the query detects creation when it exists | `$PY -I -B 02_arrival_hardness/nocreation_control.py` | `control: A+B>x satisfiable: sat (expect sat); S1+S2 certified: False (expect False)` | 1 s | quick |
| 02.eh_batch_n5 | Thm 4.4 (original construction, error hunt, own builder eh_lib): 24 random discriminating n=5 instances, no vertex deleted; every equilibrium loads the run's terminal 1 and the other 0 (Q2), no equilibrium has x_v>=K or outputs other than (h0,h1) (Q3), an equilibrium exists (Q1); 6 worker processes, 2-8 min per instance | `$PY -I -B 02_arrival_hardness/composed_batch.py 5 24 11` | `n=5 count=24 seed=11: ALL OK` | not rerun in full (original: about 13 min wall with 6 workers, 4,565 s summed over instances); first instance rerun: 108 s | full |
| 02.eh_batch_n6 | Thm 4.4, same, 10 random discriminating n=6 instances; 7-16 min per instance | `$PY -I -B 02_arrival_hardness/composed_batch.py 6 10 12` | `n=6 count=10 seed=12: ALL OK` | not rerun in full (original: about 28 min wall with 6 workers, 6,609 s summed); first instance rerun: 194 s | full |
| 02.eh_n5_selfloop_chain | Thm 4.4, hand-picked n=5 instance `n5_selfloop_chain`: an equilibrium exists (model re-checked as a fixed point) and no equilibrium decodes wrongly | `$PY -I -B 02_arrival_hardness/composed_n56.py n5_selfloop_chain` | `  OK` | 21 s | full |
| 02.eh_n5_coincident | Thm 4.4, hand-picked n=5 instance `n5_coincident`: an equilibrium exists (model re-checked as a fixed point) and no equilibrium decodes wrongly | `$PY -I -B 02_arrival_hardness/composed_n56.py n5_coincident` | `  OK` | 61 s | full |
| 02.eh_n5_bothterm_same | Thm 4.4, hand-picked n=5 instance `n5_bothterm_same`: an equilibrium exists (model re-checked as a fixed point) and no equilibrium decodes wrongly | `$PY -I -B 02_arrival_hardness/composed_n56.py n5_bothterm_same` | `  OK` | 4 s | full |
| 02.eh_n5_counter | Thm 4.4, hand-picked n=5 instance `n5_counter`: an equilibrium exists (model re-checked as a fixed point) and no equilibrium decodes wrongly | `$PY -I -B 02_arrival_hardness/composed_n56.py n5_counter` | `  OK` | 41 s | full |
| 02.eh_n5_unreach_cycle | Thm 4.4, hand-picked n=5 instance `n5_unreach_cycle`: an equilibrium exists (model re-checked as a fixed point) and no equilibrium decodes wrongly | `$PY -I -B 02_arrival_hardness/composed_n56.py n5_unreach_cycle` | `  OK` | 15 s | full |
| 02.eh_n5_deleted | Thm 4.4, hand-picked n=5 instance `n5_deleted`: an equilibrium exists (model re-checked as a fixed point) and no equilibrium decodes wrongly | `$PY -I -B 02_arrival_hardness/composed_n56.py n5_deleted` | `  OK` | 8 s | full |
| 02.eh_n6_counter | Thm 4.4, hand-picked n=6 instance (counter chain) | `$PY -I -B 02_arrival_hardness/composed_n56.py n6_counter` | `  OK` | 71 s | full |
| 02.eh_n6_mixed | Thm 4.4, hand-picked n=6 instance (11-step run) | `$PY -I -B 02_arrival_hardness/composed_n56.py n6_mixed` | `  OK` | 80 s | full |
| 02.eh_swap_n2 | Thm 4.4 control: port swap caught at n=2 (prints OK when caught) | `$PY -I -B 02_arrival_hardness/composed_n56.py n2_fig swap` | `  OK` (after `WITNESS load(want)=0 load(other)=1`) | 1 s | full |
| 02.eh_swap_n3 | Thm 4.4 control: port swap caught at n=3 | `$PY -I -B 02_arrival_hardness/composed_n56.py n3_t swap` | `  OK` (after `WITNESS load(want)=0 load(other)=1`) | <1 s | full |

The `02.eh_*` checks are the later error hunt of the original construction (Chapter 4), with its own builder `eh_lib.py` written from the book text; `composed_batch.py` uses a pool of worker processes (4th argument, default 6). `02.eh_batch_n5` and `02.eh_batch_n6` take 2-16 min per instance and are in `run_full.sh` only; REPRODUCTION.md records a rerun of the first instance of each (`composed_batch.py 5 1 11 1`, `composed_batch.py 6 1 12 1`) and the full original results. These scripts import their sibling `eh_lib.py` through their own folder and are byte-identical to the originals.

The game-level checks of Thm A by the embedding referee (n=1 full encoding, all 56 discriminating n=2 instances, 8 random n=3 instances) are the embedding checks listed under 01_market_equivalence (01.embed_*, 01.batch_n2, 01.batch_n3).


## 03_plcp/ -- Sec. 5.1: market (M1) -> P-matrix LCP, and ARRIVAL -> P-LCP

| check id | book result: what it verifies | command | expected final output line | measured runtime | quick/full |
|---|---|---|---|---|---|
| plcp-check | Lemmas plcp:formulation--plcp:gap, Thm plcp:main, Example plcp:negative: principal minors of M >= 0 (some > 0) and of M+eps I > 0; eps of the theorem; unique perturbed solution (z3 + 2^N basis enumeration for N<=8); decode tested directly against Def. m1 on 6 hand-built + 60 random + 8 large (N<=19, eps<=828 bits) markets; Lemma plcp:bound at several eps; negative control fails at eps=1 | `$PY -I -B 03_plcp/check_plcp.py` | `ALL CHECKS PASSED` | 34 s | quick |
| plcp-q0 | Prop plcp:q0: existence-and-restoration recipe on 40 random zero-margin markets, restored point solves LCP(q,M) | `$PY -I -B 03_plcp/check_q0.py` | `Q0 recipe: 40 random markets with zero margins, restored point solves LCP(q, M) exactly` | 0.2 s | quick |
| plcp-lemke-rays | Remark plcp:noray / original audit checker: on 3 markets, covered LCP admits no bound-violating point (z3 unsat), decode confirmed by two independent split-LP implementations, zero-margin/homogeneous/negative-margin boundary cases | `$PY -I -B 03_plcp/check_lemke_rays.py` | `Zero-margin lift and homogeneous direction sat, both negative margins infeasible` | 0.9 s | quick |
| plcp-e2e-n1 | Cor plcp:arrival, n=1 end to end: ARRIVAL -> composed market -> 49-dim P-LCP at 676-bit eps, certified basis (unique solution), decoded equilibrium loads the run's terminal; eps=-3 gadget control loads no=2, yes=0 | `$PY -I -B 03_plcp/e2e.py n1 cert` | last line: `RESULT n=1 ... geps=-3 ... decoded=none (yes=0, no=2) ... ok=True` (first RESULT line: `geps=3 ... delta_bits=676 ... load_yes=1 | load_no=0 ... decoded=yes ... ok=True`) | 8 s | quick |
| plcp-e2e-side | Cor plcp:arrival side checks: reduction's eps equals the independent checker's eps (n=1,2, both gadgets); random principal minors of composed M >= 0 and of M+eps I > 0; eps in {1,1/2,1/16} makes the decoding LP infeasible | `$PY -I -B 03_plcp/side_checks.py` | last line: `RESULT n=1 ... delta_bits=5 ... decode=unsat ... ok=False | why=system (1) infeasible` (expected: control caught) | 20 s | quick |
| plcp-e2e-sizes | Cor plcp:arrival sizes quoted in the book: n=2 is 146-dim with 2,482-bit eps; n=3 is 299-dim (no solving) | `$PY -I -B 03_plcp/sizes.py` | `n=4 geps=-3 discriminating=- N=508 options=287 buyers=79 goods=142 U=12532 C=24934 delta_bits=12026` | 0.4 s | quick |


## 04_ueopl/ -- Sec. 5.3-5.4: UEOPL membership via one l1 contraction

Seven runs of `check.py` (seeds 1-3 with 3 games each, seeds 4-7 with 4 games each = 25 random games, n<=3, m<=3) plus the 8 dedicated games of `sanity.py` make the book's 33 games. Gap tests (pattern LPs) run on games with n*m<=4: 18 games, 1,800 patterns, 82 with optimal slack 0. Jacobian tests: 25 x 60 + 6 x 40 = 1,740 pieces. True-constant contraction searches: 25 + 6 = 31 (book: 30 unsat, 1 unknown). The book's "companion" item 6 (six games at g=1/2) is the same check as 05_subexp/check_sec6.py, listed there.

| check id | book result: what it verifies | command | expected final output line | measured runtime | quick/full |
|---|---|---|---|---|---|
| ueopl_seed1 | Lemmas ueopl-pattern..ueopl-decoding, Thm sx-game, Thm ueopl-main: per random game, z3 finds the fixed point and excludes a second one; decoding (R unclipped, s=q, sum identity, residuals/g); exact pair tests; z3 contraction-violation search (true constants and g=1/10); exact Jacobians; pattern-LP gap test | `$PY -I -B 04_ueopl/check.py 1 3 full` | `time <t>s` (last game); key lines: `gap test: 144 patterns, 3 with t*=0, unknown 0, smallest positive t*=4/147, bad=[]` | 79 s | full |
| ueopl_seed2 | same, seed 2 (3 games) | `$PY -I -B 04_ueopl/check.py 2 3 full` | `time <t>s`; game 0 gap test `36 patterns, 3 with t*=0 ... t*=7/23` | 71 s | full |
| ueopl_seed3 | same, seed 3 (3 games); contains the book's one timeout (game 1, n=3, m=2: true-constant search `unknown`) | `$PY -I -B 04_ueopl/check.py 3 3 full` | `time <t>s`; game 1: `z3 contraction-violation search (true constants): unknown` | 235 s | full |
| ueopl_seed4 | same, seed 4 (4 games) | `$PY -I -B 04_ueopl/check.py 4 4 full` | `time <t>s`; all true-constant searches `unsat` | 236 s | full |
| ueopl_seed5 | same, seed 5 (4 games) | `$PY -I -B 04_ueopl/check.py 5 4 full` | `time <t>s` | 200 s | full |
| ueopl_seed6 | same, seed 6 (4 games) | `$PY -I -B 04_ueopl/check.py 6 4 full` | `time <t>s` | 268 s | full |
| ueopl_seed7 | same, seed 7 (4 games) | `$PY -I -B 04_ueopl/check.py 7 4 full` | `time <t>s` | 69 s | full |
| ueopl_sanity | dedicated games (all slopes zero, all gains zero, both, identical tied types, r=n-1, three n=4 games) through the full pipeline including the z3-vs-rational evaluator agreement (120 points); negative controls: factor 0.999(1-delta) and eta too large yield violating pairs | `$PY -I -B 04_ueopl/sanity.py` | `teeth: mutated eta with s-column sum 0.677 -> unsat, ratio None (expect sat if > 1)` | 317 s | full |
| ueopl_teeth_s_column | negative control: shrinking d'_j inside T so the s-column sum exceeds one yields a violating pair | `$PY -I -B 04_ueopl/teeth_s_column.py` | `mutated s-column sum 7.93 -> z3 sat, exact ratio of witness 34858354031571370628853408000000/21461297931662654231502788482799 (> 1-delta, caught)` | <1 s | quick |
| ueopl_l1_contraction | the internal (non-referee) check: l1 contraction ratio <= 1-delta on 200 random games x 200 exact pairs, cube invariance, projection KKT; control with eta=1 shows expansion; exact four-target Jv / l2-growth example | `$PY -I -B 04_ueopl/check_l1_contraction.py` | `OVERALL PASS` | 41 s | quick |


## 05_subexp/ -- Sec. 5.5: subexponential algorithm

| check id | book result: what it verifies | command | expected final output line | measured runtime | quick/full |
|---|---|---|---|---|---|
| subexp_thm1 | Thm sx-pl / Lemmas sx-sign, sx-protect, sx-denom: sign formula vs definition (20,000 random cases with forced ties), protected grid point never cut (349,550 failed-test cuts, k=1,2,3), 20,000 continued-fraction recoveries, end-to-end block-size-one search recovers the exact fixed point (12/12 in d=2, 3/3 in d=3, agreeing with z3) | `$PY -I -B 05_subexp/check_thm1.py` | `pipeline d=3 exact recoveries: 3 {'calls': 6077, 'tests': 544970, 'max_tests': 94, 'z_removed': 0}` | 144 s (under heavy machine load) | full |
| subexp_sec6 | Thm sx-game (also the "companion" UEOPL check, App. A, UEOPL row): on 6 random games (n=3, m=2, a zero slope and a zero gain, toy g=1/2) z3 proves no pair violates the (1-delta) l1 bound, and the fixed-point properties hold (0<q<kappa, unclipped R, sum identity, residual bounds); one tuple per game `(game, 'unsat', worst sampled ratio, decode_ok, failures)` | `$PY -I -B 05_subexp/check_sec6.py` | `(5, 'unsat', 0.9999976784663589, True, {})` | 38 s | quick |


## 06_lck/ -- Ch. 6: lower bounds for the Li-Conitzer-Korzhyk algorithm

| check id | book result: what it verifies | command | expected final output line | measured runtime | quick/full |
|---|---|---|---|---|---|
| lck_uniqueness_depth5 | Lemma artlck:lem:unique / Thm artlck:thm:main / Lemma artlck:lem:fold: on Gamma_h, h=1..5, SMT over all partial-budget equilibria at every breakpoint and midpoint (3+5+9+17+33=67 budgets) shows coverage P(y) is the only one; slopes of P take only values 1,2 and alternate; exact equilibrium at budget 1 | `$PY -I -B 06_lck/check_lck_security_path.py --depth 5` | `Depth 5: 27 types, 12 targets, 33 unique intermediate coverages, 16 affine pieces, integer-budget equilibrium verified.` | 21 s | quick |
| lck_endpoint_h21 | Prop. artlck:prop:easy: direct endpoint of Gamma_21 (44 targets, 107 types) computed and verified exactly, where Thm artlck:thm:main gives >= 2^20 calls | `$PY -I -B 06_lck/check_lck_security_path.py --endpoint 21` | `Direct endpoint verified for depth 21, 107 types and 44 targets. Published path bound: 1,048,576 successful updates.` | <1 s | quick |
| lck_validate | Prop. artlck:prop:impl (implementation validation): exact Algorithms 1–4 on 40 random games x rules R1–R4 = 160 runs, all outputs exact BNE by an independent security-game checker | `$PY -I -B 06_lck/validate.py 40` | `SUMMARY ok=160 bad=0 stuck=0 runs=160 time=<t>s` | <1 s | quick |
| lck_family_a_small | Prop. artlck:prop:impl, Table tab:lck-runs (Gamma_h, h=1..4, R1, R2, R3x2, R4x2): exactly 2^(h-1) successful Alg. 3 calls, exact BNE, no path mismatch | `$PY -I -B 06_lck/run_family_a.py 1,2,3,4 R1,R2,R3,R4 0,1` | `{'h': 4, 'rule': 'R4', 'seed': 1, 'bne': True, 'succ': 8, 'fail': 6, ... 'path_mismatch': 0, ...}` | 2 s | quick |
| lck_family_a_mid | same, h=5..8, R1–R4 (16,32,64,128 successful calls) | `$PY -I -B 06_lck/run_family_a.py 5,6,7,8 R1,R2,R3,R4 0` | `{'h': 8, 'rule': 'R4', 'seed': 0, 'bne': True, 'succ': 128, 'fail': 7, ... 'path_mismatch': 0, ...}` | 44 s [orig ~20 s] | full |
| lck_family_a_large | same, h=9..11, R1 and R2 (256, 512, 1024 successful calls; failed calls 1 for R1, 2h+1 for R2) | `$PY -I -B 06_lck/run_family_a.py 9,10,11 R1,R2 0` | `{'h': 11, 'rule': 'R2', 'seed': 0, 'bne': True, 'succ': 1024, 'fail': 23, ... 'path_mismatch': 0, ...}` | 726 s [orig ~180 s; R2 at h=11 87 s] | full |
| lck_family_b | Thm artlck:thm:gn, Table tab:lck-runs bottom: Algorithm runs on G_n, n=1..5, budget n+1, R1–R4: successful-call counts >= 2^n, outputs exact BNE | `$PY -I -B 06_lck/run_family_b.py 1,2,3,4,5` | `{'n': 5, 'rule': 'R4', 'seed': 0, 'bne': True, 'succ': 143, 'fail': 20, 'bound': 32, ...}` | 12 s | quick |
| lck_ds_gadget | Lemma artlck:lem:ds: Disser–Skutella network, successive-shortest-path costs exactly 0..2^n-1 with unit augmentations, n<=8 | `$PY -I -B 06_lck/run_mcf.py 8` | `n=8: nodes=18 arcs=33 SSP iterations=256 path costs 0..2^n-1: True, unit augmentations: True, recursive flows optimal with cost v(v-1)/2: True` | <1 s | quick |
| lck_gn_theorem | Thm artlck:thm:gn: every proof inequality exact for n=1..40; 2046 forced equilibria (n<=10) exact-verified; floating-point MILP over all equilibria (n<=2) shows the special-pair mass is forced | `$PY -I -B 06_lck/verify_theorem1.py 40 10 2` | `   n=2: max \|extreme return mass - (j+1)/Kappa\| over j = 1.11e-16  (<t>s)` | 16 s | quick |
| lck_gn_milp_n3 | Thm artlck:thm:gn: the MILP part for n=3 (book: "for n<=3"); argument-only variant of the same script | `$PY -I -B 06_lck/verify_theorem1.py 1 1 3` | `   n=3: max \|extreme return mass - (j+1)/Kappa\| over j = 3.89e-16  (<t>s)` | 26 s | full |
| lck_gn_bisection | Remark artlck:rem:gn-easy: bisection solves G_n for n=10,20,40,60 in 32,53,97,137 oracle calls, outputs exact equilibria | `$PY -I -B 06_lck/bisect_solver.py 10 20 40 60` | `        mid-window budget: exact equilibrium True; oracle calls=138; return flow=576460752303423489 (expected near 2^(n-1)+1 = 576460752303423489)` | 256 s [orig ~45 s] | full |

Shared code used: lib/lck_alg.py, lib/security.py (LCK implementation + independent BNE checker), lib/auction_levels_check.py (Gamma_h builder), lib/game.py, lib/mcf.py, lib/capscale.py (G_n family, min-cost flow, capacity scaling). MILP check needs numpy and scipy (HiGHS); it prints harmless HiGHS warnings on stderr.


## 07_direct_lcp/ -- Sec. 5.2: direct P0 / P-matrix LCP formulation of the game

| check id | book result: what it verifies | command | expected final output line | measured runtime | quick/full |
|---|---|---|---|---|---|
| 07-source | Lemma 5.15 (dl:lem:p0) and Thm 5.19 (dl:thm:main) (direct P-LCP, source's check): det B_{R,F} det D_{R,F} >= 0 on all 3,003 equal-size pairs of two 2x3 games (1,134 / 663 positive, 494 / 359 with budget column); on four fixed games computes K, Q, delta, solves the perturbed LCP with z3, checks box/slack identities, pattern LP, exact decoded BNE and the mixed-strategy decomposition (Lemma dl:lem:decode); 1/delta of 56-958 bits | `$PY -I -B 07_direct_lcp/check_direct_game.py` | `All direct-game checks passed.` | 1 s | quick |
| 07-referee | Lemmas 5.14, 5.15, 5.16, 5.20 (dl:lem:formulation, dl:lem:p0, dl:lem:pmatrix, dl:lem:decode) (referee's independent check): 27,904 exhaustive + 12,000 sampled principal minors nonnegative; LCP/BNE equivalence on 15 games (z3); perturbation + repair on 3 fixtures; r=0, r=n and zero-prior restoration; negative control without payoff shift rejected | `$PY -I -B 07_direct_lcp/check_review.py` | `PASS` | 3 s | quick |

## 08_short_proof/ -- Appendix C: the shorter proof of ARRIVAL-hardness

Checks of the shorter proof by its two independent referees: referee 1 (`ref_lib.py`, `check_*.py`) and referee 2
(`r2lib.py`, `r2_*.py`). Lemma numbers refer to Appendix C of the book (Thm C.1 = the theorem, Lemma C.3 = decoder by
floors, Lemma C.8 = one gadget, Thm C.9 = composition, Lemma C.10 = market-to-game decoding). All files are byte-identical
copies; each script imports its sibling builder through its own folder. `08.composed_n3` and `08.composed_n4` are sharded
with the environment variable `SHARD=<i>/<k>` (`run_full.sh` runs the shards one after another; the artifact run ran them in
parallel). Negative controls print `bad`/`caught` counts by design; their exit status is 0 when the control is caught and 1 otherwise.

| check id | book result: what it verifies | command | expected final output line | measured runtime | quick/full |
|---|---|---|---|---|---|
| 08.gadget | Lemma C.8 (referee 1): one z3 query per m=1..6 with c, x, P', P'' symbolic (optimality via complementary slackness): no optimum with (A,B) != (h0(min(x,K)), h1(min(x,K))); 5 sanity points sat | `$PY -I -B 08_short_proof/check_gadget.py 6` | `m=6 M=4374 eps=3 control=None : violation query unsat   sanity ['sat', 'sat', 'sat', 'sat', 'sat']  (<t>s)` | 4 s | quick |
| 08.gadget_smallM | Lemma C.8 control: M below the bound gives a counterexample for m=1..3 | `$PY -I -B 08_short_proof/check_gadget.py 3 smallM` | `m=3 M=40 eps=3 control=smallM : violation query sat CEX c=33/2 x=65/4 P1=1 P2=1 A=5 B=19/4 ...` | <1 s | quick |
| 08.gadget_eps1 | Lemma C.8 control: eps=1 gives a counterexample for m=1..3 | `$PY -I -B 08_short_proof/check_gadget.py 3 eps1` | `m=3 M=162 eps=1 control=eps1 : violation query sat CEX c=7/2 x=3 P1=1 P2=0 A=1 B=2 ...` | 1 s | quick |
| 08.gadget_eps55 | Lemma C.8 control: eps=5.5 gives a counterexample for m=1..3 | `$PY -I -B 08_short_proof/check_gadget.py 3 eps55` | `m=3 M=162 eps=5.5 control=eps55 : violation query sat CEX c=13 x=155/12 P1=1/4 P2=1 A=7 B=71/12 ...` | <1 s | quick |
| 08.gadget_Pbox2 | Lemma C.8, port-price box [0,2] (not a control): still unsat for m=1..3 | `$PY -I -B 08_short_proof/check_gadget.py 3 Pbox2` | `m=3 M=162 eps=3 control=Pbox2 : violation query unsat   sanity [...]  (<t>s)` | <1 s | quick |
| 08.lemmas | Lemma C.4 for k<=4; Lemma C.7 on 300 random allocation LPs (control M=sum kappa/3 fails on 97); Lemma C.10 on 60 random markets with slopes >=1 (control slopes 1/20..1/60 fails on 27) | `$PY -I -B 08_short_proof/check_lemmas.py` | `Lemma 8 control, slopes 1/20..1/60 (trials, bad): (60, 27)` | 3 s | quick |
| 08.floor_n2 | Lemma C.3 (floor step and conclusion), reduced: all instances with n<=2 (also Lemma 4.3's statement) | `$PY -I -B 08_short_proof/check_floor.py 2` | `instances 265 violations 0 with fractional fixed points 146 nonterminating-with-FP 0` | <1 s | quick |
| 08.floor | Lemma C.3: all instances with n<=3 and 3,000 random n=4 instances (18,890), 11,849 with fractional fixed points; no fixed point violates the floor step or the conclusion | `$PY -I -B 08_short_proof/check_floor.py 3 3000` | `instances 18890 violations 0 with fractional fixed points 11849 nonterminating-with-FP 0` | 66 s | full |
| 08.composed_n1 | Thm C.9, reduced: all 8 canonical preprocessed n=1 instances; every equilibrium decodes correctly, port prices <=1 | `$PY -I -B 08_short_proof/check_composed.py 1` | `n=1 control=None instances(canonical, preprocessed) 8 bad 0 tags {...}  <t>s` | <1 s | quick |
| 08.composed_n2 | Thm C.9: all 224 canonical preprocessed n<=2 instances (self-loops, a=b, both exits to one terminal, deleted vertices, origin with in-edges) | `$PY -I -B 08_short_proof/check_composed.py 2` | `n=2 control=None instances(canonical, preprocessed) 224 bad 0 tags {...}  <t>s` | 19 s | quick |
| 08.composed_n2_eps0 | Thm C.9 control eps=0: fails on 48 of 224 | `$PY -I -B 08_short_proof/check_composed.py 2 0 0 eps0` | `n=2 control=eps0 instances(canonical, preprocessed) 224 bad 48 tags {...}  <t>s` | 17 s | full |
| 08.composed_n2_lamM | Thm C.9 control lambda=1: fails on 224 of 224 (port-price bound or decoding) | `$PY -I -B 08_short_proof/check_composed.py 2 0 0 lamM` | `n=2 control=lamM instances(canonical, preprocessed) 224 bad 224 tags {...}  <t>s` | 9 s | full |
| 08.composed_n3 | Thm C.9: all 6,748 canonical preprocessed n=3 instances, in 10 shards i=0..9 (each shard about 5-15 min) | `SHARD=<i>/10 $PY -I -B 08_short_proof/check_composed.py 3` | each shard: `n=3 control=None instances(canonical, preprocessed) 675 bad 0 ...` (674 for shards 8, 9) | 309-346 s per shard (10 shards run in parallel) | full |
| 08.composed_n4 | Thm C.9: 24 random preprocessed n=4 instances (half with the longest runs, up to 20 steps), 3 shards i=0..2 | `SHARD=<i>/3 $PY -I -B 08_short_proof/check_composed_n4.py 24 44` | each shard: `n=4 instances 8 bad 0 <t>s` | 36-52 s per shard | full |
| 08.game_n1 | Thm C.1, full game: all 8 n=1 instances (20 types, 21 targets): a BNE exists, no BNE decodes wrongly | `$PY -I -B 08_short_proof/check_game.py 1` | `n=1 instances 8 bad 0` | 5 s | quick |
| 08.game_n2 | Thm C.1, full game: 6 random n=2 instances (62 types, 63 targets) | `$PY -I -B 08_short_proof/check_game.py 2 6 1` | `n=2 instances 6 bad 0` | 278 s | full |
| 08.r2_gadget | Lemma C.8 (referee 2): 3,490 exact points (m=1..6, four capacities each, x on and between integers, port prices at the corners and random); controls eps=0, eps=6, M=sum kappa/3 give counterexamples | `$PY -I -B 08_short_proof/r2_gadget.py` | `TOTAL 3490 FAILURES 0` | 198 s | full |
| 08.r2_market_n1 | Thm C.9 (referee 2): all 8 n=1 instances | `$PY -I -B 08_short_proof/r2_market.py all 1` | `n=1: OK 8, FAIL 0` | <1 s | quick |
| 08.r2_market_n2 | Thm C.9: all 216 n=2 instances | `$PY -I -B 08_short_proof/r2_market.py all 2` | `n=2: OK 216, FAIL 0` | 15 s | quick |
| 08.r2_market_n3 | Thm C.9: 30 random n=3 instances | `$PY -I -B 08_short_proof/r2_market.py rand 3 30 11` | `n=3: OK 30, FAIL 0` | 10 s | quick |
| 08.r2_market_n3_300 | Thm C.9: 300 more random n=3 instances | `$PY -I -B 08_short_proof/r2_market.py rand 3 300 31` | `n=3: OK 300, FAIL 0` | 115 s | full |
| 08.r2_market_n4 | Thm C.9: 6 random n=4 instances | `$PY -I -B 08_short_proof/r2_market.py rand 4 6 12` | `n=4: OK 6, FAIL 0` | 8 s | quick |
| 08.r2_market_n4_60 | Thm C.9: 60 more random n=4 instances | `$PY -I -B 08_short_proof/r2_market.py rand 4 60 41` | `n=4: OK 60, FAIL 0` | 130 s | full |
| 08.r2_market_n5 | Thm C.9: 4 random n=5 instances | `$PY -I -B 08_short_proof/r2_market.py rand 5 4 13` | `n=5: OK 4, FAIL 0` | 9 s | quick |
| 08.r2_market_hard_n4 | Thm C.9: 33 hard n=4 instances (20 longest runs of 20,000 samples, 10 high in-degree hubs, 3 origin self-loops) | `$PY -I -B 08_short_proof/r2_market_hard.py 4 20 21` | `n=4 hard: OK 33, FAIL 0` | 153 s | full |
| 08.r2_market_hard_n5 | Thm C.9: 27 hard n=5 instances (runs up to 52 steps) | `$PY -I -B 08_short_proof/r2_market_hard.py 5 16 22` | `n=5 hard: OK 27, FAIL 0` | 657 s | full |
| 08.r2_neg_n2_swap | Thm C.9 control: swapped ports caught on 56 of 216 n=2 instances (the discriminating ones) | `$PY -I -B 08_short_proof/r2_market.py neg 2 216 0 '{"swap":true}'` | `NEG {'swap': True}: caught 56 of 216` | 9 s | quick |
| 08.r2_neg_n2_lam1_4 | Thm C.9 control: lambda=M/4 caught on 10 of 216 | `$PY -I -B 08_short_proof/r2_market.py neg 2 216 0 '{"lamfac":"1/4"}'` | `NEG {'lamfac': Fraction(1, 4)}: caught 10 of 216` | 10 s | full |
| 08.r2_neg_n2_eps0 | Thm C.9 control: eps=0 caught on 46 of 216 | `$PY -I -B 08_short_proof/r2_market.py neg 2 216 0 '{"eps":0}'` | `NEG {'eps': 0}: caught 46 of 216` | 10 s | full |
| 08.r2_neg_n3_m1 | Thm C.9 control: gadget size m=1 at n=3 (K too small) caught | `$PY -I -B 08_short_proof/r2_market.py neg 3 600 5 '{"m":1}'` | `NEG {'m': 1}: caught 1 of 600` | 19 s | full |
| 08.r2_game_n1 | Thm C.1 (referee 2), full game: all 8 n=1 instances | `$PY -I -B 08_short_proof/r2_game.py 1 8 0` | `n=1: OK 8, other 0` | 39 s | quick |
| 08.r2_game_n1_swap | Thm C.1 control: swapped ports caught on the 2 discriminating n=1 instances | `$PY -I -B 08_short_proof/r2_game.py 1 8 0 swap` | `NEG swap: caught 2, other 6` | 9 s | full |
| 08.r2_game_n2_pruned | Thm C.1, game with strictly dominated pairs fixed to 0: 12 n=2 instances (reduced instance of 08.r2_game_n2_pruned_all) | `$PY -I -B 08_short_proof/r2_game_pruned.py 2 12 3` | `n=2 pruned: OK 12 of 12` | 64 s | full |
| 08.r2_game_n2_pruned_all | Thm C.1, same encoding: all 216 n=2 instances | `$PY -I -B 08_short_proof/r2_game_pruned.py 2 216 4` | `n=2 pruned: OK 216 of 216` | 808 s | full |
| 08.r2_game_n2_pruned_swap | Thm C.1 control: swap caught on the 11 discriminating of 40 n=2 instances | `$PY -I -B 08_short_proof/r2_game_pruned.py 2 40 9 swap` | `NEG swap caught 11 of 40` | 85 s | full |
| 08.r2_game_n2_full | Thm C.1, full encoding: one n=2 instance (62 types, 63 targets) | `$PY -I -B 08_short_proof/r2_game.py 2 1 3` | `[0] 0:(1,1) 1:(no,no) run->no types=62 targets=63 exist=sat wrong-decode=unsat <t>s` (the original log has only this line), then `n=2: OK 1, other 0` | 823 s | full |

## Runtimes

`run_quick.sh`: 56 checks (38 for chapters 01-07, including `01.adv_quick` (24 s) and `02.verify_bits`, 138 s end to end on a quiet machine for the first 36; 17 for 08_short_proof, 87 s; 1 block-search subset, 10 s; the whole quick suite took 234 s end to end on a lightly loaded machine). `run_full.sh`: all 124 checks (135 commands, including `02.verify_bits`, the three block-search checks and the three 01.adv_* checks; the 02.eh_* and 08.* checks add about 9,800 s, mostly the 10 sequential shards of `08.composed_n3`, about 1 h, and the two error-hunt batches, about 40 min with 6 workers); for the original 69 checks the per-check runtimes measured under heavy load add up to about 9,200 s (about 2.5 h); the slowest are `gadget_cp.py ... 4 5 6` (about 15 min with 6 workers), `verify_game_e2e.py 3 1` (about 15-20 min), `run_family_a.py 9,10,11` (3-12 min), `batch_reduced.py 3 8 7` and `twocopy_controls.py 4 5 6 7` (about 10 min each). `gadget_cp.py` appends to its output file in `out/`; delete that file before a rerun if you want a clean result file. Logs written by the run scripts are `<folder>/logs/run_quick_<n>.log` / `run_full_<n>.log`; the logs named `<check-id>.log` are the ones recorded in REPRODUCTION.md.

## 05_subexp/blocksearch/ -- Sec. 5.5, Thm sx-pl with block size k >= 2 (added 2026-11-22)

New checks (not copied from an earlier run; see MANIFEST.md). `blocksearch.py` implements, in exact
arithmetic (`fractions.Fraction`, Python integers), the recursive block search of Thm sx-pl exactly as in
Sec. sec:subexp. It covers:
- blocks of k coordinates, tail recursion with theta = delta^2 tau/16, and grid N = 2^beta with
  beta = ceil(log2(16k/(delta tau)));
- candidates kept as a disjoint union of integer boxes, cut by the l1 halfspace H(c, c-h) through the
  sign formula (Lemma sx-sign), and a stop when ||h-c||_1 <= tau/2;
- root tolerance tau = 2^-B <= delta/(8D^2) and continued-fraction reconstruction (Sec. sx-recon);
- the game map F of Sec. sec:contraction with the book's constants.

The deep point (Lemma sx-deep, cited from GLM) is **not** GLM's centerpoint algorithm. It is a
brute-force exact search over integer points of the bounding box: the coordinatewise median first, then
a quantile/endpoint grid, then every point of a small bounding box. The exact depth is the minimum over
v != 0, computed through one generic v per sign vector and threshold family. Each call asserts that a
point of depth >= 1/(2(k+1)) was found.

Every recursion call is checked against its exact restricted fixed point. This point is obtained by
solving the active affine piece and verifying it by exact evaluation, with a z3 fallback. The call
checks that:
- the returned residual is <= tau, and ||u-u*|| <= tau/delta;
- ||y-y(c)|| <= delta tau/16 and ||h-T(c)|| <= e at every test;
- the rounded protected grid point z is in none of the call's cuts and survives in the final union;
- every cut removes >= 1/(2(k+1)) of the candidates;
- the number of failed tests is within the O(k^2 log N) bound.

Games use a **toy threshold g = 1/2**, as in subexp_sec6; the real g = 1/(4Q) would make delta about
10^-100. The book's constants are computed from g, and before each search z3 proves the (1-delta) l1
contraction inequality for those constants on that instance (`unsat`). z3 also gives the fixed point
and proves it unique. D is the largest denominator of z3's fixed point; this is a valid
instance-specific bound, whereas the book's (MH)^M would be far larger. The returned point must equal
z3's fixed point exactly. It must then decode (Lemma ueopl-decoding) to a feasible pattern LP, solved
exactly with z3, whose solution satisfies every condition of Lemma cutoff(b) in exact arithmetic.

| check id | book result: what it verifies | command | expected final output line | measured runtime | quick/full |
|---|---|---|---|---|---|
| 05.blocksearch_k2 | Thm sx-pl, Lemmas sx-sign/sx-deep/sx-slice/sx-protect, Sec. sx-recon, Thm sx-game, k=2 (plus the k=1 baseline on one game). Primitives: sign formula vs definition (5,000), depth formula vs all integer v in [-4,4]^k (300), box cuts vs pointwise removal (300). Deep-point lemma conclusion on 700 random unions (k=1,2). Abstract max/clip l1 contractions d=2..6 (32 instances, delta 1/2 and 1/8); games n=2 (6) and n=3 (3) with k=2; one n=2 game with k=1. All equal z3's unique fixed point; games give an exact BNE; protected point never cut | `$PY -I -B 05_subexp/blocksearch/test_blocksearch.py k2` | `blocksearch k2: ALL PASS (42 instances, all equal to z3's unique fixed point; games decode to exact BNE) <t>s` | 303 s | full |
| 05.blocksearch_k3 | same with k=3. Deep-point lemma conclusion on 300 random unions (incl. sparse point clouds); abstract d=2..6 (40 instances); games n=2 (3), n=3 (2), n=4 (2), n=5 (1) | `$PY -I -B 05_subexp/blocksearch/test_blocksearch.py k3` | `blocksearch k3: ALL PASS (48 instances, all equal to z3's unique fixed point; games decode to exact BNE) <t>s` | 994 s | full |
| 05.blocksearch_controls | negative controls, each must be caught: delta=0 (refused); an l1-expanding map with claimed delta=1/4 (z3 finds a violating pair and a second fixed point; protected point cut at test 1); wrong cut orientation H(c,h-c) (5/5: protected point cut or candidates emptied); too-coarse tail tolerance theta=tau (3/3 games: hypothesis ||y-y(c)||<=delta tau/16 violated; with that check off the answer is still right, while at theta = 2^40 tau/delta^2 the protected point is cut); too-coarse root tolerance (tau for D=2: 3/3 wrong reconstruction) | `$PY -I -B 05_subexp/blocksearch/test_blocksearch.py controls` | `blocksearch controls: 5/5 caught <t>s` | 50 s | full |
| 05.blocksearch_quick | subset of the three: primitives, deep-point stress, abstract d=2..4 with k=2,3, two n=2 games with k=3, 4 controls | `$PY -I -B 05_subexp/blocksearch/test_blocksearch.py quick` | `blocksearch quick: ALL PASS (8 instances, all equal to z3's unique fixed point; games decode to exact BNE) <t>s` | 10 s | quick |

Findings:
- **k=2 exercises less geometry than it may seem.** For a generic v in R^2, H(w,v) is a coordinate
  halfspace {s_i(z_i - w_i) >= 0} for the i with the larger |v_i|. So the coordinatewise median is
  1/2-deep, and the candidates stay a single box throughout (max_boxes = 1 in every k=2 run).
- **k=3 is the real test.** It has majority-type halfspaces, unions of up to 20 boxes, and smallest
  depth used 0.419 against the bound 1/8. The deep-point stress reaches 2/5 (deepest point) and 1/4
  (median) on sparse point clouds.
- **The median always sufficed.** The fallback stages were never needed.
