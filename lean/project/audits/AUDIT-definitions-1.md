# Faithfulness audit: BssgProofs/Definitions.lean + Statements.lean

## Status after this audit (2026-11-22)
- Fixed: the bit sizes are now proved: every number of `Red I` has at most 28(n+1) bits and the whole game at most
  8500(n+1)^5 bits (`red_bits`, `red_descBits`, checked in Final.lean with only propext, Classical.choice and Quot.sound).
- Fixed: `red_bne_exists_proof` (a rational BNE of `Red I` exists, by an explicit construction) is proved and checked
  in Final.lean, so `main` is not vacuous.
- Still open (as documented): polynomial running time of Red and Dec; the two cosmetic docstrings
  (`preprocess_reaches_yes`, `reaches_iff_outcomeWithin`) are unchanged.

Sources checked: Conitzer open-problem PDF (fetched, text extracted), Dohrau et al. v4 (<scratch file>
§1, Run, Def. 1, Def. 2, Obs. 1, Lemma 1, Thm 1), simple-proof.md (SP), ch2-prelim.tex.
Sanity #evals run from <scratch file> (countD 2 = [0,6,12,18]; h0/h1 on k/2 match the figure;
2-switch run reaches yes; dead-switch instance: original outcome none, preprocessed `no`, preprocessed
instance is Preprocessed; |RTarget 1| = 21, |RType 1| = 20; |SNode 2| = 11, |SArc 2| = 18;
inCap(a) = inCap(b) = 2^m, out-cap(s) = K; |E| of the n=2 market = 78 = 2·(2·18+3)).

## Verdict
No definition is WRONG. No statement is vacuous or easier than intended. Remaining gaps are
weaker-than-intended (not formalized) or cosmetic.

## Definition by definition
- ARRIVAL `step/state/Reaches/Answer`: the token moves to succ v (sw v) and then toggles v. s0=s1 works, and so
  does a self-loop (it moves back to v toggled). Terminals absorb. `Answer = Reaches yes`, so a run that never
  terminates answers no. OK.
- `SwitchGraph.E` is a Finset union of images, so it is a set. outE/inE filter it. `IsSwitchingFlow` gives exactly
  Def. 2 (1) in ℤ, and (2) with 0 ≤ automatic in ℕ. When s0=s1, (2) compares the single edge with itself. OK.
  `runStep` matches Run: s_curr/s_next swap = Bool toggle, initial s_curr = s0, and the loop exits at d (a fixed state).
- `toSwitchGraph` has self-loops at both terminals. The run then terminates at t iff the instance reaches t,
  because the other terminal loops forever. OK.
- `reaches_iff_outcomeWithin`: the bound n·2^n counts non-terminal states (Fin n × 2^n), so it is correct and tight.
- Preprocessing: `liveWithin n` (≤ n edges) is equivalent to "can reach a terminal", because a shortest path is simple.
  A dead switch's successors are all dead, so they are redirected to `no` and the result is Preprocessed. The runs agree
  until the first edge into a dead vertex. A dead origin goes straight to `no`. OK (C3). Cosmetic: SP uses m = n' ≤ n,
  Lean uses m = n. Sizes become exact (=) instead of ≤.
- h0, h1 equal SP's definitions for x ≥ 0. Every use has x ≥ 0 (FP requires x ≥ 0, and port purchases lie on E with f ≥ 0).
  FP uses labelled edges (a double edge contributes h0+h1), matching SP and Ch2. OK.
- G_k: all four arc types, tails and heads, capacity 2^{ℓ-1}, cost 3^ℓ, and the arc s0→t0 (capacity 1, cost 0) match SP.
  The countD recursion and pwl match. N_m shares s_m and has 4m+3 nodes and 8m+2 arcs. A = false, B = true.
  K = 2^{m+1}. IsSplitFlow = SP's definition. OK.
- AllocLP / gadgetLP: masses (c for s, in-capacity otherwise), caps (c_e, c−x, none for πa/πb), options and
  coefficients all match SP §5. Lemma 5 applies to them. OK.
- Market `IsEquilibrium`: P ≥ 0, v ≥ 0, f ≥ 0 on E, and (a)–(d), each with strict-positivity triggers, match Ch2 Def. M1.
  All goods are finite with c > 0, as in M1. Options form a set, so there is at most one option per good. OK.
- `redMarket`: c_v = 1+2^n·indeg, exit cap = 1+2^n(indeg yes + indeg no), buyer masses, the four option
  kinds, intercepts 2M−κ / 2M / 2M / M / M−ε, slopes 1 / λ. All checked against the SP bullets. M = 2·3^{m+1}, ε = 3, λ = 2M. OK.
  `redX`, `exitLoad` = SP's x_v, ℓ_t. OK.
- BSSG: u₁⁰ ≤ u₁¹ (uncovered ≤ covered) and u₂⁰ ≥ u₂¹ follow Conitzer's conventions. Defender plays exactly-r subsets
  ("a subset of r targets"). IsBNE has interim type best responses and an ex-ante defender best response, both against all
  mixed deviations. Coverage form is Fact 0 (i), (ii). OK.
- Γ (`gW, gA, gS, gWeight, gPay, toGame`): every table entry, the −2 − ξ default, prior = weight/total, and 0/1 defender
  payoffs match SP §6. The real-target slope is b_ij, not divided by S, as in SP. decP/decV/decF match Lemma 8.
- Red = preprocess → §5 market → Γ. Dec reads σ of the sink types whose (preprocessed) successor is yes, weights
  them by W+μ, and tests = 1 exactly. This matches SP, and weighted σ equals decF, which equals the market purchase of E. OK.

## Statements
All of them match the SP lemmas in quantifiers and hypotheses: dohrau_lemma1 (incl. o ≠ d, profile bound for every k),
lemma1, lemma2_*, lemma3 (m ≥ 1, 0 < θ < 6, x ∈ [0,K]), lemma4 (π = 0 on J_∞), lemma5, lemma6 (c > 0, 0 ≤ x < c,
P', P'' ∈ [0,1], h_i(min(x,K))), theorem7, fact0 (true even without WellFormed), lemma8 (WellFormed, b ≥ 1), sizes.
`main` composes them: fact0 → lemma8 → theorem7 (with preprocess_preprocessed) → preprocess_reaches_yes. It is SP's Theorem
minus polynomial time and bit sizes.

Weaker than intended (not formalized; documented as C14): polynomial running time of Red/Dec, O(n)-bit numbers, and the
explicit-listing size O(n⁴).
Cosmetic: the docstring of preprocess_reaches_yes promises more ("which terminal is reached") than the statement says.
The bound in the docstring of reaches_iff_outcomeWithin is attributed to Dohrau Thm 1, whose n includes all vertices.
The statement itself is correct.

## (i) Rational BNEs only
Adequate. (1) Exact BNE search, and any oracle in Ch2, returns a rational BNE, and Dec only ever sees such outputs.
(2) For a rational profile, "best response among rational deviations" is equivalent to "among real deviations": the payoff
is linear in the deviation, and its maximum over a simplex is attained at a pure (rational) vertex. So Lean's IsBNE is exactly
the real BNE notion restricted to rational profiles. The only loss is irrational BNEs, which are irrelevant for hardness.
The same holds for lemma1 over ℚ, which is used only on rational market equilibria.

## (ii) Vacuity
No hypothesis is unsatisfiable. Preprocessed runs always terminate, integral visit counts give fixed points, and the LPs are
feasible and bounded. `red_bne_exists` (over ℚ) is true: each support pattern of the coverage form is a rational polyhedron,
and Nash gives a real point. With it, `main` is not vacuous. Proving it over ℚ is harder than Nash alone.

## (iii) Easier-than-intended choices
None found. Keeping dead switches (m = n) and using exact cardinalities keep the statement equally strong. Interim type
best responses and exactly-r subsets are the standard, stricter readings.
