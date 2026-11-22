# Adversarial audit of BssgProofs definitions (audit 2, 2026-11-22)

## Status after this audit (2026-11-22)
- Item 3: Fixed: Proofs/Size.lean compiles; Final.lean checks red_wellFormed_proof, red_sizes_proof and red_descBits,
  all with only propext, Classical.choice and Quot.sound.
- Items 1, 2, 4, 5 and 6 are unchanged: rational BNEs only (1), interim best responses also for prior-0 types,
  harmless since `red_wellFormed_proof` gives positive priors (2), running time not formalized (4), and the
  formulation choices (5, 6), which this audit found consistent.

Scope: every line of BssgProofs/Definitions.lean, Statements.lean, Final.lean, DEFINITIONS.md, compared with
Conitzer's open-problem PDF (fetched), Dohrau et al. arXiv:1605.03546v4 (<scratch file> Run, Def. 1, Def. 2),
simplify/simple/simple-proof.md and book appC-short-proof.tex.

## Verdict
No definition that `main` depends on (ArrivalInstance, succ, step, state, Reaches, preprocess/liveWithin/redirect,
indeg, redMarket and its pieces, splitter/countingNetwork, toGame/gPay/gWeight/gW/gA/gS, Red, BSSG, IsDist,
IsDefMixed, attEU, defEU, IsBNE, Dec) differs in meaning from the sources. I found no "wrong" mismatch, and nothing
that could invalidate `main`. Remaining gaps are "weaker than intended" or cosmetic.

## Findings
1. C1, rational BNEs only (weaker than intended, low). `main` covers only BNEs with values in Q. Deviations that
   range over Q lose nothing, because pure deviations are rational and payoffs are linear. But irrational points of
   non-singleton equilibrium components are not covered. Fix: parametrise δ and σ (and IsBNE) over ℝ, or over a
   LinearOrderedField with FloorRing, with the game data cast. This cannot invalidate `main`.
2. IsBNE requires interim best responses from every type, including types with prior 0 (cosmetic). For a general
   BSSG this hypothesis is stronger than ex-ante BNE. It is harmless here because `red_wellFormed_proof` proves that
   all priors of Red I are positive. I checked its statement against `red_wellFormed` with `type_of%`. Fix (optional):
   require best responses only when `0 < prior θ`.
3. Legality and size are not in Final (cosmetic, but these facts are needed for the claim). `red_wellFormed_proof`
   (axioms: standard only) and `Bssg.red_sizes_proof` exist and match their statements (checked with `type_of%`), but
   neither Final.lean nor BssgProofs.lean imports them. Proofs/Size.lean does not compile: line 521 cites
   `Emb.red_sizes_proof`, which does not exist (the theorem is `Bssg.red_sizes_proof`). So `red_descBits` (the
   polynomial bit-size bound) currently depends on sorryAx or errors. Fix: rename the reference, then add `example`
   checks for red_wellFormed, red_sizes and red_descBits to Final.
4. Running time is not formalized (C14, cosmetic). `liveWithin` as written makes about 2^n recursive calls, so `Red`
   and `Dec` are not polynomial-time code as written. Mathematically each is plain reachability. Neither Red nor Dec
   uses `state`, `Reaches` or `outcomeWithin`, so neither secretly computes the answer.
5. Problem formulation (cosmetic). `ArrivalInstance` uses two terminals and forces n ≥ 1. Dohrau's Def. 1
   (Run(G,o,d) with o ≠ d) embeds by taking switches V\{d}, mapping d to yes and leaving no unused. The case o = d is
   trivial. The successors are arbitrary maps into Fin n ⊕ {yes,no}, and the origin is arbitrary. There is no hidden
   restriction such as distinct successors or a preprocessing requirement; preprocessing is done inside Red.
6. Red uses m = n and keeps dead switches (C3) rather than SP's m = n'. This is consistent: preprocessing keeps the
   answer and the sizes are exact.

## Checked and matching
- IsDefMixed: δ ≥ 0, Σ_S δ = 1, support only on |S| = r. IsDist σ_θ for every θ. Type best response is checked against
  all mixed τ. Defender best response is ex ante against all IsDefMixed δ'. attEU and defEU use u¹ when the target is
  covered and u⁰ otherwise.
- BSSG.WellFormed equals Conitzer's conditions: r ≤ |T|, a distribution on types, u₁⁰ ≤ u₁¹, u₂⁰ ≥ u₂¹. Defender
  payoffs do not depend on the type.
- step, state, Reaches: start at the origin with every switch at s₀ (false), move to the current successor, then
  toggle. Terminals are absorbing. A run that never terminates gives Reaches yes = false, so the answer is no. This
  matches the Run pseudocode.
- Constants match SP and the book: M = 2·3^{m+1}, ε = 3, λ = 2M, K = 2^{m+1}, c_v = 1 + 2^m·indeg(v),
  cap(E) = 1 + 2^m(indeg yes + indeg no), mass of (v,s) = c_v + [v=o], other masses are in-capacities. The option
  list and intercepts/slopes match SP §5. Γ's table (W, A, S, weights, payoffs, the −2 − ξ default) matches SP §6.
- Dec reads only σ, plus W and the sink masses derived from I. It is computable: #eval works.

## Tests run (lake env lean on <scratch file>)
- Run semantics: s₀ = yes gives yes after 1 step. A self-loop s₀(0) = 0 with s₁ = yes gives yes at step 2. With
  s₀ = s₁ = 0 the run never reaches a terminal, and its preprocess gives no. A 2-switch instance gives no or yes
  depending on the origin, matching a hand trace. liveWithin values are correct.
- Sizes: |T|, |Θ| = 21, 20 (n=1) and 63, 62 (n=2), which equal 12n²+6n+3 and 12n²+6n+2. The splitter has
  7/10 and 11/18 nodes/arcs. countD gives [0], [0,6], [0,6,12,18]. inCap(sink) = 2^m.
- Constants, n=1: W = 18, A = 37, S = 704, |E| = 23, total weight 356, priors sum to 1. Payoffs (2M/S, λ) = (9/176, 36),
  (M/S, 1) = (9/352, 1), ((M−ε)/S, 1) = (15/704, 1), private (37/704, 1), outside (0, 1), dedicated and control (2, 1),
  default (−2, 1). All match hand computation.
- Constants, n=2: W = 73, A = 109, S = 6650, |E| = 78. Priors are positive and sum to 1, and u₂¹ ≤ u₂⁰ everywhere
  (checked with decide). All match hand computation.
- IsBNE on a toy game (2 targets, 1 type): the pure profile is proven not to be a BNE (the defender deviates). The
  half/half profile is proven to be a BNE. σ ≡ 0 and δ ≡ 0 are proven not to be BNEs.
- type_of% checks: main, main_coverage, red_bne_exists, red_wellFormed, fact0, fact0_realize, red_sizes. Axioms are
  only propext, Classical.choice, Quot.sound. There is no native_decide, axiom, implemented_by or extern in Proofs.
- Dec I1 (σ ≡ 0) = false, and Dec I1 (σ with 1/20 on E for sink a, weight 20) = true.
