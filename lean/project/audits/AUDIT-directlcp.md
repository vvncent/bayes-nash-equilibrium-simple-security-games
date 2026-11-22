# Faithfulness audit: BssgProofs/DirectLCP (Defs.lean, Statements.lean, DEFINITIONS-directlcp.md)

## Status after this audit (2026-11-22)
- Fixed (cosmetic item): DEFINITIONS-directlcp.md no longer lists the gap lemma as unproved, and the Proofs.lean header
  now says that the gap lemma is proved in Gap.lean, which derives `main_proof`; Final.lean checks
  `DirectLCP.main_proof` with only propext, Classical.choice and Quot.sound.
- Still open (documented): the link to the frozen IsBNE for general r, general defender payoffs and zero-prior types
  (needs the decoder); existence of the P-LCP solution; r in {0, n}; size and bit length of (q, M, delta);
  polynomial running time; the UEOPL step.

Ground truth: book/articles/07-direct-lcp.tex ([DL]). Base: Definitions.lean (BSSG, IsBNE, IsCoverageBNE).

## Verdict
Faithful. No definition or statement under audit says something other than [DL]. There are no
"wrong" mismatches. What remains is a set of documented scope limits (weaker than the full
"exact BNE <=_m P-LCP" claim) and stale documentation.

## Item-by-item
1. IsPMatrix / IsP0Matrix: quantify over all `S : Finset ι`, including the empty set (Mathlib's
   det of the 0x0 matrix is 1, which agrees with [DL] "det M_∅∅ = 1"). `principal` is
   `submatrix` with the same coercion `↥S → ι` on rows and columns, so it is a principal minor.
   OK.
2. IsLCPSol: z >= 0, q + Mz >= 0, z_k (q+Mz)_k = 0. OK. IsSignReversing: y ≠ 0, y_k (My)_k <= 0.
   OK. (The "PV2" label is only a label. M + δI is proved to be a genuine P-matrix, so no
   violation type can occur.)
3. lcpq / lcpM / incMat / shiftA: I checked every row of the table (dl:eq:lcp) against
   `fromBlocks 0 Bᵀ (−D) 0`. They match for general r: q_λ = (r : ℚ), q_f = −A_ij,
   q_t = 1, q_u = p_i, q_x = −1. A_ij = a_ij + 1 + max_k(b_ik − a_ik) via `sup'`. U, W, D_*, S and
   K match [DL] (D_* and U use `fold max 0/1`, which is harmless under WellFormed). rowCoef/rowRhs
   reproduce the 5N+2 rows with the τ coefficient inserted before the denominators are cleared.
   C is the least valid bound >= 1. Q = ((N+1)C)^(N+1) and δ = 1/(2KQ). OK.
4. IsMarginalBNE matches Def. dl:def:bne exactly: x ∈ [0,1]^n, Σx = r (cast ℕ → ℚ), f >= 0, row
   sums = p_i, (a) via the frozen U, (b) a maximum over all feasible x'. Zero-prior types are kept.
   Then Σ_j f_ij = 0 forces f_i = 0, and nothing constrains that type's best response. This is
   sensible in marginal coordinates. Quantifying x' and z over ℚ only is equivalent here (a linear
   objective over a rational polytope).
5. Bridges: MarginalIffCoverage and BNEIffMarginal hold only under r = 1, u1⁰ ≡ 0, u1¹ ≡ 1 and
   p > 0. This is stated honestly in the docstrings and in DEFINITIONS D3. It covers the
   ARRIVAL games (`toGame`: r = 1, payoffs 0/1). It does not cover the general game.
6. MainTheorem: hypotheses WellFormed, 0 < r < |T| (the same as [DL] §2 "from now on 0 < r < n").
   Conclusion: M+δI is P; 0 < δ <= 1; for every z solving LCP(q, M+δI), the pattern LP of
   supp z is feasible, and each feasible point solves LCP(q, M) and is a marginal BNE. This is the
   exact correctness content of the solution map. It is not vacuous: the hypotheses are
   satisfiable (the test game G1 below is WellFormed), and existence of z is the classical P-LCP
   fact that the oracle promise supplies.
7. Coercions/instances: `[Nonempty T]` is a Prop instance (proof-irrelevant). ℕ comparisons
   `0 < G.r`, `G.r < card T` are fine. I found no Decidable or Fintype issue that changes meaning.

## Mismatches / gaps
- (weaker than intended, documented) The Lean result is "marginal BNE <=_m P-LCP". The link to the
  frozen IsBNE is missing for general r, for general defender payoffs (even with r = 1), and for
  zero-prior types. All of these need the decoder Lemma dl:lem:decode (r-subset decomposition and
  best-response restoration), which is not formalized. Fix: formalize the decoder plus a general
  `IsBNE ↔ IsMarginalBNE` bridge.
- (not covered, documented) Existence of a P-LCP solution (Prop. classical (i)). Edge cases
  r ∈ {0, n}. Polynomial size and bit length of (q, M, δ), and polynomial running time.
  UEOPL / FGMS Thm 81.
- (cosmetic) DEFINITIONS-directlcp.md §2 still lists GapLemma/Gap as "not proved" and MainTheorem as
  "modulo Gap". Gap.lean now has `gap_proof : Gap` and `main_proof : MainTheorem`. The Proofs.lean
  header ("The only gap is ...") is stale in the same way. Fix: update both.

## Tests run (scratch <scratch file> t2.lean; `lake env lean`)
- `#print axioms` for main_proof, marginalIffCoverage_proof, bneIffMarginal_proof and
  formulationA/B_proof: only propext, Classical.choice, Quot.sound.
- G0 (2 targets, 2 types, r = 1, d = (1,2)): lcpM equals an independently hand-written matrix
  built from the table, on all 11x11 entries (true). lcpq equals the hand-written q (true). The
  hand-computed BNE x = (0,1), f = diag(1/2,1/2), λ = 3/2, t = (0,1/2), u = (4,2) is an LCP(q,M)
  solution (true). Moving the coverage to target 0 is not a solution (false). K = 20, C = 20,
  log2 Q = 94, δ <= 1.
- G1 (3 targets, r = 2, one type with prior 1 and one zero-prior type): q_λ = 2. The hand-computed
  interior BNE x = (9/11, 8/11, 5/11), f_0 = 1/3 each, zero-prior f = 0, λ = 4/3 is an
  LCP(q,M) solution (true). q + Mz = slackTable on a generic vector (true). `G1.WellFormed` is
  proved. `MainTheorem (Fin 3) (Fin 2)` is obtained from main_proof.
