# Lean formalization

`project/` is a Lean 4.36.0 + Mathlib v4.36.0 project (about 13,700 lines). For the shorter construction of
Appendix C of `main.pdf`, the statement that every rational BNE decodes to the right answer, together with the
size and bit-length bounds, is machine-checked in Lean 4. Lean does not show polynomial running time: no
running-time bound is proved for Red or Dec (see Scope below).

Build: install Lean with elan, then in `project/` run `lake exe cache get` and `lake build`. `build-output.txt` records the axiom lines of one such build from a fresh copy.
`BssgProofs/Final.lean` prints:

    'Bssg.main_proof' depends on axioms: [propext, Classical.choice, Quot.sound]
    'Bssg.main_coverage_proof' depends on axioms: [propext, Classical.choice, Quot.sound]
    'Bssg.red_bne_exists_proof' depends on axioms: [propext, Classical.choice, Quot.sound]
    'Bssg.red_wellFormed_proof' depends on axioms: [propext, Classical.choice, Quot.sound]
    'Bssg.redMarket_bits' depends on axioms: [propext, Classical.choice, Quot.sound]
    'Bssg.red_bits' depends on axioms: [propext, Classical.choice, Quot.sound]
    'Bssg.red_descBits_le_product' depends on axioms: [propext, Classical.choice, Quot.sound]
    'Bssg.red_descBits' depends on axioms: [propext, Classical.choice, Quot.sound]
    'Bssg.red_sizes_proof' depends on axioms: [propext, Classical.choice, Quot.sound]
    'Bssg.DirectLCP.main_proof' depends on axioms: [propext, Classical.choice, Quot.sound]
    'Bssg.DirectLCP.bneIffMarginal_proof' depends on axioms: [propext, Classical.choice, Quot.sound]
    'Bssg.DirectLCP.marginalIffCoverage_proof' depends on axioms: [propext, Classical.choice, Quot.sound]
    'Bssg.MarketLCP.formulation_proof' depends on axioms: [propext, Classical.choice, Quot.sound]
    'Bssg.MarketLCP.formulationEqSol_proof' depends on axioms: [propext, Classical.choice, Quot.sound]
    'Bssg.MarketLCP.formulationSolEq_proof' depends on axioms: [propext, Classical.choice, Quot.sound]
    'Bssg.MarketLCP.slackTable_proof' depends on axioms: [propext, Classical.choice, Quot.sound]
    'Bssg.MarketLCP.p0_proof' depends on axioms: [propext, Classical.choice, Quot.sound]
    'Bssg.MarketLCP.pMatrix_proof' depends on axioms: [propext, Classical.choice, Quot.sound]
    'Bssg.MarketLCP.uniformBound_proof' depends on axioms: [propext, Classical.choice, Quot.sound]
    'Bssg.MarketLCP.gap_proof' depends on axioms: [propext, Classical.choice, Quot.sound]
    'Bssg.MarketLCP.starSol_proof' depends on axioms: [propext, Classical.choice, Quot.sound]
    'Bssg.MarketLCP.main_proof' depends on axioms: [propext, Classical.choice, Quot.sound]
    'Bssg.MarketLCP.negativeExample_proof' depends on axioms: [propext, Classical.choice, Quot.sound]
    'Bssg.MarketGame.rescaleEquiv_proof' depends on axioms: [propext, Classical.choice, Quot.sound]
    'Bssg.MarketGame.rescaleEquivBack_proof' depends on axioms: [propext, Classical.choice, Quot.sound]
    'Bssg.MarketGame.nuSpec_proof' depends on axioms: [propext, Classical.choice, Quot.sound]
    'Bssg.MarketGame.rescaledWF_proof' depends on axioms: [propext, Classical.choice, Quot.sound]
    'Bssg.MarketGame.composeCoverage_proof' depends on axioms: [propext, Classical.choice, Quot.sound]
    'Bssg.MarketGame.composeBNE_proof' depends on axioms: [propext, Classical.choice, Quot.sound]
    'Bssg.MarketGame.composeLift_proof' depends on axioms: [propext, Classical.choice, Quot.sound]
    'Bssg.MarketGame.toGameW_gW_proof' depends on axioms: [propext, Classical.choice, Quot.sound]
    'Bssg.MarketGame.decodeW_proof' depends on axioms: [propext, Classical.choice, Quot.sound]
    'Bssg.MarketGame.omegaDecode_proof' depends on axioms: [propext, Classical.choice, Quot.sound]
    'Bssg.MarketGame.omegaCompose_proof' depends on axioms: [propext, Classical.choice, Quot.sound]
    'Bssg.Contraction.mapsCube_proof' depends on axioms: [propext, Classical.choice, Quot.sound]
    'Bssg.Contraction.l1Contraction_proof' depends on axioms: [propext, Classical.choice, Quot.sound]
    'Bssg.Contraction.constantsLemma_proof' depends on axioms: [propext, Classical.choice, Quot.sound]
    'Bssg.Contraction.projectionLemma_proof' depends on axioms: [propext, Classical.choice, Quot.sound]
    'Bssg.Contraction.budgetAtFixedPoint_proof' depends on axioms: [propext, Classical.choice, Quot.sound]
    'Bssg.Contraction.decodingResiduals_proof' depends on axioms: [propext, Classical.choice, Quot.sound]
    'Bssg.Contraction.patternSoundness_proof' depends on axioms: [propext, Classical.choice, Quot.sound]
    'Bssg.Contraction.repairThreshold_proof' depends on axioms: [propext, Classical.choice, Quot.sound]
    'Bssg.Contraction.fixedPointUnique_proof' depends on axioms: [propext, Classical.choice, Quot.sound]
    'Bssg.Contraction.decoding_proof' depends on axioms: [propext, Classical.choice, Quot.sound]
    'Bssg.Contraction.reduction_proof' depends on axioms: [propext, Classical.choice, Quot.sound]

and checks (`example : type_of% @main := @main_proof`) that the proved theorem has exactly the statement of
the specification `main` in `BssgProofs/Statements.lean`. (`Statements.lean` contains the specifications as
`sorry` placeholders; the proofs are in `BssgProofs/Proofs/`.)

| Book | Lean theorem | file |
|---|---|---|
| Thm. C.1 (end to end) | `main_proof`, `main_coverage_proof`, `red_wellFormed_proof`, `red_sizes_proof`, `red_bits`, `red_descBits` | Proofs/Composition.lean, Final.lean, Proofs/WellFormed.lean, Proofs/Embedding.lean, Proofs/Size.lean |
| Fact C.2 | `fact0_proof`, `fact0_realize_proof` | Proofs/Embedding.lean |
| Lemma C.3 (decoder), Dohrau et al. Lemma 1 | `lemma1_proof`, `dohrau_lemma1_proof` | Proofs/Decoder.lean |
| Lemmas C.4, C.5 | `lemma2_*_proof`, `lemma3_proof` | Proofs/Lemma23.lean |
| Lemmas C.6, C.7 | `lemma4_proof`, `lemma5_proof` | Proofs/Gadget.lean |
| Lemma C.8 | `lemma6_proof` | Proofs/Gadget.lean |
| Thm. C.9 | `theorem7_proof` | Proofs/Composition.lean |
| Lemma C.10 | `lemma8_proof` | Proofs/Embedding.lean |
| the constructed game has a rational BNE (non-vacuity) | `red_bne_exists_proof` | Proofs/Existence.lean |
| size and bit-length bounds | `red_sizes_proof`, `red_bits`, `red_descBits`, `redMarket_bits` | Proofs/Embedding.lean, Proofs/Size.lean |
| the constructed game is a legal instance (priors a distribution, payoffs ordered, r ≤ |T|) | `red_wellFormed_proof` | Proofs/WellFormed.lean |
| Section 5.2, Thm. 5.19 (direct LCP, marginal coordinates, 0 < r < n) | `DirectLCP.main_proof` (via `formulationA_proof`, `formulationB_proof`, `p0_proof`, `diagPerturbation_proof`, `uniformBound_proof`, `gap_proof`) | DirectLCP/Proofs.lean, DirectLCP/Gap.lean |
| Section 5.2, marginal BNE = BNE (r = 1, defender payoffs 0/1, positive priors) | `DirectLCP.bneIffMarginal_proof`, `DirectLCP.marginalIffCoverage_proof` | DirectLCP/Proofs.lean |
| Section 5.1, Lemmas 5.1-5.5 (LCP formulation, P0, perturbation, bound, gap), Example 5.7 | `MarketLCP.formulation_proof`, `p0_proof`, `pMatrix_proof`, `uniformBound_proof`, `gap_proof`, `starSol_proof`, `negativeExample_proof` | MarketLCP/Proofs.lean |
| Section 5.1, Thm. 5.6 (for every solution of the perturbed LCP) | `MarketLCP.main_proof` | MarketLCP/Proofs.lean |
| Lemma 3.15 (row rescaling) | `MarketGame.rescaleEquiv_proof`, `rescaleEquivBack_proof`, `nuSpec_proof` | MarketGame/Proofs.lean |
| Thm. 3.16 (every BNE of the embedding decodes), Thm. 3.1(a) (market to game) | `MarketGame.decodeW_proof`, `omegaDecode_proof`, `composeBNE_proof`, `omegaCompose_proof` | MarketGame/Proofs.lean |
| Section 5.3, Lemmas 5.22(a),(c), 5.23-5.25, residuals of 5.26, Thm. 5.27 (every fixed point decodes) | `Contraction.patternSoundness_proof`, `repairThreshold_proof`, `projectionLemma_proof`, `constantsLemma_proof`, `mapsCube_proof`, `l1Contraction_proof`, `fixedPointUnique_proof`, `budgetAtFixedPoint_proof`, `decodingResiduals_proof`, `decoding_proof`, `reduction_proof` | Contraction/Proofs.lean |

Scope: BNEs are rational (an exact BNE algorithm returns rational output). Not formalized: polynomial
running time of Red and Dec. The preprocessing's reachability test `liveWithin` is a specification of
"can reach a terminal"; evaluated by its own recursion it can take time exponential in n
(T(k) = 2T(k-1) + O(1)). `Definitions.lean` therefore also defines `liveWithinFast`, which computes the
same sets stage by stage with O(k n^2) operations, proves `liveWithinFast_eq` (the two agree everywhere),
and registers the equality with `@[csimp]` (`liveWithin_eq_liveWithinFast`), so compiled code for
`preprocess`, `Red` and `Dec` uses the fast version. Lean still proves no running-time bound; that is the
book's argument (Appendix C). Proved: every number of Red I has at most 28(n+1) bits, the whole game at most
8500(n+1)^5 bits (`red_bits`, `red_descBits`, `redMarket_bits`, in Proofs/Size.lean).  Definitions to audit:
`BssgProofs/Definitions.lean`, mapped to their sources in `DEFINITIONS.md`; also `ratBits` and `BSSG.descBits`
in `Proofs/Size.lean` (used by `red_bits`, `red_descBits`; these two are proved statements, not frozen
specifications). The direct reduction to one P-matrix LCP (Section 5.2) is in `BssgProofs/DirectLCP/`, with its
own definitions map `DirectLCP/DEFINITIONS-directlcp.md`.

Section 5.2 scope: Lean proves that for every well-formed game with 0 < r < n, M + δI is a P-matrix and
every LCP solution yields, through the support-pattern LP, an exact BNE in marginal coordinates. Not
formalized there: existence of the P-LCP solution (classical), the cases r ∈ {0, n}, the decoder from
marginals to a mixed strategy over r-subsets, the link to the base BNE definition for r > 1, the size
of (q, M), polynomial running time, and the UEOPL step (P-LCP is in UEOPL, a cited result).

Sections 5.1, 5.3 and Chapter 3 (market to game) scope: `BssgProofs/MarketLCP/`, `MarketGame/` and `Contraction/`, each with its own `DEFINITIONS-*.md`, audited against the book in `audits/AUDIT-new-sets.md`. Not formalized there: existence of a solution of the perturbed LCP and of a rational fixed point of F (classical; the statements are vacuous without them), legality and prior bounds of the game Γ_ω and the lift for Γ_ω, polynomial running time and bit sizes, the UEOPL step through FGMS, the best-response condition for zero-prior types in the contraction's output, and the link from marginal coordinates to the base BNE definition for r > 1.
