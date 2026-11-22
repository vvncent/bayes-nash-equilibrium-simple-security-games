import BssgProofs.Proofs.WellFormed
import BssgProofs.Proofs.Composition
import BssgProofs.DirectLCP.Gap
import BssgProofs.Proofs.Embedding
import BssgProofs.Proofs.Existence
import BssgProofs.Proofs.Size
import BssgProofs.MarketLCP.Proofs
import BssgProofs.MarketGame.Proofs
import BssgProofs.Contraction.Proofs
/-!
# Final check

`main_proof` is the end-to-end ARRIVAL-hardness theorem: for every ARRIVAL instance and every
(rational) Bayes–Nash equilibrium of the constructed one-resource game `Red I`, the decoder
`Dec` returns the run's answer.  The `example` below checks that its statement is *exactly*
the specification `main` in `Statements.lean` (which itself is only a placeholder with `sorry`);
`#print axioms` must list only Lean's three standard axioms.
-/
namespace Bssg
example : type_of% @main := @main_proof
example : type_of% @main_coverage := @main_coverage_proof
example : type_of% @red_bne_exists := @red_bne_exists_proof
example : type_of% @red_sizes := @red_sizes_proof
end Bssg
#print axioms Bssg.main_proof
#print axioms Bssg.main_coverage_proof
#print axioms Bssg.red_bne_exists_proof
namespace Bssg
example : type_of% @red_wellFormed := @red_wellFormed_proof
end Bssg
#print axioms Bssg.red_wellFormed_proof
#print axioms Bssg.redMarket_bits
#print axioms Bssg.red_bits
#print axioms Bssg.red_descBits_le_product
#print axioms Bssg.red_descBits
#print axioms Bssg.red_sizes_proof
/-! Direct reduction to one P-matrix LCP (Section 5.2): `main_proof` proves the specification
`MainTheorem` of `DirectLCP/Statements.lean`; the bridges connect marginal-coordinate BNE to the base
definitions for one resource, defender payoffs 0/1 and positive priors. -/
section
open Bssg.DirectLCP
example (T Θ : Type) [Fintype T] [DecidableEq T] [Fintype Θ] [DecidableEq Θ] [Nonempty T] :
    MainTheorem T Θ := main_proof T Θ
end
#print axioms Bssg.DirectLCP.main_proof
#print axioms Bssg.DirectLCP.bneIffMarginal_proof
#print axioms Bssg.DirectLCP.marginalIffCoverage_proof

/-! The market reduces to one P-matrix LCP (Section 5.1): `MarketLCP.main_proof` proves `MainTheorem`
of `MarketLCP/Statements.lean` for any solution of the perturbed LCP (existence of a solution is the
classical fact and is not formalized). -/
section
example (I J : Type) [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] :
    Bssg.MarketLCP.MainTheorem I J := Bssg.MarketLCP.main_proof I J
example (I J : Type) [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] :
    Bssg.MarketLCP.Formulation I J := Bssg.MarketLCP.formulation_proof I J
example : Bssg.MarketLCP.NegativeExample := Bssg.MarketLCP.negativeExample_proof
end
#print axioms Bssg.MarketLCP.formulation_proof
#print axioms Bssg.MarketLCP.formulationEqSol_proof
#print axioms Bssg.MarketLCP.formulationSolEq_proof
#print axioms Bssg.MarketLCP.slackTable_proof
#print axioms Bssg.MarketLCP.p0_proof
#print axioms Bssg.MarketLCP.pMatrix_proof
#print axioms Bssg.MarketLCP.uniformBound_proof
#print axioms Bssg.MarketLCP.gap_proof
#print axioms Bssg.MarketLCP.starSol_proof
#print axioms Bssg.MarketLCP.main_proof
#print axioms Bssg.MarketLCP.negativeExample_proof

/-! Market to game (Chapter 3): rescaling, the game of the market-to-game table, decoding, and the composed
reduction `omegaCompose_proof`. BNE existence for the constructed game and its legality are not
formalized. -/
section
example (I J : Type) [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] :
    Bssg.MarketGame.OmegaCompose I J := Bssg.MarketGame.omegaCompose_proof
example (I J : Type) [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] :
    Bssg.MarketGame.ComposeBNE I J := Bssg.MarketGame.composeBNE_proof
end
#print axioms Bssg.MarketGame.rescaleEquiv_proof
#print axioms Bssg.MarketGame.rescaleEquivBack_proof
#print axioms Bssg.MarketGame.nuSpec_proof
#print axioms Bssg.MarketGame.rescaledWF_proof
#print axioms Bssg.MarketGame.composeCoverage_proof
#print axioms Bssg.MarketGame.composeBNE_proof
#print axioms Bssg.MarketGame.composeLift_proof
#print axioms Bssg.MarketGame.toGameW_gW_proof
#print axioms Bssg.MarketGame.decodeW_proof
#print axioms Bssg.MarketGame.omegaDecode_proof
#print axioms Bssg.MarketGame.omegaCompose_proof

/-! One l1 contraction for the game (Section 5.3): every fixed point of `F` decodes to an exact
marginal BNE (`reduction_proof`); existence of a rational fixed point is not formalized. -/
section
example (T Θ : Type) [Fintype T] [DecidableEq T] [Fintype Θ] [DecidableEq Θ] [Nonempty T] :
    Bssg.Contraction.Reduction T Θ := Bssg.Contraction.reduction_proof T Θ
end
#print axioms Bssg.Contraction.mapsCube_proof
#print axioms Bssg.Contraction.l1Contraction_proof
#print axioms Bssg.Contraction.constantsLemma_proof
#print axioms Bssg.Contraction.projectionLemma_proof
#print axioms Bssg.Contraction.budgetAtFixedPoint_proof
#print axioms Bssg.Contraction.decodingResiduals_proof
#print axioms Bssg.Contraction.patternSoundness_proof
#print axioms Bssg.Contraction.repairThreshold_proof
#print axioms Bssg.Contraction.fixedPointUnique_proof
#print axioms Bssg.Contraction.decoding_proof
#print axioms Bssg.Contraction.reduction_proof
