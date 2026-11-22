import Mathlib
import BssgProofs.Statements
import BssgProofs.Proofs.Composition

/-!
# `red_wellFormed`: `Red I` is a legal one-resource BSSG with 0/1 defender payoffs and positive priors
-/

namespace Bssg

open Finset

set_option linter.unusedSectionVars false

namespace WF

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

/-- For a well-formed market, every type weight of Γ is positive. -/
theorem gWeight_pos (Mk : Market I J) (hwf : Mk.WellFormed) (θ : MType I J) :
    0 < Mk.gWeight θ := by
  obtain ⟨hμ, hc, _⟩ := hwf
  have hF0 : (0 : ℚ) ≤ univ.fold max 0 Mk.cap := (le_fold_max _).mpr (Or.inl le_rfl)
  have hFc : ∀ j, Mk.cap j ≤ univ.fold max 0 Mk.cap :=
    fun j => (le_fold_max _).mpr (Or.inr ⟨j, mem_univ _, le_rfl⟩)
  have hsumμ : 0 ≤ ∑ i, Mk.mass i := sum_nonneg fun i _ => (hμ i).le
  have hWc : ∀ j, Mk.cap j < Mk.gW := fun j => by unfold Market.gW; linarith [hFc j]
  have hWpos : 0 < Mk.gW := by unfold Market.gW; linarith
  rcases θ with i | j | ⟨⟩
  · simp only [Market.gWeight]; linarith [hμ i]
  · simp only [Market.gWeight]; linarith [hWc j]
  · exact hWpos

/-- Slopes of Γ are nonnegative for a well-formed market. -/
theorem gPay_slope_nonneg (Mk : Market I J) (hwf : Mk.WellFormed) (θ : MType I J)
    (k : MTarget I J) : 0 ≤ (Mk.gPay θ k).2 := by
  obtain ⟨_, _, hb⟩ := hwf
  rcases θ with i | j | ⟨⟩ <;> rcases k with j' | i' | ⟨⟩ | ⟨⟩ <;>
    simp only [Market.gPay] <;> (try split_ifs) <;> simp
  exact (hb _ ‹_›).le

theorem toGame_props (Mk : Market I J) (hwf : Mk.WellFormed) :
    Mk.toGame.WellFormed ∧ Mk.toGame.r = 1 ∧
      (∀ t, Mk.toGame.ud0 t = 0 ∧ Mk.toGame.ud1 t = 1) ∧ ∀ θ, 0 < Mk.toGame.prior θ := by
  have hw := gWeight_pos Mk hwf
  have hZ : 0 < ∑ θ, Mk.gWeight θ :=
    sum_pos (fun θ _ => hw θ) ⟨.inr (.inr ()), mem_univ _⟩
  have hprior : ∀ θ, 0 < Mk.toGame.prior θ := fun θ => by
    simp only [Market.toGame]; exact div_pos (hw θ) hZ
  refine ⟨⟨?_, fun θ => (hprior θ).le, ?_, ?_, ?_⟩, rfl, fun _ => ⟨rfl, rfl⟩, hprior⟩
  · show 1 ≤ Fintype.card (MTarget I J)
    exact Fintype.card_pos
  · simp only [Market.toGame, ← sum_div]; exact div_self hZ.ne'
  · intro t; simp only [Market.toGame]; norm_num
  · intro θ t; simp only [Market.toGame]; linarith [gPay_slope_nonneg Mk hwf θ t]

end WF

/-- `red_wellFormed`, restated verbatim from `Statements.lean`. -/
theorem red_wellFormed_proof {n : ℕ} (I : ArrivalInstance n) :
    (Red I).WellFormed ∧ (Red I).r = 1 ∧ (∀ t, (Red I).ud0 t = 0 ∧ (Red I).ud1 t = 1) ∧
      ∀ θ, 0 < (Red I).prior θ :=
  WF.toGame_props _ (redMarket_wellFormed_proof I.preprocess).1

end Bssg

#print axioms Bssg.red_wellFormed_proof
