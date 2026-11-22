import Mathlib
import BssgProofs.Statements
import BssgProofs.Proofs.Decoder
import BssgProofs.Proofs.Lemma23
import BssgProofs.Proofs.Embedding

/-!
# Existence of a rational BNE of `Red I` (constructive)

Plan (no Nash theorem):
1. `Exist.exists_nat_fp`: the preprocessed instance has an integral fixed point `x` with
   `x_v ≤ 2^{n+1} - 1` (Kleene iteration of the integral switch map from `0`, bounded by the
   path argument of Theorem 7, Step 3).
2. `Exist.gadget potentials`: for every integral value the explicit optimal flow `L23.optFlow` of
   the counting network `G_m` admits explicit node potentials (complementary slackness), built
   level by level from the increment list `countD`.
3. `Exist.market_eq`: these flows, potentials and the prices `P_{p_v} = π_s(x_v)/λ` form an
   explicit equilibrium of the §5 market.
4. `Exist.lift_bne`: every equilibrium of a well-formed market with slopes `≥ 1` lifts to a
   coverage-form BNE of the §6 game (`ξ_j = P_j/S`, `ξ_{g_i} = (A - v_i)/S`, `ξ_o = 0`,
   control coverage the rest).
5. Fact 0 (`fact0_realize_proof`) gives a general BNE.
-/

namespace Bssg

open Finset

set_option linter.unusedSectionVars false

namespace Exist

/-! ## 1. Lift: market equilibrium → coverage-form BNE of Γ -/

theorem sum_filter_fst {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (S : Finset (α × β)) (f : α × β → ℚ) (a : α) :
    ∑ e ∈ S.filter (fun e => e.1 = a), f e = ∑ b, if (a, b) ∈ S then f (a, b) else 0 := by
  rw [← Finset.sum_ite_mem_eq, Fintype.sum_prod_type]
  have : ∀ x : α, ∀ y : β, (if (x, y) ∈ S.filter (fun e => e.1 = a) then f (x, y) else 0) =
      if x = a then (if (x, y) ∈ S then f (x, y) else 0) else 0 := by
    intro x y; by_cases hx : x = a <;> simp [hx]
  simp only [this]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]

theorem sum_filter_snd {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (S : Finset (α × β)) (f : α × β → ℚ) (b : β) :
    ∑ e ∈ S.filter (fun e => e.2 = b), f e = ∑ a, if (a, b) ∈ S then f (a, b) else 0 := by
  rw [← Finset.sum_ite_mem_eq, Fintype.sum_prod_type]
  have : ∀ x : α, ∀ y : β, (if (x, y) ∈ S.filter (fun e => e.2 = b) then f (x, y) else 0) =
      if y = b then (if (x, y) ∈ S then f (x, y) else 0) else 0 := by
    intro x y; by_cases hy : y = b <;> simp [hy]
  simp only [this]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]

section Lift

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

/-- Coverage of the lifted equilibrium. -/
def liftξ (Mk : Market I J) (P : J → ℚ) (v : I → ℚ) : MTarget I J → ℚ
  | .inl j => P j / Mk.gS
  | .inr (.inl i) => (Mk.gA - v i) / Mk.gS
  | .inr (.inr (.inl ())) => 0
  | .inr (.inr (.inr ())) => 1 - (∑ j, P j / Mk.gS) - ∑ i, (Mk.gA - v i) / Mk.gS

/-- Type strategies of the lifted equilibrium. -/
def liftσ (Mk : Market I J) (f : I × J → ℚ) : MType I J → MTarget I J → ℚ
  | .inl i, .inl j => (if (i, j) ∈ Mk.E then f (i, j) else 0) / (Mk.gW + Mk.mass i)
  | .inl i, .inr (.inl i') => if i' = i then Mk.gW / (Mk.gW + Mk.mass i) else 0
  | .inl i, .inr (.inr (.inl ())) => (Mk.mass i - Mk.rowSum f i) / (Mk.gW + Mk.mass i)
  | .inl _, .inr (.inr (.inr ())) => 0
  | .inr (.inl j), .inl j' => if j' = j then 1 else 0
  | .inr (.inl _), .inr _ => 0
  | .inr (.inr ()), .inr (.inr (.inr ())) => 1
  | .inr (.inr ()), .inl _ => 0
  | .inr (.inr ()), .inr (.inl _) => 0
  | .inr (.inr ()), .inr (.inr (.inl ())) => 0

theorem sum_unit (g : Unit → ℚ) : ∑ u, g u = g () := Fintype.sum_unique g

theorem sum_mtype (F : MType I J → ℚ) :
    ∑ θ, F θ = (∑ i, F (.inl i)) + (∑ j, F (.inr (.inl j))) + F (.inr (.inr ())) := by
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type, sum_unit]; ring

theorem sum_mtarget (F : MTarget I J → ℚ) :
    ∑ k, F k = (∑ j, F (.inl j)) + (∑ i, F (.inr (.inl i))) + F (.inr (.inr (.inl ()))) +
      F (.inr (.inr (.inr ()))) := by
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_sum_type, sum_unit, sum_unit]; ring

set_option maxHeartbeats 2000000 in
theorem lift_bne (Mk : Market I J) (hwf : Mk.WellFormed) (hb : ∀ e ∈ Mk.E, 1 ≤ Mk.b e)
    (P : J → ℚ) (v : I → ℚ) (f : I × J → ℚ) (heq : Mk.IsEquilibrium P v f) :
    Mk.toGame.IsCoverageBNE (liftξ Mk P v) (liftσ Mk f) := by
  obtain ⟨hμ, hc, hbpos⟩ := hwf
  have hF0 : (0 : ℚ) ≤ univ.fold max 0 Mk.cap := (le_fold_max _).mpr (Or.inl le_rfl)
  have hFc : ∀ j, Mk.cap j ≤ univ.fold max 0 Mk.cap :=
    fun j => (le_fold_max _).mpr (Or.inr ⟨j, mem_univ _, le_rfl⟩)
  have hsumμ : 0 ≤ ∑ i, Mk.mass i := sum_nonneg fun i _ => (hμ i).le
  have hWμ : ∑ i, Mk.mass i < Mk.gW := by unfold Market.gW; linarith
  have hWc : ∀ j, Mk.cap j < Mk.gW := fun j => by unfold Market.gW; linarith [hFc j]
  have hWpos : 0 < Mk.gW := by linarith
  have hWμi : ∀ i, 0 < Mk.gW + Mk.mass i := fun i => by linarith [hμ i]
  have hAa : ∀ e ∈ Mk.E, Mk.a e < Mk.gA := fun e he => by
    have : Mk.a e ≤ Mk.E.fold max 0 Mk.a := (le_fold_max _).mpr (Or.inr ⟨e, he, le_rfl⟩)
    unfold Market.gA; linarith
  have hA0 : (0 : ℚ) ≤ Mk.E.fold max 0 Mk.a := (le_fold_max _).mpr (Or.inl le_rfl)
  have hA1 : 1 ≤ Mk.gA := by unfold Market.gA; linarith
  have hcard : (0 : ℚ) ≤ (Fintype.card I : ℚ) + Fintype.card J := by positivity
  have hSA : ((Fintype.card I : ℚ) + Fintype.card J) * Mk.gA < Mk.gS := by
    unfold Market.gS; linarith
  have hS0 : 0 < Mk.gS := by nlinarith
  -- bounds on utilities and prices
  have hv_lt : ∀ i, v i < Mk.gA := by
    intro i
    by_cases hvi : 0 < v i
    · have hrow := heq.cond_c_eq i hvi
      unfold Market.rowSum at hrow
      obtain ⟨e, he, hfe⟩ : ∃ e ∈ Mk.E.filter (fun e => e.1 = i), 0 < f e := by
        by_contra hne
        push Not at hne
        have := Finset.sum_nonpos hne
        linarith [hμ i]
      rw [Finset.mem_filter] at he
      have h1 := heq.cond_b e he.1 hfe
      have h2 := hAa e he.1
      have h3 := hbpos e he.1
      have h4 := heq.P_nonneg e.2
      rw [he.2] at h1
      nlinarith
    · linarith [heq.v_nonneg i]
  have hP_lt : ∀ j, P j < Mk.gA := by
    intro j
    by_cases hPj : 0 < P j
    · have hcol := heq.cond_d_eq j hPj
      unfold Market.colSum at hcol
      obtain ⟨e, he, hfe⟩ : ∃ e ∈ Mk.E.filter (fun e => e.2 = j), 0 < f e := by
        by_contra hne
        push Not at hne
        have := Finset.sum_nonpos hne
        linarith [hc j]
      rw [Finset.mem_filter] at he
      have h1 := heq.cond_b e he.1 hfe
      have h2 := hAa e he.1
      have h3 := hb e he.1
      have h5 := heq.v_nonneg e.1
      rw [he.2] at h1
      nlinarith
    · linarith
  have hsum : (∑ j, P j / Mk.gS) + (∑ i, (Mk.gA - v i) / Mk.gS) < 1 := by
    rw [← Finset.sum_div, ← Finset.sum_div, ← add_div, div_lt_one hS0]
    have e1 : (∑ j, P j) ≤ ∑ _j : J, Mk.gA := Finset.sum_le_sum fun j _ => (hP_lt j).le
    have e2 : (∑ i, (Mk.gA - v i)) ≤ ∑ _i : I, Mk.gA :=
      Finset.sum_le_sum fun i _ => by linarith [heq.v_nonneg i]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at e1 e2
    nlinarith
  have hsum0 : 0 ≤ (∑ j, P j / Mk.gS) + (∑ i, (Mk.gA - v i) / Mk.gS) := by
    have := Finset.sum_nonneg fun j (_ : j ∈ univ) => div_nonneg (heq.P_nonneg j) hS0.le
    have := Finset.sum_nonneg fun i (_ : i ∈ univ) =>
      div_nonneg (show 0 ≤ Mk.gA - v i by linarith [hv_lt i]) hS0.le
    linarith
  have hξ0 : ∀ k, 0 ≤ liftξ Mk P v k := by
    rintro (j | i | ⟨⟩ | ⟨⟩)
    · exact div_nonneg (heq.P_nonneg j) hS0.le
    · exact div_nonneg (by linarith [hv_lt i]) hS0.le
    · exact le_rfl
    · show 0 ≤ 1 - _ - _; linarith
  have hξh : liftξ Mk P v (.inr (.inr (.inr ()))) ≤ 1 := by
    show 1 - _ - _ ≤ 1; linarith
  have hPS : ∀ j, P j / Mk.gS < 1 := fun j => by
    have hJ : (1 : ℚ) ≤ Fintype.card J := by
      exact_mod_cast Fintype.card_pos_iff.2 ⟨j⟩
    have hI : (0 : ℚ) ≤ Fintype.card I := by positivity
    rw [div_lt_one hS0]; nlinarith [hP_lt j]
  have hξj : ∀ j, 0 ≤ P j / Mk.gS := fun j => div_nonneg (heq.P_nonneg j) hS0.le
  have hξg : ∀ i, 0 ≤ (Mk.gA - v i) / Mk.gS := fun i =>
    div_nonneg (by linarith [hv_lt i]) hS0.le
  -- rows and columns as sums over all goods/buyers
  have hrow : ∀ i, Mk.rowSum f i = ∑ j, if (i, j) ∈ Mk.E then f (i, j) else 0 :=
    fun i => sum_filter_fst _ _ _
  have hcol : ∀ j, Mk.colSum f j = ∑ i, if (i, j) ∈ Mk.E then f (i, j) else 0 :=
    fun j => sum_filter_snd _ _ _
  have hrow0 : ∀ i, 0 ≤ Mk.rowSum f i := fun i =>
    Finset.sum_nonneg fun e he => heq.f_nonneg e (Finset.mem_filter.1 he).1
  have hU : ∀ θ k, Mk.toGame.U θ k (liftξ Mk P v) =
      (Mk.gPay θ k).1 - (Mk.gPay θ k).2 * liftξ Mk P v k := by
    intro θ k; simp only [BSSG.U, Market.toGame]; ring
  have hσ0 : ∀ θ k, 0 ≤ liftσ Mk f θ k := by
    rintro (i | j | ⟨⟩) (j' | i' | ⟨⟩ | ⟨⟩) <;> simp only [liftσ]
    · exact div_nonneg (by split_ifs with h; exacts [heq.f_nonneg _ h, le_rfl]) (hWμi i).le
    · split_ifs; exacts [div_nonneg hWpos.le (hWμi i).le, le_rfl]
    · exact div_nonneg (by linarith [heq.cond_c_le i]) (hWμi i).le
    · exact le_rfl
    all_goals first | exact le_rfl | exact zero_le_one | (split_ifs <;> norm_num)
  refine ⟨⟨hξ0, ?_⟩, fun θ => ⟨hσ0 θ, ?_⟩, ?_, ?_⟩
  · -- coverage sums to one
    rw [sum_mtarget]; simp only [liftξ]; ring
  · -- each type's strategy sums to one
    rw [sum_mtarget]
    rcases θ with i | j | ⟨⟩
    · simp only [liftσ]
      rw [Finset.sum_ite_eq' univ i, if_pos (mem_univ _), ← Finset.sum_div, ← hrow]
      field_simp [(hWμi i).ne']
      ring
    · simp only [liftσ]
      rw [Finset.sum_ite_eq' univ j, if_pos (mem_univ _)]; simp
    · simp only [liftσ]; simp
  · -- best responses
    intro θ k hk j
    rcases θ with i | jd | ⟨⟩
    · have hle : ∀ k, Mk.toGame.U (.inl i) k (liftξ Mk P v) ≤ v i / Mk.gS := by
        rintro (j' | i' | ⟨⟩ | ⟨⟩) <;> rw [hU] <;> simp only [Market.gPay]
        · split_ifs with hE
          · simp only [liftξ]
            have := heq.cond_a _ hE
            rw [show Mk.a (i, j') / Mk.gS - Mk.b (i, j') * (P j' / Mk.gS) =
              (Mk.a (i, j') - Mk.b (i, j') * P j') / Mk.gS by ring]
            exact div_le_div_of_nonneg_right this hS0.le
          · have := hξ0 (.inl j'); have := div_nonneg (heq.v_nonneg i) hS0.le
            simp only at *; linarith
        · split_ifs with hi
          · subst hi; simp only [liftξ]; apply le_of_eq; field_simp; ring
          · have := hξ0 (.inr (.inl i')); have := div_nonneg (heq.v_nonneg i) hS0.le
            simp only at *; linarith
        · simp only [liftξ]; have := div_nonneg (heq.v_nonneg i) hS0.le; linarith
        · simp only [liftξ]; have := div_nonneg (heq.v_nonneg i) hS0.le; linarith
      have heqk : Mk.toGame.U (.inl i) k (liftξ Mk P v) = v i / Mk.gS := by
        rcases k with j' | i' | ⟨⟩ | ⟨⟩ <;> rw [hU] <;> simp only [Market.gPay]
        · simp only [liftσ] at hk
          split_ifs at hk ⊢ with hE
          · have hf : 0 < f (i, j') := by
              have := hWμi i
              by_contra hh; push Not at hh
              have : f (i, j') / (Mk.gW + Mk.mass i) ≤ 0 := div_nonpos_of_nonpos_of_nonneg hh this.le
              linarith
            have := heq.cond_b _ hE hf
            simp only [liftξ]; rw [this]; ring
          · simp at hk
        · simp only [liftσ] at hk
          split_ifs at hk ⊢ with hi
          · subst hi; simp only [liftξ]; field_simp; ring
          · simp at hk
        · simp only [liftσ] at hk
          have hlt : Mk.rowSum f i < Mk.mass i := by
            by_contra hh; push Not at hh
            have : (Mk.mass i - Mk.rowSum f i) / (Mk.gW + Mk.mass i) ≤ 0 :=
              div_nonpos_of_nonpos_of_nonneg (by linarith) (hWμi i).le
            linarith
          have hv0 : v i = 0 := by
            by_contra hh
            have := heq.cond_c_eq i (lt_of_le_of_ne (heq.v_nonneg i) (Ne.symm hh))
            linarith
          simp only [liftξ, hv0]; ring
        · simp [liftσ] at hk
      rw [heqk]; exact hle j
    · -- dedicated type
      have hk' : k = .inl jd := by
        rcases k with j' | i' | ⟨⟩ | ⟨⟩ <;> simp only [liftσ] at hk
        · split_ifs at hk with h
          · rw [h]
          · simp at hk
        all_goals simp at hk
      subst hk'
      rw [hU, hU]
      have hp := hPS jd
      rcases j with j' | i' | ⟨⟩ | ⟨⟩
      · simp only [Market.gPay, liftξ]
        split_ifs with h
        · subst h; linarith
        · linarith [hξj j']
      · simp only [Market.gPay, liftξ, if_true]; linarith [hξg i']
      · simp only [Market.gPay, liftξ, if_true]; linarith
      · simp only [Market.gPay, liftξ, if_true]; linarith
    · -- control type
      have hk' : k = .inr (.inr (.inr ())) := by
        rcases k with j' | i' | ⟨⟩ | ⟨⟩ <;> simp [liftσ] at hk ⊢
      subst hk'
      rw [hU, hU]
      rcases j with j' | i' | ⟨⟩ | ⟨⟩ <;> simp only [Market.gPay, liftξ]
      · linarith [hξj j']
      · linarith [hξg i']
      · linarith
      · linarith
  · -- coverage only on max-load targets
    set T := ∑ θ', Mk.gWeight θ' with hT
    have hwpos : ∀ θ, 0 < Mk.gWeight θ := by
      rintro (i | j | ⟨⟩)
      · exact hWμi i
      · show 0 < Mk.gW - Mk.cap j; linarith [hWc j]
      · exact hWpos
    have hTpos : 0 < T := Finset.sum_pos (fun θ _ => hwpos θ) univ_nonempty
    have hload : ∀ k, Mk.toGame.load (liftσ Mk f) k =
        (∑ θ, Mk.gWeight θ * liftσ Mk f θ k) / T := by
      intro k
      simp only [BSSG.load, Market.toGame]
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun θ _ => ?_
      rw [← hT]; ring
    have hwl_le : ∀ k, (∑ θ, Mk.gWeight θ * liftσ Mk f θ k) ≤ Mk.gW := by
      rintro (j | i | ⟨⟩ | ⟨⟩) <;> rw [sum_mtype] <;> simp only [liftσ, Market.gWeight]
      · have hdiv : ∀ i, (Mk.gW + Mk.mass i) *
            ((if (i, j) ∈ Mk.E then f (i, j) else 0) / (Mk.gW + Mk.mass i)) =
            if (i, j) ∈ Mk.E then f (i, j) else 0 := fun i => by
          field_simp [(hWμi i).ne']
        simp only [hdiv, ← hcol, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, mem_univ,
          if_true]
        linarith [heq.cond_d_le j]
      · simp only [mul_ite, mul_zero, Finset.sum_ite_eq, mem_univ, if_true]
        field_simp [(hWμi i).ne']; simp
      · have hdiv : ∀ i, (Mk.gW + Mk.mass i) *
            ((Mk.mass i - Mk.rowSum f i) / (Mk.gW + Mk.mass i)) = Mk.mass i - Mk.rowSum f i :=
          fun i => by field_simp [(hWμi i).ne']
        simp only [hdiv, mul_zero, Finset.sum_const_zero, add_zero]
        have : (∑ i, (Mk.mass i - Mk.rowSum f i)) ≤ ∑ i, Mk.mass i :=
          Finset.sum_le_sum fun i _ => by linarith [hrow0 i]
        linarith
      · simp
    have hwl_eq : ∀ k, 0 < liftξ Mk P v k → (∑ θ, Mk.gWeight θ * liftσ Mk f θ k) = Mk.gW := by
      rintro (j | i | ⟨⟩ | ⟨⟩) hk <;> rw [sum_mtype] <;> simp only [liftσ, Market.gWeight]
      · have hPj : 0 < P j := by
          simp only [liftξ] at hk; exact (div_pos_iff_of_pos_right hS0).1 hk
        have hdiv : ∀ i, (Mk.gW + Mk.mass i) *
            ((if (i, j) ∈ Mk.E then f (i, j) else 0) / (Mk.gW + Mk.mass i)) =
            if (i, j) ∈ Mk.E then f (i, j) else 0 := fun i => by
          field_simp [(hWμi i).ne']
        simp only [hdiv, ← hcol, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, mem_univ,
          if_true]
        rw [heq.cond_d_eq j hPj]; ring
      · simp only [mul_ite, mul_zero, Finset.sum_ite_eq, mem_univ, if_true]
        field_simp [(hWμi i).ne']; simp
      · simp [liftξ] at hk
      · simp
    intro k hk j
    rw [hload, hload, hwl_eq k hk]
    exact div_le_div_of_nonneg_right (hwl_le j) hTpos.le

end Lift

/-! ## 2. An integral fixed point with the bound `x_v < 2^{n+1}` -/

section FP

variable {n : ℕ} (I : ArrivalInstance n)

open Decoder in
/-- The integral switch map. -/
def PhiN (x : Fin n → ℕ) (v : Fin n) : ℕ :=
  (if v = I.origin then 1 else 0) +
    ∑ u, ∑ i : Bool, if I.succ u i = .inl v then hN i (x u) else 0

open Decoder in
/-- Integral terminal inflow. -/
def yN (x : Fin n → ℕ) (t : Terminal) : ℕ :=
  ∑ u, ∑ i : Bool, if I.succ u i = .inr t then hN i (x u) else 0

/-- Kleene iterates from `0`. -/
def iterN (t : ℕ) : Fin n → ℕ := (PhiN I)^[t] (fun _ => 0)

theorem iterN_succ (t : ℕ) : iterN I (t + 1) = PhiN I (iterN I t) := by
  unfold iterN; rw [Function.iterate_succ_apply']

theorem hN_mono (i : Bool) {a b : ℕ} (h : a ≤ b) : Decoder.hN i a ≤ Decoder.hN i b := by
  unfold Decoder.hN; split <;> omega

theorem hN_sum (m : ℕ) : Decoder.hN false m + Decoder.hN true m = m := by
  unfold Decoder.hN; simp; omega

theorem hN_ge (i : Bool) (m : ℕ) : m ≤ 2 * Decoder.hN i m + 1 := by
  unfold Decoder.hN; split <;> omega

theorem PhiN_mono {x x' : Fin n → ℕ} (h : ∀ v, x v ≤ x' v) (v : Fin n) :
    PhiN I x v ≤ PhiN I x' v := by
  unfold PhiN
  apply Nat.add_le_add_left
  apply Finset.sum_le_sum; intro u _
  apply Finset.sum_le_sum; intro i _
  split_ifs
  · exact hN_mono i (h u)
  · exact le_rfl

theorem iterN_chain (t : ℕ) (v : Fin n) : iterN I t v ≤ iterN I (t + 1) v := by
  induction t generalizing v with
  | zero => exact Nat.zero_le _
  | succ t ih =>
    rw [iterN_succ I (t + 1), iterN_succ I t]
    have := PhiN_mono I ih v
    rwa [iterN_succ I t] at this

theorem sum_PhiN (x : Fin n → ℕ) :
    (∑ v, PhiN I x v) + (yN I x .yes + yN I x .no) = 1 + ∑ u, x u := by
  have key := Decoder.sum_heads I (fun u i => Decoder.hN i (x u))
  have hs : ∀ u, ∑ i : Bool, Decoder.hN i (x u) = x u := fun u => by
    rw [Fintype.sum_bool, add_comm, hN_sum]
  simp only [hs] at key
  unfold PhiN yN
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq' univ I.origin (fun _ => 1), if_pos (mem_univ _),
    ← key]
  ring

theorem single_le (x : Fin n → ℕ) (w : Node n) (v : Fin n) (i : Bool) (h : I.succ v i = w) :
    Decoder.hN i (x v) ≤ ∑ u, ∑ i' : Bool, if I.succ u i' = w then Decoder.hN i' (x u) else 0 := by
  refine le_trans ?_ (Finset.single_le_sum (f := fun u => ∑ i' : Bool,
    if I.succ u i' = w then Decoder.hN i' (x u) else 0) (fun u _ => Nat.zero_le _) (mem_univ v))
  refine le_trans ?_ (Finset.single_le_sum (f := fun i' : Bool =>
    if I.succ v i' = w then Decoder.hN i' (x v) else 0) (fun u _ => Nat.zero_le _) (mem_univ i))
  simp [h]

theorem yN_iter_le (t : ℕ) : yN I (iterN I t) .yes + yN I (iterN I t) .no ≤ 1 := by
  have h1 := sum_PhiN I (iterN I t)
  have h2 : (∑ u, iterN I t u) ≤ ∑ v, PhiN I (iterN I t) v := by
    rw [← iterN_succ]; exact Finset.sum_le_sum fun v _ => iterN_chain I t v
  omega

theorem iterN_bound (l : ℕ) : ∀ v, I.liveWithin l v = true → ∀ t, iterN I t v + 1 ≤ 2 ^ (l + 1) := by
  induction l with
  | zero => intro v hv; simp [ArrivalInstance.liveWithin] at hv
  | succ l ih =>
    intro v hv t
    rw [Decoder.liveWithin_succ] at hv
    have h4 : 4 ≤ 2 ^ (l + 1 + 1) := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (l + 1 + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    obtain ⟨i, hi⟩ : ∃ i, Decoder.gl I l (I.succ v i) = true := by
      rcases Bool.or_eq_true_iff.1 hv with h | h
      · exact ⟨false, h⟩
      · exact ⟨true, h⟩
    have hge := hN_ge i (iterN I t v)
    rcases hs : I.succ v i with w | tt
    · rw [hs] at hi
      have hw : I.liveWithin l w = true := hi
      have h1 := single_le I (iterN I t) (.inl w) v i hs
      have h2 : PhiN I (iterN I t) w = iterN I (t + 1) w := by rw [iterN_succ]
      have h3 := ih w hw (t + 1)
      have h5 : (∑ u, ∑ i' : Bool, if I.succ u i' = .inl w then Decoder.hN i' (iterN I t u) else 0)
          ≤ PhiN I (iterN I t) w := by unfold PhiN; omega
      rw [pow_succ]; rw [pow_succ] at h3
      omega
    · have h1 := single_le I (iterN I t) (.inr tt) v i hs
      have h2 := yN_iter_le I t
      have h3 : yN I (iterN I t) tt ≤ 1 := by cases tt <;> unfold yN at * <;> omega
      unfold yN at h3
      omega

theorem exists_nat_fp (hI : I.Preprocessed) :
    ∃ x : Fin n → ℕ, (∀ v, PhiN I x v = x v) ∧ ∀ v, x v + 1 ≤ 2 ^ (n + 1) := by
  have hb : ∀ t v, iterN I t v + 1 ≤ 2 ^ (n + 1) := fun t v => iterN_bound I n v (hI v) t
  by_cases H : ∃ t, PhiN I (iterN I t) = iterN I t
  · obtain ⟨t, ht⟩ := H
    exact ⟨iterN I t, fun v => congrFun ht v, hb t⟩
  push Not at H
  have hgrow : ∀ t, t ≤ ∑ v, iterN I t v := by
    intro t
    induction t with
    | zero => exact Nat.zero_le _
    | succ t ih =>
      have hlt : ∑ v, iterN I t v < ∑ v, iterN I (t + 1) v := by
        obtain ⟨v, hv⟩ : ∃ v, iterN I (t + 1) v ≠ iterN I t v := by
          by_contra hh; push Not at hh
          exact H t (by rw [← iterN_succ]; funext v; exact hh v)
        exact Finset.sum_lt_sum (fun v _ => iterN_chain I t v)
          ⟨v, mem_univ _, lt_of_le_of_ne (iterN_chain I t v) (Ne.symm hv)⟩
      omega
  have hbound : ∀ t, ∑ v, iterN I t v ≤ n * 2 ^ (n + 1) := by
    intro t
    calc ∑ v, iterN I t v ≤ ∑ _v : Fin n, 2 ^ (n + 1) :=
          Finset.sum_le_sum fun v _ => by have := hb t v; omega
      _ = n * 2 ^ (n + 1) := by simp
  have := hgrow (n * 2 ^ (n + 1) + 1)
  have := hbound (n * 2 ^ (n + 1) + 1)
  omega

theorem yN_fp (x : Fin n → ℕ) (hx : ∀ v, PhiN I x v = x v) : yN I x .yes + yN I x .no = 1 := by
  have h := sum_PhiN I x
  simp only [hx] at h
  omega

end FP

/-! ## 3. Explicit potentials for the optimal flows of the counting network -/

section Pot

/-- Gap `π(s_ℓ) - π(t_ℓ)` at depth `d` (level `ℓ = k - d`). -/
def gg (k : ℕ) (g : ℚ) : ℕ → ℚ
  | 0 => g
  | d + 1 => if gg k g d ≤ 3 ^ (k - d) then gg k g d else 2 * 3 ^ (k - d) - gg k g d

/-- Potential of `s_ℓ` at depth `d`. -/
def pp (k : ℕ) (p g : ℚ) : ℕ → ℚ
  | 0 => p
  | d + 1 => if gg k g d ≤ 3 ^ (k - d) then pp k p g d else pp k p g d - gg k g d + 3 ^ (k - d)

/-- Potential of `t_ℓ` at depth `d`. -/
def qq (k : ℕ) (p g : ℚ) (d : ℕ) : ℚ := pp k p g d - gg k g d

/-- Node potentials of `G_k` (top potential `p` at `s_k`, `p - g` at `t_k`). -/
def pot (k : ℕ) (p g : ℚ) : GNode k → ℚ
  | .inl i => pp k p g (k - i)
  | .inr i => qq k p g (k - i)

/-- Complementary slackness for one arc (potentials decrease along the flow). -/
def ArcOK (cost cap φ diff : ℚ) : Prop := (0 < φ → cost ≤ diff) ∧ (φ < cap → diff ≤ cost)

theorem countD_getD_bounds (j i : ℕ) :
    0 ≤ (countD j).getD i 0 ∧ (countD j).getD i 0 ≤ 2 * 3 ^ j := by
  by_cases hi : i < (countD j).length
  · rw [List.getD_eq_getElem _ _ hi]
    exact L23.mem_bounds j _ (List.getElem_mem hi)
  · rw [List.getD_eq_default _ _ (by omega)]
    exact ⟨le_rfl, by positivity⟩

/-- Validity of the gap at depth `d`. -/
def Inv (k : ℕ) (y : ℚ) (g : ℚ) (d : ℕ) : Prop :=
  ∃ N : ℕ, L23.uu k y d = N ∧ N ≤ 2 ^ (k - d) ∧
    (1 ≤ N → (countD (k - d)).getD (N - 1) 0 ≤ gg k g d) ∧
    (N < 2 ^ (k - d) → gg k g d ≤ (countD (k - d)).getD N 0)

/-- Level condition at depth `d`. -/
def LC (k : ℕ) (y : ℚ) (g : ℚ) (d : ℕ) : Prop :=
  (gg k g d < 3 ^ (k - d) → L23.uu k y d ≤ 2 ^ (k - d - 1)) ∧
  (3 ^ (k - d) < gg k g d → 2 ^ (k - d - 1) ≤ L23.uu k y d)

theorem inv_step (k : ℕ) (y g : ℚ) (d : ℕ) (hd : d < k) (h : Inv k y g d) :
    LC k y g d ∧ Inv k y g (d + 1) := by
  obtain ⟨N, hN, hN2, hlo, hhi⟩ := h
  obtain ⟨j, hj⟩ : ∃ j, k - d = j + 1 := ⟨k - d - 1, by omega⟩
  have hj' : k - (d + 1) = j := by omega
  have hjd : k - d - 1 = j := by omega
  unfold LC Inv
  rw [hj] at hN2 hlo hhi ⊢
  rw [hj', show j + 1 - 1 = j by omega]
  have hc2 : (2 : ℚ) ^ (j + 1) = 2 * 2 ^ j := by ring
  have hw : (3 : ℚ) ^ (j + 1) = 3 * 3 ^ j := by ring
  have hN2' : N ≤ 2 * 2 ^ j := by rw [pow_succ] at hN2; omega
  have hc1 : 1 ≤ 2 ^ j := Nat.one_le_two_pow
  have h3 : (0 : ℚ) < 3 ^ j := by positivity
  have hD := countD_getD_bounds j
  have hDs := fun i (hi : i < 2 * 2 ^ j) => L23.countD_getD_succ j i hi
  have huu : L23.uu k y (d + 1) = min (L23.uu k y d) (2 ^ (k - d) - L23.uu k y d) := rfl
  rw [hj, hN] at huu
  have hgg : gg k g (d + 1) = if gg k g d ≤ 3 ^ (k - d) then gg k g d
      else 2 * 3 ^ (k - d) - gg k g d := rfl
  rw [hj] at hgg
  rw [hN]
  set G := gg k g d with hG
  by_cases hGw : G ≤ 3 ^ (j + 1)
  · rw [if_pos hGw] at hgg
    have hNc : N ≤ 2 ^ j := by
      by_contra hh
      push Not at hh
      have e := hDs (N - 1) (by omega)
      rw [if_neg (by omega)] at e
      have h1 := hlo (by omega)
      rw [e, hw] at h1
      have h2 := (hD (2 * 2 ^ j - 1 - (N - 1))).2
      rw [hw] at hGw
      linarith
    have hmin : min (N : ℚ) (2 ^ (j + 1) - N) = N := by
      apply min_eq_left
      have : (N : ℚ) ≤ 2 ^ j := by exact_mod_cast hNc
      linarith
    refine ⟨⟨fun _ => by exact_mod_cast hNc, fun h => absurd hGw (not_le.2 h)⟩,
      N, by rw [huu, hmin], hNc, fun h1 => ?_, fun h1 => ?_⟩
    · rw [hgg]
      have e := hDs (N - 1) (by omega)
      rw [if_pos (by omega)] at e
      rw [← e]; exact hlo h1
    · rw [hgg]
      have e := hDs N (by omega)
      rw [if_pos (by omega)] at e
      rw [← e]; exact hhi (by rw [pow_succ]; omega)
  · push Not at hGw
    rw [if_neg (not_le.2 hGw)] at hgg
    have hNc : 2 ^ j ≤ N := by
      by_contra hh
      push Not at hh
      have e := hDs N (by omega)
      rw [if_pos hh] at e
      have := hhi (by rw [pow_succ]; omega)
      rw [e] at this
      have := (hD N).2
      rw [hw] at hGw
      linarith
    have hmin : min (N : ℚ) (2 ^ (j + 1) - N) = ((2 * 2 ^ j - N : ℕ) : ℚ) := by
      rw [Nat.cast_sub hN2', hc2]
      push_cast
      apply min_eq_right
      have : (2 : ℚ) ^ j ≤ N := by exact_mod_cast hNc
      linarith
    refine ⟨⟨fun h => absurd hGw (not_lt.2 h.le), fun _ => by exact_mod_cast hNc⟩,
      2 * 2 ^ j - N, by rw [huu, hmin], by omega, fun h1 => ?_, fun h1 => ?_⟩
    · rw [hgg]
      have e := hDs N (by omega)
      rw [if_neg (by omega)] at e
      have := hhi (by rw [pow_succ]; omega)
      rw [e, show 2 * 2 ^ j - 1 - N = 2 * 2 ^ j - N - 1 by omega] at this
      linarith
    · rw [hgg]
      have e := hDs (N - 1) (by omega)
      rw [if_neg (by omega)] at e
      have := hlo (by omega)
      rw [e, show 2 * 2 ^ j - 1 - (N - 1) = 2 * 2 ^ j - N by omega] at this
      linarith

theorem inv_all (k : ℕ) (y : ℕ) (hy : y ≤ 2 ^ k) (g : ℚ)
    (hlo : 1 ≤ y → (countD k).getD (y - 1) 0 ≤ g) (hhi : y < 2 ^ k → g ≤ (countD k).getD y 0) :
    ∀ d, d ≤ k → Inv k y g d := by
  intro d hd
  induction d with
  | zero => exact ⟨y, rfl, by simpa using hy, by simpa [gg] using hlo, by simpa [gg] using hhi⟩
  | succ d ih => exact (inv_step k y g d (by omega) (ih (by omega))).2

theorem arcOK_level (k : ℕ) (y : ℚ) (p g : ℚ) (d j : ℕ) (hj : k - d = j + 1)
    (hlc : LC k y g d) (_hY0 : 0 ≤ L23.uu k y d) (_hY1 : L23.uu k y d ≤ 2 ^ (j + 1)) :
    let Y := L23.uu k y d
    let Y' := L23.uu k y (d + 1)
    ArcOK 0 (2 ^ j) ((Y' + Y) / 2) (pp k p g d - pp k p g (d + 1)) ∧
    ArcOK 0 (2 ^ j) ((Y' + Y) / 2) (qq k p g (d + 1) - qq k p g d) ∧
    ArcOK (3 ^ (j + 1)) (2 ^ j) ((Y - Y') / 2) (pp k p g d - qq k p g (d + 1)) ∧
    ArcOK (3 ^ (j + 1)) (2 ^ j) ((Y - Y') / 2) (pp k p g (d + 1) - qq k p g d) := by
  intro Y Y'
  have hY' : Y' = min Y (2 ^ (k - d) - Y) := rfl
  rw [hj] at hY'
  unfold LC at hlc
  rw [hj, show j + 1 - 1 = j by omega] at hlc
  have hpp : pp k p g (d + 1) = if gg k g d ≤ 3 ^ (k - d) then pp k p g d
      else pp k p g d - gg k g d + 3 ^ (k - d) := rfl
  have hgg : gg k g (d + 1) = if gg k g d ≤ 3 ^ (k - d) then gg k g d
      else 2 * 3 ^ (k - d) - gg k g d := rfl
  rw [hj] at hpp hgg
  have hq1 : qq k p g (d + 1) = pp k p g (d + 1) - gg k g (d + 1) := rfl
  have hq0 : qq k p g d = pp k p g d - gg k g d := rfl
  rw [hq1, hq0]
  have hc2 : (2 : ℚ) ^ (j + 1) = 2 * 2 ^ j := by ring
  rw [hc2] at hY'
  have hcpos : (0 : ℚ) < 2 ^ j := by positivity
  unfold ArcOK
  by_cases hGw : gg k g d ≤ 3 ^ (j + 1)
  · rw [if_pos hGw] at hpp hgg
    rw [hpp, hgg]
    rcases lt_or_eq_of_le hGw with hlt | heq
    · have hYc := hlc.1 hlt
      have : Y' = Y := by rw [hY']; apply min_eq_left; linarith
      rw [this]
      refine ⟨⟨fun _ => by linarith, fun _ => by linarith⟩, ⟨fun _ => by linarith, fun _ => by linarith⟩,
        ⟨fun h => by linarith, fun _ => by linarith⟩, ⟨fun h => by linarith, fun _ => by linarith⟩⟩
    · refine ⟨⟨fun _ => by linarith, fun _ => by linarith⟩, ⟨fun _ => by linarith, fun _ => by linarith⟩,
        ⟨fun _ => by linarith, fun _ => by linarith⟩, ⟨fun _ => by linarith, fun _ => by linarith⟩⟩
  · push Not at hGw
    rw [if_neg (not_le.2 hGw)] at hpp hgg
    rw [hpp, hgg]
    have hYc := hlc.2 hGw
    have : Y' = 2 * 2 ^ j - Y := by rw [hY']; apply min_eq_right; linarith
    rw [this]
    refine ⟨⟨fun _ => by linarith, fun h => by linarith⟩, ⟨fun _ => by linarith, fun h => by linarith⟩,
      ⟨fun _ => by linarith, fun _ => by linarith⟩, ⟨fun _ => by linarith, fun _ => by linarith⟩⟩

theorem gnet_ok (k : ℕ) (y : ℕ) (hy : y ≤ 2 ^ k) (p g : ℚ)
    (hlo : 1 ≤ y → (countD k).getD (y - 1) 0 ≤ g) (hhi : y < 2 ^ k → g ≤ (countD k).getD y 0) :
    ∀ a : GArc k, ArcOK (gCost a) (gCap a) (L23.optFlow k y a)
      (pot k p g (gTail a) - pot k p g (gHead a)) := by
  have hinv := inv_all k y hy g hlo hhi
  have hb := L23.uu_bounds k (y := (y : ℚ)) (by positivity) (by exact_mod_cast hy)
  rintro (_ | ⟨⟨j, hjk⟩, r⟩)
  · -- the arc `s₀ → t₀`
    obtain ⟨N, hN, hN1, hlo', hhi'⟩ := hinv k le_rfl
    simp only [Nat.sub_self, pow_zero] at hN1 hlo' hhi'
    simp only [gCost, gCap, gTail, gHead, pot, L23.optFlow, Fin.val_zero, Nat.sub_zero, qq]
    rw [hN]
    have e0 : (countD 0).getD 0 0 = 0 := rfl
    refine ⟨fun h => ?_, fun h => ?_⟩
    · have : 1 ≤ N := by exact_mod_cast h
      have := hlo' this
      rw [show N - 1 = 0 by omega, e0] at this; linarith
    · have : N < 1 := by exact_mod_cast h
      have := hhi' this
      rw [show N = 0 by omega, e0] at this; linarith
  · set d := k - (j + 1) with hd
    have hj : k - d = j + 1 := by omega
    have hkj : k - j = d + 1 := by omega
    have hlc := (inv_step k y g d (by omega) (hinv d (by omega))).1
    have hbd := hb d (by omega)
    rw [hj] at hbd
    have L := arcOK_level k y p g d j hj hlc hbd.1 hbd.2
    simp only at L
    have hflow : ∀ r : Fin 4, L23.optFlow k y (some (⟨j, hjk⟩, r)) =
        if r.val ≤ 1 then (L23.uu k y (d + 1) + L23.uu k y d) / 2
        else (L23.uu k y d - L23.uu k y (d + 1)) / 2 := by
      intro r; simp only [L23.optFlow]; rw [hkj, ← hd]
    rw [hflow]
    rcases r with ⟨_ | _ | _ | _ | r, hr⟩
    · have L' := L.1
      simp [gCost, gCap, gTail, gHead, pot, hkj, ← hd]
      simpa using L'
    · have L' := L.2.1
      simp [gCost, gCap, gTail, gHead, pot, hkj, ← hd]
      simpa using L'
    · have L' := L.2.2.1
      simp [gCost, gCap, gTail, gHead, pot, hkj, ← hd]
      simpa using L'
    · have L' := L.2.2.2
      simp [gCost, gCap, gTail, gHead, pot, hkj, ← hd]
      simpa using L'
    · omega

theorem pot_bounds (k : ℕ) (p g lo hi : ℚ) (h1 : lo ≤ p) (h2 : p ≤ hi) (h3 : lo ≤ p - g)
    (h4 : p - g ≤ hi) : ∀ u, lo ≤ pot k p g u ∧ pot k p g u ≤ hi := by
  have key : ∀ d, lo ≤ pp k p g d ∧ pp k p g d ≤ hi ∧ lo ≤ qq k p g d ∧ qq k p g d ≤ hi := by
    intro d
    induction d with
    | zero => exact ⟨h1, h2, h3, h4⟩
    | succ d ih =>
      obtain ⟨a1, a2, a3, a4⟩ := ih
      have hw : (0 : ℚ) < 3 ^ (k - d) := by positivity
      have hpp : pp k p g (d + 1) = if gg k g d ≤ 3 ^ (k - d) then pp k p g d
          else pp k p g d - gg k g d + 3 ^ (k - d) := rfl
      have hgg : gg k g (d + 1) = if gg k g d ≤ 3 ^ (k - d) then gg k g d
          else 2 * 3 ^ (k - d) - gg k g d := rfl
      have hq1 : qq k p g (d + 1) = pp k p g (d + 1) - gg k g (d + 1) := rfl
      have hq0 : qq k p g d = pp k p g d - gg k g d := rfl
      rw [hq1]; rw [hq0] at a3 a4
      split_ifs at hpp hgg with h
      · rw [hpp, hgg]; exact ⟨a1, a2, by linarith, by linarith⟩
      · push Not at h
        rw [hpp, hgg]
        refine ⟨by linarith, by linarith, by linarith, by linarith⟩
  rintro (i | i)
  · exact ⟨(key _).1, (key _).2.1⟩
  · exact ⟨(key _).2.2.1, (key _).2.2.2⟩

end Pot

/-! ## 4. Market bookkeeping (copied from `Composition.lean`, namespace `Exist`) -/

theorem sSource_ne_sinkA (m : ℕ) : sSource m ≠ sinkA m := by simp [sSource, sinkA]
theorem sSource_ne_sinkB (m : ℕ) : sSource m ≠ sinkB m := by simp [sSource, sinkB]
theorem sinkA_ne_sinkB (m : ℕ) : sinkA m ≠ sinkB m := by simp [sinkA, sinkB]

theorem sinkOf_ne_sSource (m : ℕ) (i : Bool) : sinkOf m i ≠ sSource m := by
  cases i
  · exact (sSource_ne_sinkA m).symm
  · exact (sSource_ne_sinkB m).symm

theorem sinkOf_inj (m : ℕ) {i j : Bool} (h : sinkOf m i = sinkOf m j) : i = j := by
  cases i <;> cases j <;> simp_all [sinkOf, sinkA, sinkB]

theorem sum_gadgetPort (F : GadgetPort → ℚ) : ∑ j, F j = F .p + F .πa + F .πb := by
  show ∑ j ∈ ({.p, .πa, .πb} : Finset GadgetPort), F j = _
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  ring

theorem mem_gadgetE_arc (m : ℕ) (u : SNode m) (e : SArc m) :
    (u, (.inl e : SArc m ⊕ GadgetPort)) ∈ gadgetE m ↔
      (splitter m).tail e = u ∨ (splitter m).head e = u := by
  simp [gadgetE]

theorem mem_gadgetE_p (m : ℕ) (u : SNode m) :
    (u, (.inr .p : SArc m ⊕ GadgetPort)) ∈ gadgetE m ↔ u = sSource m := by
  simp [gadgetE]

theorem mem_gadgetE_πa (m : ℕ) (u : SNode m) :
    (u, (.inr .πa : SArc m ⊕ GadgetPort)) ∈ gadgetE m ↔ u = sinkA m := by
  simp [gadgetE]

theorem mem_gadgetE_πb (m : ℕ) (u : SNode m) :
    (u, (.inr .πb : SArc m ⊕ GadgetPort)) ∈ gadgetE m ↔ u = sinkB m := by
  simp [gadgetE]

/-! ### The §5 market: options -/

section Market

variable {n : ℕ} (I : ArrivalInstance n)

theorem mem_E (e : RBuyer n × RGood n) : e ∈ I.redMarket.E ↔ I.redIsOption e := by
  simp [ArrivalInstance.redMarket]

theorem portGood_ne_arc (v : Fin n) (i : Bool) (q : Fin n × SArc n) :
    I.portGood v i ≠ .inr (.inl q) := by
  unfold ArrivalInstance.portGood; split <;> simp

theorem portGood_eq_inl (v : Fin n) (i : Bool) (w : Fin n) :
    I.portGood v i = .inl w ↔ I.succ v i = .inl w := by
  unfold ArrivalInstance.portGood; split <;> simp_all

theorem portGood_eq_exit (v : Fin n) (i : Bool) :
    I.portGood v i = .inr (.inr ()) ↔ (I.succ v i = .inr .yes ∨ I.succ v i = .inr .no) := by
  unfold ArrivalInstance.portGood
  split
  · simp_all
  · rename_i t ht; cases t <;> simp_all

/-- Options on a non-arc good. -/
theorem opt_nonarc (v : Fin n) (u : SNode n) (g : RGood n) (hg : ∀ q, g ≠ .inr (.inl q)) :
    I.redIsOption ((v, u), g) ↔
      (u = sSource n ∧ g = .inl v) ∨ (u = sinkA n ∧ g = I.portGood v false) ∨
        (u = sinkB n ∧ g = I.portGood v true) := by
  unfold ArrivalInstance.redIsOption
  constructor
  · rintro (h | h | h | ⟨a, ha, _⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
    · exact absurd ha (hg _)
  · rintro (h | h | h)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))

theorem ite_opt_nonarc (v : Fin n) (u : SNode n) (g : RGood n) (hg : ∀ q, g ≠ .inr (.inl q))
    (F : ℚ) :
    (if I.redIsOption ((v, u), g) then F else 0) =
      (if u = sSource n then (if g = .inl v then F else 0) else 0) +
      (if u = sinkA n then (if g = I.portGood v false then F else 0) else 0) +
      (if u = sinkB n then (if g = I.portGood v true then F else 0) else 0) := by
  simp only [opt_nonarc I v u g hg]
  have h1 := sSource_ne_sinkA n
  have h2 := sSource_ne_sinkB n
  have h3 := sinkA_ne_sinkB n
  by_cases hs : u = sSource n
  · subst hs; simp [h1, h2]
  by_cases ha : u = sinkA n
  · subst ha; simp [h1.symm, h3]
  by_cases hb : u = sinkB n
  · subst hb; simp [h2.symm, h3.symm]
  simp [hs, ha, hb]

/-- Options on an arc good. -/
theorem opt_arc (v' : Fin n) (u : SNode n) (v : Fin n) (e : SArc n) :
    I.redIsOption ((v', u), .inr (.inl (v, e))) ↔
      v' = v ∧ ((splitter n).tail e = u ∨ (splitter n).head e = u) := by
  unfold ArrivalInstance.redIsOption
  constructor
  · rintro (⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ | ⟨a, ha, h⟩)
    · simp at h
    · exact absurd h.symm (portGood_ne_arc I _ _ _)
    · exact absurd h.symm (portGood_ne_arc I _ _ _)
    · simp only [Sum.inr.injEq, Sum.inl.injEq, Prod.mk.injEq] at ha
      obtain ⟨rfl, rfl⟩ := ha
      exact ⟨rfl, h⟩
  · rintro ⟨rfl, h⟩
    exact Or.inr (Or.inr (Or.inr ⟨e, rfl, h⟩))

theorem opt_port (u : Fin n) (i : Bool) :
    I.redIsOption ((u, sinkOf n i), I.portGood u i) := by
  cases i
  · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))

theorem opt_src (v : Fin n) : I.redIsOption ((v, sSource n), .inl v) := Or.inl ⟨rfl, rfl⟩

/-- Sum over the non-arc goods picks out a non-arc good. -/
theorem sum_nonarc (X : RGood n) (hX : ∀ q, X ≠ .inr (.inl q)) (F : RGood n → ℚ) :
    (∑ w : Fin n, if (.inl w : RGood n) = X then F (.inl w) else 0) +
      (if (.inr (.inr ()) : RGood n) = X then F (.inr (.inr ())) else 0) = F X := by
  rcases X with w | q | ⟨⟩
  · simp
  · exact absurd rfl (hX q)
  · simp

theorem portGood_nonarc (v : Fin n) (i : Bool) : ∀ q, I.portGood v i ≠ .inr (.inl q) :=
  portGood_ne_arc I v i

variable (f : RBuyer n × RGood n → ℚ)

theorem colSum_eq (j : RGood n) :
    I.redMarket.colSum f j = ∑ b, if I.redIsOption (b, j) then f (b, j) else 0 := by
  unfold Market.colSum; rw [sum_filter_snd]; simp only [mem_E]

theorem rowSum_eq (b : RBuyer n) :
    I.redMarket.rowSum f b = ∑ j, if I.redIsOption (b, j) then f (b, j) else 0 := by
  unfold Market.rowSum; rw [sum_filter_fst]; simp only [mem_E]

theorem colSum_nonarc (g : RGood n) (hg : ∀ q, g ≠ .inr (.inl q)) :
    I.redMarket.colSum f g =
      (∑ u : Fin n, if g = .inl u then f ((u, sSource n), g) else 0) +
      ∑ u : Fin n, ∑ i : Bool, if g = I.portGood u i then f ((u, sinkOf n i), g) else 0 := by
  rw [colSum_eq, Fintype.sum_prod_type]
  simp only [ite_opt_nonarc I _ _ g hg, Finset.sum_add_distrib, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true, Fintype.sum_bool]
  simp only [sinkOf]
  ring

theorem colSum_inl (w : Fin n) :
    I.redMarket.colSum f (.inl w) = f ((w, sSource n), .inl w) +
      ∑ u : Fin n, ∑ i : Bool, if I.succ u i = .inl w then I.portPurchase f u i else 0 := by
  rw [colSum_nonarc I f _ (by simp)]
  congr 1
  · simp
  · refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun i _ => ?_
    by_cases h : I.succ u i = .inl w
    · have h' := (portGood_eq_inl I u i w).2 h
      simp [h, h', ArrivalInstance.portPurchase]
    · have h' : ¬ I.portGood u i = .inl w := fun h' => h ((portGood_eq_inl I u i w).1 h')
      simp only [h, Ne.symm h', ite_false]

theorem colSum_exit :
    I.redMarket.colSum f (.inr (.inr ())) = I.exitLoad f .yes + I.exitLoad f .no := by
  rw [colSum_nonarc I f _ (by simp)]
  simp only [reduceCtorEq, ite_false, Finset.sum_const_zero, zero_add, ArrivalInstance.exitLoad,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun i _ => ?_
  have := portGood_eq_exit I u i
  rcases hs : I.succ u i with w | t
  · have h' : ¬ (Sum.inr (Sum.inr ()) : RGood n) = I.portGood u i := by
      intro h'; rcases this.1 h'.symm with h'' | h'' <;> rw [hs] at h'' <;> simp at h''
    simp [h']
  · have h' : (Sum.inr (Sum.inr ()) : RGood n) = I.portGood u i := by
      rw [this.2]; cases t <;> simp [hs]
    simp only [h', ite_true]
    cases t <;> simp [ArrivalInstance.portPurchase]

theorem rowSum_market (v : Fin n) (u : SNode n) :
    I.redMarket.rowSum f (v, u) =
      (∑ e : SArc n, if (splitter n).tail e = u ∨ (splitter n).head e = u then
          f ((v, u), .inr (.inl (v, e))) else 0) +
      ((if u = sSource n then f ((v, u), .inl v) else 0) +
       (if u = sinkA n then f ((v, u), I.portGood v false) else 0) +
       (if u = sinkB n then f ((v, u), I.portGood v true) else 0)) := by
  rw [rowSum_eq, Fintype.sum_sum_type, Fintype.sum_sum_type]
  have harc : (∑ q : Fin n × SArc n, if I.redIsOption ((v, u), .inr (.inl q)) then
      f ((v, u), .inr (.inl q)) else 0) =
      ∑ e : SArc n, if (splitter n).tail e = u ∨ (splitter n).head e = u then
          f ((v, u), .inr (.inl (v, e))) else 0 := by
    rw [Fintype.sum_prod_type]
    simp only [opt_arc I v u, ite_and]
    rw [Fintype.sum_eq_single v (fun x hx => by simp [Ne.symm hx])]
    simp
  rw [harc, add_left_comm]
  congr 1
  simp only [Finset.univ_unique, Finset.sum_singleton]
  have hw : ∀ w : Fin n, (if I.redIsOption ((v, u), .inl w) then f ((v, u), .inl w) else 0) = _ :=
    fun w => ite_opt_nonarc I v u (.inl w) (by simp) _
  have hx := ite_opt_nonarc I v u (.inr (.inr default)) (by simp) (f ((v, u), .inr (.inr default)))
  simp only [hw, hx, Finset.sum_add_distrib]
  rw [show (default : Unit) = () from rfl] at *
  have e1 := sum_nonarc (.inl v) (by simp) (fun j => f ((v, u), j))
  have e2 := sum_nonarc (I.portGood v false) (portGood_nonarc I v false) (fun j => f ((v, u), j))
  have e3 := sum_nonarc (I.portGood v true) (portGood_nonarc I v true) (fun j => f ((v, u), j))
  have h1 := sSource_ne_sinkA n
  have h2 := sSource_ne_sinkB n
  have h3 := sinkA_ne_sinkB n
  by_cases hs : u = sSource n
  · subst hs; simp only [h1, h2, ite_false, ite_true, add_zero, Finset.sum_const_zero]; exact e1
  by_cases ha : u = sinkA n
  · subst ha; simp only [h1.symm, h3, ite_false, ite_true, zero_add, add_zero, Finset.sum_const_zero]; exact e2
  by_cases hb : u = sinkB n
  · subst hb; simp only [h2.symm, h3.symm, ite_false, ite_true, zero_add, add_zero, Finset.sum_const_zero]; exact e3
  simp [hs, ha, hb]

theorem colSum_arc (v : Fin n) (e : SArc n) :
    I.redMarket.colSum f (.inr (.inl (v, e))) =
      ∑ u : SNode n, if (splitter n).tail e = u ∨ (splitter n).head e = u then
        f ((v, u), .inr (.inl (v, e))) else 0 := by
  rw [colSum_eq, Fintype.sum_prod_type]
  simp only [opt_arc I, ite_and]
  rw [Fintype.sum_eq_single v (fun x hx => by simp [hx])]
  simp

end Market

section Coef2

variable {n : ℕ} (I : ArrivalInstance n)

theorem a_nonarc (b : RBuyer n) (g : RGood n) (hg : ∀ q, g ≠ .inr (.inl q)) :
    I.redMarket.a (b, g) = if b.2 = sSource n then 2 * bigM n
      else if b.2 = sinkA n then bigM n else bigM n - epsC := by
  rcases g with w | q | ⟨⟩
  · rfl
  · exact absurd rfl (hg q)
  · rfl

theorem b_nonarc (b : RBuyer n) (g : RGood n) (hg : ∀ q, g ≠ .inr (.inl q)) :
    I.redMarket.b (b, g) = if b.2 = sSource n then lam n else 1 := by
  rcases g with w | q | ⟨⟩
  · rfl
  · exact absurd rfl (hg q)
  · rfl

theorem a_arc (b : RBuyer n) (q : Fin n × SArc n) :
    I.redMarket.a (b, .inr (.inl q)) =
      if (splitter n).tail q.2 = b.2 then 2 * bigM n - gCost q.2.2 else 2 * bigM n := rfl

theorem b_arc (b : RBuyer n) (q : Fin n × SArc n) : I.redMarket.b (b, .inr (.inl q)) = 1 := rfl

end Coef2

theorem gCap_pos {k : ℕ} (a : GArc k) : 0 < gCap a := by
  rcases a with _ | ⟨j, r⟩
  · simp [gCap]
  · simp only [gCap]; positivity

theorem exists_arc_into (m : ℕ) (u : SNode m) (hu : u ≠ sSource m) :
    ∃ a, (splitter m).head a = u := by
  rcases u with ⟨⟩ | ⟨c, i | i⟩
  · exact absurd rfl hu
  · refine ⟨(c, some (i, 0)), ?_⟩
    simp [splitter, embed, gHead]
  · induction i using Fin.cases with
    | zero => exact ⟨(c, none), by simp [splitter, embed, gHead]⟩
    | succ j => exact ⟨(c, some (j, 1)), by simp [splitter, embed, gHead]⟩

theorem inCap_pos (m : ℕ) (u : SNode m) (hu : u ≠ sSource m) : 0 < inCap m u := by
  obtain ⟨a, ha⟩ := exists_arc_into m u hu
  unfold inCap Network.inflow
  refine lt_of_lt_of_le (gCap_pos a.2) ?_
  exact Finset.single_le_sum (f := (splitter m).cap)
    (fun b _ => (gCap_pos b.2).le) (Finset.mem_filter.2 ⟨Finset.mem_univ _, ha⟩)

theorem redMarket_wf {n : ℕ} (I : ArrivalInstance n) :
    I.redMarket.WellFormed ∧ ∀ e ∈ I.redMarket.E, 1 ≤ I.redMarket.b e := by
  have hcapV : ∀ v, 1 ≤ I.capV v := fun v => by
    unfold ArrivalInstance.capV; have : (0 : ℚ) ≤ 2 ^ n * (I.indeg (.inl v) : ℚ) := by positivity
    linarith
  have hb : ∀ e ∈ I.redMarket.E, 1 ≤ I.redMarket.b e := by
    rintro ⟨b, g⟩ _
    rcases g with w | q | ⟨⟩
    · show 1 ≤ (if b.2 = sSource n then lam n else 1)
      split_ifs
      · unfold lam bigM
        have : (1 : ℚ) ≤ 3 ^ (n + 1) := one_le_pow₀ (by norm_num)
        linarith
      · exact le_rfl
    · exact le_of_eq (b_arc I b q).symm
    · show 1 ≤ (if b.2 = sSource n then lam n else 1)
      split_ifs
      · unfold lam bigM
        have : (1 : ℚ) ≤ 3 ^ (n + 1) := one_le_pow₀ (by norm_num)
        linarith
      · exact le_rfl
  refine ⟨⟨?_, ?_, fun e he => lt_of_lt_of_le one_pos (hb e he)⟩, hb⟩
  · rintro ⟨v, u⟩
    show 0 < (if u = sSource n then I.capV v + (if v = I.origin then 1 else 0) else inCap n u)
    split_ifs with hu hv
    · linarith [hcapV v]
    · linarith [hcapV v]
    · exact inCap_pos n u hu
  · rintro (w | ⟨v, a⟩ | ⟨⟩)
    · exact lt_of_lt_of_le one_pos (hcapV w)
    · exact gCap_pos a.2
    · show (0 : ℚ) < 1 + 2 ^ n * ((I.indeg (.inr .yes) : ℚ) + (I.indeg (.inr .no) : ℚ))
      positivity


section Counting

variable {n : ℕ} (I : ArrivalInstance n)

theorem sum_ite_succ_le (w : Node n) (g : Fin n → Bool → ℚ) (B : ℚ)
    (hg : ∀ u i, I.succ u i = w → g u i ≤ B) :
    (∑ u : Fin n, ∑ i : Bool, if I.succ u i = w then g u i else 0) ≤ B * (I.indeg w : ℚ) := by
  have hcard : (I.indeg w : ℚ) = ∑ u : Fin n, ∑ i : Bool, if I.succ u i = w then 1 else 0 := by
    unfold ArrivalInstance.indeg
    rw [Finset.card_filter, ← Fintype.sum_prod_type']
    push_cast
    rfl
  rw [hcard, Finset.mul_sum]
  refine Finset.sum_le_sum fun u _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  split_ifs with h
  · simpa using hg u i h
  · simp

end Counting

/-! ## 5. The explicit market equilibrium of the §5 market -/

section Equil

variable {n : ℕ} (I : ArrivalInstance n) (x : Fin n → ℕ)

/-- Source potential `π_s` of a gadget fed with the integer `z`. -/
def piS (n : ℕ) (z : ℕ) : ℚ :=
  if z = 0 then bigM n
  else if z % 2 = 0 then bigM n + (countD n).getD (z / 2 - 1) 0 + 5
  else bigM n + (countD n).getD (z / 2) 0 + 2

/-- Price of the input good `p_w`. -/
def priceP (w : Fin n) : ℚ := piS n (x w) / lam n

/-- Price of the port of the labelled edge `(v, i)`. -/
def portPrice (v : Fin n) (i : Bool) : ℚ :=
  match I.succ v i with
  | .inl w => priceP x w
  | .inr _ => 0

/-- Top gap of copy `c` of gadget `v`. -/
def gapOf (v : Fin n) (c : Bool) : ℚ :=
  if c then piS n (x v) - (bigM n + epsC + portPrice I x v true)
  else piS n (x v) - (bigM n + portPrice I x v false)

/-- Value routed through copy `c` (`h₀`, `h₁` at integers). -/
def valOf (v : Fin n) (c : Bool) : ℕ := Decoder.hN c (x v)

/-- The splitter flow of gadget `v`. -/
def gflow (v : Fin n) : SArc n → ℚ :=
  L23.glue (L23.optFlow n (valOf x v false)) (L23.optFlow n (valOf x v true))

/-- Node potentials of gadget `v`. -/
def spot (v : Fin n) : SNode n → ℚ
  | .inl () => piS n (x v)
  | .inr (c, .inl i) => pot n (piS n (x v)) (gapOf I x v c) (.inl i.castSucc)
  | .inr (c, .inr i) => pot n (piS n (x v)) (gapOf I x v c) (.inr i)

/-- Prices. -/
def Pr : RGood n → ℚ
  | .inl w => priceP x w
  | .inr (.inl (w, a)) =>
      max (spot I x w ((splitter n).tail a) - gCost a.2) (spot I x w ((splitter n).head a))
  | .inr (.inr ()) => 0

/-- Utilities. -/
def Vb (b : RBuyer n) : ℚ := 2 * bigM n - spot I x b.1 b.2

/-- Purchase of the source buyer on its input good. -/
def yS (v : Fin n) : ℚ := I.capV v + (if v = I.origin then 1 else 0) - (x v : ℚ)

def arcF (b : RBuyer n) (g : RGood n) : ℚ :=
  match g with
  | .inr (.inl (w, a)) =>
      if w = b.1 then (if (splitter n).tail a = b.2 then gflow x w a
        else if (splitter n).head a = b.2 then gCap a.2 - gflow x w a else 0) else 0
  | _ => 0

def nonArcF (b : RBuyer n) (g : RGood n) : ℚ :=
  if b.2 = sSource n ∧ g = .inl b.1 then yS I x b.1
  else if b.2 = sinkA n ∧ g = I.portGood b.1 false then (valOf x b.1 false : ℚ)
  else if b.2 = sinkB n ∧ g = I.portGood b.1 true then (valOf x b.1 true : ℚ) else 0

/-- Purchases. -/
def Fq (e : RBuyer n × RGood n) : ℚ := arcF x e.1 e.2 + nonArcF I x e.1 e.2

/-! ### Basic facts -/

theorem gflow_apply (v : Fin n) (c : Bool) (a : GArc n) :
    gflow x v (c, a) = L23.optFlow n (valOf x v c) a := by
  cases c <;> rfl

theorem valOf_sum (v : Fin n) : (valOf x v false : ℚ) + valOf x v true = x v := by
  have := hN_sum (x v); unfold valOf; exact_mod_cast this

theorem valOf_le (v : Fin n) (hxb : x v + 1 ≤ 2 ^ (n + 1)) (c : Bool) : valOf x v c ≤ 2 ^ n := by
  unfold valOf Decoder.hN; rw [pow_succ] at hxb; split <;> omega

theorem gflow_split (v : Fin n) (hxb : x v + 1 ≤ 2 ^ (n + 1)) : IsSplitFlow n (x v) (gflow x v) := by
  have hA := (L23.optFlow_spec n (y := (valOf x v false : ℚ)) (by positivity)
    (by exact_mod_cast valOf_le x v hxb false)).1
  have hB := (L23.optFlow_spec n (y := (valOf x v true : ℚ)) (by positivity)
    (by exact_mod_cast valOf_le x v hxb true)).1
  have := L23.glue_split _ _ hA hB
  rwa [valOf_sum] at this

theorem netOut_optFlow_sink (y : ℕ) :
    (countingNetwork n).netOut (L23.optFlow n y) (gSink n) = -(y : ℚ) := by
  rw [gSink, L23.netOut_inr, Fin.val_last, L23.A_zero _ le_rfl, L23.A_zero _ le_rfl,
    L23.ww_optFlow n _ n le_rfl, Nat.sub_self]
  simp [L23.uu]

theorem netOut_sink (v : Fin n) (c : Bool) :
    (splitter n).netOut (gflow x v) (sinkOf n c) = -(valOf x v c : ℚ) := by
  rw [L23.sinkOf_eq, L23.s_netOut _ c _ L23.gSink_ne_gSource]
  have : L23.cp (gflow x v) c = L23.optFlow n (valOf x v c) := by
    cases c
    · exact L23.cp_glue_false _ _
    · exact L23.cp_glue_true _ _
  rw [this, netOut_optFlow_sink]

theorem inCap_src : inCap n (sSource n) = 0 := by
  unfold inCap
  rw [L23.s_inflow_src, gSource, L23.inflow_inl, L23.inflow_inl, Fin.val_last,
    L23.A_zero _ le_rfl, L23.A_zero _ le_rfl]
  ring

theorem spot_embed (v : Fin n) (c : Bool) (u : GNode n) :
    spot I x v (embed c u) = pot n (piS n (x v)) (gapOf I x v c) u := by
  rcases u with ⟨i, hi⟩ | ⟨i, hi⟩
  · simp only [embed]
    split_ifs with h
    · simp only [spot]; rfl
    · have : i = n := by omega
      subst this
      simp [spot, pot, pp]
  · rfl

theorem spot_sink (v : Fin n) (c : Bool) :
    spot I x v (sinkOf n c) = piS n (x v) - gapOf I x v c := by
  rw [L23.sinkOf_eq, spot_embed]
  simp [pot, gSink, qq, pp, gg]

theorem tail_ne_head (e : SArc n) : (splitter n).tail e ≠ (splitter n).head e := by
  rcases e with ⟨c, _ | ⟨⟨j, hj⟩, r⟩⟩
  · simp only [splitter, gTail, gHead, embed]
    split_ifs <;> simp
  · rcases r with ⟨_ | _ | _ | _ | r, hr⟩
    all_goals simp only [splitter, gTail, gHead, Fin.succ_mk, Fin.castSucc_mk]
    all_goals first
      | omega
      | (by_cases h1 : j + 1 < n <;> simp [embed, h1, hj])

theorem piS_zero : piS n 0 = bigM n := by simp [piS]

theorem piS_even (z : ℕ) (hz : 1 ≤ z) :
    piS n (2 * z) = bigM n + (countD n).getD (z - 1) 0 + 5 := by
  unfold piS; rw [if_neg (by omega), if_pos (by omega), show 2 * z / 2 = z by omega]

theorem piS_odd (z : ℕ) : piS n (2 * z + 1) = bigM n + (countD n).getD z 0 + 2 := by
  unfold piS; rw [if_neg (by omega), if_neg (by omega), show (2 * z + 1) / 2 = z by omega]

theorem piS_bounds (z : ℕ) : bigM n ≤ piS n z ∧ piS n z ≤ bigM n + 2 * 3 ^ n + 5 := by
  unfold piS
  split_ifs
  · exact ⟨le_rfl, by linarith [show (0 : ℚ) ≤ 2 * 3 ^ n by positivity]⟩
  · have := countD_getD_bounds n (z / 2 - 1); constructor <;> linarith
  · have := countD_getD_bounds n (z / 2); constructor <;> linarith

theorem bigM_eq : bigM n = 6 * 3 ^ n := by unfold bigM; ring

theorem hi_le (hn : 1 ≤ n) : bigM n + 2 * 3 ^ n + 5 ≤ lam n := by
  have h3 : (3 : ℚ) ≤ 3 ^ n := by
    calc (3 : ℚ) = 3 ^ 1 := by norm_num
      _ ≤ 3 ^ n := pow_le_pow_right₀ (by norm_num) hn
  unfold lam; rw [bigM_eq]; linarith

theorem lam_pos : 0 < lam n := by unfold lam bigM; positivity

theorem priceP_bounds (hn : 1 ≤ n) (w : Fin n) : 0 ≤ priceP x w ∧ priceP x w ≤ 1 := by
  unfold priceP
  have := piS_bounds (n := n) (x w)
  have := hi_le hn
  have hM : (0 : ℚ) ≤ bigM n := by unfold bigM; positivity
  have hl := lam_pos (n := n)
  refine ⟨div_nonneg (by linarith) hl.le, (div_le_one hl).2 (by linarith)⟩

theorem portPrice_bounds (hn : 1 ≤ n) (v : Fin n) (i : Bool) :
    0 ≤ portPrice I x v i ∧ portPrice I x v i ≤ 1 := by
  unfold portPrice
  split
  · exact priceP_bounds x hn _
  · exact ⟨le_rfl, zero_le_one⟩

theorem top_valid (hn : 1 ≤ n) (v : Fin n) (hxb : x v + 1 ≤ 2 ^ (n + 1)) (c : Bool) :
    (1 ≤ valOf x v c → (countD n).getD (valOf x v c - 1) 0 ≤ gapOf I x v c) ∧
    (valOf x v c < 2 ^ n → gapOf I x v c ≤ (countD n).getD (valOf x v c) 0) := by
  have hg := L23.gaps n hn
  have h0 := L23.first n
  obtain ⟨P0a, P0b⟩ := portPrice_bounds I x hn v false
  obtain ⟨P1a, P1b⟩ := portPrice_bounds I x hn v true
  rw [pow_succ] at hxb
  unfold valOf gapOf
  obtain ⟨z, hz | hz⟩ : ∃ z, x v = 2 * z ∨ x v = 2 * z + 1 := ⟨x v / 2, by omega⟩
  · rw [hz]
    rcases Nat.eq_zero_or_pos z with rfl | hz1
    · simp only [mul_zero, piS_zero]
      cases c
      · simp only [Decoder.hN, Bool.false_eq_true, if_false]
        refine ⟨fun h => by omega, fun _ => ?_⟩
        rw [show (0 + 1) / 2 = 0 by rfl, h0]; linarith
      · simp only [Decoder.hN, if_true]
        refine ⟨fun h => by omega, fun _ => ?_⟩
        rw [show 0 / 2 = 0 by rfl, h0]; unfold epsC; linarith
    · rw [piS_even z hz1]
      have hN0 : Decoder.hN false (2 * z) = z := by simp [Decoder.hN]; omega
      have hN1 : Decoder.hN true (2 * z) = z := by simp [Decoder.hN]
      have gz := hg (z - 1) (by omega)
      rw [show z - 1 + 1 = z by omega] at gz
      cases c
      · simp only [hN0, Bool.false_eq_true, if_false]
        exact ⟨fun _ => by linarith, fun _ => by linarith⟩
      · simp only [hN1, if_true]; unfold epsC
        exact ⟨fun _ => by linarith, fun _ => by linarith⟩
  · rw [hz, piS_odd]
    have hN0 : Decoder.hN false (2 * z + 1) = z + 1 := by simp [Decoder.hN]; omega
    have hN1 : Decoder.hN true (2 * z + 1) = z := by simp [Decoder.hN]; omega
    cases c
    · simp only [hN0, Bool.false_eq_true, if_false, Nat.add_sub_cancel]
      refine ⟨fun _ => by linarith, fun h => ?_⟩
      have := hg z (by omega); linarith
    · simp only [hN1, if_true]; unfold epsC
      refine ⟨fun h => ?_, fun _ => by linarith⟩
      have := hg (z - 1) (by omega)
      rw [show z - 1 + 1 = z by omega] at this; linarith

theorem spot_bounds (hn : 1 ≤ n) (v : Fin n) (u : SNode n) :
    bigM n ≤ spot I x v u ∧ spot I x v u ≤ bigM n + 2 * 3 ^ n + 5 := by
  have hp := piS_bounds (n := n) (x v)
  have h3 : (0 : ℚ) ≤ 2 * 3 ^ n := by positivity
  have hpb := fun c => portPrice_bounds I x hn v c
  have hg : ∀ c, bigM n ≤ piS n (x v) - gapOf I x v c ∧
      piS n (x v) - gapOf I x v c ≤ bigM n + 2 * 3 ^ n + 5 := by
    intro c; cases c
    · simp only [gapOf, Bool.false_eq_true, if_false]
      have := hpb false; constructor <;> linarith
    · simp only [gapOf, if_true]; unfold epsC
      have := hpb true; constructor <;> linarith
  rcases u with ⟨⟩ | ⟨c, i | i⟩
  · exact hp
  · exact pot_bounds n _ _ _ _ hp.1 hp.2 (hg c).1 (hg c).2 _
  · exact pot_bounds n _ _ _ _ hp.1 hp.2 (hg c).1 (hg c).2 _

theorem arc_ok (hn : 1 ≤ n) (v : Fin n) (hxb : x v + 1 ≤ 2 ^ (n + 1)) (e : SArc n) :
    ArcOK (gCost e.2) (gCap e.2) (gflow x v e)
      (spot I x v ((splitter n).tail e) - spot I x v ((splitter n).head e)) := by
  rcases e with ⟨c, a⟩
  show ArcOK (gCost a) (gCap a) (gflow x v (c, a))
    (spot I x v (embed c (gTail a)) - spot I x v (embed c (gHead a)))
  rw [spot_embed, spot_embed, gflow_apply]
  have hv := top_valid I x hn v hxb c
  exact gnet_ok n (valOf x v c) (valOf_le x v hxb c) _ _ hv.1 hv.2 a

theorem gflow_bounds (v : Fin n) (hxb : x v + 1 ≤ 2 ^ (n + 1)) (e : SArc n) :
    0 ≤ gflow x v e ∧ gflow x v e ≤ gCap e.2 :=
  (gflow_split x v hxb).1 e

/-! ### Purchases -/

theorem Fq_arc (v w : Fin n) (a : SArc n) (uu : SNode n) :
    Fq I x ((v, uu), .inr (.inl (w, a))) =
      if w = v then (if (splitter n).tail a = uu then gflow x w a
        else if (splitter n).head a = uu then gCap a.2 - gflow x w a else 0) else 0 := by
  have h1 : ∀ i, ¬ ((Sum.inr (Sum.inl (w, a)) : RGood n) = I.portGood v i) :=
    fun i h => portGood_ne_arc I v i (w, a) h.symm
  simp [Fq, arcF, nonArcF, h1]

theorem Fq_nonarc (b : RBuyer n) (g : RGood n) (hg : ∀ q, g ≠ .inr (.inl q)) :
    Fq I x (b, g) = nonArcF I x b g := by
  have : arcF x b g = 0 := by
    rcases g with w | q | ⟨⟩
    · rfl
    · exact absurd rfl (hg q)
    · rfl
  simp [Fq, this]

theorem Fq_src (v : Fin n) : Fq I x ((v, sSource n), .inl v) = yS I x v := by
  rw [Fq_nonarc I x _ _ (by simp)]; simp [nonArcF]

theorem Fq_port (v : Fin n) (i : Bool) :
    Fq I x ((v, sinkOf n i), I.portGood v i) = (valOf x v i : ℚ) := by
  rw [Fq_nonarc I x _ _ (portGood_ne_arc I v i)]
  cases i
  · simp [nonArcF, sinkOf, (sSource_ne_sinkA n).symm]
  · simp [nonArcF, sinkOf, (sSource_ne_sinkB n).symm, (sinkA_ne_sinkB n).symm]

theorem portPurchase_Fq (u : Fin n) (i : Bool) :
    I.portPurchase (Fq I x) u i = (valOf x u i : ℚ) := Fq_port I x u i

theorem ite_or_split (p q : Prop) [Decidable p] [Decidable q] (h : ¬ (p ∧ q)) (a b : ℚ) :
    (if p ∨ q then (if p then a else if q then b else 0) else 0) =
      (if p then a else 0) + (if q then b else 0) := by
  by_cases hp : p <;> by_cases hq : q <;> simp_all

theorem arc_part (v : Fin n) (u : SNode n) :
    (∑ e : SArc n, if (splitter n).tail e = u ∨ (splitter n).head e = u then
        Fq I x ((v, u), .inr (.inl (v, e))) else 0) =
      (splitter n).netOut (gflow x v) u + inCap n u := by
  simp only [Fq_arc, if_true]
  rw [Finset.sum_congr rfl fun e _ => ite_or_split _ _ (fun h => tail_ne_head e (h.1.trans h.2.symm))
    (gflow x v e) (gCap e.2 - gflow x v e), Finset.sum_add_distrib]
  unfold Network.netOut Network.outflow Network.inflow inCap Network.inflow
  rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_filter]
  have : ∀ e : SArc n, (if (splitter n).head e = u then gCap e.2 - gflow x v e else 0) =
      (if (splitter n).head e = u then (splitter n).cap e else 0) -
        (if (splitter n).head e = u then gflow x v e else 0) := by
    intro e; split_ifs <;> simp [splitter]
  simp only [this, Finset.sum_sub_distrib]
  ring

theorem row_eq (v : Fin n) (u : SNode n) :
    I.redMarket.rowSum (Fq I x) (v, u) =
      (splitter n).netOut (gflow x v) u + inCap n u +
      ((if u = sSource n then yS I x v else 0) +
       (if u = sinkA n then (valOf x v false : ℚ) else 0) +
       (if u = sinkB n then (valOf x v true : ℚ) else 0)) := by
  rw [rowSum_market, arc_part]
  have e1 : (if u = sSource n then Fq I x ((v, u), .inl v) else 0) =
      (if u = sSource n then yS I x v else 0) := by
    split_ifs with h
    · subst h; exact Fq_src I x v
    · rfl
  have e2 : (if u = sinkA n then Fq I x ((v, u), I.portGood v false) else 0) =
      (if u = sinkA n then (valOf x v false : ℚ) else 0) := by
    split_ifs with h
    · subst h; exact Fq_port I x v false
    · rfl
  have e3 : (if u = sinkB n then Fq I x ((v, u), I.portGood v true) else 0) =
      (if u = sinkB n then (valOf x v true : ℚ) else 0) := by
    split_ifs with h
    · subst h; exact Fq_port I x v true
    · rfl
  rw [e1, e2, e3]

theorem row_full (hfp : ∀ v, PhiN I x v = x v) (hxb : ∀ v, x v + 1 ≤ 2 ^ (n + 1))
    (b : RBuyer n) : I.redMarket.rowSum (Fq I x) b = I.redMarket.mass b := by
  obtain ⟨v, u⟩ := b
  rw [row_eq]
  have hsp := gflow_split x v (hxb v)
  show _ = if u = sSource n then I.capV v + (if v = I.origin then 1 else 0) else inCap n u
  by_cases hs : u = sSource n
  · subst hs
    rw [hsp.2.1, inCap_src]
    simp only [if_true, sSource_ne_sinkA, sSource_ne_sinkB, if_false, yS]
    ring
  by_cases ha : u = sinkA n
  · subst ha
    have := netOut_sink x v false
    simp only [sinkOf] at this
    rw [this]
    simp only [hs, if_false, if_true, sinkA_ne_sinkB]
    ring
  by_cases hb : u = sinkB n
  · subst hb
    have := netOut_sink x v true
    simp only [sinkOf] at this
    rw [this]
    simp only [hs, if_false, if_true, (sinkA_ne_sinkB n).symm]
    ring
  rw [hsp.2.2 u hs ha hb]
  simp [hs, ha, hb]

theorem col_arc (v : Fin n) (e : SArc n) :
    I.redMarket.colSum (Fq I x) (.inr (.inl (v, e))) = gCap e.2 := by
  rw [colSum_arc]
  simp only [Fq_arc, if_true]
  rw [Finset.sum_congr rfl fun u _ => ite_or_split _ _
    (fun h => tail_ne_head e (h.1.trans h.2.symm)) (gflow x v e) (gCap e.2 - gflow x v e),
    Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq]
  simp

theorem hN_cast_sum (w : Node n) :
    ((∑ u, ∑ i : Bool, if I.succ u i = w then Decoder.hN i (x u) else 0 : ℕ) : ℚ) =
      ∑ u, ∑ i : Bool, if I.succ u i = w then (valOf x u i : ℚ) else 0 := by
  push_cast
  refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> simp [valOf]

theorem col_inl (hfp : ∀ v, PhiN I x v = x v) (w : Fin n) :
    I.redMarket.colSum (Fq I x) (.inl w) = I.capV w := by
  rw [colSum_inl, Fq_src]
  simp only [portPurchase_Fq]
  rw [← hN_cast_sum]
  have h := hfp w
  unfold PhiN at h
  have h' : ((x w : ℕ) : ℚ) = (if w = I.origin then 1 else 0) +
      ((∑ u, ∑ i : Bool, if I.succ u i = .inl w then Decoder.hN i (x u) else 0 : ℕ) : ℚ) := by
    rw [← h]; push_cast; split_ifs <;> simp
  unfold yS
  rw [h']
  ring

theorem exitLoad_Fq (t : Terminal) :
    I.exitLoad (Fq I x) t = ((yN I x t : ℕ) : ℚ) := by
  unfold ArrivalInstance.exitLoad yN
  simp only [portPurchase_Fq]
  rw [hN_cast_sum]

theorem col_exit (hfp : ∀ v, PhiN I x v = x v) :
    I.redMarket.colSum (Fq I x) (.inr (.inr ())) = 1 := by
  rw [colSum_exit, exitLoad_Fq, exitLoad_Fq]
  have := yN_fp I x hfp
  exact_mod_cast this

theorem yS_pos (hfp : ∀ v, PhiN I x v = x v) (hxb : ∀ v, x v + 1 ≤ 2 ^ (n + 1)) (v : Fin n) :
    0 < yS I x v := by
  have hsum := sum_ite_succ_le I (.inl v) (fun u i => (valOf x u i : ℚ)) (2 ^ n)
    (fun u i _ => by exact_mod_cast valOf_le x u (hxb u) i)
  rw [← hN_cast_sum] at hsum
  have h := hfp v
  unfold PhiN at h
  have h' : ((x v : ℕ) : ℚ) = (if v = I.origin then 1 else 0) +
      ((∑ u, ∑ i : Bool, if I.succ u i = .inl v then Decoder.hN i (x u) else 0 : ℕ) : ℚ) := by
    rw [← h]; push_cast; split_ifs <;> simp
  unfold yS ArrivalInstance.capV
  rw [h']
  linarith

theorem Pr_port (v : Fin n) (i : Bool) :
    Pr I x (I.portGood v i) = portPrice I x v i := by
  unfold ArrivalInstance.portGood portPrice
  rcases h : I.succ v i with w | t <;> simp only [h] <;> rfl

theorem Fq_nonneg (hfp : ∀ v, PhiN I x v = x v) (hxb : ∀ v, x v + 1 ≤ 2 ^ (n + 1))
    (e : RBuyer n × RGood n) : 0 ≤ Fq I x e := by
  obtain ⟨⟨v, u⟩, g⟩ := e
  unfold Fq
  have h1 : 0 ≤ arcF x (v, u) g := by
    unfold arcF
    rcases g with w | ⟨w, a⟩ | ⟨⟩
    · exact le_rfl
    · have := gflow_bounds x w (hxb w) a
      simp only
      split_ifs <;> linarith
    · exact le_rfl
  have h2 : 0 ≤ nonArcF I x (v, u) g := by
    unfold nonArcF
    have := yS_pos I x hfp hxb v
    split_ifs <;> first | positivity | linarith
  linarith

theorem market_eq (hn : 1 ≤ n) (hfp : ∀ v, PhiN I x v = x v) (hxb : ∀ v, x v + 1 ≤ 2 ^ (n + 1)) :
    I.redMarket.IsEquilibrium (Pr I x) (Vb I x) (Fq I x) := by
  have hM : (0 : ℚ) < bigM n := by unfold bigM; positivity
  have hsb := spot_bounds I x hn
  have hhi := hi_le (n := n) hn
  have hl := lam_pos (n := n)
  have hlam : lam n = 2 * bigM n := rfl
  -- non-arc options are tight
  have htight : ∀ v u g, (∀ q, g ≠ .inr (.inl q)) → I.redIsOption ((v, u), g) →
      I.redMarket.a ((v, u), g) - I.redMarket.b ((v, u), g) * Pr I x g = Vb I x (v, u) := by
    intro v u g hg hopt
    rw [a_nonarc I _ g hg, b_nonarc I _ g hg]
    simp only
    rcases (opt_nonarc I v u g hg).1 hopt with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · have hs : spot I x v (sSource n) = piS n (x v) := rfl
      simp only [if_true, Pr, priceP, Vb, hs]
      field_simp
    · simp only [(sSource_ne_sinkA n).symm, if_false, if_true, Vb]
      rw [Pr_port I x, show sinkA n = sinkOf n false from rfl, spot_sink]
      simp only [gapOf, Bool.false_eq_true, if_false]
      ring
    · simp only [(sSource_ne_sinkB n).symm, (sinkA_ne_sinkB n).symm, if_false, Vb]
      rw [Pr_port I x, show sinkB n = sinkOf n true from rfl, spot_sink]
      simp only [gapOf, if_true]
      ring
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro (w | ⟨w, a⟩ | ⟨⟩)
    · exact (priceP_bounds x hn w).1
    · exact le_trans (by linarith [(hsb w ((splitter n).head a)).1]) (le_max_right _ _)
    · exact le_rfl
  · rintro ⟨v, u⟩
    simp only [Vb]; linarith [(hsb v u).2]
  · intro e _; exact Fq_nonneg I x hfp hxb e
  · rintro ⟨⟨v, u⟩, g⟩ he
    rw [mem_E] at he
    rcases g with w | ⟨w, a⟩ | ⟨⟩
    · exact le_of_eq (htight v u _ (by simp) he)
    · obtain ⟨rfl, hta⟩ := (opt_arc I v u w a).1 he
      rw [a_arc, b_arc]
      simp only [Pr, Vb]
      split_ifs with ht
      · rw [← ht]; linarith [le_max_left (spot I x v ((splitter n).tail a) - gCost a.2)
          (spot I x v ((splitter n).head a))]
      · have hh : (splitter n).head a = u := hta.resolve_left ht
        rw [← hh]; linarith [le_max_right (spot I x v ((splitter n).tail a) - gCost a.2)
          (spot I x v ((splitter n).head a))]
    · exact le_of_eq (htight v u _ (by simp) he)
  · rintro ⟨⟨v, u⟩, g⟩ he hf
    rw [mem_E] at he
    rcases g with w | ⟨w, a⟩ | ⟨⟩
    · exact (htight v u _ (by simp) he).symm
    · obtain ⟨rfl, hta⟩ := (opt_arc I v u w a).1 he
      have hok := arc_ok I x hn v (hxb v) a
      rw [a_arc, b_arc]
      simp only [Pr, Vb]
      rw [Fq_arc] at hf
      simp only [if_true] at hf
      split_ifs at hf ⊢ with ht hh
      · rw [← ht]
        have := hok.1 hf
        rw [max_eq_left (by linarith)]; ring
      · have := hok.2 (by linarith)
        rw [← hh, max_eq_right (by linarith)]; ring
      · exact absurd hf (lt_irrefl _)
    · exact (htight v u _ (by simp) he).symm
  · intro b; rw [row_full I x hfp hxb]
  · intro b _; exact row_full I x hfp hxb b
  · rintro (w | ⟨w, a⟩ | ⟨⟩)
    · rw [col_inl I x hfp]; exact le_rfl
    · rw [col_arc]; exact le_rfl
    · rw [col_exit I x hfp]
      show (1 : ℚ) ≤ 1 + 2 ^ n * ((I.indeg (.inr .yes) : ℚ) + (I.indeg (.inr .no) : ℚ))
      have : (0 : ℚ) ≤ 2 ^ n * ((I.indeg (.inr .yes) : ℚ) + (I.indeg (.inr .no) : ℚ)) := by
        positivity
      linarith
  · rintro (w | ⟨w, a⟩ | ⟨⟩) hP
    · exact col_inl I x hfp w
    · exact col_arc I x w a
    · exact absurd hP (lt_irrefl _)


end Equil


end Exist

/-! ## 6. The target -/

/-- Helper: the §5 market of the preprocessed instance has an explicit equilibrium. -/
theorem redMarket_preprocess_eq_exists {n : ℕ} (I : ArrivalInstance n) :
    ∃ P v f, I.preprocess.redMarket.IsEquilibrium P v f := by
  have hn : 1 ≤ n := Fin.pos I.origin
  obtain ⟨x, hfp, hxb⟩ := Exist.exists_nat_fp I.preprocess (preprocess_preprocessed_proof I)
  exact ⟨_, _, _, Exist.market_eq I.preprocess x hn hfp hxb⟩

/-- Helper: `Red I` has an explicit coverage-form BNE. -/
theorem red_coverage_bne_exists {n : ℕ} (I : ArrivalInstance n) :
    ∃ ξ σ, (Red I).IsCoverageBNE ξ σ := by
  obtain ⟨P, v, f, heq⟩ := redMarket_preprocess_eq_exists I
  obtain ⟨hwf, hb⟩ := Exist.redMarket_wf I.preprocess
  exact ⟨_, _, Exist.lift_bne I.preprocess.redMarket hwf hb P v f heq⟩

/-- `red_bne_exists`, restated verbatim from `Statements.lean`. -/
theorem red_bne_exists_proof {n : ℕ} (I : ArrivalInstance n) :
    ∃ δ σ, (Red I).IsBNE δ σ := by
  obtain ⟨ξ, σ, h⟩ := red_coverage_bne_exists I
  exact ⟨_, σ, (fact0_realize_proof (Red I) rfl (fun _ => rfl) (fun _ => rfl) ξ σ h).1⟩


end Bssg

