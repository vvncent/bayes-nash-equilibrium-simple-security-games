import Mathlib
import BssgProofs.Statements

/-!
# Fact 0 (both directions), Lemma 8 (market → game decoding), sizes of `Red`
-/

namespace Bssg

open Finset

set_option linter.unusedSectionVars false

namespace Emb

/-! ### Sizes -/

theorem card_SNode (n : ℕ) : Fintype.card (SNode n) = 4 * n + 3 := by
  simp [Fintype.card_sum, Fintype.card_prod]; ring

theorem card_SArc (n : ℕ) : Fintype.card (SArc n) = 8 * n + 2 := by
  simp [SArc, GArc, Fintype.card_prod, Fintype.card_option]; ring

theorem card_RBuyer (n : ℕ) : Fintype.card (RBuyer n) = 4 * n ^ 2 + 3 * n := by
  rw [Fintype.card_prod, card_SNode]; simp; ring

theorem card_RGood (n : ℕ) : Fintype.card (RGood n) = 8 * n ^ 2 + 3 * n + 1 := by
  rw [Fintype.card_sum, Fintype.card_sum, Fintype.card_prod, card_SArc]; simp; ring

/-! ### Fact 0 -/

section Fact0

variable {T Θ : Type*} [Fintype T] [DecidableEq T] [Fintype Θ]

/-- Best response over the simplex ⇔ support in the argmax. -/
theorem simplex_br (u x : T → ℚ) (hx : BSSG.IsDist x) :
    (∀ y, BSSG.IsDist y → ∑ t, y t * u t ≤ ∑ t, x t * u t) ↔
      ∀ k, 0 < x k → ∀ j, u j ≤ u k := by
  constructor
  · intro H k hk j
    by_contra hlt
    push Not at hlt
    have hjk : j ≠ k := by rintro rfl; exact lt_irrefl _ hlt
    set y : T → ℚ := fun t => x t + (if t = j then x k else 0) - (if t = k then x k else 0)
    have hy : BSSG.IsDist y := by
      refine ⟨fun t => ?_, ?_⟩
      · simp only [y]
        by_cases htk : t = k
        · subst htk; simp [hjk.symm]
        · have := hx.1 t; split_ifs <;> linarith
      · simp only [y, sum_sub_distrib, sum_add_distrib, sum_ite_eq', mem_univ, ite_true, hx.2]
        ring
    have := H y hy
    simp only [y, add_mul, sub_mul, sum_sub_distrib, sum_add_distrib, ite_mul, zero_mul,
      sum_ite_eq', mem_univ, ite_true] at this
    nlinarith
  · intro H y hy
    have hne : (univ : Finset T).Nonempty := by
      by_contra hne
      rw [not_nonempty_iff_eq_empty] at hne
      have := hx.2; rw [hne, sum_empty] at this; exact zero_ne_one this
    obtain ⟨m, -, hm⟩ := exists_max_image univ u hne
    have h1 : ∑ t, y t * u t ≤ ∑ t, y t * u m :=
      sum_le_sum fun t _ => mul_le_mul_of_nonneg_left (hm t (mem_univ _)) (hy.1 t)
    have h2 : ∑ t, x t * u t = ∑ t, x t * u m := by
      refine sum_congr rfl fun t _ => ?_
      rcases (hx.1 t).lt_or_eq with h | h
      · rw [le_antisymm (hm t (mem_univ _)) (H t h m)]
      · rw [← h]; ring
    rw [← sum_mul] at h1 h2
    rw [hy.2] at h1; rw [hx.2] at h2
    linarith

variable (G : BSSG T Θ)

theorem attEU_eq (θ : Θ) (δ : Finset T → ℚ) (τ : T → ℚ) (hδ : ∑ S, δ S = 1) :
    G.attEU θ δ τ = ∑ t, τ t * G.U θ t (BSSG.coverage δ) := by
  unfold BSSG.attEU BSSG.U BSSG.coverage
  simp_rw [mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun t _ => ?_
  have : ∀ S : Finset T, δ S * (τ t * if t ∈ S then G.ua1 θ t else G.ua0 θ t) =
      τ t * (δ S * G.ua0 θ t) - τ t * ((G.ua0 θ t - G.ua1 θ t) * (δ S * if t ∈ S then 1 else 0)) := by
    intro S; split_ifs <;> ring
  simp_rw [this, sum_sub_distrib, ← mul_sum, ← sum_mul, hδ]
  ring

theorem defEU_eq (hd0 : ∀ t, G.ud0 t = 0) (hd1 : ∀ t, G.ud1 t = 1)
    (δ : Finset T → ℚ) (σ : Θ → T → ℚ) :
    G.defEU δ σ = ∑ t, BSSG.coverage δ t * G.load σ t := by
  unfold BSSG.defEU BSSG.load
  simp only [hd0, hd1]
  change ∑ θ, G.prior θ * ∑ t, σ θ t * BSSG.coverage δ t = _
  simp_rw [mul_sum]
  rw [sum_comm]
  exact sum_congr rfl fun t _ => sum_congr rfl fun θ _ => by ring

theorem coverage_dist (hr : G.r = 1) (δ : Finset T → ℚ) (hδ : G.IsDefMixed δ) :
    BSSG.IsDist (BSSG.coverage δ) := by
  refine ⟨fun t => sum_nonneg fun S _ => mul_nonneg (hδ.1.1 S) (by split_ifs <;> norm_num), ?_⟩
  unfold BSSG.coverage
  rw [sum_comm]
  refine Eq.trans ?_ hδ.1.2
  refine sum_congr rfl fun S _ => ?_
  rw [← mul_sum]
  by_cases h0 : δ S = 0
  · simp [h0]
  · have hc := hδ.2 S h0
    rw [hr] at hc
    obtain ⟨a, rfl⟩ := card_eq_one.mp hc
    simp

theorem coverage_singletonDefense (ξ : T → ℚ) : BSSG.coverage (BSSG.singletonDefense ξ) = ξ := by
  funext t
  unfold BSSG.coverage BSSG.singletonDefense
  simp_rw [sum_mul]
  rw [sum_comm]
  simp only [ite_mul, zero_mul]
  simp [sum_ite_eq']

theorem singletonDefense_mixed (hr : G.r = 1) (ξ : T → ℚ) (hξ : BSSG.IsDist ξ) :
    G.IsDefMixed (BSSG.singletonDefense ξ) := by
  refine ⟨⟨fun S => sum_nonneg fun t _ => by split_ifs <;> simp [hξ.1 t], ?_⟩, ?_⟩
  · unfold BSSG.singletonDefense
    rw [sum_comm]
    simp [sum_ite_eq', hξ.2]
  · intro S hS
    unfold BSSG.singletonDefense at hS
    obtain ⟨t, -, ht⟩ := exists_ne_zero_of_sum_ne_zero hS
    have : S = {t} := by by_contra h; simp [h] at ht
    rw [this, hr, card_singleton]

theorem fact0_main (hr : G.r = 1) (hd0 : ∀ t, G.ud0 t = 0) (hd1 : ∀ t, G.ud1 t = 1)
    (δ : Finset T → ℚ) (σ : Θ → T → ℚ) :
    G.IsBNE δ σ ↔ G.IsDefMixed δ ∧ G.IsCoverageBNE (BSSG.coverage δ) σ := by
  constructor
  · rintro ⟨hδ, hσ, hatt, hdef⟩
    have hcov := Emb.coverage_dist G hr δ hδ
    refine ⟨hδ, hcov, hσ, ?_, ?_⟩
    · intro θ
      have := (simplex_br (fun t => G.U θ t (BSSG.coverage δ)) (σ θ) (hσ θ)).mp
      apply this
      intro y hy
      have := hatt θ y hy
      rwa [Emb.attEU_eq G θ δ y hδ.1.2, Emb.attEU_eq G θ δ (σ θ) hδ.1.2] at this
    · apply (simplex_br (G.load σ) (BSSG.coverage δ) hcov).mp
      intro y hy
      have := hdef _ (Emb.singletonDefense_mixed G hr y hy)
      rwa [Emb.defEU_eq G hd0 hd1, Emb.defEU_eq G hd0 hd1, coverage_singletonDefense] at this
  · rintro ⟨hδ, hcov, hσ, hatt, hdef⟩
    refine ⟨hδ, hσ, ?_, ?_⟩
    · intro θ τ hτ
      rw [Emb.attEU_eq G θ δ τ hδ.1.2, Emb.attEU_eq G θ δ (σ θ) hδ.1.2]
      exact (simplex_br (fun t => G.U θ t (BSSG.coverage δ)) (σ θ) (hσ θ)).mpr (hatt θ) τ hτ
    · intro δ' hδ'
      rw [Emb.defEU_eq G hd0 hd1, Emb.defEU_eq G hd0 hd1]
      exact (simplex_br (G.load σ) (BSSG.coverage δ) hcov).mpr hdef _
        (Emb.coverage_dist G hr δ' hδ')

end Fact0

/-! ### Lemma 8 -/

section L8

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

/-- Weighted load `Σ_θ w_θ σ_θ(k)` (prior times total weight). -/
def wload (Mk : Market I J) (σ : MType I J → MTarget I J → ℚ) (k : MTarget I J) : ℚ :=
  ∑ θ, Mk.gWeight θ * σ θ k

theorem sum_unit' (f : Unit → ℚ) : ∑ u, f u = f () := Fintype.sum_unique f

set_option maxHeartbeats 1000000 in
theorem lemma8_main (Mk : Market I J) (hwf : Mk.WellFormed) (hb : ∀ e ∈ Mk.E, 1 ≤ Mk.b e)
    (ξ : MTarget I J → ℚ) (σ : MType I J → MTarget I J → ℚ)
    (h : Mk.toGame.IsCoverageBNE ξ σ) :
    Mk.IsEquilibrium (Mk.decP ξ) (Mk.decV ξ) (Mk.decF σ) := by
  obtain ⟨hμ, hc, hbpos⟩ := hwf
  obtain ⟨hξ, hσ, hbr, hcov⟩ := h
  -- the constants `W`, `A`, `S`
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
  have hAS : 0 < Mk.gA / Mk.gS := div_pos (by linarith) hS0
  -- basic facts on strategies
  have hξ0 : ∀ k, 0 ≤ ξ k := hξ.1
  have hξ1 : ∀ k, ξ k ≤ 1 := fun k => by
    rw [← hξ.2]; exact single_le_sum (fun k _ => hξ0 k) (mem_univ k)
  have hσ0 : ∀ θ k, 0 ≤ σ θ k := fun θ => (hσ θ).1
  have hU : ∀ θ k, Mk.toGame.U θ k ξ = (Mk.gPay θ k).1 - (Mk.gPay θ k).2 * ξ k := by
    intro θ k; simp only [BSSG.U, Market.toGame]; ring
  -- pairs with payoff `-2 - ξ` are never used
  have hzero : ∀ θ k, Mk.gPay θ k = (-2, 1) → σ θ k = 0 := by
    intro θ k hk
    by_contra hne
    have hpos : 0 < σ θ k := lt_of_le_of_ne (hσ0 θ k) (Ne.symm hne)
    have hk' : Mk.toGame.U θ k ξ ≤ -2 := by rw [hU, hk]; linarith [hξ0 k]
    rcases θ with i | j | ⟨⟩
    · have := hbr _ _ hpos (.inr (.inr (.inl ())))
      rw [hU] at this; simp [Market.gPay] at this; linarith [hξ1 (.inr (.inr (.inl ())))]
    · have := hbr _ _ hpos (.inl j)
      rw [hU] at this; simp [Market.gPay] at this; linarith [hξ1 (.inl j)]
    · have := hbr _ _ hpos (.inr (.inr (.inr ())))
      rw [hU] at this; simp [Market.gPay] at this; linarith [hξ1 (.inr (.inr (.inr ())))]
  have hpayC : ∀ k : MTarget I J, k ≠ .inr (.inr (.inr ())) →
      Mk.gPay (.inr (.inr ())) k = (-2, 1) := by
    rintro (j | i | ⟨⟩ | ⟨⟩) hk <;> simp [Market.gPay] at hk ⊢
  have hpayD : ∀ j (k : MTarget I J), k ≠ .inl j → Mk.gPay (.inr (.inl j)) k = (-2, 1) := by
    rintro j (j' | i | ⟨⟩ | ⟨⟩) hk <;> simp [Market.gPay] at hk ⊢
    exact fun h' => absurd h' hk
  have hpayS_h : ∀ i, Mk.gPay (.inl i) (.inr (.inr (.inr ()))) = (-2, 1) := by
    intro i; simp [Market.gPay]
  have hpayS_g : ∀ i i', i' ≠ i → Mk.gPay (.inl i) (.inr (.inl i')) = (-2, 1) := by
    intro i i' h; simp [Market.gPay, h]
  have hpayS_j : ∀ i j, (i, j) ∉ Mk.E → Mk.gPay (.inl i) (.inl j) = (-2, 1) := by
    intro i j h; simp [Market.gPay, h]
  have hUo : ∀ i, Mk.toGame.U (.inl i) (.inr (.inr (.inl ()))) ξ = - ξ (.inr (.inr (.inl ()))) := by
    intro i; rw [hU]; simp [Market.gPay]
  have hUg : ∀ i, Mk.toGame.U (.inl i) (.inr (.inl i)) ξ = Mk.gA / Mk.gS - ξ (.inr (.inl i)) := by
    intro i; rw [hU]; simp [Market.gPay]
  have hUj : ∀ i j, (i, j) ∈ Mk.E →
      Mk.toGame.U (.inl i) (.inl j) ξ = Mk.a (i, j) / Mk.gS - Mk.b (i, j) * ξ (.inl j) := by
    intro i j h; rw [hU]; simp [Market.gPay, h]
  -- weighted loads
  have hwθ : ∀ θ, 0 < Mk.gWeight θ := by
    rintro (i | j | ⟨⟩)
    · exact hWμi i
    · simp only [Market.gWeight]; linarith [hWc j]
    · exact hWpos
  have hZ : 0 < ∑ θ, Mk.gWeight θ :=
    sum_pos (fun θ _ => hwθ θ) ⟨.inr (.inr ()), mem_univ _⟩
  have hload : ∀ k, Mk.toGame.load σ k = wload Mk σ k / ∑ θ, Mk.gWeight θ := by
    intro k; simp only [BSSG.load, Market.toGame, wload, sum_div]
    exact sum_congr rfl fun θ _ => by ring
  have hcov' : ∀ k, 0 < ξ k → ∀ j, wload Mk σ j ≤ wload Mk σ k := by
    intro k hk j
    have := hcov k hk j
    rwa [hload, hload, div_le_div_iff_of_pos_right hZ] at this
  have hexp : ∀ k, wload Mk σ k = ∑ i, (Mk.gW + Mk.mass i) * σ (.inl i) k +
      ∑ j, (Mk.gW - Mk.cap j) * σ (.inr (.inl j)) k + Mk.gW * σ (.inr (.inr ())) k := by
    intro k; simp only [wload, Fintype.sum_sum_type, sum_unit', Market.gWeight]; ring
  -- control and dedicated types
  have hσC : ∀ k, k ≠ .inr (.inr (.inr ())) → σ (.inr (.inr ())) k = 0 :=
    fun k hk => hzero _ _ (hpayC k hk)
  have hσCh : σ (.inr (.inr ())) (.inr (.inr (.inr ()))) = 1 := by
    have := (hσ (.inr (.inr ()))).2
    rwa [sum_eq_single_of_mem _ (mem_univ _) (fun k _ hk => hσC k hk)] at this
  have hσD : ∀ j k, k ≠ .inl j → σ (.inr (.inl j)) k = 0 :=
    fun j k hk => hzero _ _ (hpayD j k hk)
  have hσDj : ∀ j, σ (.inr (.inl j)) (.inl j) = 1 := by
    intro j
    have := (hσ (.inr (.inl j))).2
    rwa [sum_eq_single_of_mem _ (mem_univ _) (fun k _ hk => hσD j k hk)] at this
  have hwlH : wload Mk σ (.inr (.inr (.inr ()))) = Mk.gW := by
    rw [hexp, sum_eq_zero (fun i _ => by rw [hzero _ _ (hpayS_h i), mul_zero]),
      sum_eq_zero (fun (j : J) _ => by rw [hσD j _ (by simp), mul_zero]), hσCh]; ring
  have hwlG : ∀ i, wload Mk σ (.inr (.inl i)) = (Mk.gW + Mk.mass i) * σ (.inl i) (.inr (.inl i)) := by
    intro i
    rw [hexp, sum_eq_single i (fun i' _ hi' => by rw [hzero _ _ (hpayS_g i' i (Ne.symm hi')), mul_zero])
      (by simp), sum_eq_zero (fun (j : J) _ => by rw [hσD j _ (by simp), mul_zero]), hσC _ (by simp)]
    ring
  have hwlO : wload Mk σ (.inr (.inr (.inl ()))) =
      ∑ i, (Mk.gW + Mk.mass i) * σ (.inl i) (.inr (.inr (.inl ()))) := by
    rw [hexp, sum_eq_zero (fun (j : J) _ => by rw [hσD j _ (by simp), mul_zero]), hσC _ (by simp)]
    ring
  have hwlJ : ∀ j, wload Mk σ (.inl j) =
      (Mk.gW - Mk.cap j) + ∑ i, (Mk.gW + Mk.mass i) * σ (.inl i) (.inl j) := by
    intro j
    rw [hexp, sum_eq_single j (fun j' _ hj' => by
        rw [hσD j' _ (Sum.inl_injective.ne (Ne.symm hj')), mul_zero]) (by simp), hσDj,
      hσC _ (by simp)]
    ring
  -- a source type puts its mass on real options, its private target and the outside target
  have hsrc : ∀ i, ∑ j, σ (.inl i) (.inl j) + σ (.inl i) (.inr (.inl i)) +
      σ (.inl i) (.inr (.inr (.inl ()))) = 1 := by
    intro i
    have := (hσ (.inl i)).2
    simp only [Fintype.sum_sum_type, sum_unit'] at this
    rw [sum_eq_single i (fun i' _ hi' => hzero _ _ (hpayS_g i i' hi')) (by simp),
      hzero _ _ (hpayS_h i)] at this
    linarith
  -- (2) every source type puts weight `≥ W` on its private target; `ξ_o = 0`
  have hUlt : ∀ i (k : MTarget I J), k ≠ .inr (.inl i) → Mk.toGame.U (.inl i) k ξ < Mk.gA / Mk.gS := by
    rintro i (j | i' | ⟨⟩ | ⟨⟩) hk
    · by_cases hj : (i, j) ∈ Mk.E
      · rw [hUj i j hj]
        have h1 : Mk.a (i, j) / Mk.gS < Mk.gA / Mk.gS :=
          (div_lt_div_iff_of_pos_right hS0).mpr (hAa _ hj)
        have h2 : 0 ≤ Mk.b (i, j) * ξ (.inl j) := mul_nonneg (hbpos _ hj).le (hξ0 _)
        linarith
      · rw [hU, hpayS_j i j hj]; simp; linarith [hξ0 (.inl j)]
    · have hi' : i' ≠ i := fun h => hk (by rw [h])
      rw [hU, hpayS_g i i' hi']; simp; linarith [hξ0 (.inr (.inl i'))]
    · rw [hUo]; linarith [hξ0 (.inr (.inr (.inl ())))]
    · rw [hU, hpayS_h]; simp; linarith [hξ0 (.inr (.inr (.inr ())))]
  have hg0 : ∀ i, ξ (.inr (.inl i)) = 0 → σ (.inl i) (.inr (.inl i)) = 1 := by
    intro i h0
    have hk0 : ∀ k, k ≠ .inr (.inl i) → σ (.inl i) k = 0 := by
      intro k hk
      by_contra hne
      have hpos : 0 < σ (.inl i) k := lt_of_le_of_ne (hσ0 _ k) (Ne.symm hne)
      have := hbr _ _ hpos (.inr (.inl i))
      rw [hUg, h0] at this
      linarith [hUlt i k hk]
    have := (hσ (.inl i)).2
    rwa [sum_eq_single_of_mem _ (mem_univ _) (fun k _ hk => hk0 k hk)] at this
  have hg : ∀ i, Mk.gW ≤ (Mk.gW + Mk.mass i) * σ (.inl i) (.inr (.inl i)) := by
    intro i
    by_cases hx : 0 < ξ (.inr (.inl i))
    · have := hcov' _ hx (.inr (.inr (.inr ())))
      rwa [hwlH, hwlG] at this
    · have h0 : ξ (.inr (.inl i)) = 0 := le_antisymm (not_lt.mp hx) (hξ0 _)
      rw [hg0 i h0]; linarith [hμ i]
  have hσo : ∀ i, (Mk.gW + Mk.mass i) * σ (.inl i) (.inr (.inr (.inl ()))) ≤ Mk.mass i := by
    intro i
    have hs := hsrc i
    have hj0 : 0 ≤ ∑ j, σ (.inl i) (.inl j) := sum_nonneg fun j _ => hσ0 _ _
    have h1 : σ (.inl i) (.inr (.inl i)) + σ (.inl i) (.inr (.inr (.inl ()))) ≤ 1 := by linarith
    have h2 := mul_le_mul_of_nonneg_left h1 (hWμi i).le
    rw [mul_add, mul_one] at h2
    linarith [hg i]
  have hξo : ξ (.inr (.inr (.inl ()))) = 0 := by
    by_contra hne
    have hpos : 0 < ξ (.inr (.inr (.inl ()))) := lt_of_le_of_ne (hξ0 _) (Ne.symm hne)
    have := hcov' _ hpos (.inr (.inr (.inr ())))
    rw [hwlH, hwlO] at this
    have : ∑ i, (Mk.gW + Mk.mass i) * σ (.inl i) (.inr (.inr (.inl ()))) ≤ ∑ i, Mk.mass i :=
      sum_le_sum fun i _ => hσo i
    linarith
  have hv0 : ∀ i, 0 ≤ Mk.toGame.typeValue (.inl i) ξ := by
    intro i
    refine le_trans ?_ (le_sup' (fun k => Mk.toGame.U (.inl i) k ξ) (mem_univ (.inr (.inr (.inl ())))))
    simp only [hUo, hξo]; norm_num
  have hσg_pos : ∀ i, 0 < σ (.inl i) (.inr (.inl i)) := by
    intro i
    by_contra hn
    push Not at hn
    have := mul_le_mul_of_nonneg_left hn (hWμi i).le
    linarith [hg i]
  -- (3) coverage of real and private targets is small, so `ξ_h > 0`
  have hξg : ∀ i, ξ (.inr (.inl i)) ≤ Mk.gA / Mk.gS := by
    intro i
    have := hbr _ _ (hσg_pos i) (.inr (.inr (.inl ())))
    rw [hUo, hUg, hξo] at this
    linarith
  have hξj : ∀ j, ξ (.inl j) < Mk.gA / Mk.gS := by
    intro j
    by_cases hx : 0 < ξ (.inl j)
    · have hl := hcov' _ hx (.inr (.inr (.inr ())))
      rw [hwlH, hwlJ] at hl
      have hpos : 0 < ∑ i, (Mk.gW + Mk.mass i) * σ (.inl i) (.inl j) := by linarith [hc j]
      obtain ⟨i, -, hi⟩ := exists_ne_zero_of_sum_ne_zero hpos.ne'
      have hσi : 0 < σ (.inl i) (.inl j) :=
        lt_of_le_of_ne (hσ0 _ _) (Ne.symm (right_ne_zero_of_mul hi))
      have hE : (i, j) ∈ Mk.E := by
        by_contra hE; exact hσi.ne' (hzero _ _ (hpayS_j i j hE))
      have := hbr _ _ hσi (.inr (.inr (.inl ())))
      rw [hUo, hUj i j hE, hξo] at this
      have h1 : ξ (.inl j) ≤ Mk.b (i, j) * ξ (.inl j) := le_mul_of_one_le_left (hξ0 _) (hb _ hE)
      have h2 : Mk.a (i, j) / Mk.gS < Mk.gA / Mk.gS :=
        (div_lt_div_iff_of_pos_right hS0).mpr (hAa _ hE)
      linarith
    · linarith
  have hξh : 0 < ξ (.inr (.inr (.inr ()))) := by
    have hs := hξ.2
    simp only [Fintype.sum_sum_type, sum_unit'] at hs
    have h1 : ∑ j, ξ (.inl j) ≤ ∑ _j : J, Mk.gA / Mk.gS := sum_le_sum fun j _ => (hξj j).le
    have h2 : ∑ i, ξ (.inr (.inl i)) ≤ ∑ _i : I, Mk.gA / Mk.gS := sum_le_sum fun i _ => hξg i
    rw [sum_const, card_univ, nsmul_eq_mul] at h1 h2
    have h3 : ((Fintype.card I : ℚ) + Fintype.card J) * (Mk.gA / Mk.gS) < 1 := by
      rw [← mul_div_assoc, div_lt_one hS0]; exact hSA
    rw [add_mul] at h3
    linarith
  have hmax : ∀ k, wload Mk σ k ≤ Mk.gW := fun k => hwlH ▸ hcov' _ hξh k
  have hgeq : ∀ i, (Mk.gW + Mk.mass i) * σ (.inl i) (.inr (.inl i)) = Mk.gW := by
    intro i
    exact le_antisymm (hwlG i ▸ hmax _) (hg i)
  have hrow : ∀ i, (Mk.gW + Mk.mass i) * ∑ j, σ (.inl i) (.inl j) +
      (Mk.gW + Mk.mass i) * σ (.inl i) (.inr (.inr (.inl ()))) = Mk.mass i := by
    intro i
    linear_combination (Mk.gW + Mk.mass i) * hsrc i - hgeq i
  -- (4) decoding
  have hrowSum : ∀ i, Mk.rowSum (Mk.decF σ) i = (Mk.gW + Mk.mass i) * ∑ j, σ (.inl i) (.inl j) := by
    intro i
    unfold Market.rowSum Market.decF
    rw [mul_sum, ← sum_filter_of_ne (p := fun j => (i, j) ∈ Mk.E) (fun j _ hj => by
      by_contra hE; exact hj (by rw [hzero _ _ (hpayS_j i j hE), mul_zero]))]
    apply sum_nbij' Prod.snd (fun j => (i, j))
    · rintro ⟨a, b⟩ he
      simp only [mem_filter, mem_univ, true_and] at he ⊢
      obtain ⟨he, rfl⟩ := he; exact he
    · intro j hj
      simp only [mem_filter, mem_univ, true_and] at hj ⊢
      exact ⟨hj, trivial⟩
    · rintro ⟨a, b⟩ he
      simp only [mem_filter] at he
      simp [he.2]
    · intro j _; rfl
    · rintro ⟨a, b⟩ he
      simp only [mem_filter] at he
      simp only at he ⊢; rw [he.2]
  have hcolSum : ∀ j, Mk.colSum (Mk.decF σ) j = ∑ i, (Mk.gW + Mk.mass i) * σ (.inl i) (.inl j) := by
    intro j
    unfold Market.colSum Market.decF
    rw [← sum_filter_of_ne (p := fun i => (i, j) ∈ Mk.E) (fun i _ hi => by
      by_contra hE; exact hi (by rw [hzero _ _ (hpayS_j i j hE), mul_zero]))]
    apply sum_nbij' Prod.fst (fun i => (i, j))
    · rintro ⟨a, b⟩ he
      simp only [mem_filter, mem_univ, true_and] at he ⊢
      obtain ⟨he, rfl⟩ := he; exact he
    · intro i hi
      simp only [mem_filter, mem_univ, true_and] at hi ⊢
      exact ⟨hi, trivial⟩
    · rintro ⟨a, b⟩ he
      simp only [mem_filter] at he
      simp [he.2]
    · intro i _; rfl
    · rintro ⟨a, b⟩ he
      simp only [mem_filter] at he
      simp only at he ⊢; rw [he.2]
  have hS1 : ∀ x : ℚ, Mk.gS * (x / Mk.gS) = x := fun x => mul_div_cancel₀ x hS0.ne'
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j; exact mul_nonneg hS0.le (hξ0 _)
  · intro i; exact mul_nonneg hS0.le (hv0 i)
  · rintro ⟨i, j⟩ _; exact mul_nonneg (hWμi i).le (hσ0 _ _)
  · rintro ⟨i, j⟩ he
    have h1 : Mk.toGame.U (.inl i) (.inl j) ξ ≤ Mk.toGame.typeValue (.inl i) ξ :=
      le_sup' (fun k => Mk.toGame.U (.inl i) k ξ) (mem_univ (.inl j))
    rw [hUj i j he] at h1
    have h2 := mul_le_mul_of_nonneg_left h1 hS0.le
    rw [mul_sub, hS1] at h2
    simp only [Market.decV, Market.decP]
    linarith
  · rintro ⟨i, j⟩ he hf
    have hσp : 0 < σ (.inl i) (.inl j) :=
      lt_of_mul_lt_mul_left (by rw [mul_zero]; exact hf) (hWμi i).le
    have hv : Mk.toGame.typeValue (.inl i) ξ = Mk.toGame.U (.inl i) (.inl j) ξ :=
      le_antisymm (sup'_le _ _ fun k _ => hbr _ _ hσp k)
        (le_sup' (fun k => Mk.toGame.U (.inl i) k ξ) (mem_univ (.inl j)))
    simp only [Market.decV, Market.decP]
    rw [hv, hUj i j he, mul_sub, hS1]; ring
  · intro i; rw [hrowSum]; linarith [hrow i, mul_nonneg (hWμi i).le (hσ0 (.inl i) (.inr (.inr (.inl ()))))]
  · intro i hv
    have ho : σ (.inl i) (.inr (.inr (.inl ()))) = 0 := by
      by_contra hne
      have hpos := lt_of_le_of_ne (hσ0 _ _) (Ne.symm hne)
      have : Mk.toGame.typeValue (.inl i) ξ = Mk.toGame.U (.inl i) (.inr (.inr (.inl ()))) ξ :=
        le_antisymm (sup'_le _ _ fun k _ => hbr _ _ hpos k)
          (le_sup' (fun k => Mk.toGame.U (.inl i) k ξ) (mem_univ _))
      rw [hUo, hξo, neg_zero] at this
      simp only [Market.decV, this, mul_zero, lt_irrefl] at hv
    rw [hrowSum]; have := hrow i; rw [ho, mul_zero, add_zero] at this; exact this
  · intro j; rw [hcolSum]; have := hmax (.inl j); rw [hwlJ] at this; linarith
  · intro j hP
    have hx : 0 < ξ (.inl j) := pos_of_mul_pos_right hP hS0.le
    have h1 := hcov' _ hx (.inr (.inr (.inr ())))
    have h2 := hmax (.inl j)
    rw [hwlH, hwlJ] at h1
    rw [hwlJ] at h2
    rw [hcolSum]; linarith

end L8

end Emb

theorem fact0_proof {T Θ : Type*} [Fintype T] [DecidableEq T] [Fintype Θ] (G : BSSG T Θ)
    (hr : G.r = 1) (hd0 : ∀ t, G.ud0 t = 0) (hd1 : ∀ t, G.ud1 t = 1)
    (δ : Finset T → ℚ) (σ : Θ → T → ℚ) :
    G.IsBNE δ σ ↔ G.IsDefMixed δ ∧ G.IsCoverageBNE (BSSG.coverage δ) σ :=
  Emb.fact0_main G hr hd0 hd1 δ σ

theorem fact0_realize_proof {T Θ : Type*} [Fintype T] [DecidableEq T] [Fintype Θ] (G : BSSG T Θ)
    (hr : G.r = 1) (hd0 : ∀ t, G.ud0 t = 0) (hd1 : ∀ t, G.ud1 t = 1)
    (ξ : T → ℚ) (σ : Θ → T → ℚ) (h : G.IsCoverageBNE ξ σ) :
    G.IsBNE (BSSG.singletonDefense ξ) σ ∧ BSSG.coverage (BSSG.singletonDefense ξ) = ξ := by
  have hc := Emb.coverage_singletonDefense ξ
  refine ⟨(Emb.fact0_main G hr hd0 hd1 _ σ).mpr ⟨Emb.singletonDefense_mixed G hr ξ h.1, ?_⟩, hc⟩
  rw [hc]; exact h

theorem red_sizes_proof (n : ℕ) :
    Fintype.card (RTarget n) = 12 * n ^ 2 + 6 * n + 3 ∧
      Fintype.card (RType n) = 12 * n ^ 2 + 6 * n + 2 := by
  simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, Fintype.card_option,
    Fintype.card_bool, Fintype.card_unit]
  constructor <;> ring

theorem lemma8_proof {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (Mk : Market I J) (hwf : Mk.WellFormed) (hb : ∀ e ∈ Mk.E, 1 ≤ Mk.b e)
    (ξ : MTarget I J → ℚ) (σ : MType I J → MTarget I J → ℚ)
    (h : Mk.toGame.IsCoverageBNE ξ σ) :
    Mk.IsEquilibrium (Mk.decP ξ) (Mk.decV ξ) (Mk.decF σ) :=
  Emb.lemma8_main Mk hwf hb ξ σ h

/-- Sizes of the §5 market: `4n² + 3n` buyers and `8n² + 3n + 1` goods. -/
theorem red_market_sizes (n : ℕ) :
    Fintype.card (RBuyer n) = 4 * n ^ 2 + 3 * n ∧ Fintype.card (RGood n) = 8 * n ^ 2 + 3 * n + 1 :=
  ⟨Emb.card_RBuyer n, Emb.card_RGood n⟩

end Bssg

