import Mathlib
import BssgProofs.MarketGame.Statements
import BssgProofs.Proofs.Embedding
import BssgProofs.Proofs.Existence

/-!
# Market → game (book Chapter 3): proofs

* §1 row rescaling (`rescaleEquiv_proof`, `rescaleEquivBack_proof`, `nuSpec_proof`,
  `rescaledWF_proof`);
* §2 the one-call reduction with the frozen `toGame` (`composeCoverage_proof`,
  `composeBNE_proof`, `composeLift_proof`), reusing `lemma8_proof`, `fact0_proof`,
  `Exist.lift_bne`, `fact0_realize_proof`;
* §3 Chapter 3's `Γ_ω` (`toGameW_gW_proof`, `decodeW_proof`, `omegaDecode_proof`,
  `omegaCompose_proof`); `decodeW_proof` is the proof of `Emb.lemma8_main` with `Mk.gW`
  replaced by an arbitrary `W` with `W > Σμ`, `W > c_j`.
-/

namespace Bssg
namespace MarketGame

open Finset

set_option linter.unusedSectionVars false

/-! ## 1. Row rescaling -/

section Rescale

variable {I J : Type*} [DecidableEq I] [DecidableEq J]

theorem rescale_rowSum (Mk : Market I J) (ν : I → ℚ) (f : I × J → ℚ) (i : I) :
    (rescale Mk ν).rowSum f i = Mk.rowSum f i := rfl

theorem rescale_colSum (Mk : Market I J) (ν : I → ℚ) (f : I × J → ℚ) (j : J) :
    (rescale Mk ν).colSum f j = Mk.colSum f j := rfl

/-- Forward map. -/
theorem rescale_up (Mk : Market I J) (ν : I → ℚ) (hν : ∀ i, 0 < ν i) (P : J → ℚ) (v : I → ℚ)
    (f : I × J → ℚ) (h : Mk.IsEquilibrium P v f) :
    (rescale Mk ν).IsEquilibrium P (upV ν v) f := by
  obtain ⟨hP, hv, hf, ha, hb, hcl, hce, hdl, hde⟩ := h
  refine ⟨hP, fun i => mul_nonneg (hν i).le (hv i), hf, ?_, ?_, hcl, ?_, hdl, hde⟩
  · intro e he
    have := mul_le_mul_of_nonneg_left (ha e he) (hν e.1).le
    simp only [rescale, upV]; linarith
  · intro e he hfe
    simp only [rescale, upV]; rw [hb e he hfe]; ring
  · intro i hi
    exact hce i (pos_of_mul_pos_right hi (hν i).le)

/-- Backward map. -/
theorem rescale_down (Mk : Market I J) (ν : I → ℚ) (hν : ∀ i, 0 < ν i) (P : J → ℚ) (v' : I → ℚ)
    (f : I × J → ℚ) (h : (rescale Mk ν).IsEquilibrium P v' f) :
    Mk.IsEquilibrium P (downV ν v') f := by
  obtain ⟨hP, hv, hf, ha, hb, hcl, hce, hdl, hde⟩ := h
  refine ⟨hP, fun i => div_nonneg (hv i) (hν i).le, hf, ?_, ?_, hcl, ?_, hdl, hde⟩
  · intro e he
    have h1 := ha e he
    simp only [rescale] at h1
    simp only [downV]
    rw [le_div_iff₀ (hν e.1)]; linarith
  · intro e he hfe
    have h1 := hb e he hfe
    simp only [rescale] at h1
    simp only [downV]
    rw [div_eq_iff (hν e.1).ne', h1]; ring
  · intro i hi
    exact hce i ((div_pos_iff_of_pos_right (hν i)).mp hi)

theorem down_up (ν v : I → ℚ) (hν : ∀ i, 0 < ν i) : downV ν (upV ν v) = v := by
  funext i; simp only [downV, upV]; field_simp [(hν i).ne']

theorem up_down (ν v : I → ℚ) (hν : ∀ i, 0 < ν i) : upV ν (downV ν v) = v := by
  funext i; simp only [downV, upV]; field_simp [(hν i).ne']

theorem rescaleEquiv_proof : RescaleEquiv I J := by
  intro Mk ν hν P v f
  refine ⟨rescale_up Mk ν hν P v f, fun h => ?_⟩
  have := rescale_down Mk ν hν P _ f h
  rwa [down_up ν v hν] at this

theorem rescaleEquivBack_proof : RescaleEquivBack I J := by
  intro Mk ν hν
  refine ⟨fun v => down_up ν v hν, fun v => up_down ν v hν, fun P v' f => ⟨rescale_down Mk ν hν P v' f,
    fun h => ?_⟩⟩
  have := rescale_up Mk ν hν P _ f h
  rwa [up_down ν v' hν] at this

theorem nu_pos (Mk : Market I J) (i : I) : 0 < nu Mk i := by
  unfold nu; positivity

theorem one_le_nu_mul (Mk : Market I J) (hwf : Mk.WellFormed) (e : I × J) (he : e ∈ Mk.E) :
    1 ≤ nu Mk e.1 * Mk.b e := by
  have hb := hwf.2.2 e he
  have hk : Nat.size (Mk.b e).den ≤ nuExp Mk e.1 :=
    le_sup (f := fun e => Nat.size (Mk.b e).den) (mem_filter.mpr ⟨he, rfl⟩)
  have hden : ((Mk.b e).den : ℚ) < 2 ^ nuExp Mk e.1 := by
    have h1 := Nat.lt_size_self (Mk.b e).den
    have h2 : 2 ^ Nat.size (Mk.b e).den ≤ 2 ^ nuExp Mk e.1 := Nat.pow_le_pow_right (by norm_num) hk
    exact_mod_cast lt_of_lt_of_le h1 h2
  have hnum : (1 : ℚ) ≤ (Mk.b e).num := by
    have : 0 < (Mk.b e).num := Rat.num_pos.mpr hb
    exact_mod_cast this
  have hd : (0 : ℚ) < (Mk.b e).den := by exact_mod_cast (Mk.b e).den_pos
  have hbe : Mk.b e = (Mk.b e).num / (Mk.b e).den := (Rat.num_div_den _).symm
  unfold nu
  rw [hbe, mul_div_assoc', le_div_iff₀ hd]
  nlinarith

theorem nuSpec_proof : NuSpec I J := by
  intro Mk hwf
  refine ⟨fun i => ⟨rfl, nu_pos Mk i⟩, fun e he => one_le_nu_mul Mk hwf e he, fun i => ?_⟩
  by_cases hne : (Mk.E.filter (fun e => e.1 = i)).Nonempty
  · right
    obtain ⟨e, he, hmax⟩ := exists_mem_eq_sup _ hne (fun e => Nat.size (Mk.b e).den)
    exact ⟨e, (mem_filter.mp he).1, (mem_filter.mp he).2, hmax⟩
  · left
    rw [not_nonempty_iff_eq_empty] at hne
    simp [nuExp, hne]

theorem rescaledWF_proof : RescaledWF I J := by
  intro Mk hwf
  refine ⟨⟨hwf.1, hwf.2.1, fun e he => ?_⟩, fun e he => one_le_nu_mul Mk hwf e he⟩
  exact mul_pos (nu_pos Mk e.1) (hwf.2.2 e he)

end Rescale

/-! ## 2. The one-call reduction with the frozen `toGame` -/

section Reduce

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

theorem composeCoverage_proof : ComposeCoverage I J := by
  intro Mk hwf ξ σ h
  obtain ⟨hwf', hb'⟩ := rescaledWF_proof Mk hwf
  exact rescale_down Mk (nu Mk) (nu_pos Mk) _ _ _ (lemma8_proof (rescaled Mk) hwf' hb' ξ σ h)

theorem composeBNE_proof : ComposeBNE I J := by
  intro Mk hwf δ σ h
  have hc := ((fact0_proof (reduce Mk) rfl (fun _ => rfl) (fun _ => rfl) δ σ).mp h).2
  exact composeCoverage_proof Mk hwf _ σ hc

theorem composeLift_proof : ComposeLift I J := by
  intro Mk hwf P v f heq
  obtain ⟨hwf', hb'⟩ := rescaledWF_proof Mk hwf
  have heq' := rescale_up Mk (nu Mk) (nu_pos Mk) P v f heq
  have hl := Exist.lift_bne (rescaled Mk) hwf' hb' P _ f heq'
  obtain ⟨hbne, hcov⟩ := fact0_realize_proof (reduce Mk) rfl (fun _ => rfl) (fun _ => rfl) _ _ hl
  refine ⟨_, _, hbne, ?_⟩
  simp only [decode, hcov]
  funext j
  have hS : 0 < (rescaled Mk).gS := by
    have hA : 0 ≤ (rescaled Mk).E.fold max 0 (rescaled Mk).a :=
      (le_fold_max _).mpr (Or.inl le_rfl)
    have hc : (0 : ℚ) ≤ (Fintype.card I : ℚ) + Fintype.card J := by positivity
    unfold Market.gS Market.gA; nlinarith
  simp only [Market.decP, Exist.liftξ]
  field_simp [hS.ne']

end Reduce

/-! ## 3. Chapter 3's `Γ_ω`: decoding for an arbitrary base weight `W` -/

section Omega

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

/-- Weighted load `Σ_θ w_θ σ_θ(k)` in `toGameW Mk W`. -/
def wloadW (Mk : Market I J) (W : ℚ) (σ : MType I J → MTarget I J → ℚ) (k : MTarget I J) : ℚ :=
  ∑ θ, gWeightW Mk W θ * σ θ k

set_option maxHeartbeats 1000000 in
/-- Proof of `Emb.lemma8_main` (Proofs/Embedding.lean) verbatim, with `Mk.gW` replaced by `W`;
the only facts about `W` used are `Σμ < W` and `c_j < W`. -/
theorem decodeW_proof : DecodeW I J := by
  intro Mk W hwf hb hWμ hWc ξ σ h
  obtain ⟨hμ, hc, hbpos⟩ := hwf
  obtain ⟨hξ, hσ, hbr, hcov⟩ := h
  -- the constants `W`, `A`, `S`
  have hsumμ : 0 ≤ ∑ i, Mk.mass i := sum_nonneg fun i _ => (hμ i).le
  have hWpos : 0 < W := by linarith
  have hWμi : ∀ i, 0 < W + Mk.mass i := fun i => by linarith [hμ i]
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
  have hU : ∀ θ k, (toGameW Mk W).U θ k ξ = (Mk.gPay θ k).1 - (Mk.gPay θ k).2 * ξ k := by
    intro θ k; simp only [BSSG.U, toGameW]; ring
  -- pairs with payoff `-2 - ξ` are never used
  have hzero : ∀ θ k, Mk.gPay θ k = (-2, 1) → σ θ k = 0 := by
    intro θ k hk
    by_contra hne
    have hpos : 0 < σ θ k := lt_of_le_of_ne (hσ0 θ k) (Ne.symm hne)
    have hk' : (toGameW Mk W).U θ k ξ ≤ -2 := by rw [hU, hk]; linarith [hξ0 k]
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
  have hUo : ∀ i, (toGameW Mk W).U (.inl i) (.inr (.inr (.inl ()))) ξ = - ξ (.inr (.inr (.inl ()))) := by
    intro i; rw [hU]; simp [Market.gPay]
  have hUg : ∀ i, (toGameW Mk W).U (.inl i) (.inr (.inl i)) ξ = Mk.gA / Mk.gS - ξ (.inr (.inl i)) := by
    intro i; rw [hU]; simp [Market.gPay]
  have hUj : ∀ i j, (i, j) ∈ Mk.E →
      (toGameW Mk W).U (.inl i) (.inl j) ξ = Mk.a (i, j) / Mk.gS - Mk.b (i, j) * ξ (.inl j) := by
    intro i j h; rw [hU]; simp [Market.gPay, h]
  -- weighted loads
  have hwθ : ∀ θ, 0 < gWeightW Mk W θ := by
    rintro (i | j | ⟨⟩)
    · exact hWμi i
    · simp only [gWeightW]; linarith [hWc j]
    · exact hWpos
  have hZ : 0 < ∑ θ, gWeightW Mk W θ :=
    sum_pos (fun θ _ => hwθ θ) ⟨.inr (.inr ()), mem_univ _⟩
  have hload : ∀ k, (toGameW Mk W).load σ k = wloadW Mk W σ k / ∑ θ, gWeightW Mk W θ := by
    intro k; simp only [BSSG.load, toGameW, wloadW, sum_div]
    exact sum_congr rfl fun θ _ => by ring
  have hcov' : ∀ k, 0 < ξ k → ∀ j, wloadW Mk W σ j ≤ wloadW Mk W σ k := by
    intro k hk j
    have := hcov k hk j
    rwa [hload, hload, div_le_div_iff_of_pos_right hZ] at this
  have hexp : ∀ k, wloadW Mk W σ k = ∑ i, (W + Mk.mass i) * σ (.inl i) k +
      ∑ j, (W - Mk.cap j) * σ (.inr (.inl j)) k + W * σ (.inr (.inr ())) k := by
    intro k; simp only [wloadW, Fintype.sum_sum_type, Emb.sum_unit', gWeightW]; ring
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
  have hwlH : wloadW Mk W σ (.inr (.inr (.inr ()))) = W := by
    rw [hexp, sum_eq_zero (fun i _ => by rw [hzero _ _ (hpayS_h i), mul_zero]),
      sum_eq_zero (fun (j : J) _ => by rw [hσD j _ (by simp), mul_zero]), hσCh]; ring
  have hwlG : ∀ i, wloadW Mk W σ (.inr (.inl i)) = (W + Mk.mass i) * σ (.inl i) (.inr (.inl i)) := by
    intro i
    rw [hexp, sum_eq_single i (fun i' _ hi' => by rw [hzero _ _ (hpayS_g i' i (Ne.symm hi')), mul_zero])
      (by simp), sum_eq_zero (fun (j : J) _ => by rw [hσD j _ (by simp), mul_zero]), hσC _ (by simp)]
    ring
  have hwlO : wloadW Mk W σ (.inr (.inr (.inl ()))) =
      ∑ i, (W + Mk.mass i) * σ (.inl i) (.inr (.inr (.inl ()))) := by
    rw [hexp, sum_eq_zero (fun (j : J) _ => by rw [hσD j _ (by simp), mul_zero]), hσC _ (by simp)]
    ring
  have hwlJ : ∀ j, wloadW Mk W σ (.inl j) =
      (W - Mk.cap j) + ∑ i, (W + Mk.mass i) * σ (.inl i) (.inl j) := by
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
    simp only [Fintype.sum_sum_type, Emb.sum_unit'] at this
    rw [sum_eq_single i (fun i' _ hi' => hzero _ _ (hpayS_g i i' hi')) (by simp),
      hzero _ _ (hpayS_h i)] at this
    linarith
  -- (2) every source type puts weight `≥ W` on its private target; `ξ_o = 0`
  have hUlt : ∀ i (k : MTarget I J), k ≠ .inr (.inl i) → (toGameW Mk W).U (.inl i) k ξ < Mk.gA / Mk.gS := by
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
  have hg : ∀ i, W ≤ (W + Mk.mass i) * σ (.inl i) (.inr (.inl i)) := by
    intro i
    by_cases hx : 0 < ξ (.inr (.inl i))
    · have := hcov' _ hx (.inr (.inr (.inr ())))
      rwa [hwlH, hwlG] at this
    · have h0 : ξ (.inr (.inl i)) = 0 := le_antisymm (not_lt.mp hx) (hξ0 _)
      rw [hg0 i h0]; linarith [hμ i]
  have hσo : ∀ i, (W + Mk.mass i) * σ (.inl i) (.inr (.inr (.inl ()))) ≤ Mk.mass i := by
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
    have : ∑ i, (W + Mk.mass i) * σ (.inl i) (.inr (.inr (.inl ()))) ≤ ∑ i, Mk.mass i :=
      sum_le_sum fun i _ => hσo i
    linarith
  have hv0 : ∀ i, 0 ≤ (toGameW Mk W).typeValue (.inl i) ξ := by
    intro i
    refine le_trans ?_ (le_sup' (fun k => (toGameW Mk W).U (.inl i) k ξ) (mem_univ (.inr (.inr (.inl ())))))
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
      have hpos : 0 < ∑ i, (W + Mk.mass i) * σ (.inl i) (.inl j) := by linarith [hc j]
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
    simp only [Fintype.sum_sum_type, Emb.sum_unit'] at hs
    have h1 : ∑ j, ξ (.inl j) ≤ ∑ _j : J, Mk.gA / Mk.gS := sum_le_sum fun j _ => (hξj j).le
    have h2 : ∑ i, ξ (.inr (.inl i)) ≤ ∑ _i : I, Mk.gA / Mk.gS := sum_le_sum fun i _ => hξg i
    rw [sum_const, card_univ, nsmul_eq_mul] at h1 h2
    have h3 : ((Fintype.card I : ℚ) + Fintype.card J) * (Mk.gA / Mk.gS) < 1 := by
      rw [← mul_div_assoc, div_lt_one hS0]; exact hSA
    rw [add_mul] at h3
    linarith
  have hmax : ∀ k, wloadW Mk W σ k ≤ W := fun k => by
    have := hcov' _ hξh k; rwa [hwlH] at this
  have hgeq : ∀ i, (W + Mk.mass i) * σ (.inl i) (.inr (.inl i)) = W := by
    intro i
    exact le_antisymm (hwlG i ▸ hmax _) (hg i)
  have hrow : ∀ i, (W + Mk.mass i) * ∑ j, σ (.inl i) (.inl j) +
      (W + Mk.mass i) * σ (.inl i) (.inr (.inr (.inl ()))) = Mk.mass i := by
    intro i
    linear_combination (W + Mk.mass i) * hsrc i - hgeq i
  -- (4) decoding
  have hrowSum : ∀ i, Mk.rowSum (decFW Mk W σ) i = (W + Mk.mass i) * ∑ j, σ (.inl i) (.inl j) := by
    intro i
    unfold Market.rowSum decFW
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
  have hcolSum : ∀ j, Mk.colSum (decFW Mk W σ) j = ∑ i, (W + Mk.mass i) * σ (.inl i) (.inl j) := by
    intro j
    unfold Market.colSum decFW
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
    have h1 : (toGameW Mk W).U (.inl i) (.inl j) ξ ≤ (toGameW Mk W).typeValue (.inl i) ξ :=
      le_sup' (fun k => (toGameW Mk W).U (.inl i) k ξ) (mem_univ (.inl j))
    rw [hUj i j he] at h1
    have h2 := mul_le_mul_of_nonneg_left h1 hS0.le
    rw [mul_sub, hS1] at h2
    simp only [decVW, Market.decP]
    linarith
  · rintro ⟨i, j⟩ he hf
    have hσp : 0 < σ (.inl i) (.inl j) :=
      lt_of_mul_lt_mul_left (by rw [mul_zero]; exact hf) (hWμi i).le
    have hv : (toGameW Mk W).typeValue (.inl i) ξ = (toGameW Mk W).U (.inl i) (.inl j) ξ :=
      le_antisymm (sup'_le _ _ fun k _ => hbr _ _ hσp k)
        (le_sup' (fun k => (toGameW Mk W).U (.inl i) k ξ) (mem_univ (.inl j)))
    simp only [decVW, Market.decP]
    rw [hv, hUj i j he, mul_sub, hS1]; ring
  · intro i; rw [hrowSum]; linarith [hrow i, mul_nonneg (hWμi i).le (hσ0 (.inl i) (.inr (.inr (.inl ()))))]
  · intro i hv
    have ho : σ (.inl i) (.inr (.inr (.inl ()))) = 0 := by
      by_contra hne
      have hpos := lt_of_le_of_ne (hσ0 _ _) (Ne.symm hne)
      have : (toGameW Mk W).typeValue (.inl i) ξ = (toGameW Mk W).U (.inl i) (.inr (.inr (.inl ()))) ξ :=
        le_antisymm (sup'_le _ _ fun k _ => hbr _ _ hpos k)
          (le_sup' (fun k => (toGameW Mk W).U (.inl i) k ξ) (mem_univ _))
      rw [hUo, hξo, neg_zero] at this
      simp only [decVW, this, mul_zero, lt_irrefl] at hv
    rw [hrowSum]; have := hrow i; rw [ho, mul_zero, add_zero] at this; exact this
  · intro j; rw [hcolSum]; have := hmax (.inl j); rw [hwlJ] at this; linarith
  · intro j hP
    have hx : 0 < ξ (.inl j) := pos_of_mul_pos_right hP hS0.le
    have h1 := hcov' _ hx (.inr (.inr (.inr ())))
    have h2 := hmax (.inl j)
    rw [hwlH, hwlJ] at h1
    rw [hwlJ] at h2
    rw [hcolSum]; linarith


theorem toGameW_gW_proof : ToGameW_gW I J := fun _ => rfl

theorem wOmega_gt (Mk : Market I J) (hwf : Mk.WellFormed) (ω : ℚ) (hω : 0 < ω) :
    (∑ i, Mk.mass i) < wOmega Mk ω ∧ ∀ j, Mk.cap j < wOmega Mk ω := by
  have hF0 : (0 : ℚ) ≤ univ.fold max 0 Mk.cap := (le_fold_max _).mpr (Or.inl le_rfl)
  have hFc : ∀ j, Mk.cap j ≤ univ.fold max 0 Mk.cap :=
    fun j => (le_fold_max _).mpr (Or.inr ⟨j, mem_univ _, le_rfl⟩)
  have hsumμ : 0 ≤ ∑ i, Mk.mass i := sum_nonneg fun i _ => (hwf.1 i).le
  have h1 : ∑ i, Mk.mass i < hatD Mk := by unfold hatD; linarith [le_max_left (∑ i, Mk.mass i) (univ.fold max 0 Mk.cap)]
  have h2 : ∀ j, Mk.cap j < hatD Mk := fun j => by
    unfold hatD; linarith [le_max_right (∑ i, Mk.mass i) (univ.fold max 0 Mk.cap), hFc j]
  have hD : 0 < hatD Mk := lt_of_le_of_lt hsumμ h1
  have h3 : hatD Mk ≤ wOmega Mk ω := by
    unfold wOmega
    have : 0 ≤ 2 / ω := by positivity
    nlinarith
  exact ⟨lt_of_lt_of_le h1 h3, fun j => lt_of_lt_of_le (h2 j) h3⟩

theorem omegaDecode_proof : OmegaDecode I J := by
  intro Mk ω hω hwf hb δ σ h
  have hc := ((fact0_proof (gameOmega Mk ω) rfl (fun _ => rfl) (fun _ => rfl) δ σ).mp h).2
  obtain ⟨h1, h2⟩ := wOmega_gt Mk hwf ω hω
  exact decodeW_proof Mk _ hwf hb h1 h2 _ σ hc

theorem omegaCompose_proof : OmegaCompose I J := by
  intro Mk ω hω hwf δ σ h
  obtain ⟨hwf', hb'⟩ := rescaledWF_proof Mk hwf
  exact rescale_down Mk (nu Mk) (nu_pos Mk) _ _ _ (omegaDecode_proof (rescaled Mk) ω hω hwf' hb' δ σ h)

end Omega

end MarketGame
end Bssg
