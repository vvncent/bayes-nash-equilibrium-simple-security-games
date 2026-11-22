import BssgProofs.Contraction.Statements
import BssgProofs.DirectLCP.Gap

/-!
# One `ℓ₁` contraction for the game: proofs

No `sorry`, `admit` or `axiom`.
-/

namespace Bssg
namespace Contraction

open Finset
open DirectLCP (aa bb dd wload score IsFeasibleCov IsMarginalBNE)

set_option linter.unusedSectionVars false

/-! ## Clipping -/

theorem clip_mono {l h a b : ℚ} (hab : a ≤ b) : clip l h a ≤ clip l h b := by
  unfold clip; exact min_le_min_left _ (max_le_max_left _ hab)

/-- `clip` is monotone and `1`-Lipschitz from above: `clip b − clip a ≤ b − a` for `a ≤ b`. -/
theorem clip_sub_le {l h a b : ℚ} (_hlh : l ≤ h) (hab : a ≤ b) :
    clip l h b - clip l h a ≤ b - a := by
  unfold clip
  simp only [max_def, min_def]
  split_ifs <;> linarith

theorem abs_clip_sub_le {l h a b : ℚ} (hlh : l ≤ h) : |clip l h a - clip l h b| ≤ |a - b| := by
  rcases le_total a b with hab | hab
  · have h1 := clip_sub_le hlh hab
    have h2 := clip_mono (l := l) (h := h) hab
    rw [abs_sub_comm, abs_of_nonneg (by linarith), abs_sub_comm, abs_of_nonneg (by linarith)]
    exact h1
  · have h1 := clip_sub_le hlh hab
    have h2 := clip_mono (l := l) (h := h) hab
    rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
    exact h1

theorem clip_mem {l h : ℚ} (hlh : l ≤ h) (a : ℚ) : l ≤ clip l h a ∧ clip l h a ≤ h := by
  unfold clip
  exact ⟨le_min hlh (le_max_left _ _), min_le_left _ _⟩

theorem clip_of_mem {l h a : ℚ} (h1 : l ≤ a) (h2 : a ≤ h) : clip l h a = a := by
  unfold clip; rw [max_eq_right h1, min_eq_right h2]

/-! ## The simplex projection -/

section Proj

variable {T : Type*} [Fintype T] [DecidableEq T] [Nonempty T]

theorem le_projTheta (u : T → ℚ) (S : Finset T) (hS : S.Nonempty) :
    (∑ h ∈ S, u h - 1) / S.card ≤ projTheta u :=
  le_sup' (fun S : Finset T => (∑ h ∈ S, u h - 1) / S.card) (mem_filter.mpr ⟨mem_univ _, hS⟩)

theorem projTheta_mono {u u' : T → ℚ} (h : ∀ j, u j ≤ u' j) : projTheta u ≤ projTheta u' := by
  unfold projTheta
  refine sup'_le _ _ fun S hS => le_trans ?_ (le_projTheta u' S (mem_filter.mp hS).2)
  have hc : (0 : ℚ) < S.card := by exact_mod_cast (mem_filter.mp hS).2.card_pos
  exact div_le_div_of_nonneg_right (by linarith [sum_le_sum fun j (_ : j ∈ S) => h j]) hc.le

theorem proj_nonneg (u : T → ℚ) (j : T) : 0 ≤ proj u j := le_max_left _ _

/-- `Σ_j max(0, u_j − θ) = 1`. -/
theorem proj_sum (u : T → ℚ) : ∑ j, proj u j = 1 := by
  set θ := projTheta u with hθ
  -- lower bound
  obtain ⟨S0, hS0, hS0eq⟩ := exists_mem_eq_sup' nonemptySubsets_nonempty
    (fun S : Finset T => (∑ h ∈ S, u h - 1) / S.card)
  have hS0ne : S0.Nonempty := (mem_filter.mp hS0).2
  have hc0 : (0 : ℚ) < S0.card := by exact_mod_cast hS0ne.card_pos
  have hθS0 : θ * S0.card = ∑ h ∈ S0, u h - 1 := by
    rw [hθ, projTheta, hS0eq]; field_simp
  have hlow : 1 ≤ ∑ j, proj u j := by
    calc (1 : ℚ) = ∑ h ∈ S0, (u h - θ) := by
            rw [sum_sub_distrib, sum_const, nsmul_eq_mul]; linarith
      _ ≤ ∑ h ∈ S0, proj u h := sum_le_sum fun h _ => le_max_right _ _
      _ ≤ ∑ j, proj u j := sum_le_sum_of_subset_of_nonneg (subset_univ _)
            fun j _ _ => proj_nonneg u j
  -- upper bound
  set S := univ.filter fun j => θ < u j with hS
  have hsplit : ∑ j, proj u j = ∑ j ∈ S, (u j - θ) := by
    rw [← sum_filter_add_sum_filter_not univ (fun j => θ < u j)]
    have h1 : ∑ j ∈ univ.filter (fun j => ¬ θ < u j), proj u j = 0 :=
      sum_eq_zero fun j hj => by
        have : u j ≤ θ := not_lt.mp (mem_filter.mp hj).2
        simp only [proj]; rw [← hθ]; exact max_eq_left (by linarith)
    rw [h1, add_zero]
    refine sum_congr rfl fun j hj => ?_
    have : θ < u j := (mem_filter.mp hj).2
    simp only [proj]; rw [← hθ]; exact max_eq_right (by linarith)
  by_cases hSne : S.Nonempty
  · have h := le_projTheta u S hSne
    rw [← hθ] at h
    have hc : (0 : ℚ) < S.card := by exact_mod_cast hSne.card_pos
    have : ∑ j ∈ S, u j - 1 ≤ θ * S.card := by rwa [div_le_iff₀ hc] at h
    have hup : ∑ j, proj u j ≤ 1 := by
      rw [hsplit, sum_sub_distrib, sum_const, nsmul_eq_mul]; linarith
    linarith
  · rw [not_nonempty_iff_eq_empty] at hSne
    rw [hsplit, hSne, sum_empty] at hlow
    linarith

theorem proj_le_one (u : T → ℚ) (j : T) : proj u j ≤ 1 := by
  rw [← proj_sum u]
  exact single_le_sum (fun k _ => proj_nonneg u k) (mem_univ j)

/-- [C, Lemma ueopl-proj (a)] in units of `u`: a positive coordinate is within `1` of the maximum. -/
theorem proj_pos_near_max (u : T → ℚ) (j : T) (hj : 0 < proj u j) (k : T) : u k < u j + 1 := by
  have h1 : projTheta u < u j := by
    by_contra h; push Not at h
    have : proj u j = 0 := max_eq_left (by linarith)
    linarith
  have h2 : u k - projTheta u ≤ 1 := le_trans (le_max_right _ _) (proj_le_one u k)
  linarith

/-- The projection decreases by at most the decrease of the input:
`u' ≤ u ⇒ y(u')_j ≥ y(u)_j − (u_j − u'_j)`. -/
theorem proj_lower (u u' : T → ℚ) (h : ∀ j, u' j ≤ u j) (j : T) :
    proj u j - (u j - u' j) ≤ proj u' j := by
  have hθ := projTheta_mono h
  unfold proj
  rcases le_total (u j - projTheta u) 0 with h1 | h1
  · rw [max_eq_left h1]; have := h j; linarith [le_max_left 0 (u' j - projTheta u')]
  · rw [max_eq_right h1]; linarith [le_max_right 0 (u' j - projTheta u')]

/-- `y` is the Euclidean projection of `u` onto the probability simplex [C, *The map*]. -/
theorem proj_euclidean (u : T → ℚ) (z : T → ℚ) (hz : BSSG.IsDist z) :
    ∑ j, (u j - proj u j) ^ 2 ≤ ∑ j, (u j - z j) ^ 2 := by
  set θ := projTheta u
  have hkey : ∀ j, (u j - proj u j) * (z j - proj u j) ≤ θ * (z j - proj u j) := by
    intro j
    rcases le_total (u j - θ) 0 with h1 | h1
    · have hp : proj u j = 0 := max_eq_left h1
      rw [hp]; have := hz.1 j; nlinarith
    · have hp : proj u j = u j - θ := max_eq_right h1
      rw [hp]; ring_nf; exact le_refl _
  have hsum : ∑ j, (u j - proj u j) * (z j - proj u j) ≤ 0 := by
    calc ∑ j, (u j - proj u j) * (z j - proj u j) ≤ ∑ j, θ * (z j - proj u j) :=
          sum_le_sum fun j _ => hkey j
      _ = θ * (∑ j, z j - ∑ j, proj u j) := by rw [← mul_sum, sum_sub_distrib]
      _ = 0 := by rw [hz.2, proj_sum]; ring
  have : ∑ j, (u j - z j) ^ 2 = ∑ j, (u j - proj u j) ^ 2 -
      2 * ∑ j, (u j - proj u j) * (z j - proj u j) + ∑ j, (z j - proj u j) ^ 2 := by
    rw [mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
    refine sum_congr rfl fun j _ => by ring
  rw [this]
  have : 0 ≤ ∑ j, (z j - proj u j) ^ 2 := sum_nonneg fun j _ => sq_nonneg _
  linarith

end Proj


/-! ## Constants -/

section Consts

variable {T Θ : Type*} [Fintype T] [DecidableEq T] [Fintype Θ] [DecidableEq Θ] [Nonempty T]
variable (G : BSSG T Θ)

theorem one_le_cH : 1 ≤ cH G := le_max_left _ _

theorem cN_pos : 0 < cN (Θ := Θ) (T := T) := Fintype.card_pos

theorem one_le_cQ : (1 : ℚ) ≤ cQ G := by
  have h1 : 1 ≤ cN (Θ := Θ) (T := T) * cH G :=
    Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (cN_pos (Θ := Θ) (T := T)).ne'
      (by have := one_le_cH G; omega))
  have : 1 ≤ cQ G := Nat.one_le_pow _ _ h1
  exact_mod_cast this

theorem g_pos : 0 < gThr G := by
  unfold gThr; have := one_le_cQ G; positivity

theorem g_le : gThr G ≤ 1 / 4 := by
  unfold gThr
  have := one_le_cQ G
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith

theorem σ_pos : 0 < cσ G := by unfold cσ; have := g_pos G; positivity
theorem κ_pos : 0 < cκ G := by unfold cκ; have := g_pos G; positivity
theorem κ_le : cκ G ≤ 1 / 32 := by unfold cκ; have := g_le G; linarith
theorem σ_eq : cσ G = gThr G / 8 := rfl
theorem κ_eq : cκ G = gThr G / 8 := rfl

theorem bMax_nonneg : 0 ≤ bMax G := (le_fold_max _).mpr (Or.inl le_rfl)

theorem bb_le_bMax (i : Θ) (j : T) : bb G i j ≤ bMax G :=
  (le_fold_max _).mpr (Or.inr ⟨(i, j), mem_univ _, le_rfl⟩)

theorem dMax_nonneg : 0 ≤ dMax G := (le_fold_max _).mpr (Or.inl le_rfl)

theorem dd_le_dMax (j : T) : dd G j ≤ dMax G :=
  (le_fold_max _).mpr (Or.inr ⟨j, mem_univ _, le_rfl⟩)

theorem abMax_nonneg : 0 ≤ abMax G := (le_fold_max _).mpr (Or.inl le_rfl)

theorem ab_le_abMax (i : Θ) (j : T) : |aa G i j| + bb G i j ≤ abMax G :=
  (le_fold_max _).mpr (Or.inr ⟨(i, j), mem_univ _, le_rfl⟩)

variable {G}

theorem dP_pos (hwf : G.WellFormed) (j : T) : 0 < dP G j := by
  unfold dP; have := DirectLCP.dd_nonneg G hwf j; have := g_pos G; positivity

theorem dP_le_dBar (j : T) : dP G j ≤ dBar G := le_sup' (dP G) (mem_univ j)

theorem dBar_pos (hwf : G.WellFormed) : 0 < dBar G :=
  lt_of_lt_of_le (dP_pos hwf (Classical.arbitrary T)) (dP_le_dBar _)

theorem dBar_le : dBar G ≤ dMax G + gThr G / 16 :=
  sup'_le _ _ fun j _ => by unfold dP; linarith [dd_le_dMax G j]

theorem dBar_le_lamBox : dBar G ≤ lamBox G := by
  unfold lamBox; have := dBar_le (G := G); have := g_le G; linarith

theorem invSum_nonneg (hwf : G.WellFormed) : 0 ≤ invSum G :=
  sum_nonneg fun j _ => by have := dP_pos hwf j; positivity

theorem η_pos (hwf : G.WellFormed) : 0 < cη G := by
  unfold cη
  have := σ_pos G; have := κ_pos G; have := bMax_nonneg G; have := dBar_pos hwf
  have := invSum_nonneg hwf
  refine lt_min one_pos (lt_min (by positivity) (by positivity))

theorem η_le_one : cη G ≤ 1 := min_le_left _ _

theorem η_bmax : cη G * (1 + bMax G) ≤ cσ G := by
  have h : cη G ≤ cσ G / (1 + bMax G) := le_trans (min_le_right _ _) (min_le_left _ _)
  have := bMax_nonneg G
  rwa [le_div_iff₀ (by linarith)] at h

theorem η_kappa (hwf : G.WellFormed) :
    cη G * (4 * (1 + dBar G) * (1 + invSum G)) ≤ cκ G := by
  have h : cη G ≤ cκ G / (4 * (1 + dBar G) * (1 + invSum G)) :=
    le_trans (min_le_right _ _) (min_le_right _ _)
  have := dBar_pos hwf; have := invSum_nonneg hwf
  rwa [le_div_iff₀ (by positivity)] at h

theorem δ_pos (hwf : G.WellFormed) : 0 < cδ G := by
  unfold cδ
  have := η_pos hwf; have := g_pos G; have := dBar_pos hwf; have := bMax_nonneg G
  exact lt_min (by norm_num) (lt_min (by positivity) (by positivity))

theorem δ_le : cδ G ≤ 1 / 8 := min_le_left _ _

theorem δ_eta (hwf : G.WellFormed) : cδ G * (8 * (1 + dBar G)) ≤ cη G * gThr G := by
  have h : cδ G ≤ cη G * gThr G / (8 * (1 + dBar G)) :=
    le_trans (min_le_right _ _) (min_le_left _ _)
  have := dBar_pos hwf
  rwa [le_div_iff₀ (by positivity)] at h

theorem δ_bmax : cδ G * (8 * (1 + bMax G)) ≤ gThr G := by
  have h : cδ G ≤ gThr G / (8 * (1 + bMax G)) := le_trans (min_le_right _ _) (min_le_right _ _)
  have := bMax_nonneg G
  rwa [le_div_iff₀ (by positivity)] at h

/-- (eq:ueopl-const): `η d̄ Σ_j 1/d'_j ≤ κ/4 ≤ κ(1−2δ)`. -/
theorem ueopl_const (hwf : G.WellFormed) :
    cη G * dBar G * invSum G ≤ cκ G / 4 ∧ cκ G / 4 ≤ cκ G * (1 - 2 * cδ G) := by
  have h := η_kappa hwf
  have hη := η_pos hwf; have hD := dBar_pos hwf; have hI := invSum_nonneg hwf
  have hκ := κ_pos G; have hδ := δ_le (G := G)
  have h2 : cη G * (dBar G * invSum G) ≤ cη G * ((1 + dBar G) * (1 + invSum G)) :=
    mul_le_mul_of_nonneg_left (by nlinarith) hη.le
  constructor
  · have : cη G * dBar G * invSum G = cη G * (dBar G * invSum G) := by ring
    have h3 : cη G * (4 * (1 + dBar G) * (1 + invSum G)) =
      4 * (cη G * ((1 + dBar G) * (1 + invSum G))) := by ring
    linarith
  · nlinarith

theorem a0_mem (hwf : G.WellFormed) : 0 ≤ a0 G ∧ a0 G ≤ 1 := by
  unfold a0
  have hn : (0 : ℚ) < Fintype.card T := by exact_mod_cast Fintype.card_pos
  have hr : (G.r : ℚ) ≤ Fintype.card T := by exact_mod_cast hwf.1
  exact ⟨by positivity, (div_le_one hn).mpr hr⟩

theorem sum_a0 : ∑ _j : T, a0 G = G.r := by
  unfold a0
  have hn : (Fintype.card T : ℚ) ≠ 0 := by exact_mod_cast Fintype.card_pos.ne'
  rw [sum_const, card_univ, nsmul_eq_mul]; field_simp

end Consts

/-! ## The attacker response and the loads -/

section Loads

variable {T Θ : Type*} [Fintype T] [DecidableEq T] [Fintype Θ] [DecidableEq Θ] [Nonempty T]
variable {G : BSSG T Θ}

theorem yA_nonneg (x : T → ℚ) (i : Θ) (j : T) : 0 ≤ yA G x i j := proj_nonneg _ _
theorem yA_le_one (x : T → ℚ) (i : Θ) (j : T) : yA G x i j ≤ 1 := proj_le_one _ _
theorem yA_sum (x : T → ℚ) (i : Θ) : ∑ j, yA G x i j = 1 := proj_sum _

theorem wA_nonneg (hwf : G.WellFormed) (x : T → ℚ) (j : T) : 0 ≤ wA G x j :=
  sum_nonneg fun i _ => mul_nonneg (hwf.2.1 i) (yA_nonneg x i j)

theorem wA_le_one (hwf : G.WellFormed) (x : T → ℚ) (j : T) : wA G x j ≤ 1 := by
  calc wA G x j ≤ ∑ i, G.prior i := sum_le_sum fun i _ =>
        mul_le_of_le_one_right (hwf.2.1 i) (yA_le_one x i j)
    _ = 1 := hwf.2.2.1

theorem wA_sum (hwf : G.WellFormed) (x : T → ℚ) : ∑ j, wA G x j = 1 := by
  unfold wA
  rw [sum_comm]
  simp_rw [← mul_sum, yA_sum, mul_one]
  exact hwf.2.2.1

theorem wA_eq_wload (x : T → ℚ) (j : T) : wA G x j = wload (fA G x) j := rfl

/-- Raising coverage lowers each load by at most `b_max/σ` times the raise of its own target. -/
theorem wA_lower (hwf : G.WellFormed) (x x' : T → ℚ) (hx : ∀ j, x j ≤ x' j) (j : T) :
    wA G x j - bMax G / cσ G * (x' j - x j) ≤ wA G x' j := by
  have hσ := σ_pos G
  have hy : ∀ i, yA G x i j - bb G i j * (x' j - x j) / cσ G ≤ yA G x' i j := by
    intro i
    have hle : ∀ k, G.U i k x' / cσ G ≤ G.U i k x / cσ G := by
      intro k
      rw [DirectLCP.U_eq, DirectLCP.U_eq]
      have := DirectLCP.bb_nonneg G hwf i k; have := hx k
      exact div_le_div_of_nonneg_right (by nlinarith) hσ.le
    have := proj_lower _ _ hle j
    rw [DirectLCP.U_eq, DirectLCP.U_eq] at this
    unfold yA
    convert this using 2
    field_simp; ring
  have hsum : ∑ i, G.prior i * (bb G i j * (x' j - x j) / cσ G) ≤
      bMax G / cσ G * (x' j - x j) := by
    have hxj : 0 ≤ x' j - x j := by linarith [hx j]
    calc ∑ i, G.prior i * (bb G i j * (x' j - x j) / cσ G)
        ≤ ∑ i, G.prior i * (bMax G * (x' j - x j) / cσ G) := sum_le_sum fun i _ =>
          mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_right (bb_le_bMax G i j) hxj) hσ.le) (hwf.2.1 i)
      _ = bMax G / cσ G * (x' j - x j) := by rw [← sum_mul, hwf.2.2.1]; ring
  have : ∑ i, G.prior i * (yA G x i j - bb G i j * (x' j - x j) / cσ G) ≤ wA G x' j :=
    sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hy i) (hwf.2.1 i)
  have e : ∀ i, G.prior i * (yA G x i j - bb G i j * (x' j - x j) / cσ G) =
      G.prior i * yA G x i j - G.prior i * (bb G i j * (x' j - x j) / cσ G) := fun i => mul_sub _ _ _
  simp only [e, sum_sub_distrib] at this
  have hw : wA G x j = ∑ i, G.prior i * yA G x i j := rfl
  linarith

end Loads

/-! ## The cutoff `λ(s)` -/

section Lam

variable {T Θ : Type*} [Fintype T] [DecidableEq T] [Fintype Θ] [DecidableEq Θ] [Nonempty T]
variable {G : BSSG T Θ}

theorem den_pos : 0 < (1 - 2 * cδ G) * cκ G := by
  have := δ_le (G := G); have := κ_pos G; nlinarith

theorem lam_mem (hwf : G.WellFormed) (s : ℚ) : 0 ≤ lam G s ∧ lam G s ≤ dBar G :=
  clip_mem (dBar_pos hwf).le _

theorem lam_anti (hwf : G.WellFormed) {s s' : ℚ} (h : s ≤ s') : lam G s' ≤ lam G s := by
  unfold lam
  apply clip_mono
  have := dBar_pos hwf; have := den_pos (G := G)
  apply div_le_div_of_nonneg_right _ this.le
  nlinarith

/-- `λ` is Lipschitz with constant `d̄/((1−2δ)κ)`. -/
theorem lam_lip (hwf : G.WellFormed) {s s' : ℚ} (h : s ≤ s') :
    lam G s - lam G s' ≤ dBar G / ((1 - 2 * cδ G) * cκ G) * (s' - s) := by
  unfold lam
  have := dBar_pos hwf; have hd := den_pos (G := G)
  have hle : dBar G * ((1 - cδ G) * cκ G - s') / ((1 - 2 * cδ G) * cκ G) ≤
      dBar G * ((1 - cδ G) * cκ G - s) / ((1 - 2 * cδ G) * cκ G) :=
    div_le_div_of_nonneg_right (by nlinarith) hd.le
  refine le_trans (clip_sub_le this.le hle) (le_of_eq ?_)
  field_simp; ring

theorem lam_of_le (hwf : G.WellFormed) {s : ℚ} (h : s ≤ cδ G * cκ G) : lam G s = dBar G := by
  unfold lam clip
  have := dBar_pos hwf; have hd := den_pos (G := G)
  have : 1 ≤ ((1 - cδ G) * cκ G - s) / ((1 - 2 * cδ G) * cκ G) := by
    rw [le_div_iff₀ hd]; nlinarith
  have : dBar G ≤ dBar G * ((1 - cδ G) * cκ G - s) / ((1 - 2 * cδ G) * cκ G) := by
    rw [mul_div_assoc]; nlinarith
  rw [max_eq_right (by linarith), min_eq_left this]

theorem lam_of_ge (hwf : G.WellFormed) {s : ℚ} (h : (1 - cδ G) * cκ G ≤ s) : lam G s = 0 := by
  unfold lam clip
  have := dBar_pos hwf; have hd := den_pos (G := G)
  have : dBar G * ((1 - cδ G) * cκ G - s) / ((1 - 2 * cδ G) * cκ G) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by nlinarith) hd.le
  rw [max_eq_left this]
  exact min_eq_right (dBar_pos hwf).le

end Lam


/-! ## Contraction: a derivative-free argument

On every affine piece the book bounds the Jacobian of `(T, R̃)` (`R̃ = s + Σx − ΣT`, before
clipping `R`): nonnegative with column sums one.  We use the two order-theoretic facts this
encodes, proved without derivatives for all inputs: `(T, R̃)` is **monotone** in `(x, s)` and
**mass-preserving** (`Σ_j T_j + R̃ = s + Σ_j x_j`).  A monotone mass-preserving map is
`ℓ₁`-nonexpansive (Crandall–Tartar): with `m = u ⊔ u'`,
`Σ|G u − G u'| ≤ Σ (2 G m − G u − G u') = Σ (2m − u − u') = Σ|u − u'|`.
Clipping `R` and `q` and the factor `1 − δ` finish. -/

section Contract

variable {T Θ : Type*} [Fintype T] [DecidableEq T] [Fintype Θ] [DecidableEq Θ] [Nonempty T]
variable {G : BSSG T Θ}

theorem preT_mono (hwf : G.WellFormed) {x x' : T → ℚ} {s s' : ℚ} (hx : ∀ j, x j ≤ x' j)
    (hs : s ≤ s') (j : T) : preT G x s j ≤ preT G x' s' j := by
  have hw := wA_lower hwf x x' hx j
  have hl := lam_anti hwf hs
  have hη := η_pos hwf; have hb := η_bmax (G := G); have hσ := σ_pos G; have hd := dP_pos hwf j
  have hxj : 0 ≤ x' j - x j := by linarith [hx j]
  have h1 : cη G * (bMax G / cσ G * (x' j - x j)) ≤ x' j - x j := by
    have : cη G * bMax G ≤ cσ G := by nlinarith [bMax_nonneg G]
    calc cη G * (bMax G / cσ G * (x' j - x j)) = (cη G * bMax G / cσ G) * (x' j - x j) := by ring
      _ ≤ 1 * (x' j - x j) := mul_le_mul_of_nonneg_right ((div_le_one hσ).mpr this) hxj
      _ = _ := one_mul _
  have h2 : lam G s' / dP G j ≤ lam G s / dP G j := div_le_div_of_nonneg_right hl hd.le
  have h3 : cη G * (wA G x j - bMax G / cσ G * (x' j - x j)) ≤ cη G * wA G x' j :=
    mul_le_mul_of_nonneg_left hw hη.le
  have h4 : cη G * (lam G s' / dP G j) ≤ cη G * (lam G s / dP G j) :=
    mul_le_mul_of_nonneg_left h2 hη.le
  unfold preT
  nlinarith

theorem sum_lam_div (s : ℚ) : ∑ j, lam G s / dP G j = lam G s * invSum G := by
  unfold invSum; rw [mul_sum]; exact sum_congr rfl fun j _ => by ring

theorem sum_preT (hwf : G.WellFormed) (x : T → ℚ) (s : ℚ) :
    ∑ j, preT G x s j = ∑ j, x j + cη G - cη G * (lam G s * invSum G) := by
  unfold preT
  rw [sum_add_distrib, ← mul_sum, sum_sub_distrib, wA_sum hwf, sum_lam_div]; ring

/-- The total defender update rises by at most the total rise of the inputs. -/
theorem sum_preT_le (hwf : G.WellFormed) {x x' : T → ℚ} {s s' : ℚ} (hs : s ≤ s') :
    ∑ j, preT G x' s' j - ∑ j, preT G x s j ≤ (∑ j, x' j - ∑ j, x j) + (s' - s) := by
  rw [sum_preT hwf, sum_preT hwf]
  have hl := lam_lip hwf hs
  have hη := η_pos hwf; have hI := invSum_nonneg hwf; have hD := dBar_pos hwf
  have hden := den_pos (G := G)
  obtain ⟨hc1, hc2⟩ := ueopl_const hwf
  have hc : cη G * invSum G * (dBar G / ((1 - 2 * cδ G) * cκ G)) ≤ 1 := by
    rw [show cη G * invSum G * (dBar G / ((1 - 2 * cδ G) * cκ G)) =
      cη G * dBar G * invSum G / ((1 - 2 * cδ G) * cκ G) by ring, div_le_one hden]
    linarith
  have h5 : cη G * invSum G * (lam G s - lam G s') ≤
      cη G * invSum G * (dBar G / ((1 - 2 * cδ G) * cκ G) * (s' - s)) :=
    mul_le_mul_of_nonneg_left hl (mul_nonneg hη.le hI)
  have h6 : cη G * invSum G * (dBar G / ((1 - 2 * cδ G) * cκ G)) * (s' - s) ≤ 1 * (s' - s) :=
    mul_le_mul_of_nonneg_right hc (by linarith)
  nlinarith

theorem Tm_mono (hwf : G.WellFormed) {x x' : T → ℚ} {s s' : ℚ} (hx : ∀ j, x j ≤ x' j)
    (hs : s ≤ s') (j : T) : Tm G x s j ≤ Tm G x' s' j :=
  clip_mono (preT_mono hwf hx hs j)

theorem sum_Tm_le (hwf : G.WellFormed) {x x' : T → ℚ} {s s' : ℚ} (hx : ∀ j, x j ≤ x' j)
    (hs : s ≤ s') :
    ∑ j, Tm G x' s' j - ∑ j, Tm G x s j ≤ (∑ j, x' j - ∑ j, x j) + (s' - s) := by
  have : ∑ j, (Tm G x' s' j - Tm G x s j) ≤ ∑ j, (preT G x' s' j - preT G x s j) :=
    sum_le_sum fun j _ => clip_sub_le zero_le_one (preT_mono hwf hx hs j)
  rw [sum_sub_distrib, sum_sub_distrib] at this
  linarith [sum_preT_le hwf (x := x) (x' := x') hs]

theorem preR_mono (hwf : G.WellFormed) {x x' : T → ℚ} {s s' : ℚ} (hx : ∀ j, x j ≤ x' j)
    (hs : s ≤ s') : preR G x s ≤ preR G x' s' := by
  unfold preR; linarith [sum_Tm_le hwf hx hs]

/-- Mass preservation: `Σ_j T_j + R̃ = s + Σ_j x_j`. -/
theorem mass (x : T → ℚ) (s : ℚ) : ∑ j, Tm G x s j + preR G x s = s + ∑ j, x j := by
  unfold preR; ring

theorem abs_le_two_sub {a b c : ℚ} (ha : a ≤ c) (hb : b ≤ c) : |a - b| ≤ 2 * c - a - b :=
  abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩

theorem abs_eq_two_max (a b : ℚ) : |a - b| = 2 * max a b - a - b := by
  rcases le_total a b with h | h
  · rw [max_eq_right h, abs_of_nonpos (by linarith)]; ring
  · rw [max_eq_left h, abs_of_nonneg (by linarith)]; ring

/-- `(T, R̃)` is `ℓ₁`-nonexpansive in `(x, s)` (Crandall–Tartar). -/
theorem core_l1 (hwf : G.WellFormed) (x x' : T → ℚ) (s s' : ℚ) :
    ∑ j, |Tm G x s j - Tm G x' s' j| + |preR G x s - preR G x' s'| ≤
      ∑ j, |x j - x' j| + |s - s'| := by
  set X : T → ℚ := fun j => max (x j) (x' j) with hX
  set S := max s s' with hS
  have hx1 : ∀ j, x j ≤ X j := fun j => le_max_left _ _
  have hx2 : ∀ j, x' j ≤ X j := fun j => le_max_right _ _
  have h1 : ∑ j, |Tm G x s j - Tm G x' s' j| ≤
      2 * ∑ j, Tm G X S j - ∑ j, Tm G x s j - ∑ j, Tm G x' s' j := by
    have := sum_le_sum fun j (_ : j ∈ univ) =>
      abs_le_two_sub (Tm_mono hwf hx1 (le_max_left s s') j) (Tm_mono hwf hx2 (le_max_right s s') j)
    rw [sum_sub_distrib, sum_sub_distrib, ← mul_sum] at this; exact this
  have h2 : |preR G x s - preR G x' s'| ≤ 2 * preR G X S - preR G x s - preR G x' s' :=
    abs_le_two_sub (preR_mono hwf hx1 (le_max_left s s')) (preR_mono hwf hx2 (le_max_right s s'))
  have h3 : ∑ j, |x j - x' j| = 2 * ∑ j, X j - ∑ j, x j - ∑ j, x' j := by
    simp_rw [abs_eq_two_max]
    rw [sum_sub_distrib, sum_sub_distrib, ← mul_sum]
  have h4 : |s - s'| = 2 * S - s - s' := abs_eq_two_max s s'
  have m1 := mass (G := G) X S
  have m2 := mass (G := G) x s
  have m3 := mass (G := G) x' s'
  linarith

theorem sOf_lip (u u' : T ⊕ Unit → ℚ) : |sOf G u - sOf G u'| ≤ |qPart u - qPart u'| :=
  abs_clip_sub_le (κ_pos G).le

theorem l1_split (u : T ⊕ Unit → ℚ) : l1 u = ∑ j, |xPart u j| + |qPart u| := by
  unfold l1; rw [Fintype.sum_sum_type]; simp [xPart, qPart]

/-- **[C, Lemma ueopl-contraction]** `‖F u − F u'‖₁ ≤ (1−δ)‖u − u'‖₁`, for all rational `u, u'`
(not only on the cube). -/
theorem F_contraction (hwf : G.WellFormed) (u u' : T ⊕ Unit → ℚ) :
    l1 (F G u - F G u') ≤ (1 - cδ G) * l1 (u - u') := by
  have hδ := δ_le (G := G)
  have hδ1 : 0 ≤ 1 - cδ G := by linarith
  rw [l1_split, l1_split]
  have ex : ∀ j, |xPart (F G u - F G u') j| =
      (1 - cδ G) * |Tm G (xPart u) (sOf G u) j - Tm G (xPart u') (sOf G u') j| := by
    intro j
    simp only [xPart, Pi.sub_apply, F, Sum.elim_inl]
    rw [show (1 - cδ G) * Tm G (xPart u) (sOf G u) j + cδ G * a0 G -
        ((1 - cδ G) * Tm G (xPart u') (sOf G u') j + cδ G * a0 G) =
        (1 - cδ G) * (Tm G (xPart u) (sOf G u) j -
          Tm G (xPart u') (sOf G u') j) by ring, abs_mul, abs_of_nonneg hδ1]
  have eq : |qPart (F G u - F G u')| =
      (1 - cδ G) * |Rm G (xPart u) (sOf G u) - Rm G (xPart u') (sOf G u')| := by
    simp only [qPart, Pi.sub_apply, F, Sum.elim_inr]
    rw [show (1 - cδ G) * Rm G (xPart u) (sOf G u) + cδ G * (cκ G / 2) -
        ((1 - cδ G) * Rm G (xPart u') (sOf G u') + cδ G * (cκ G / 2)) =
        (1 - cδ G) * (Rm G (xPart u) (sOf G u) - Rm G (xPart u') (sOf G u')) by ring,
      abs_mul, abs_of_nonneg hδ1]
  simp_rw [ex]
  rw [eq, ← mul_sum, ← mul_add]
  apply mul_le_mul_of_nonneg_left _ hδ1
  have hR : |Rm G (xPart u) (sOf G u) - Rm G (xPart u') (sOf G u')| ≤
      |preR G (xPart u) (sOf G u) - preR G (xPart u') (sOf G u')| :=
    abs_clip_sub_le (κ_pos G).le
  have hc := core_l1 hwf (xPart u) (xPart u') (sOf G u) (sOf G u')
  have hs := sOf_lip (G := G) u u'
  have : ∀ j, |xPart (u - u') j| = |xPart u j - xPart u' j| := fun j => rfl
  simp_rw [this]
  have : |qPart (u - u')| = |qPart u - qPart u'| := rfl
  rw [this]
  linarith

/-- [C, *The map*] `F` maps `[0,1]^{n+1}` (indeed all of `ℚ^{n+1}`) into `[0,1]^{n+1}`. -/
theorem F_mem_cube (hwf : G.WellFormed) (u : T ⊕ Unit → ℚ) : InCube (F G u) := by
  have hδ0 := (δ_pos hwf).le; have hδ := δ_le (G := G)
  have ha := a0_mem hwf; have hκ := κ_pos G; have hκ1 := κ_le G
  rintro (j | ⟨⟩)
  · have hT := clip_mem (zero_le_one (α := ℚ)) (preT G (xPart u) (sOf G u) j)
    simp only [F, Sum.elim_inl]
    unfold Tm
    constructor <;> nlinarith
  · have hR := clip_mem hκ.le (preR G (xPart u) (sOf G u))
    simp only [F, Sum.elim_inr]
    unfold Rm
    constructor <;> nlinarith

/-- [C, Lemma ueopl-contraction] uniqueness of the fixed point. -/
theorem F_fixed_unique (hwf : G.WellFormed) (u u' : T ⊕ Unit → ℚ) (hu : F G u = u)
    (hu' : F G u' = u') : u = u' := by
  have h := F_contraction hwf u u'
  rw [hu, hu'] at h
  have hδ := δ_pos hwf
  have hn : 0 ≤ l1 (u - u') := sum_nonneg fun k _ => abs_nonneg _
  have h0 : l1 (u - u') = 0 := by nlinarith
  funext k
  have : |(u - u') k| ≤ l1 (u - u') := single_le_sum (fun k _ => abs_nonneg ((u - u') k)) (mem_univ k)
  rw [h0] at this
  have := abs_nonpos_iff.mp this
  simpa [sub_eq_zero] using this

end Contract


/-! ## The budget at the fixed point [C, Lemma ueopl-budget] -/

section Budget

variable {T Θ : Type*} [Fintype T] [DecidableEq T] [Fintype Θ] [DecidableEq Θ] [Nonempty T]
variable {G : BSSG T Θ}

theorem fix_x (u : T ⊕ Unit → ℚ) (hu : F G u = u) (j : T) :
    xPart u j = (1 - cδ G) * zOf G u j + cδ G * a0 G := by
  have := congrFun hu (.inl j); simp only [F, Sum.elim_inl] at this
  exact this.symm

theorem fix_q (u : T ⊕ Unit → ℚ) (hu : F G u = u) :
    qPart u = (1 - cδ G) * Rm G (xPart u) (sOf G u) + cδ G * (cκ G / 2) := by
  have := congrFun hu (.inr ()); simp only [F, Sum.elim_inr] at this
  exact this.symm

theorem fix_cube (hwf : G.WellFormed) (u : T ⊕ Unit → ℚ) (hu : F G u = u) : InCube u := by
  rw [← hu]; exact F_mem_cube hwf u

theorem z_mem (u : T ⊕ Unit → ℚ) (j : T) : 0 ≤ zOf G u j ∧ zOf G u j ≤ 1 :=
  clip_mem zero_le_one _

/-- `|x_j − z_j| ≤ δ` at the fixed point. -/
theorem fix_xz (hwf : G.WellFormed) (u : T ⊕ Unit → ℚ) (hu : F G u = u) (j : T) :
    |xPart u j - zOf G u j| ≤ cδ G := by
  rw [fix_x u hu j]
  have ha := a0_mem hwf; have hz := z_mem (G := G) u j; have hδ := δ_pos hwf
  rw [show (1 - cδ G) * zOf G u j + cδ G * a0 G - zOf G u j = cδ G * (a0 G - zOf G u j) by ring,
    abs_mul, abs_of_pos hδ]
  have : |a0 G - zOf G u j| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
  nlinarith

theorem fix_q_mem (hwf : G.WellFormed) (u : T ⊕ Unit → ℚ) (hu : F G u = u) :
    cδ G * cκ G / 2 ≤ qPart u ∧ qPart u ≤ (1 - cδ G / 2) * cκ G := by
  have hR := clip_mem (κ_pos G).le (preR G (xPart u) (sOf G u))
  have hq := fix_q u hu
  have hδ := δ_pos hwf; have hδ1 := δ_le (G := G)
  unfold Rm at hq
  constructor <;> nlinarith

theorem fix_s (hwf : G.WellFormed) (u : T ⊕ Unit → ℚ) (hu : F G u = u) : sOf G u = qPart u := by
  have := fix_q_mem hwf u hu
  have hδ := δ_pos hwf; have hκ := κ_pos G
  exact clip_of_mem (by nlinarith) (by nlinarith)

/-- [C, Lemma ueopl-budget]: `R` is unclipped at the fixed point. -/
theorem fix_R_unclipped (hwf : G.WellFormed) (u : T ⊕ Unit → ℚ) (hu : F G u = u) :
    Rm G (xPart u) (sOf G u) = preR G (xPart u) (sOf G u) := by
  have hcube := fix_cube hwf u hu
  have hq := fix_q u hu
  have hqm := fix_q_mem hwf u hu
  have hs := fix_s hwf u hu
  have hδ := δ_pos hwf; have hδ1 := δ_le (G := G); have hκ := κ_pos G
  have hx : ∀ j, 0 ≤ xPart u j ∧ xPart u j ≤ 1 := fun j => hcube (.inl j)
  have hpos : 0 < preR G (xPart u) (sOf G u) := by
    by_contra hneg; push Not at hneg
    have hR0 : Rm G (xPart u) (sOf G u) = 0 := by
      unfold Rm clip; rw [max_eq_left hneg]; exact min_eq_right hκ.le
    rw [hR0] at hq
    have hlam : lam G (sOf G u) = dBar G := lam_of_le hwf (by rw [hs, hq]; nlinarith)
    have hT : ∀ j, Tm G (xPart u) (sOf G u) j ≤ xPart u j := by
      intro j
      have hw := wA_le_one hwf (xPart u) j
      have hd := dP_pos hwf j
      have h1 : 1 ≤ lam G (sOf G u) / dP G j := by
        rw [hlam, le_div_iff₀ hd, one_mul]; exact dP_le_dBar j
      have h2 : preT G (xPart u) (sOf G u) j ≤ xPart u j := by
        unfold preT; have := η_pos hwf; nlinarith
      unfold Tm clip
      exact le_trans (min_le_right _ _) (max_le (hx j).1 h2)
    have : sOf G u ≤ preR G (xPart u) (sOf G u) := by
      unfold preR; linarith [sum_le_sum fun j (_ : j ∈ univ) => hT j]
    nlinarith [mul_pos hδ hκ]
  have hlt : preR G (xPart u) (sOf G u) < cκ G := by
    by_contra hneg; push Not at hneg
    have hRk : Rm G (xPart u) (sOf G u) = cκ G := by
      unfold Rm clip; rw [max_eq_right (by linarith)]; exact min_eq_left hneg
    rw [hRk] at hq
    have hlam : lam G (sOf G u) = 0 := lam_of_ge hwf (by rw [hs, hq]; nlinarith)
    have hT : ∀ j, xPart u j ≤ Tm G (xPart u) (sOf G u) j := by
      intro j
      have hw := wA_nonneg hwf (xPart u) j
      have h2 : xPart u j ≤ preT G (xPart u) (sOf G u) j := by
        unfold preT; rw [hlam, zero_div, sub_zero]; have := η_pos hwf; nlinarith
      unfold Tm clip
      exact le_min (hx j).2 (le_trans h2 (le_max_right _ _))
    have : preR G (xPart u) (sOf G u) ≤ sOf G u := by
      unfold preR; linarith [sum_le_sum fun j (_ : j ∈ univ) => hT j]
    nlinarith [mul_pos hδ hκ]
  exact clip_of_mem hpos.le hlt.le

/-- [C, Lemma ueopl-budget]: `Σ_j x_j + q = r + κ/2`. -/
theorem fix_budget_identity (hwf : G.WellFormed) (u : T ⊕ Unit → ℚ) (hu : F G u = u) :
    ∑ j, xPart u j + qPart u = G.r + cκ G / 2 := by
  have hq := fix_q u hu
  rw [fix_R_unclipped hwf u hu, fix_s hwf u hu] at hq
  have hsx : ∑ j, xPart u j = (1 - cδ G) * ∑ j, zOf G u j + cδ G * G.r := by
    simp_rw [fix_x u hu]
    rw [sum_add_distrib, ← mul_sum, ← mul_sum, sum_a0]
  have hδ := δ_pos hwf
  unfold preR at hq
  have hz : ∑ j, Tm G (xPart u) (qPart u) j = ∑ j, zOf G u j := by
    unfold zOf; rw [fix_s hwf u hu]
  rw [hz] at hq
  have : cδ G * (∑ j, xPart u j + qPart u) = cδ G * (G.r + cκ G / 2) := by nlinarith
  exact mul_left_cancel₀ hδ.ne' this

/-- [C, Lemma ueopl-budget] (sharper form after the lemma): `|Σ_j T_j − r| ≤ κ/2`. -/
theorem fix_budget (hwf : G.WellFormed) (u : T ⊕ Unit → ℚ) (hu : F G u = u) :
    |∑ j, zOf G u j - G.r| ≤ cκ G / 2 := by
  have hid := fix_budget_identity hwf u hu
  have hqm := fix_q_mem hwf u hu
  have hsx : ∑ j, xPart u j = (1 - cδ G) * ∑ j, zOf G u j + cδ G * G.r := by
    simp_rw [fix_x u hu]
    rw [sum_add_distrib, ← mul_sum, ← mul_sum, sum_a0]
  have hδ := δ_pos hwf; have hδ1 := δ_le (G := G); have hκ := κ_pos G
  -- (1−δ)(Σz − r) = κ/2 − q
  have key : (1 - cδ G) * (∑ j, zOf G u j - G.r) = cκ G / 2 - qPart u := by linarith
  have hb : |cκ G / 2 - qPart u| ≤ (1 - cδ G) * (cκ G / 2) :=
    abs_le.mpr ⟨by nlinarith, by nlinarith⟩
  rw [← key, abs_mul, abs_of_pos (by linarith : (0 : ℚ) < 1 - cδ G)] at hb
  exact le_of_mul_le_mul_left hb (by linarith)

end Budget


/-! ## Pattern LPs: soundness and the repair threshold [C, Lemma ueopl-pattern] -/

section PatternSound

variable {T Θ : Type*} [Fintype T] [DecidableEq T] [Fintype Θ] [DecidableEq Θ]
variable (G : BSSG T Θ)

/-- [C, Lemma ueopl-pattern (a)]: every feasible point of a pattern LP is an exact BNE (in marginal
coordinates), even if some allowed flows vanish. -/
theorem pattern_sound (P : Pattern Θ T) (x : T → ℚ) (f : Θ → T → ℚ) (v : Θ → ℚ) (l : ℚ)
    (h : IsPatternPoint G P x f v l) : IsMarginalBNE G x f := by
  have hfeas : IsFeasibleCov G x :=
    ⟨h.x_box, le_antisymm (by linarith [h.budget_le]) (by linarith [h.budget_ge])⟩
  refine ⟨hfeas, fun i j => (h.f_box i j).1, fun i => ?_, fun i j hij k => ?_, ?_⟩
  · exact le_antisymm (by linarith [h.rowsum_le i]) (by linarith [h.rowsum_ge i])
  · have hall : P.allowed i j = true := by
      by_contra hc
      have := h.off i j (by simpa using hc)
      linarith
    have h1 := h.br i k
    have h2 := h.br_eq i j hall
    linarith
  · refine (DirectLCP.cutoff_form G (score G f) x hfeas).mpr ⟨l, fun j => ⟨fun hj => ?_, fun hj => ?_⟩⟩
    · have hne : P.label j ≠ .zero := fun hz => by have := h.zero_x j hz; linarith
      have := h.cut_ge j hne; linarith
    · have hne : P.label j ≠ .one := fun ho => by have := h.one_x j ho; linarith
      have := h.cut_le j hne; linarith

end PatternSound

section Rows

variable {T Θ : Type*} [Fintype T] [DecidableEq T] [Fintype Θ] [DecidableEq Θ]
variable (G : BSSG T Θ)

theorem dot_vec (cx : T → ℚ) (cf : Θ → T → ℚ) (cv : Θ → ℚ) (cl ct : ℚ)
    (x : T → ℚ) (f : Θ → T → ℚ) (v : Θ → ℚ) (l t : ℚ) :
    vec cx cf cv cl ct ⬝ᵥ vec x f v l t =
      ∑ j, cx j * x j + ∑ i, ∑ j, cf i j * f i j + ∑ i, cv i * v i + cl * l + ct * t := by
  simp [dotProduct, vec, Fintype.sum_sum_type, Fintype.sum_prod_type]
  ring

/-- Reassemble a vector on `Var` from its blocks. -/
theorem vec_eta (y : Var Θ T → ℚ) :
    vec (fun j => y (.inl j)) (fun i j => y (.inr (.inl (i, j)))) (fun i => y (.inr (.inr (.inl i))))
      (y (.inr (.inr (.inr (.inl ()))))) (y (.inr (.inr (.inr (.inr ()))))) = y := by
  ext (j | ⟨i, j⟩ | i | ⟨⟩ | ⟨⟩) <;> rfl

theorem sum_ite_mul_left {α : Type*} [Fintype α] [DecidableEq α] (a : α) (c : ℚ) (g : α → ℚ) :
    ∑ a', (if a' = a then c else 0) * g a' = c * g a := by
  simp [ite_mul]

theorem sum_sum_ite_fst (i : Θ) (c : ℚ) (f : Θ → T → ℚ) :
    ∑ i', ∑ j, (if i' = i then c else 0) * f i' j = c * ∑ j, f i j := by
  simp [ite_mul, mul_sum]

theorem sum_sum_ite_snd (j : T) (c : ℚ) (f : Θ → T → ℚ) :
    ∑ i, ∑ j', (if j' = j then c else 0) * f i j' = c * ∑ i, f i j := by
  simp [ite_mul, mul_sum]

theorem sum_sum_ite_pair (i : Θ) (j : T) (c : ℚ) (f : Θ → T → ℚ) :
    ∑ i', ∑ j', (if i' = i ∧ j' = j then c else 0) * f i' j' = c * f i j := by
  simp [ite_mul, ite_and]

end Rows


section Rows2

variable {T Θ : Type*} [Fintype T] [DecidableEq T] [Fintype Θ] [DecidableEq Θ]
variable (G : BSSG T Θ)

/-- The value `coef ⬝ (x,f,v,λ,t)` of each row, in readable form. -/
def rowVal (x : T → ℚ) (f : Θ → T → ℚ) (v : Θ → ℚ) (l t : ℚ) : Row Θ T → ℚ
  | .budLe => -∑ j, x j + t
  | .budGe => ∑ j, x j + t
  | .sumLe i => -∑ j, f i j + t
  | .sumGe i => ∑ j, f i j + t
  | .off i j => -f i j + t
  | .br i j => bb G i j * x j + v i + t
  | .brEq i j => -(bb G i j * x j) - v i + t
  | .zeroX j => -x j + t
  | .oneX j => x j + t
  | .cutLe j => -(dd G j * ∑ i, f i j) + l + t
  | .cutGe j => dd G j * ∑ i, f i j - l + t
  | .xLo j => x j
  | .xHi j => -x j
  | .fLo i j => f i j
  | .fHi i j => -f i j
  | .lLo => l
  | .lHi => -l
  | .vLo i => v i
  | .vHi i => -v i
  | .tLo => t
  | .tHi => -t

theorem row_dot (x : T → ℚ) (f : Θ → T → ℚ) (v : Θ → ℚ) (l t : ℚ) (r : Row Θ T) :
    coef G r ⬝ᵥ vec x f v l t = rowVal G x f v l t r := by
  cases r <;>
    simp only [coef, rowVal, dot_vec, ind, Pi.zero_apply, zero_mul, sum_const_zero,
      sum_ite_mul_left, sum_sum_ite_fst, sum_sum_ite_pair] <;>
    simp [sum_neg_distrib, neg_mul, one_mul, mul_sum] <;> ring

theorem U_eq' (i : Θ) (k : T) (x : T → ℚ) : G.U i k x = aa G i k - bb G i k * x k := by
  unfold BSSG.U aa bb; ring

theorem score_eq (f : Θ → T → ℚ) (j : T) : score G f j = dd G j * ∑ i, f i j := rfl

/-- The relaxed pattern LP is exactly its list of active rows. -/
theorem relaxed_iff (P : Pattern Θ T) (t : ℚ) (x : T → ℚ) (f : Θ → T → ℚ) (v : Θ → ℚ) (l : ℚ) :
    IsRelaxedPattern G P t x f v l ↔
      ∀ r, isActive P r = true → rhs G r ≤ coef G r ⬝ᵥ vec x f v l t := by
  simp only [row_dot]
  constructor
  · intro h r hr
    cases r with
    | budLe => simp only [rowVal, rhs]; linarith [h.budget_le]
    | budGe => simp only [rowVal, rhs]; linarith [h.budget_ge]
    | sumLe i => simp only [rowVal, rhs]; linarith [h.rowsum_le i]
    | sumGe i => simp only [rowVal, rhs]; linarith [h.rowsum_ge i]
    | off i j =>
      simp only [isActive, Bool.not_eq_true'] at hr
      simp only [rowVal, rhs]; linarith [h.off i j hr]
    | br i j =>
      simp only [rowVal, rhs]; have := h.br i j; rw [U_eq'] at this; linarith
    | brEq i j =>
      simp only [isActive] at hr
      simp only [rowVal, rhs]; have := h.br_eq i j hr; rw [U_eq'] at this; linarith
    | zeroX j =>
      simp only [isActive, decide_eq_true_eq] at hr
      simp only [rowVal, rhs]; linarith [h.zero_x j hr]
    | oneX j =>
      simp only [isActive, decide_eq_true_eq] at hr
      simp only [rowVal, rhs]; linarith [h.one_x j hr]
    | cutLe j =>
      simp only [isActive, decide_eq_true_eq] at hr
      simp only [rowVal, rhs]; have := h.cut_le j hr; rw [score_eq] at this; linarith
    | cutGe j =>
      simp only [isActive, decide_eq_true_eq] at hr
      simp only [rowVal, rhs]; have := h.cut_ge j hr; rw [score_eq] at this; linarith
    | xLo j => simp only [rowVal, rhs]; linarith [(h.x_box j).1]
    | xHi j => simp only [rowVal, rhs]; linarith [(h.x_box j).2]
    | fLo i j => simp only [rowVal, rhs]; linarith [(h.f_box i j).1]
    | fHi i j => simp only [rowVal, rhs]; linarith [(h.f_box i j).2]
    | lLo => simp only [rowVal, rhs]; linarith [h.l_box.1]
    | lHi => simp only [rowVal, rhs]; linarith [h.l_box.2]
    | vLo i => simp only [rowVal, rhs]; linarith [(h.v_box i).1]
    | vHi i => simp only [rowVal, rhs]; linarith [(h.v_box i).2]
    | tLo => simp only [rowVal, rhs]; linarith [h.t_nonneg]
    | tHi => simp only [rowVal, rhs]; linarith [h.t_le_one]
  · intro H
    have A : ∀ r, isActive P r = true → rhs G r ≤ rowVal G x f v l t r := H
    refine
      { t_nonneg := by have := A .tLo rfl; simp only [rowVal, rhs] at this; linarith
        t_le_one := by have := A .tHi rfl; simp only [rowVal, rhs] at this; linarith
        x_box := fun j => ⟨by have := A (.xLo j) rfl; simp only [rowVal, rhs] at this; linarith,
          by have := A (.xHi j) rfl; simp only [rowVal, rhs] at this; linarith⟩
        f_box := fun i j => ⟨by have := A (.fLo i j) rfl; simp only [rowVal, rhs] at this; linarith,
          by have := A (.fHi i j) rfl; simp only [rowVal, rhs] at this; linarith⟩
        l_box := ⟨by have := A .lLo rfl; simp only [rowVal, rhs] at this; linarith,
          by have := A .lHi rfl; simp only [rowVal, rhs] at this; linarith⟩
        v_box := fun i => ⟨by have := A (.vLo i) rfl; simp only [rowVal, rhs] at this; linarith,
          by have := A (.vHi i) rfl; simp only [rowVal, rhs] at this; linarith⟩
        budget_le := by have := A .budLe rfl; simp only [rowVal, rhs] at this; linarith
        budget_ge := by have := A .budGe rfl; simp only [rowVal, rhs] at this; linarith
        rowsum_le := fun i => by have := A (.sumLe i) rfl; simp only [rowVal, rhs] at this; linarith
        rowsum_ge := fun i => by have := A (.sumGe i) rfl; simp only [rowVal, rhs] at this; linarith
        off := fun i j hij => by
          have := A (.off i j) (by simp [isActive, hij]); simp only [rowVal, rhs] at this; linarith
        br := fun i j => by
          have := A (.br i j) rfl; simp only [rowVal, rhs] at this
          rw [U_eq']; linarith
        br_eq := fun i j hij => by
          have := A (.brEq i j) (by simp [isActive, hij]); simp only [rowVal, rhs] at this
          rw [U_eq']; linarith
        zero_x := fun j hj => by
          have := A (.zeroX j) (by simp [isActive, hj]); simp only [rowVal, rhs] at this; linarith
        one_x := fun j hj => by
          have := A (.oneX j) (by simp [isActive, hj]); simp only [rowVal, rhs] at this; linarith
        cut_le := fun j hj => by
          have := A (.cutLe j) (by simp [isActive, hj]); simp only [rowVal, rhs] at this
          rw [score_eq]; linarith
        cut_ge := fun j hj => by
          have := A (.cutGe j) (by simp [isActive, hj]); simp only [rowVal, rhs] at this
          rw [score_eq]; linarith }

end Rows2


section Repair

variable {T Θ : Type*} [Fintype T] [DecidableEq T] [Fintype Θ] [DecidableEq Θ]
variable (G : BSSG T Θ)

theorem rowDen_pos (r : Row Θ T) : 0 < rowDen G r := by
  unfold rowDen
  apply Nat.lcm_pos
  · apply Nat.pos_of_ne_zero
    rw [Ne, Finset.lcm_eq_zero_iff]
    simp [Rat.den_ne_zero]
  · exact Rat.den_pos _

theorem cleared_int (r : Row Θ T) (q : ℚ) (hden : q.den ∣ rowDen G r)
    (hle : ((rowDen G r : ℚ) * q).num.natAbs ≤ cH G) :
    ∃ m : ℤ, (rowDen G r : ℚ) * q = m ∧ |m| ≤ (cH G : ℕ) := by
  obtain ⟨m, hm⟩ := DirectLCP.int_of_den_dvd q _ hden
  refine ⟨m, hm, ?_⟩
  rw [hm, Rat.num_intCast] at hle
  rw [← Int.natCast_natAbs]; exact_mod_cast hle

theorem coef_int (r : Row Θ T) (c : Var Θ T) :
    ∃ m : ℤ, (rowDen G r : ℚ) * coef G r c = m ∧ |m| ≤ (cH G : ℕ) := by
  refine cleared_int G r _ ((Finset.dvd_lcm (mem_univ c)).trans (Nat.dvd_lcm_left _ _)) ?_
  refine le_trans ?_ (le_max_right _ _)
  refine le_trans ?_ (Finset.le_sup (f := fun ρ : Row Θ T =>
    (univ.sup fun c => ((rowDen G ρ : ℚ) * coef G ρ c).num.natAbs) ⊔
      ((rowDen G ρ : ℚ) * rhs G ρ).num.natAbs) (mem_univ r))
  exact le_trans (Finset.le_sup (f := fun c => ((rowDen G r : ℚ) * coef G r c).num.natAbs)
    (mem_univ c)) le_sup_left

theorem rhs_int (r : Row Θ T) :
    ∃ m : ℤ, (rowDen G r : ℚ) * rhs G r = m ∧ |m| ≤ (cH G : ℕ) := by
  refine cleared_int G r _ (Nat.dvd_lcm_right _ _) ?_
  refine le_trans ?_ (le_max_right _ _)
  refine le_trans ?_ (Finset.le_sup (f := fun ρ : Row Θ T =>
    (univ.sup fun c => ((rowDen G ρ : ℚ) * coef G ρ c).num.natAbs) ⊔
      ((rowDen G ρ : ℚ) * rhs G ρ).num.natAbs) (mem_univ r))
  exact le_sup_right

/-- The active rows of pattern `P`. -/
abbrev ARow (P : Pattern Θ T) := {r : Row Θ T // isActive P r = true}

/-- Cleared (integer) coefficients of the active rows. -/
def ga (P : Pattern Θ T) : ARow P → Var Θ T → ℚ := fun r => (rowDen G r.1 : ℚ) • coef G r.1

/-- Cleared (integer) right sides of the active rows. -/
def gb (P : Pattern Θ T) : ARow P → ℚ := fun r => (rowDen G r.1 : ℚ) * rhs G r.1

theorem feas_iff (P : Pattern Θ T) (y : Var Θ T → ℚ) :
    (∀ r, isActive P r = true → rhs G r ≤ coef G r ⬝ᵥ y) ↔
      ∀ r : ARow P, gb G P r ≤ ga G P r ⬝ᵥ y := by
  constructor
  · intro h r
    simp only [ga, gb, smul_dotProduct, smul_eq_mul]
    exact mul_le_mul_of_nonneg_left (h r.1 r.2) (by positivity)
  · intro h r hr
    have := h ⟨r, hr⟩
    simp only [ga, gb, smul_dotProduct, smul_eq_mul] at this
    exact le_of_mul_le_mul_left this (by exact_mod_cast rowDen_pos G r)

/-- The `t` variable. -/
abbrev tVar : Var Θ T := .inr (.inr (.inr (.inr ())))

/-- The polytope of every relaxed pattern LP is bounded (trivial recession cone): every variable
is boxed, `t` included. -/
theorem grec (P : Pattern Θ T) : ∀ d, (∀ r : ARow P, 0 ≤ ga G P r ⬝ᵥ d) → d = 0 := by
  intro d h
  have h' : ∀ r, isActive P r = true →
      0 ≤ rowVal G (fun j => d (.inl j)) (fun i j => d (.inr (.inl (i, j))))
        (fun i => d (.inr (.inr (.inl i)))) (d (.inr (.inr (.inr (.inl ())))))
        (d (.inr (.inr (.inr (.inr ()))))) r := fun r hr => by
    have := h ⟨r, hr⟩
    simp only [ga, smul_dotProduct, smul_eq_mul] at this
    rw [← row_dot, vec_eta]
    exact (mul_nonneg_iff_of_pos_left (by exact_mod_cast rowDen_pos G r)).mp this
  ext (j | ⟨i, j⟩ | i | ⟨⟩ | ⟨⟩)
  · have a1 := h' (.xLo j) rfl; have a2 := h' (.xHi j) rfl
    simp only [rowVal] at a1 a2; simp only [Pi.zero_apply]; linarith
  · have a1 := h' (.fLo i j) rfl; have a2 := h' (.fHi i j) rfl
    simp only [rowVal] at a1 a2; simp only [Pi.zero_apply]; linarith
  · have a1 := h' (.vLo i) rfl; have a2 := h' (.vHi i) rfl
    simp only [rowVal] at a1 a2; simp only [Pi.zero_apply]; linarith
  · have a1 := h' .lLo rfl; have a2 := h' .lHi rfl
    simp only [rowVal] at a1 a2; simp only [Pi.zero_apply]; linarith
  · have a1 := h' .tLo rfl; have a2 := h' .tHi rfl
    simp only [rowVal] at a1 a2; simp only [Pi.zero_apply]; linarith

theorem one_le_cH' : 1 ≤ cH G := le_max_left _ _

theorem one_le_cQ' : (1 : ℚ) ≤ cQ G := by
  have hN : 0 < cN (Θ := Θ) (T := T) := Fintype.card_pos
  have h1 : 1 ≤ cN (Θ := Θ) (T := T) * cH G :=
    Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero hN.ne' (by have := one_le_cH' G; omega))
  have : 1 ≤ cQ G := Nat.one_le_pow _ _ h1
  exact_mod_cast this

/-- **[C, Lemma ueopl-pattern (b), (c)]** (repair threshold): if a point satisfies every
constraint of pattern `P` up to a slack `t₀ < g` and the outer boxes exactly, the unrelaxed pattern
LP of `P` is feasible.  (Vertex of the relaxed polytope with no larger `t`, Cramer's rule, and
`|det| ≤ N! H^N ≤ Q`: a positive `t` at a vertex is `≥ 1/Q > g`.) -/
theorem repair (P : Pattern Θ T) (t0 : ℚ) (x : T → ℚ) (f : Θ → T → ℚ) (v : Θ → ℚ) (l : ℚ)
    (ht : t0 < gThr G) (h : IsRelaxedPattern G P t0 x f v l) : PatternFeasible G P := by
  classical
  have hy : ∀ r : ARow P, gb G P r ≤ ga G P r ⬝ᵥ vec x f v l t0 :=
    (feas_iff G P _).mp ((relaxed_iff G P t0 x f v l).mp h)
  obtain ⟨y', hf, hc, htop⟩ := DirectLCP.exists_vertex (ga G P) (gb G P) (grec G P)
    (Pi.single tVar 1) _ _ hy rfl
  simp only [single_dotProduct, one_mul] at hc
  have hct : vec x f v l t0 tVar = t0 := rfl
  rw [hct] at hc
  obtain ⟨p, q, hq, hqle, hval⟩ := DirectLCP.vertex_value (ga G P) (gb G P) (cH G)
    (fun r c => coef_int G r.1 c) (fun r => rhs_int G r.1) y' htop tVar
  have hrel : IsRelaxedPattern G P (y' tVar) (fun j => y' (.inl j))
      (fun i j => y' (.inr (.inl (i, j)))) (fun i => y' (.inr (.inr (.inl i))))
      (y' (.inr (.inr (.inr (.inl ()))))) := by
    rw [relaxed_iff, vec_eta]; exact (feas_iff G P _).mpr hf
  have hNat : (Fintype.card (Var Θ T)).factorial * cH G ^ Fintype.card (Var Θ T) ≤ cQ G := by
    rw [cQ, cN, mul_pow]
    exact Nat.mul_le_mul_right _ (Nat.factorial_le_pow _)
  have hqQ : |(q : ℚ)| ≤ (cQ G : ℚ) := by
    have : |q| ≤ (cQ G : ℤ) := le_trans hqle (by exact_mod_cast hNat)
    exact_mod_cast this
  have h0 := hrel.t_nonneg
  have hz : y' tVar = 0 := by
    by_contra hne
    have hpos : 0 < y' tVar := lt_of_le_of_ne h0 (Ne.symm hne)
    have hq0 : (q : ℚ) ≠ 0 := by exact_mod_cast hq
    have hp0 : p ≠ 0 := by
      intro hp; rw [hp, Int.cast_zero, zero_div] at hval; linarith
    have hp1 : (1 : ℚ) ≤ |(p : ℚ)| := by
      have : (1 : ℤ) ≤ |p| := Int.one_le_abs hp0
      exact_mod_cast this
    have habs : y' tVar = |(p : ℚ)| / |(q : ℚ)| := by
      rw [← abs_div, ← hval, abs_of_pos hpos]
    have hq1 : 0 < |(q : ℚ)| := abs_pos.mpr hq0
    have hQ := one_le_cQ' G
    have hge : 1 / (cQ G : ℚ) ≤ y' tVar := by
      rw [habs, div_le_div_iff₀ (by linarith) hq1]; nlinarith
    have hg : gThr G * (4 * cQ G) = 1 := by unfold gThr; field_simp
    have : y' tVar * (cQ G : ℚ) < 1 := by nlinarith
    rw [div_le_iff₀ (by linarith)] at hge
    linarith
  rw [hz] at hrel
  exact ⟨_, _, _, _, hrel⟩

end Repair


/-! ## Decoding the fixed point [C, Lemma ueopl-decoding] -/

section Decoding

variable {T Θ : Type*} [Fintype T] [DecidableEq T] [Fintype Θ] [DecidableEq Θ] [Nonempty T]
variable {G : BSSG T Θ}

theorem prior_le_one (hwf : G.WellFormed) (i : Θ) : G.prior i ≤ 1 := by
  rw [← hwf.2.2.1]; exact single_le_sum (fun k _ => hwf.2.1 k) (mem_univ i)

theorem fA_nonneg (hwf : G.WellFormed) (x : T → ℚ) (i : Θ) (j : T) : 0 ≤ fA G x i j :=
  mul_nonneg (hwf.2.1 i) (yA_nonneg x i j)

theorem fA_le_one (hwf : G.WellFormed) (x : T → ℚ) (i : Θ) (j : T) : fA G x i j ≤ 1 :=
  le_trans (mul_le_of_le_one_right (hwf.2.1 i) (yA_le_one x i j)) (prior_le_one hwf i)

theorem fA_rowsum (x : T → ℚ) (i : Θ) : ∑ j, fA G x i j = G.prior i := by
  unfold fA; rw [← mul_sum, yA_sum, mul_one]

theorem U_close (hwf : G.WellFormed) (x z : T → ℚ) (ε : ℚ) (hxz : ∀ k, |x k - z k| ≤ ε)
    (i : Θ) (k : T) : |G.U i k z - G.U i k x| ≤ bMax G * ε := by
  rw [U_eq', U_eq', show aa G i k - bb G i k * z k - (aa G i k - bb G i k * x k) =
    bb G i k * (x k - z k) by ring, abs_mul, abs_of_nonneg (DirectLCP.bb_nonneg G hwf i k)]
  have := abs_nonneg (x k - z k)
  exact mul_le_mul (bb_le_bMax G i k) (hxz k) this (bMax_nonneg G)

theorem vOf_ge (z : T → ℚ) (i : Θ) (j : T) : G.U i j z ≤ vOf G z i :=
  le_sup' (fun j => G.U i j z) (mem_univ j)

theorem U_abs_le (hwf : G.WellFormed) (z : T → ℚ) (hz : ∀ k, 0 ≤ z k ∧ z k ≤ 1) (i : Θ) (k : T) :
    |G.U i k z| ≤ abMax G := by
  refine le_trans ?_ (ab_le_abMax G i k)
  rw [U_eq']
  have hb := DirectLCP.bb_nonneg G hwf i k
  have h1 := neg_abs_le (aa G i k); have h2 := le_abs_self (aa G i k)
  have := hz k
  exact abs_le.mpr ⟨by nlinarith, by nlinarith⟩

theorem vOf_box (hwf : G.WellFormed) (z : T → ℚ) (hz : ∀ k, 0 ≤ z k ∧ z k ≤ 1) (i : Θ) :
    -vBox G ≤ vOf G z i ∧ vOf G z i ≤ vBox G := by
  obtain ⟨k, -, hk⟩ := exists_mem_eq_sup' univ_nonempty (fun j => G.U i j z)
  have hv : vOf G z i = G.U i k z := hk
  have := abs_le.mp (U_abs_le hwf z hz i k)
  unfold vBox; rw [hv]; constructor <;> linarith

theorem labelOf_zero {z : ℚ} (h : labelOf z = .zero) : z = 0 := by
  unfold labelOf at h; split_ifs at h with h1 h2; exact h1

theorem labelOf_one {z : ℚ} (h : labelOf z = .one) : z = 1 := by
  unfold labelOf at h; split_ifs at h with h1 h2; exact h2

theorem labelOf_ne_zero {z : ℚ} (h : labelOf z ≠ .zero) : z ≠ 0 := by
  intro hz; apply h; unfold labelOf; simp [hz]

theorem labelOf_ne_one {z : ℚ} (h : labelOf z ≠ .one) : z ≠ 1 := by
  intro hz; apply h; unfold labelOf; simp [hz]

theorem clip_lt_one_le {a : ℚ} (h : clip 0 1 a < 1) : a ≤ clip 0 1 a := by
  unfold clip at *
  rcases le_total 1 (max 0 a) with h1 | h1
  · rw [min_eq_left h1] at h; linarith
  · rw [min_eq_right h1]; exact le_max_right _ _

theorem clip_pos_ge {a : ℚ} (h : 0 < clip 0 1 a) : clip 0 1 a ≤ a := by
  unfold clip at *
  rcases le_total a 0 with h1 | h1
  · rw [max_eq_left h1] at h; simp at h
  · rw [max_eq_right h1]; exact min_le_right _ _

/-- **[C, Lemma ueopl-decoding]** At the fixed point `u = (x, q)`, with `z = T(x, q)`, the point
`(z, f(x), v, λ(q))`, `v_i = max_j U_ij(z)`, satisfies the outer boxes exactly and every constraint
of the recorded pattern with residual at most `3g/8 < g`: best responses `σ + 2 b_max δ ≤ 3g/8`,
cutoffs `d̄δ/η + g/16 ≤ 3g/16`, budget `κ/2 = g/16`. -/
theorem decode_relaxed (hwf : G.WellFormed) (u : T ⊕ Unit → ℚ) (hu : F G u = u) :
    IsRelaxedPattern G (patternOf G u) (3 * gThr G / 8) (zOf G u) (fA G (xPart u))
      (vOf G (zOf G u)) (lam G (sOf G u)) := by
  have hg := g_pos G; have hg1 := g_le G
  have hz := z_mem (G := G) u
  have hxz := fix_xz hwf u hu
  have hbud := abs_le.mp (fix_budget hwf u hu)
  have hκ : cκ G = gThr G / 8 := rfl
  have hσ : cσ G = gThr G / 8 := rfl
  have hδ := δ_pos hwf; have hη := η_pos hwf
  have hδb := δ_bmax (G := G); have hδe := δ_eta hwf
  have hbm := bMax_nonneg G
  -- the cutoff estimate, both sides: `|η (d'_j w_j − λ)| ≤ d̄ δ ≤ η g/8`
  have hcut : ∀ j, (zOf G u j < 1 →
        dP G j * wA G (xPart u) j ≤ lam G (sOf G u) + gThr G / 8) ∧
      (0 < zOf G u j → lam G (sOf G u) - gThr G / 8 ≤ dP G j * wA G (xPart u) j) := by
    intro j
    have hd := dP_pos hwf j; have hdb := dP_le_dBar (G := G) j
    have hxj := abs_le.mp (hxz j)
    have e : cη G * (wA G (xPart u) j - lam G (sOf G u) / dP G j) * dP G j =
        cη G * (dP G j * wA G (xPart u) j - lam G (sOf G u)) := by field_simp
    have hdδ : dP G j * cδ G ≤ cη G * gThr G / 8 := by nlinarith
    have hzdef : zOf G u j = clip 0 1 (preT G (xPart u) (sOf G u) j) := rfl
    have hpre : preT G (xPart u) (sOf G u) j =
      xPart u j + cη G * (wA G (xPart u) j - lam G (sOf G u) / dP G j) := rfl
    constructor
    · intro h1
      have ha := clip_lt_one_le h1
      have : cη G * (wA G (xPart u) j - lam G (sOf G u) / dP G j) ≤ cδ G := by
        linarith
      have h2 : cη G * (dP G j * wA G (xPart u) j - lam G (sOf G u)) ≤ cη G * (gThr G / 8) := by
        rw [← e]; nlinarith
      have := le_of_mul_le_mul_left h2 hη
      linarith
    · intro h1
      have ha := clip_pos_ge h1
      have : -cδ G ≤ cη G * (wA G (xPart u) j - lam G (sOf G u) / dP G j) := by
        linarith
      have h2 : cη G * (-(gThr G / 8)) ≤ cη G * (dP G j * wA G (xPart u) j - lam G (sOf G u)) := by
        rw [← e]; nlinarith
      have := le_of_mul_le_mul_left h2 hη
      linarith
  exact
    { t_nonneg := by positivity
      t_le_one := by linarith
      x_box := hz
      f_box := fun i j => ⟨fA_nonneg hwf _ i j, fA_le_one hwf _ i j⟩
      l_box := ⟨(lam_mem hwf _).1, le_trans (lam_mem hwf _).2 dBar_le_lamBox⟩
      v_box := vOf_box hwf _ hz
      budget_le := by linarith [hbud.2]
      budget_ge := by linarith [hbud.1]
      rowsum_le := fun i => by rw [fA_rowsum]; linarith
      rowsum_ge := fun i => by rw [fA_rowsum]; linarith
      off := fun i j h => by
        simp only [patternOf, decide_eq_false_iff_not, not_lt] at h; linarith
      br := fun i j => by linarith [vOf_ge (G := G) (zOf G u) i j]
      br_eq := fun i j h => by
        simp only [patternOf, decide_eq_true_eq] at h
        have hy : 0 < yA G (xPart u) i j := by
          by_contra hy; push Not at hy
          have : fA G (xPart u) i j ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (hwf.2.1 i) hy
          linarith
        obtain ⟨k, -, hk⟩ := exists_mem_eq_sup' univ_nonempty (fun j => G.U i j (zOf G u))
        have hv : vOf G (zOf G u) i = G.U i k (zOf G u) := hk
        have hnear := proj_pos_near_max _ j hy k
        have hσp := σ_pos G
        have hnear' : G.U i k (xPart u) < G.U i j (xPart u) + cσ G := by
          have := (div_lt_iff₀ hσp).mp (by
            have : G.U i k (xPart u) / cσ G - G.U i j (xPart u) / cσ G < 1 := by linarith
            rwa [← sub_div] at this)
          linarith
        have c1 := abs_le.mp (U_close hwf (xPart u) (zOf G u) (cδ G) hxz i k)
        have c2 := abs_le.mp (U_close hwf (xPart u) (zOf G u) (cδ G) hxz i j)
        rw [hv]
        nlinarith
      zero_x := fun j h => by
        have := labelOf_zero (show labelOf (zOf G u j) = .zero from h); linarith
      one_x := fun j h => by
        have := labelOf_one (show labelOf (zOf G u j) = .one from h); linarith
      cut_le := fun j h => by
        have hne := labelOf_ne_one (show labelOf (zOf G u j) ≠ .one from h)
        have hlt : zOf G u j < 1 := lt_of_le_of_ne (hz j).2 hne
        have h1 := (hcut j).1 hlt
        have hw := wA_nonneg hwf (xPart u) j
        have : score G (fA G (xPart u)) j ≤ dP G j * wA G (xPart u) j := by
          show dd G j * wA G (xPart u) j ≤ (dd G j + gThr G / 16) * wA G (xPart u) j
          nlinarith
        linarith
      cut_ge := fun j h => by
        have hne := labelOf_ne_zero (show labelOf (zOf G u j) ≠ .zero from h)
        have hlt : 0 < zOf G u j := lt_of_le_of_ne (hz j).1 (Ne.symm hne)
        have h1 := (hcut j).2 hlt
        have hw := wA_nonneg hwf (xPart u) j; have hw1 := wA_le_one hwf (xPart u) j
        have : dP G j * wA G (xPart u) j - gThr G / 16 ≤ score G (fA G (xPart u)) j := by
          show (dd G j + gThr G / 16) * wA G (xPart u) j - gThr G / 16 ≤ dd G j * wA G (xPart u) j
          nlinarith
        linarith }

/-- **[C, Lemma ueopl-decoding] + [C, Thm. sx-game]**: from a fixed point of `F`, the pattern LP
recorded at it is feasible, and every solution of it is an exact BNE in marginal coordinates. -/
theorem decode_fixed (hwf : G.WellFormed) (u : T ⊕ Unit → ℚ) (hu : F G u = u) :
    PatternFeasible G (patternOf G u) ∧
      ∀ x f v l, IsPatternPoint G (patternOf G u) x f v l → IsMarginalBNE G x f := by
  refine ⟨repair G _ (3 * gThr G / 8) _ _ _ _ ?_ (decode_relaxed hwf u hu), fun x f v l h =>
    pattern_sound G _ x f v l h⟩
  have := g_pos G; linarith

end Decoding


/-! ## The statements of `Statements.lean` -/

section Final

variable (T Θ : Type*) [Fintype T] [DecidableEq T] [Fintype Θ] [DecidableEq Θ]

theorem patternSoundness_proof : PatternSoundness T Θ := fun G P x f v l h =>
  pattern_sound G P x f v l h

theorem repairThreshold_proof : RepairThreshold T Θ := fun G P t0 x f v l ht h =>
  repair G P t0 x f v l ht h

variable [Nonempty T]

theorem projectionLemma_proof : ProjectionLemma T := fun u =>
  ⟨⟨proj_nonneg u, proj_sum u⟩, proj_euclidean u, proj_pos_near_max u⟩

theorem constantsLemma_proof : ConstantsLemma T Θ := fun G hwf =>
  ⟨g_pos G, dP_pos hwf, η_pos hwf, δ_pos hwf, δ_le, (ueopl_const hwf).1, (ueopl_const hwf).2⟩

theorem mapsCube_proof : MapsCube T Θ := fun _G hwf u _ => F_mem_cube hwf u

theorem l1Contraction_proof : L1Contraction T Θ := fun _G hwf =>
  ⟨δ_pos hwf, fun u u' _ _ => F_contraction hwf u u'⟩

theorem fixedPointUnique_proof : FixedPointUnique T Θ := fun _G hwf u u' hu hu' =>
  F_fixed_unique hwf u u' hu hu'

theorem budgetAtFixedPoint_proof : BudgetAtFixedPoint T Θ := by
  intro G hwf u hu
  have hb := fix_budget hwf u hu
  have hδ := δ_pos hwf; have hδ1 := δ_le (G := G); have hκ := κ_pos G
  refine ⟨fix_q_mem hwf u hu, fix_s hwf u hu, fix_R_unclipped hwf u hu,
    fix_budget_identity hwf u hu, le_trans hb ?_, hb⟩
  rw [div_le_div_iff₀ (by norm_num) (by nlinarith)]; nlinarith

theorem decodingResiduals_proof : DecodingResiduals T Θ := fun _G hwf u hu =>
  decode_relaxed hwf u hu

theorem decoding_proof : Decoding T Θ := fun _G hwf u hu => decode_fixed hwf u hu

theorem reduction_proof : Reduction T Θ := by
  intro G hwf
  refine ⟨δ_pos hwf, fun u _ => F_mem_cube hwf u, fun u u' _ _ => F_contraction hwf u u',
    fun u u' hu hu' => F_fixed_unique hwf u u' hu hu', fun u hu => ?_⟩
  obtain ⟨hfeas, hsound⟩ := decode_fixed hwf u hu
  obtain ⟨x, f, v, l, h⟩ := hfeas
  exact ⟨fix_cube hwf u hu, ⟨x, f, v, l, h⟩, hsound, x, f, hsound x f v l h⟩

end Final

end Contraction
end Bssg
