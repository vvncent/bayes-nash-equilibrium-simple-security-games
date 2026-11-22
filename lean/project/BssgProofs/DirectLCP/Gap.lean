import BssgProofs.DirectLCP.Proofs

/-!
# The gap lemma [DL Lemma dl:lem:gap] and the main theorem

Generic LP facts (vertex walk along tight-row spans, Cramer's rule, `|det| ≤ n! C^n`), then the
gap lemma for the relaxed pattern LP, then `main_proof : MainTheorem T Θ`.
-/

namespace Bssg
namespace DirectLCP

open Finset Matrix

set_option linter.unusedSectionVars false

section LP

variable {V Rw : Type*} [Fintype V] [DecidableEq V] [Fintype Rw] [DecidableEq Rw]

/-- `|det M| ≤ n! C^n` for integer entries bounded by `C`. -/
theorem abs_det_le (M : Matrix V V ℤ) (C : ℕ) (hM : ∀ i j, |M i j| ≤ C) :
    |M.det| ≤ (Fintype.card V).factorial * (C : ℤ) ^ Fintype.card V := by
  rw [det_apply]
  refine le_trans (abs_sum_le_sum_abs _ _) ?_
  have : ∀ σ : Equiv.Perm V, |Equiv.Perm.sign σ • ∏ i, M (σ i) i| ≤ (C : ℤ) ^ Fintype.card V := by
    intro σ
    have hp : |∏ i, M (σ i) i| ≤ (C : ℤ) ^ Fintype.card V := by
      rw [abs_prod]
      calc ∏ i, |M (σ i) i| ≤ ∏ _i : V, (C : ℤ) := by
            gcongr with i _; exact hM _ _
        _ = (C : ℤ) ^ Fintype.card V := by simp
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simpa [h] using hp
  refine le_trans (sum_le_sum fun σ _ => this σ) ?_
  simp [Fintype.card_perm]

/-- Span of the rows of `a ⬝ y ≥ b` that are tight at `y`. -/
def tightSpan (a : Rw → V → ℚ) (b : Rw → ℚ) (y : V → ℚ) : Submodule ℚ (V → ℚ) :=
  Submodule.span ℚ (a '' {r | a r ⬝ᵥ y = b r})

theorem exists_perp (W : Submodule ℚ (V → ℚ)) (hW : W ≠ ⊤) :
    ∃ d : V → ℚ, d ≠ 0 ∧ ∀ w ∈ W, w ⬝ᵥ d = 0 := by
  obtain ⟨f, hf0, hle⟩ := W.exists_le_ker_of_lt_top (lt_top_iff_ne_top.mpr hW)
  refine ⟨fun i => f (fun j => if i = j then 1 else 0), ?_, ?_⟩
  · intro h
    apply hf0
    apply LinearMap.ext
    intro x
    rw [LinearMap.pi_apply_eq_sum_univ f x]
    simp [fun i => congrFun h i]
  · intro w hw
    have := hle hw
    rw [LinearMap.mem_ker] at this
    rw [LinearMap.pi_apply_eq_sum_univ f w] at this
    simpa [dotProduct, smul_eq_mul] using this

/-- From a feasible point of a polyhedron with trivial recession cone one reaches a vertex
(tight rows spanning everything) without increasing a linear objective `c`. -/
theorem exists_vertex (a : Rw → V → ℚ) (b : Rw → ℚ)
    (hrec : ∀ d : V → ℚ, (∀ r, 0 ≤ a r ⬝ᵥ d) → d = 0) (c : V → ℚ) :
    ∀ (m : ℕ) (y : V → ℚ), (∀ r, b r ≤ a r ⬝ᵥ y) →
      Fintype.card V - Module.finrank ℚ (tightSpan a b y) = m →
      ∃ y', (∀ r, b r ≤ a r ⬝ᵥ y') ∧ c ⬝ᵥ y' ≤ c ⬝ᵥ y ∧ tightSpan a b y' = ⊤ := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m IH =>
  intro y hy hm
  by_cases htop : tightSpan a b y = ⊤
  · exact ⟨y, hy, le_rfl, htop⟩
  obtain ⟨d0, hd0, hperp0⟩ := exists_perp _ htop
  obtain ⟨d, hd, hperp, hcd⟩ : ∃ d : V → ℚ, d ≠ 0 ∧ (∀ w ∈ tightSpan a b y, w ⬝ᵥ d = 0) ∧
      c ⬝ᵥ d ≤ 0 := by
    by_cases h : c ⬝ᵥ d0 ≤ 0
    · exact ⟨d0, hd0, hperp0, h⟩
    · refine ⟨-d0, neg_ne_zero.mpr hd0, fun w hw => by rw [dotProduct_neg, hperp0 w hw, neg_zero],
        ?_⟩
      rw [dotProduct_neg]; linarith
  have hex : ∃ r, a r ⬝ᵥ d < 0 := by
    by_contra h; push Not at h; exact hd (hrec d h)
  set S := univ.filter fun r => a r ⬝ᵥ d < 0 with hS
  have hSne : S.Nonempty := by obtain ⟨r, hr⟩ := hex; exact ⟨r, by simp [hS, hr]⟩
  set t : Rw → ℚ := fun r => (a r ⬝ᵥ y - b r) / (-(a r ⬝ᵥ d)) with ht
  obtain ⟨rs, hrsS, hrs⟩ := exists_mem_eq_inf' hSne t
  set ts := S.inf' hSne t with hts
  have hts0 : 0 ≤ ts := le_inf' _ _ fun r hr => by
    have : a r ⬝ᵥ d < 0 := by simpa [hS] using hr
    exact div_nonneg (by linarith [hy r]) (by linarith)
  set y' := y + ts • d with hy'
  have hdot : ∀ w, w ⬝ᵥ y' = w ⬝ᵥ y + ts * (w ⬝ᵥ d) := by
    intro w; simp [hy', dotProduct_add, dotProduct_smul]
  have hfeas : ∀ r, b r ≤ a r ⬝ᵥ y' := by
    intro r; rw [hdot]
    by_cases hr : a r ⬝ᵥ d < 0
    · have hle : ts ≤ t r := inf'_le _ (by simp [hS, hr])
      have hpos : 0 < -(a r ⬝ᵥ d) := by linarith
      have : ts * (-(a r ⬝ᵥ d)) ≤ a r ⬝ᵥ y - b r := by
        have := mul_le_mul_of_nonneg_right hle hpos.le
        rwa [ht, div_mul_cancel₀ _ hpos.ne'] at this
      linarith
    · push Not at hr; nlinarith [hy r]
  have hle_span : tightSpan a b y ≤ tightSpan a b y' := by
    apply Submodule.span_mono
    rintro _ ⟨r, hr, rfl⟩
    refine ⟨r, ?_, rfl⟩
    simp only [Set.mem_setOf_eq] at hr ⊢
    rw [hdot, hperp (a r) (Submodule.subset_span ⟨r, hr, rfl⟩), mul_zero, add_zero, hr]
  have hneg : a rs ⬝ᵥ d < 0 := by simpa [hS] using hrsS
  have hrs_tight : a rs ⬝ᵥ y' = b rs := by
    rw [hdot, hrs]; simp only [ht]
    have hne : a rs ⬝ᵥ d ≠ 0 := hneg.ne
    field_simp
    ring
  have hlt : tightSpan a b y < tightSpan a b y' := by
    refine lt_of_le_of_ne hle_span fun heq => ?_
    have hmem : a rs ∈ tightSpan a b y := heq ▸ Submodule.subset_span ⟨rs, hrs_tight, rfl⟩
    have := hperp _ hmem
    linarith
  have hfr := Submodule.finrank_lt_finrank_of_lt hlt
  have hfr' : Module.finrank ℚ (tightSpan a b y') ≤ Fintype.card V := by
    have := Submodule.finrank_le (tightSpan a b y'); simpa using this
  obtain ⟨y'', h1, h2, h3⟩ := IH _ (by omega) y' hfeas rfl
  refine ⟨y'', h1, le_trans h2 ?_, h3⟩
  rw [hdot]; nlinarith

/-- At a vertex of an integer system, each coordinate is `p / q` with `0 < |q| ≤ n! C^n`. -/
theorem vertex_value (a : Rw → V → ℚ) (b : Rw → ℚ) (C : ℕ)
    (ha : ∀ r v, ∃ m : ℤ, a r v = m ∧ |m| ≤ C) (hb : ∀ r, ∃ m : ℤ, b r = m ∧ |m| ≤ C)
    (y : V → ℚ) (hy : tightSpan a b y = ⊤) (τ : V) :
    ∃ p q : ℤ, q ≠ 0 ∧ |q| ≤ (Fintype.card V).factorial * (C : ℤ) ^ Fintype.card V ∧
      y τ = p / q := by
  classical
  let Tt := {r // a r ⬝ᵥ y = b r}
  let v : Tt → (V → ℚ) := fun r => a r.1
  have hspan : Submodule.span ℚ (Set.range v) = ⊤ := by
    rw [← hy]; congr 1; ext w; constructor
    · rintro ⟨r, rfl⟩; exact ⟨r.1, r.2, rfl⟩
    · rintro ⟨r, hr, rfl⟩; exact ⟨⟨r, hr⟩, rfl⟩
  obtain ⟨κ, f, hf, hsp, hli⟩ := exists_linearIndependent' ℚ v
  haveI : Finite κ := Finite.of_injective f hf
  haveI : Fintype κ := Fintype.ofFinite κ
  have hsp' : Submodule.span ℚ (Set.range (v ∘ f)) = ⊤ := by rw [hsp, hspan]
  let bas : Module.Basis κ ℚ (V → ℚ) := Module.Basis.mk hli (by rw [hsp'])
  have hcard : Fintype.card κ = Fintype.card V := by
    have := Module.finrank_eq_card_basis bas
    simpa using this.symm
  let e : κ ≃ V := Fintype.equivOfCardEq hcard
  let G : Matrix V V ℚ := Matrix.of fun p => v (f (e.symm p))
  let h : V → ℚ := fun p => b (f (e.symm p)).1
  have hGy : G *ᵥ y = h := by
    ext p; exact (f (e.symm p)).2
  have hGli : LinearIndependent ℚ G.row := hli.comp e.symm e.symm.injective
  have hGu : IsUnit G := Matrix.linearIndependent_row_iff_isUnit.mp hGli
  have hdet : G.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det G).mp hGu).ne_zero
  have hcr : G.det * y τ = (G.updateCol τ h).det := by
    have : G.det • y = cramer G h := by
      rw [cramer_eq_adjugate_mulVec, ← hGy, mulVec_mulVec, adjugate_mul, smul_mulVec, one_mulVec]
    have := congrFun this τ
    rw [cramer_apply] at this
    simpa using this
  choose am ham using ha
  choose bm hbm using hb
  let Gz : Matrix V V ℤ := Matrix.of fun p w => am (f (e.symm p)).1 w
  let hz : V → ℤ := fun p => bm (f (e.symm p)).1
  have hGcast : G = Gz.map (Int.castRingHom ℚ) := by
    ext p w; simp [G, Gz, v, (ham _ _).1]
  have hcolcast : G.updateCol τ h = (Gz.updateCol τ hz).map (Int.castRingHom ℚ) := by
    ext p w
    by_cases hw : w = τ
    · subst hw; simp [h, hz, (hbm _).1]
    · simp [updateCol_ne hw, G, Gz, v, (ham _ _).1]
  have hdetG : G.det = (Gz.det : ℚ) := by
    rw [hGcast, ← RingHom.mapMatrix_apply, ← RingHom.map_det]; rfl
  have hdetC : (G.updateCol τ h).det = ((Gz.updateCol τ hz).det : ℚ) := by
    rw [hcolcast, ← RingHom.mapMatrix_apply, ← RingHom.map_det]; rfl
  have hq : Gz.det ≠ 0 := by intro h0; apply hdet; rw [hdetG, h0]; simp
  refine ⟨(Gz.updateCol τ hz).det, Gz.det, hq, abs_det_le Gz C fun p w => (ham _ _).2, ?_⟩
  rw [← hdetG, ← hdetC, ← hcr]
  field_simp

end LP

/-! ## The relaxed pattern LP as a row system -/

section Rows

variable {T Θ : Type*} [Fintype T] [DecidableEq T] [Fintype Θ] [DecidableEq Θ] [Nonempty T]
variable (G : BSSG T Θ)

/-- Which of the `5N+2` rows belong to the relaxed LP of pattern `P`. -/
def isActive (P : Finset (Idx Θ T)) : RowIdx Θ T → Bool
  | .inl _ => true
  | .inr (.inl k) => decide (k ∈ P)
  | .inr (.inr (.inl _)) => true
  | .inr (.inr (.inr (.inl _))) => true
  | .inr (.inr (.inr (.inr (.inl k)))) => decide (k ∉ P)
  | .inr (.inr (.inr (.inr (.inr _)))) => true

/-- `(z, τ)` as one vector on `Idx ⊕ Unit`. -/
def zτ (z : Idx Θ T → ℚ) (τ : ℚ) : Idx Θ T ⊕ Unit → ℚ := Sum.elim z (fun _ => τ)

theorem dot_R1 (k : Idx Θ T) (z : Idx Θ T → ℚ) (τ : ℚ) :
    rowCoef G (.inl k) ⬝ᵥ zτ z τ = slack (lcpq G) (lcpM G) z k - lcpq G k + τ := by
  simp [rowCoef, zτ, dotProduct, Fintype.sum_sum_type, slack, mulVec]

theorem dot_R2 (k : Idx Θ T) (z : Idx Θ T → ℚ) (τ : ℚ) :
    rowCoef G (.inr (.inl k)) ⬝ᵥ zτ z τ = -(slack (lcpq G) (lcpM G) z k - lcpq G k) + τ := by
  simp [rowCoef, zτ, dotProduct, Fintype.sum_sum_type, slack, mulVec]

theorem dot_R3 (k : Idx Θ T) (z : Idx Θ T → ℚ) (τ : ℚ) :
    rowCoef G (.inr (.inr (.inl k))) ⬝ᵥ zτ z τ = z k := by
  simp [rowCoef, zτ, dotProduct, Fintype.sum_sum_type]

theorem dot_R3' (k : Idx Θ T) (z : Idx Θ T → ℚ) (τ : ℚ) :
    rowCoef G (.inr (.inr (.inr (.inl k)))) ⬝ᵥ zτ z τ = -z k := by
  simp [rowCoef, zτ, dotProduct, Fintype.sum_sum_type]

theorem dot_R4 (k : Idx Θ T) (z : Idx Θ T → ℚ) (τ : ℚ) :
    rowCoef G (.inr (.inr (.inr (.inr (.inl k))))) ⬝ᵥ zτ z τ = -z k := by
  simp [rowCoef, zτ, dotProduct, Fintype.sum_sum_type]

theorem dot_R5 (bo : Bool) (z : Idx Θ T → ℚ) (τ : ℚ) :
    rowCoef G (.inr (.inr (.inr (.inr (.inr bo))))) ⬝ᵥ zτ z τ = if bo then -τ else τ := by
  cases bo <;> simp [rowCoef, zτ, dotProduct, Fintype.sum_sum_type]

/-- (R1)–(R5) are exactly the active rows `rhs ≤ coef ⬝ (z, τ)`. -/
theorem relaxed_iff (P : Finset (Idx Θ T)) (z : Idx Θ T → ℚ) (τ : ℚ) :
    IsRelaxedFeasible G P z τ ↔
      ∀ r, isActive P r = true → rowRhs G r ≤ rowCoef G r ⬝ᵥ zτ z τ := by
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, h6⟩ r hr
    rcases r with k | k | k | k | k | bo
    · rw [dot_R1]; simp only [rowRhs]; linarith [h1 k]
    · have hk : k ∈ P := by simpa [isActive] using hr
      rw [dot_R2]; simp only [rowRhs]; linarith [h2 k hk]
    · rw [dot_R3]; simp only [rowRhs]; exact (h3 k).1
    · rw [dot_R3']; simp only [rowRhs]; linarith [(h3 k).2]
    · have hk : k ∉ P := by simpa [isActive] using hr
      rw [dot_R4]; simp only [rowRhs]; linarith [h4 k hk]
    · rw [dot_R5]; cases bo <;> simp only [rowRhs] <;> simp <;> linarith
  · intro h
    refine ⟨fun k => ?_, fun k hk => ?_, fun k => ⟨?_, ?_⟩, fun k hk => ?_, ?_, ?_⟩
    · have := h (.inl k) rfl; rw [dot_R1] at this; simp only [rowRhs] at this; linarith
    · have := h (.inr (.inl k)) (by simp [isActive, hk]); rw [dot_R2] at this
      simp only [rowRhs] at this; linarith
    · have := h (.inr (.inr (.inl k))) rfl; rw [dot_R3] at this; simpa [rowRhs] using this
    · have := h (.inr (.inr (.inr (.inl k)))) rfl; rw [dot_R3'] at this
      simp only [rowRhs] at this; linarith
    · have := h (.inr (.inr (.inr (.inr (.inl k))))) (by simp [isActive, hk]); rw [dot_R4] at this
      simp only [rowRhs] at this; linarith
    · have := h (.inr (.inr (.inr (.inr (.inr false))))) rfl; rw [dot_R5] at this
      simpa [rowRhs] using this
    · have := h (.inr (.inr (.inr (.inr (.inr true))))) rfl; rw [dot_R5] at this
      simp [rowRhs] at this; linarith

theorem rowDen_pos (r : RowIdx Θ T) : 0 < rowDen G r := by
  unfold rowDen
  apply Nat.lcm_pos
  · apply Nat.pos_of_ne_zero
    rw [Ne, Finset.lcm_eq_zero_iff]
    simp [Rat.den_ne_zero]
  · exact Rat.den_pos _

theorem int_of_den_dvd (q : ℚ) (L : ℕ) (h : q.den ∣ L) : ∃ m : ℤ, (L : ℚ) * q = m := by
  obtain ⟨k, rfl⟩ := h
  refine ⟨k * q.num, ?_⟩
  push_cast
  rw [← Rat.mul_den_eq_num]; ring

/-- A cleared row entry is an integer bounded by `C`. -/
theorem cleared_int (r : RowIdx Θ T) (q : ℚ) (hden : q.den ∣ rowDen G r)
    (hle : ((rowDen G r : ℚ) * q).num.natAbs ≤ cC G) :
    ∃ m : ℤ, (rowDen G r : ℚ) * q = m ∧ |m| ≤ (cC G : ℕ) := by
  obtain ⟨m, hm⟩ := int_of_den_dvd q _ hden
  refine ⟨m, hm, ?_⟩
  rw [hm, Rat.num_intCast] at hle
  rw [← Int.natCast_natAbs]; exact_mod_cast hle

theorem coef_int (r : RowIdx Θ T) (c : Idx Θ T ⊕ Unit) :
    ∃ m : ℤ, (rowDen G r : ℚ) * rowCoef G r c = m ∧ |m| ≤ (cC G : ℕ) := by
  refine cleared_int G r _ ((Finset.dvd_lcm (mem_univ c)).trans (Nat.dvd_lcm_left _ _)) ?_
  refine le_trans ?_ (le_max_right _ _)
  refine le_trans ?_ (Finset.le_sup (f := fun ρ : RowIdx Θ T =>
    (univ.sup fun c => ((rowDen G ρ : ℚ) * rowCoef G ρ c).num.natAbs) ⊔
      ((rowDen G ρ : ℚ) * rowRhs G ρ).num.natAbs) (mem_univ r))
  exact le_trans (Finset.le_sup (f := fun c => ((rowDen G r : ℚ) * rowCoef G r c).num.natAbs)
    (mem_univ c)) le_sup_left

theorem rhs_int (r : RowIdx Θ T) :
    ∃ m : ℤ, (rowDen G r : ℚ) * rowRhs G r = m ∧ |m| ≤ (cC G : ℕ) := by
  refine cleared_int G r _ (Nat.dvd_lcm_right _ _) ?_
  refine le_trans ?_ (le_max_right _ _)
  refine le_trans ?_ (Finset.le_sup (f := fun ρ : RowIdx Θ T =>
    (univ.sup fun c => ((rowDen G ρ : ℚ) * rowCoef G ρ c).num.natAbs) ⊔
      ((rowDen G ρ : ℚ) * rowRhs G ρ).num.natAbs) (mem_univ r))
  exact le_sup_right

/-- The active rows of pattern `P`. -/
abbrev ARow (P : Finset (Idx Θ T)) := {r : RowIdx Θ T // isActive P r = true}

/-- Cleared (integer) coefficients of the active rows. -/
def ga (P : Finset (Idx Θ T)) : ARow P → (Idx Θ T ⊕ Unit) → ℚ :=
  fun r => (rowDen G r.1 : ℚ) • rowCoef G r.1

/-- Cleared (integer) right sides of the active rows. -/
def gb (P : Finset (Idx Θ T)) : ARow P → ℚ := fun r => (rowDen G r.1 : ℚ) * rowRhs G r.1

theorem feas_iff (P : Finset (Idx Θ T)) (z : Idx Θ T → ℚ) (τ : ℚ) :
    IsRelaxedFeasible G P z τ ↔ ∀ r : ARow P, gb G P r ≤ ga G P r ⬝ᵥ zτ z τ := by
  rw [relaxed_iff]
  constructor
  · intro h r
    simp only [ga, gb, smul_dotProduct, smul_eq_mul]
    exact mul_le_mul_of_nonneg_left (h r.1 r.2) (by positivity)
  · intro h r hr
    have := h ⟨r, hr⟩
    simp only [ga, gb, smul_dotProduct, smul_eq_mul] at this
    exact le_of_mul_le_mul_left this (by exact_mod_cast rowDen_pos G r)

theorem zτ_eta (y : Idx Θ T ⊕ Unit → ℚ) : zτ (fun k => y (.inl k)) (y (.inr ())) = y := by
  ext (k | u) <;> rfl

theorem grec (P : Finset (Idx Θ T)) : ∀ d, (∀ r : ARow P, 0 ≤ ga G P r ⬝ᵥ d) → d = 0 := by
  intro d h
  have h' : ∀ r, isActive P r = true →
      0 ≤ rowCoef G r ⬝ᵥ zτ (fun k => d (.inl k)) (d (.inr ())) := fun r hr => by
    have := h ⟨r, hr⟩
    simp only [ga, smul_dotProduct, smul_eq_mul] at this
    rw [zτ_eta]
    exact (mul_nonneg_iff_of_pos_left (by exact_mod_cast rowDen_pos G r)).mp this
  ext (k | u)
  · have a1 := h' (.inr (.inr (.inl k))) rfl
    have a2 := h' (.inr (.inr (.inr (.inl k)))) rfl
    simp only [dot_R3] at a1; simp only [dot_R3'] at a2
    simp only [Pi.zero_apply]; linarith
  · have a1 := h' (.inr (.inr (.inr (.inr (.inr false))))) rfl
    have a2 := h' (.inr (.inr (.inr (.inr (.inr true))))) rfl
    simp only [dot_R5] at a1 a2
    simp at a1 a2 ⊢; linarith

theorem card_vars : Fintype.card (Idx Θ T ⊕ Unit) = Fintype.card (Idx Θ T) + 1 := by
  simp

theorem vertex_cand (P : Finset (Idx Θ T)) (y : Idx Θ T ⊕ Unit → ℚ)
    (hy : ∀ r : ARow P, gb G P r ≤ ga G P r ⬝ᵥ y) :
    ∃ y', (∀ r : ARow P, gb G P r ≤ ga G P r ⬝ᵥ y') ∧ y' (.inr ()) ≤ y (.inr ()) ∧
      ∃ p q : ℤ, |p| ≤ (cQ G : ℤ) ∧ |q| ≤ (cQ G : ℤ) ∧ y' (.inr ()) = p / q := by
  classical
  obtain ⟨y', hf, hc, htop⟩ := exists_vertex (ga G P) (gb G P) (grec G P)
    (Pi.single (.inr ()) 1) _ y hy rfl
  simp only [single_dotProduct, one_mul] at hc
  obtain ⟨p, q, hq, hqle, hval⟩ := vertex_value (ga G P) (gb G P) (cC G)
    (fun r c => coef_int G r.1 c) (fun r => rhs_int G r.1) y' htop (.inr ())
  have hNat : (Fintype.card (Idx Θ T ⊕ Unit)).factorial * cC G ^ Fintype.card (Idx Θ T ⊕ Unit)
      ≤ cQ G := by
    rw [cQ, ← card_vars, mul_pow]
    exact Nat.mul_le_mul_right _ (Nat.factorial_le_pow _)
  have hqQ : |q| ≤ (cQ G : ℤ) := le_trans hqle (by exact_mod_cast hNat)
  have hrel : IsRelaxedFeasible G P (fun k => y' (.inl k)) (y' (.inr ())) :=
    (feas_iff G P _ _).mpr (by rw [zτ_eta]; exact hf)
  have h0 := hrel.2.2.2.2.1
  have h1 := hrel.2.2.2.2.2
  have hq0 : (q : ℚ) ≠ 0 := by exact_mod_cast hq
  have hp : (p : ℚ) = y' (.inr ()) * q := by rw [hval]; field_simp
  have hpq : |(p : ℚ)| ≤ |(q : ℚ)| := by
    rw [hp, abs_mul, abs_of_nonneg h0]
    exact mul_le_of_le_one_left (abs_nonneg _) h1
  have hpq' : |p| ≤ |q| := by exact_mod_cast hpq
  exact ⟨y', hf, hc, p, q, le_trans hpq' hqQ, hqQ, hval⟩

end Rows

/-! ## The gap lemma and the main theorem -/

section GapMain

variable {T Θ : Type*} [Fintype T] [DecidableEq T] [Fintype Θ] [DecidableEq Θ] [Nonempty T]

/-- [DL Lemma dl:lem:gap] for one game. -/
theorem gap_lemma (G : BSSG T Θ) : GapLemma T Θ G := by
  classical
  rintro P ⟨z, τ, hzτ⟩
  set QZ : ℤ := (cQ G : ℤ) with hQZ
  set Cand : Finset ℚ :=
    ((Icc (-QZ) QZ) ×ˢ (Icc (-QZ) QZ)).image (fun pq : ℤ × ℤ => (pq.1 : ℚ) / pq.2) with hCand
  have key : ∀ y, (∀ r : ARow P, gb G P r ≤ ga G P r ⬝ᵥ y) →
      ∃ y', (∀ r : ARow P, gb G P r ≤ ga G P r ⬝ᵥ y') ∧ y' (.inr ()) ≤ y (.inr ()) ∧
        y' (.inr ()) ∈ Cand := by
    intro y hy
    obtain ⟨y', hy', hle, p, q, hp, hq, hv⟩ := vertex_cand G P y hy
    exact ⟨y', hy', hle, mem_image.mpr ⟨(p, q),
      mem_product.mpr ⟨mem_Icc.mpr (abs_le.mp hp), mem_Icc.mpr (abs_le.mp hq)⟩, hv.symm⟩⟩
  set Vals := Cand.filter
    (fun v => ∃ y, (∀ r : ARow P, gb G P r ≤ ga G P r ⬝ᵥ y) ∧ y (.inr ()) = v) with hVals
  obtain ⟨y1, hy1, -, hc1⟩ := key _ ((feas_iff G P z τ).mp hzτ)
  have hne : Vals.Nonempty := ⟨_, mem_filter.mpr ⟨hc1, y1, hy1, rfl⟩⟩
  have hmem := Vals.min'_mem hne
  obtain ⟨hcand, y₀, hy₀, hy₀τ⟩ := mem_filter.mp hmem
  have hrel0 : IsRelaxedFeasible G P (fun k => y₀ (.inl k)) (y₀ (.inr ())) :=
    (feas_iff G P _ _).mpr (by rw [zτ_eta]; exact hy₀)
  refine ⟨fun k => y₀ (.inl k), Vals.min' hne, by rw [← hy₀τ]; exact hrel0, ?_, ?_⟩
  · intro z' τ' h'
    obtain ⟨y', hy', hle, hc'⟩ := key _ ((feas_iff G P z' τ').mp h')
    have h1 : Vals.min' hne ≤ y' (.inr ()) := Vals.min'_le _ (mem_filter.mpr ⟨hc', y', hy', rfl⟩)
    have h2 : zτ z' τ' (.inr ()) = τ' := rfl
    linarith
  · have h0 : 0 ≤ Vals.min' hne := hy₀τ ▸ hrel0.2.2.2.2.1
    rcases h0.lt_or_eq with hpos | hzero
    · right
      obtain ⟨⟨p, q⟩, hpq, hval⟩ := mem_image.mp hcand
      simp only [mem_product, mem_Icc] at hpq
      simp only at hval
      have hq0 : (q : ℚ) ≠ 0 := by intro h; rw [h, div_zero] at hval; linarith
      have hp0 : p ≠ 0 := by intro h; rw [h, Int.cast_zero, zero_div] at hval; linarith
      have habs : Vals.min' hne = |(p : ℚ)| / |(q : ℚ)| := by
        rw [← abs_div, hval, abs_of_pos hpos]
      have hp1 : (1 : ℚ) ≤ |(p : ℚ)| := by
        have : (1 : ℤ) ≤ |p| := Int.one_le_abs hp0
        exact_mod_cast this
      have hqQ : |(q : ℚ)| ≤ (cQ G : ℚ) := by
        have : |q| ≤ QZ := abs_le.mpr hpq.2
        rw [hQZ] at this; exact_mod_cast this
      have hq1 : 0 < |(q : ℚ)| := abs_pos.mpr hq0
      rw [habs, div_le_div_iff₀ (by linarith) hq1]
      nlinarith
    · left; exact hzero.symm

variable (T Θ)

/-- [DL Lemma dl:lem:gap]. -/
theorem gap_proof : Gap T Θ := fun G => gap_lemma G

/-- [DL Thm. dl:thm:main] (mathematical content), unconditionally. -/
theorem main_proof : MainTheorem T Θ := main_proof_of_gap T Θ (gap_proof T Θ)

end GapMain

end DirectLCP
end Bssg
