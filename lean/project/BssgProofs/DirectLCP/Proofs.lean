import BssgProofs.DirectLCP.Statements
import BssgProofs.Proofs.Embedding

/-!
# Exact BNE reduces to one P-matrix LCP: proofs

Proofs of the statements in `Statements.lean`.  No `sorry`, `admit` or `axiom`.  The gap lemma [DL Lemma dl:lem:gap] enters
`main_proof_of_gap` as a hypothesis here; it is proved in `Gap.lean`, which derives `main_proof`.

Route of the P₀ proof (differs from [DL], see `DEFINITIONS-directlcp.md`): induction on the size of
the selection, by Laplace expansion along a column with one nonzero entry of `D`; when no such
column exists and `d > 0`, every column of `D` is a full attack column or the budget column, the
vector `y = (1 on type rows, −1/d_j on target rows)` kills every attack column of `D`, so either
`det D = 0` (no budget column) or `det D · y = κ · adj(D)_{λ,·}` with `κ > 0`, and the Laplace
expansion of `det B` along the budget column has terms of one sign by the induction hypothesis on
the cofactors.  Zero `d_j` are reached by continuity in `d`.
-/

namespace Bssg
namespace DirectLCP

open Finset Matrix

set_option linter.unusedSectionVars false

/-! ## P₀ core: `det B_{ρφ} · det D_{ρφ} ≥ 0` -/

section P0core

variable {T Θ : Type*} [Fintype T] [DecidableEq T] [Fintype Θ] [DecidableEq Θ]

/-- Laplace expansion along a column with a single possibly nonzero entry. -/
theorem det_eq_of_col_single {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ) (c r0 : Fin (n + 1))
    (h : ∀ r, r ≠ r0 → A r c = 0) :
    A.det = (-1) ^ (r0 + c : ℕ) * A r0 c * (A.submatrix r0.succAbove c.succAbove).det := by
  rw [det_succ_column A c, Finset.sum_eq_single r0]
  · intro r _ hr; rw [h r hr]; ring
  · intro h'; exact absurd (mem_univ _) h'

theorem incMat_entry_mul_nonneg (β : Θ → T → ℚ) (hβ : ∀ i j, 0 ≤ β i j) (d : T → ℚ)
    (hd : ∀ j, 0 ≤ d j) (r : RIdx Θ T) (c : FIdx Θ T) :
    0 ≤ incMat β r c * incMat (fun _ j => d j) r c := by
  rcases r with i | j <;> rcases c with ⟨i', j'⟩ | j' | _ <;> simp only [incMat, of_apply] <;>
    (try split_ifs) <;> first | exact mul_nonneg (hβ _ _) (hd _) | norm_num

/-- With `d > 0`, a zero entry of `D` is a zero entry of `B`. -/
theorem incMat_zero_of_zero (β : Θ → T → ℚ) (d : T → ℚ) (hd : ∀ j, 0 < d j) (r : RIdx Θ T)
    (c : FIdx Θ T) (h : incMat (fun _ j => d j) r c = 0) : incMat β r c = 0 := by
  rcases r with i | j <;> rcases c with ⟨i', j'⟩ | j' | _ <;> simp only [incMat, of_apply] at h ⊢ <;>
    (try split_ifs at h ⊢) <;> first | rfl | (subst_vars; exact absurd h (hd _).ne') | norm_num at h

theorem p0core_pos (β : Θ → T → ℚ) (hβ : ∀ i j, 0 ≤ β i j) (d : T → ℚ) (hd : ∀ j, 0 < d j) :
    ∀ (n : ℕ) (ρ : Fin n → RIdx Θ T) (φ : Fin n → FIdx Θ T),
      0 ≤ ((incMat β).submatrix ρ φ).det * ((incMat (fun _ j => d j)).submatrix ρ φ).det
  | 0, ρ, φ => by simp
  | n + 1, ρ, φ => by
    set B := (incMat β).submatrix ρ φ with hBdef
    set D := (incMat (fun _ j => d j)).submatrix ρ φ with hDdef
    have IH := p0core_pos β hβ d hd n
    -- non-injective rows or columns
    by_cases hρ : Function.Injective ρ
    swap
    · obtain ⟨a, b, hab, hne⟩ : ∃ a b, ρ a = ρ b ∧ a ≠ b := by
        simp only [Function.Injective, not_forall] at hρ
        obtain ⟨a, b, h1, h2⟩ := hρ; exact ⟨a, b, h1, h2⟩
      have : B.det = 0 := det_zero_of_row_eq hne (by ext c; simp [hBdef, hab])
      simp [this]
    by_cases hφ : Function.Injective φ
    swap
    · obtain ⟨a, b, hab, hne⟩ : ∃ a b, φ a = φ b ∧ a ≠ b := by
        simp only [Function.Injective, not_forall] at hφ
        obtain ⟨a, b, h1, h2⟩ := hφ; exact ⟨a, b, h1, h2⟩
      have : B.det = 0 := det_zero_of_column_eq hne (by intro r; simp [hBdef, hab])
      simp [this]
    -- a column with at most one nonzero entry
    by_cases hcol : ∃ c r0, ∀ r, r ≠ r0 → D r c = 0
    · obtain ⟨c, r0, h⟩ := hcol
      have hB : ∀ r, r ≠ r0 → B r c = 0 := fun r hr =>
        incMat_zero_of_zero β d hd _ _ (h r hr)
      rw [det_eq_of_col_single B c r0 hB, det_eq_of_col_single D c r0 h]
      have h1 := IH (ρ ∘ r0.succAbove) (φ ∘ c.succAbove)
      have h2 := incMat_entry_mul_nonneg β hβ d (fun j => (hd j).le) (ρ r0) (φ c)
      have e1 : B.submatrix r0.succAbove c.succAbove = (incMat β).submatrix (ρ ∘ r0.succAbove)
          (φ ∘ c.succAbove) := rfl
      have e2 : D.submatrix r0.succAbove c.succAbove =
          (incMat (fun _ j => d j)).submatrix (ρ ∘ r0.succAbove) (φ ∘ c.succAbove) := rfl
      rw [e1, e2]
      have h3 : B r0 c * D r0 c = incMat β (ρ r0) (φ c) * incMat (fun _ j => d j) (ρ r0) (φ c) :=
        rfl
      have hsq : ((-1 : ℚ) ^ (r0 + c : ℕ)) * ((-1 : ℚ) ^ (r0 + c : ℕ)) = 1 := by
        rw [← mul_pow]; norm_num
      calc (0 : ℚ) ≤ (B r0 c * D r0 c) * (((incMat β).submatrix (ρ ∘ r0.succAbove)
              (φ ∘ c.succAbove)).det * ((incMat (fun _ j => d j)).submatrix (ρ ∘ r0.succAbove)
              (φ ∘ c.succAbove)).det) := by rw [h3]; exact mul_nonneg h2 h1
        _ = _ := by linear_combination (B r0 c * D r0 c * (((incMat β).submatrix
              (ρ ∘ r0.succAbove) (φ ∘ c.succAbove)).det * ((incMat (fun _ j => d j)).submatrix
              (ρ ∘ r0.succAbove) (φ ∘ c.succAbove)).det)) * hsq.symm
    push Not at hcol
    -- every column has two nonzero entries in `D`; classify the columns
    have hcap : ∀ c j, φ c ≠ .inr (.inl j) := by
      intro c j hc
      by_cases hex : ∃ r0, ρ r0 = .inr j
      · obtain ⟨r0, hr0⟩ := hex
        obtain ⟨r, hr, hne⟩ := hcol c r0
        apply hne
        simp only [hDdef, submatrix_apply, hc]
        rcases hρr : ρ r with i | j'
        · simp [incMat]
        · simp only [incMat, of_apply]
          rw [if_neg]; intro hjj; subst hjj; exact hr (hρ (hρr.trans hr0.symm))
      · push Not at hex
        obtain ⟨r, -, hne⟩ := hcol c 0
        apply hne
        simp only [hDdef, submatrix_apply, hc]
        rcases hρr : ρ r with i | j'
        · simp [incMat]
        · simp only [incMat, of_apply]
          rw [if_neg]; intro hjj; subst hjj; exact hex r hρr
    have hatt : ∀ c i j, φ c = .inl (i, j) → (∃ r, ρ r = .inl i) ∧ ∃ r, ρ r = .inr j := by
      intro c i j hc
      constructor
      · by_contra hex
        push Not at hex
        by_cases hex2 : ∃ r0, ρ r0 = .inr j
        · obtain ⟨r0, hr0⟩ := hex2
          obtain ⟨r, hr, hne⟩ := hcol c r0
          apply hne
          simp only [hDdef, submatrix_apply, hc]
          rcases hρr : ρ r with i' | j'
          · simp only [incMat, of_apply]
            rw [if_neg]; rintro rfl; exact hex r hρr
          · simp only [incMat, of_apply]
            rw [if_neg]; intro hjj; subst hjj; exact hr (hρ (hρr.trans hr0.symm))
        · push Not at hex2
          obtain ⟨r, -, hne⟩ := hcol c 0
          apply hne
          simp only [hDdef, submatrix_apply, hc]
          rcases hρr : ρ r with i' | j'
          · simp only [incMat, of_apply]
            rw [if_neg]; rintro rfl; exact hex r hρr
          · simp only [incMat, of_apply]
            rw [if_neg]; rintro rfl; exact hex2 r hρr
      · by_contra hex
        push Not at hex
        by_cases hex2 : ∃ r0, ρ r0 = .inl i
        · obtain ⟨r0, hr0⟩ := hex2
          obtain ⟨r, hr, hne⟩ := hcol c r0
          apply hne
          simp only [hDdef, submatrix_apply, hc]
          rcases hρr : ρ r with i' | j'
          · simp only [incMat, of_apply]
            rw [if_neg]; rintro rfl; exact hr (hρ (hρr.trans hr0.symm))
          · simp only [incMat, of_apply]
            rw [if_neg]; rintro rfl; exact hex r hρr
        · push Not at hex2
          obtain ⟨r, -, hne⟩ := hcol c 0
          apply hne
          simp only [hDdef, submatrix_apply, hc]
          rcases hρr : ρ r with i' | j'
          · simp only [incMat, of_apply]
            rw [if_neg]; rintro rfl; exact hex2 r hρr
          · simp only [incMat, of_apply]
            rw [if_neg]; rintro rfl; exact hex r hρr
    -- the vector `y`: `1` on type rows, `−1/d_j` on target rows
    set y : Fin (n + 1) → ℚ := fun r => Sum.elim (fun _ => 1) (fun j => -1 / d j) (ρ r) with hy
    have hyatt : ∀ c i j, φ c = .inl (i, j) → (y ᵥ* D) c = 0 := by
      intro c i j hc
      obtain ⟨⟨ru, hru⟩, ⟨rx, hrx⟩⟩ := hatt c i j hc
      have hne : ru ≠ rx := by intro h; rw [h, hrx] at hru; cases hru
      simp only [vecMul, dotProduct]
      rw [Fintype.sum_eq_add ru rx hne]
      · simp only [hy, hDdef, submatrix_apply, hc, hru, hrx, incMat, of_apply, Sum.elim_inl,
          Sum.elim_inr, if_true]
        field_simp [(hd j).ne']; ring
      · rintro r ⟨h1, h2⟩
        simp only [hDdef, submatrix_apply, hc]
        rcases hρr : ρ r with i' | j'
        · simp only [incMat, of_apply]
          rw [if_neg, mul_zero]; rintro rfl; exact h1 (hρ (hρr.trans hru.symm))
        · simp only [incMat, of_apply]
          rw [if_neg, mul_zero]; rintro rfl; exact h2 (hρ (hρr.trans hrx.symm))
    have hy0 : y ≠ 0 := by
      intro h
      have := congrFun h 0
      simp only [hy, Pi.zero_apply] at this
      rcases hρ0 : ρ 0 with i | j <;> rw [hρ0] at this <;> simp at this
      exact (hd j).ne' this
    by_cases hbud : ∃ c0, φ c0 = .inr (.inr ())
    · -- the budget column is selected
      obtain ⟨c0, hc0⟩ := hbud
      set κ : ℚ := (y ᵥ* D) c0 with hκ
      have hother : ∀ c, c ≠ c0 → (y ᵥ* D) c = 0 := by
        intro c hc
        rcases hφc : φ c with ⟨i, j⟩ | j | u
        · exact hyatt c i j hφc
        · exact absurd hφc (hcap c j)
        · exact absurd (hφ (hφc.trans hc0.symm)) hc
      have hκpos : 0 < κ := by
        obtain ⟨r1, -, hr1⟩ := hcol c0 0
        simp only [hκ, vecMul, dotProduct]
        have hterm : ∀ r, 0 ≤ y r * D r c0 := by
          intro r
          simp only [hy, hDdef, submatrix_apply, hc0]
          rcases ρ r with i | j
          · simp [incMat]
          · simp only [incMat, of_apply, Sum.elim_inr]
            have := (hd j); rw [div_mul_eq_mul_div]; positivity
        have hpos : 0 < y r1 * D r1 c0 := by
          simp only [hDdef, submatrix_apply, hc0] at hr1 ⊢
          simp only [hy]
          rcases hρr : ρ r1 with i | j
          · rw [hρr] at hr1; simp [incMat] at hr1
          · simp only [incMat, of_apply, Sum.elim_inr]
            have := (hd j); rw [div_mul_eq_mul_div]; positivity
        exact lt_of_lt_of_le hpos (single_le_sum (fun r _ => hterm r) (mem_univ r1))
      have hyD : y ᵥ* D = Pi.single c0 κ := by
        ext c
        by_cases hc : c = c0
        · subst hc; simp [hκ]
        · rw [hother c hc, Pi.single_eq_of_ne hc]
      -- `det D · y = κ · adj(D)_{c0, ·}`
      have hadj : ∀ r, D.det * y r = κ * adjugate D c0 r := by
        intro r
        have h1 : y ᵥ* (D * adjugate D) = D.det • y := by
          rw [mul_adjugate, vecMul_smul, vecMul_one]
        have h2 : (y ᵥ* D) ᵥ* adjugate D = y ᵥ* (D * adjugate D) := vecMul_vecMul _ _ _
        rw [hyD, h1] at h2
        have := congrFun h2 r
        simp only [Pi.smul_apply, smul_eq_mul] at this
        rw [← this, single_vecMul]
        simp
      -- Laplace expansion of `det B` along the budget column
      have hBexp : B.det = ∑ r, B r c0 * adjugate B c0 r := by
        rw [det_succ_column B c0]
        refine sum_congr rfl fun r _ => ?_
        rw [adjugate_fin_succ_eq_det_submatrix]; ring
      have hIH : ∀ r, 0 ≤ adjugate B c0 r * adjugate D c0 r := by
        intro r
        rw [adjugate_fin_succ_eq_det_submatrix, adjugate_fin_succ_eq_det_submatrix]
        have := IH (ρ ∘ r.succAbove) (φ ∘ c0.succAbove)
        have hsq : ((-1 : ℚ) ^ (r + c0 : ℕ)) * ((-1 : ℚ) ^ (r + c0 : ℕ)) = 1 := by
          rw [← mul_pow]; norm_num
        calc (0 : ℚ) ≤ ((incMat β).submatrix (ρ ∘ r.succAbove) (φ ∘ c0.succAbove)).det *
              ((incMat (fun _ j => d j)).submatrix (ρ ∘ r.succAbove) (φ ∘ c0.succAbove)).det := this
          _ = _ := by
            rw [show B.submatrix r.succAbove c0.succAbove = (incMat β).submatrix (ρ ∘ r.succAbove)
              (φ ∘ c0.succAbove) from rfl, show D.submatrix r.succAbove c0.succAbove =
              (incMat (fun _ j => d j)).submatrix (ρ ∘ r.succAbove) (φ ∘ c0.succAbove) from rfl]
            linear_combination (((incMat β).submatrix (ρ ∘ r.succAbove) (φ ∘ c0.succAbove)).det *
              ((incMat (fun _ j => d j)).submatrix (ρ ∘ r.succAbove)
              (φ ∘ c0.succAbove)).det) * hsq.symm
      have : 0 ≤ D.det * B.det := by
        rw [hBexp, mul_sum]
        refine sum_nonneg fun r _ => ?_
        have hr := hadj r
        have hi := hIH r
        have hBr : B r c0 = Sum.elim (fun _ => 0) (fun _ => -1) (ρ r) := by
          simp only [hBdef, submatrix_apply, hc0]; rcases ρ r with i | j <;> simp [incMat]
        rw [hBr]
        simp only [hy] at hr
        rcases hρr : ρ r with i | j
        · simp
        · rw [hρr] at hr
          simp only [Sum.elim_inr] at hr ⊢
          have hdj := hd j
          -- `det D = −d_j κ adj(D)_{c0 r}`
          have hD : D.det = -(d j * κ * adjugate D c0 r) := by
            field_simp at hr; linear_combination -hr
          rw [hD]
          have : 0 ≤ d j * κ * (adjugate B c0 r * adjugate D c0 r) :=
            mul_nonneg (mul_nonneg hdj.le hκpos.le) hi
          linarith
      linarith
    · -- no budget column: `y` is a nonzero left-kernel vector of `D`
      push Not at hbud
      have hyD : y ᵥ* D = 0 := by
        ext c
        rcases hφc : φ c with ⟨i, j⟩ | j | u
        · exact hyatt c i j hφc
        · exact absurd hφc (hcap c j)
        · exact absurd hφc (hbud c)
      have : D.det = 0 := exists_vecMul_eq_zero_iff.mp ⟨y, hy0, hyD⟩
      simp [this]

/-- [DL Lemma P0, Steps 0–4] core: for `β ≥ 0`, `d ≥ 0` and any row/column selections,
`det B_{ρφ} · det D_{ρφ} ≥ 0`.  Proof: the case `d > 0` (`p0core_pos`), then continuity in `d`. -/
theorem p0core (β : Θ → T → ℚ) (hβ : ∀ i j, 0 ≤ β i j) (d : T → ℚ) (hd : ∀ j, 0 ≤ d j)
    (n : ℕ) (ρ : Fin n → RIdx Θ T) (φ : Fin n → FIdx Θ T) :
    0 ≤ ((incMat β).submatrix ρ φ).det * ((incMat (fun _ j => d j)).submatrix ρ φ).det := by
  set f : ℚ → ℚ := fun ε => ((incMat β).submatrix ρ φ).det *
    ((incMat (fun _ j => d j + ε)).submatrix ρ φ).det with hf
  have hcont : Continuous f := by
    refine continuous_const.mul (Continuous.matrix_det ?_)
    refine continuous_pi fun r => continuous_pi fun c => ?_
    simp only [submatrix_apply]
    rcases ρ r with i | j <;> rcases φ c with ⟨i', j'⟩ | j' | _ <;> simp only [incMat, of_apply] <;>
      (try split_ifs) <;> fun_prop
  have hpos : ∀ ε ∈ Set.Ioi (0 : ℚ), f ε ∈ Set.Ici (0 : ℚ) := fun ε hε =>
    p0core_pos β hβ (fun j => d j + ε) (fun j => by have := hd j; simp at hε; linarith) n ρ φ
  have hcl : IsClosed {ε : ℚ | 0 ≤ f ε} := isClosed_le continuous_const hcont
  have h0 : (0 : ℚ) ∈ closure (Set.Ioi (0 : ℚ)) := by rw [closure_Ioi]; simp
  have := (hcl.closure_subset_iff.mpr (fun ε hε => hpos ε hε)) h0
  simpa [hf] using this

end P0core

/-! ## The block determinant -/

section Block

theorem det_swapJ (k : ℕ) :
    (fromBlocks (0 : Matrix (Fin k) (Fin k) ℚ) (1 : Matrix (Fin k) (Fin k) ℚ) 1 0).det = (-1) ^ k := by
  have : fromBlocks (0 : Matrix (Fin k) (Fin k) ℚ) (1 : Matrix (Fin k) (Fin k) ℚ) 1 0 =
      fromBlocks (1 : Matrix (Fin k) (Fin k) ℚ) 0 1 (1 : Matrix (Fin k) (Fin k) ℚ) *
        fromBlocks (1 : Matrix (Fin k) (Fin k) ℚ) (-1) 0 (1 : Matrix (Fin k) (Fin k) ℚ) *
        fromBlocks (1 : Matrix (Fin k) (Fin k) ℚ) 0 1 (1 : Matrix (Fin k) (Fin k) ℚ) *
        fromBlocks (1 : Matrix (Fin k) (Fin k) ℚ) 0 0 (-1 : Matrix (Fin k) (Fin k) ℚ) := by
    simp [fromBlocks_multiply]
  rw [this, det_mul, det_mul, det_mul]
  simp [det_fromBlocks_zero₁₂, det_neg]

theorem det_antidiag_square {k : ℕ} (P Q : Matrix (Fin k) (Fin k) ℚ) :
    (fromBlocks 0 P Q 0).det = (-1) ^ k * P.det * Q.det := by
  have : fromBlocks 0 P Q 0 = fromBlocks P 0 0 Q * fromBlocks 0 1 1 0 := by
    simp [fromBlocks_multiply]
  rw [this, det_mul, det_fromBlocks_zero₂₁, det_swapJ]; ring

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

theorem det_antidiag (X : Matrix m n ℚ) (Y : Matrix n m ℚ) {k : ℕ} (e1 : Fin k ≃ m)
    (e2 : Fin k ≃ n) :
    (fromBlocks 0 X Y 0).det = (-1) ^ k * (X.submatrix e1 e2).det * (Y.submatrix e2 e1).det := by
  rw [← det_submatrix_equiv_self (Equiv.sumCongr e1 e2)]
  have : (fromBlocks 0 X Y 0).submatrix (Equiv.sumCongr e1 e2) (Equiv.sumCongr e1 e2) =
      fromBlocks 0 (X.submatrix e1 e2) (Y.submatrix e2 e1) 0 := by
    ext (a | a) (b | b) <;> simp
  rw [this, det_antidiag_square]

theorem det_antidiag_of_card_ne (X : Matrix m n ℚ) (Y : Matrix n m ℚ)
    (h : Fintype.card m ≠ Fintype.card n) : (fromBlocks 0 X Y 0).det = 0 := by
  rcases lt_or_gt_of_ne h with h | h
  · -- more `n`-columns than rows of `X`
    have hk : LinearMap.ker X.mulVecLin ≠ ⊥ := LinearMap.ker_ne_bot_of_finrank_lt (by simpa using h)
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hk
    refine exists_mulVec_eq_zero_iff.mp ⟨Sum.elim 0 v, ?_, ?_⟩
    · intro h0; apply hv0; ext b; simpa using congrFun h0 (Sum.inr b)
    · rw [fromBlocks_mulVec]
      have : X *ᵥ v = 0 := hv
      ext (a | b) <;> simp [this]
  · have hk : LinearMap.ker Y.mulVecLin ≠ ⊥ := LinearMap.ker_ne_bot_of_finrank_lt (by simpa using h)
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hk
    refine exists_mulVec_eq_zero_iff.mp ⟨Sum.elim v 0, ?_, ?_⟩
    · intro h0; apply hv0; ext b; simpa using congrFun h0 (Sum.inl b)
    · rw [fromBlocks_mulVec]
      have : Y *ᵥ v = 0 := hv
      ext (a | b) <;> simp [this]

end Block

/-! ## Principal minors of `M = (0 Bᵀ; −D 0)` and the P₀ lemma -/

section P0

variable {F R : Type*} [Fintype F] [Fintype R] [DecidableEq F] [DecidableEq R]

/-- A principal index set `S ⊆ F ⊕ R` splits into its first-block part and second-block part. -/
def splitEquiv (S : Finset (F ⊕ R)) : S ≃ {a // Sum.inl a ∈ S} ⊕ {b // Sum.inr b ∈ S} where
  toFun x := match x with
    | ⟨.inl a, h⟩ => .inl ⟨a, h⟩
    | ⟨.inr b, h⟩ => .inr ⟨b, h⟩
  invFun y := match y with
    | .inl a => ⟨.inl a.1, a.2⟩
    | .inr b => ⟨.inr b.1, b.2⟩
  left_inv := by rintro ⟨(a | b), h⟩ <;> rfl
  right_inv := by rintro (a | b) <;> rfl

theorem principal_fromBlocks (B D : Matrix R F ℚ) (S : Finset (F ⊕ R)) :
    (principal (fromBlocks 0 Bᵀ (-D) 0) S).submatrix (splitEquiv S).symm (splitEquiv S).symm =
      fromBlocks 0 (Bᵀ.submatrix (fun a : {a // Sum.inl a ∈ S} => a.1)
        (fun b : {b // Sum.inr b ∈ S} => b.1))
        ((-D).submatrix (fun b : {b // Sum.inr b ∈ S} => b.1)
          (fun a : {a // Sum.inl a ∈ S} => a.1)) 0 := by
  ext (a | a) (b | b) <;> rfl

/-- [DL §3, "The block determinant"], unequal sizes: the minor is `0`. -/
theorem blockdet_card_ne (B D : Matrix R F ℚ) (S : Finset (F ⊕ R))
    (h : Fintype.card {a // Sum.inl a ∈ S} ≠ Fintype.card {b // Sum.inr b ∈ S}) :
    (principal (fromBlocks 0 Bᵀ (-D) 0) S).det = 0 := by
  rw [← det_submatrix_equiv_self (splitEquiv S).symm, principal_fromBlocks]
  exact det_antidiag_of_card_ne _ _ h

/-- [DL eq. (dl:eq:blockdet)]: with `|F| = |R| = k`, `det M_{F∪R} = det B_{R,F} · det D_{R,F}`
(rows and columns listed through any bijections `e₂ : Fin k ≃ R`, `e₁ : Fin k ≃ F`). -/
theorem blockdet (B D : Matrix R F ℚ) (S : Finset (F ⊕ R)) {k : ℕ}
    (e1 : Fin k ≃ {a // Sum.inl a ∈ S}) (e2 : Fin k ≃ {b // Sum.inr b ∈ S}) :
    (principal (fromBlocks 0 Bᵀ (-D) 0) S).det =
      (B.submatrix (fun p => (e2 p).1) (fun p => (e1 p).1)).det *
        (D.submatrix (fun p => (e2 p).1) (fun p => (e1 p).1)).det := by
  rw [← det_submatrix_equiv_self (splitEquiv S).symm, principal_fromBlocks, det_antidiag _ _ e1 e2]
  have h1 : (Bᵀ.submatrix (fun a : {a // Sum.inl a ∈ S} => a.1)
      (fun b : {b // Sum.inr b ∈ S} => b.1)).submatrix e1 e2 =
      (B.submatrix (fun p => (e2 p).1) (fun p => (e1 p).1))ᵀ := rfl
  have h2 : ((-D).submatrix (fun b : {b // Sum.inr b ∈ S} => b.1)
      (fun a : {a // Sum.inl a ∈ S} => a.1)).submatrix e2 e1 =
      -(D.submatrix (fun p => (e2 p).1) (fun p => (e1 p).1)) := rfl
  rw [h1, h2, det_transpose, det_neg, Fintype.card_fin]
  have : ((-1 : ℚ) ^ k) * ((-1 : ℚ) ^ k) = 1 := by rw [← mul_pow]; norm_num
  linear_combination ((B.submatrix (fun p => (e2 p).1) (fun p => (e1 p).1)).det *
    (D.submatrix (fun p => (e2 p).1) (fun p => (e1 p).1)).det) * this

end P0

section P0game

variable {T Θ : Type*} [Fintype T] [DecidableEq T] [Fintype Θ] [DecidableEq Θ]

/-- [DL Lemma P0] for the incidence form: `(0 B(β)ᵀ; −B(d) 0)` is P₀ when `β ≥ 0`, `d ≥ 0`. -/
theorem incMat_isP0 (β : Θ → T → ℚ) (hβ : ∀ i j, 0 ≤ β i j) (d : T → ℚ) (hd : ∀ j, 0 ≤ d j) :
    IsP0Matrix (fromBlocks 0 (incMat β)ᵀ (-incMat (fun _ j => d j)) 0) := by
  intro S
  by_cases h : Fintype.card {a // Sum.inl a ∈ S} = Fintype.card {b // Sum.inr b ∈ S}
  · rw [blockdet _ _ S (Fintype.equivFin _).symm (Fintype.equivFinOfCardEq h.symm).symm]
    exact p0core β hβ d hd _ _ _
  · rw [blockdet_card_ne _ _ S h]

variable (G : BSSG T Θ)

theorem bb_nonneg (hwf : G.WellFormed) (i : Θ) (j : T) : 0 ≤ bb G i j := by
  have := hwf.2.2.2.2 i j; unfold bb; linarith

theorem dd_nonneg (hwf : G.WellFormed) (j : T) : 0 ≤ dd G j := by
  have := hwf.2.2.2.1 j; unfold dd; linarith

/-- [DL Lemma P0]: the LCP matrix `M` of a well-formed game is a P₀-matrix. -/
theorem lcpM_isP0 (hwf : G.WellFormed) : IsP0Matrix (lcpM G) :=
  incMat_isP0 (bb G) (bb_nonneg G hwf) (dd G) (dd_nonneg G hwf)

end P0game

/-! ## Diagonal perturbation: `M + δ I` is a P-matrix -/

section Pmat

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem principal_det_eq_fin (M : Matrix ι ι ℚ) (S : Finset ι) :
    (principal M S).det =
      (M.submatrix (fun p => (S.equivFin.symm p).1) (fun p => (S.equivFin.symm p).1)).det := by
  rw [← det_submatrix_equiv_self S.equivFin.symm (principal M S)]; rfl

theorem fin_det_eq_principal (M : Matrix ι ι ℚ) {n : ℕ} (σ : Fin n → ι)
    (hσ : Function.Injective σ) : (M.submatrix σ σ).det = (principal M (univ.image σ)).det := by
  let e : Fin n ≃ (univ.image σ) := Equiv.ofBijective
    (fun p => ⟨σ p, mem_image_of_mem σ (mem_univ p)⟩)
    ⟨fun a b h => hσ (congrArg Subtype.val h), fun ⟨x, hx⟩ => by
      obtain ⟨p, -, rfl⟩ := mem_image.mp hx; exact ⟨p, rfl⟩⟩
  rw [← det_submatrix_equiv_self e (principal M _)]; rfl

/-- Diagonal perturbation, `Fin` form, by adding the diagonal entries of `F` one at a time:
for `M` P₀ and `c ≥ 0`, `det (M + diag(c·1_F))_{σσ} ≥ ∏_p (c·1_F)(σ p)`. -/
theorem det_add_diag_ge_aux (M : Matrix ι ι ℚ) (hM : IsP0Matrix M) (c : ι → ℚ)
    (hc : ∀ k, 0 ≤ c k) (F : Finset ι) :
    ∀ (n : ℕ) (σ : Fin n → ι), Function.Injective σ →
      ∏ p, (if σ p ∈ F then c (σ p) else 0) ≤
        ((M + diagonal (fun k => if k ∈ F then c k else 0)).submatrix σ σ).det := by
  induction F using Finset.induction_on with
  | empty =>
    intro n σ hσ
    simp only [notMem_empty, if_false, diagonal_zero, add_zero]
    rcases n with _ | n
    · simp
    · rw [Fin.prod_univ_succ, zero_mul, fin_det_eq_principal M σ hσ]; exact hM _
  | @insert k F hkF IH =>
    intro n σ hσ
    by_cases hk : ∃ p0, σ p0 = k
    · obtain ⟨p0, hp0⟩ := hk
      rcases n with _ | n
      · exact p0.elim0
      set A := (M + diagonal (fun k => if k ∈ F then c k else 0)).submatrix σ σ with hA
      have hupd : (M + diagonal (fun k' => if k' ∈ insert k F then c k' else 0)).submatrix σ σ =
          updateRow A p0 (A p0 + c k • Pi.single p0 1) := by
        ext a b
        by_cases ha : a = p0
        · subst ha
          simp only [updateRow_self, hA, submatrix_apply, add_apply, Pi.add_apply,
            Pi.smul_apply, smul_eq_mul, diagonal_apply]
          by_cases hb : b = a
          · subst hb; simp [hp0, hkF]
          · have : σ a ≠ σ b := fun h => hb (hσ h).symm
            simp [this, Pi.single_eq_of_ne hb]
        · rw [updateRow_ne ha]
          have hne : σ a ≠ k := by rw [← hp0]; exact fun h => ha (hσ h)
          simp [hA, diagonal_apply, mem_insert, hne]
      rw [hupd, det_updateRow_add, det_updateRow_smul, updateRow_eq_self]
      have hminor : (updateRow A p0 (Pi.single p0 1)).det =
          ((M + diagonal (fun k => if k ∈ F then c k else 0)).submatrix (σ ∘ p0.succAbove)
            (σ ∘ p0.succAbove)).det := by
        rw [← adjugate_apply, adjugate_fin_succ_eq_det_submatrix]
        have : ((-1 : ℚ) ^ (p0 + p0 : ℕ)) = 1 := by rw [← two_mul, pow_mul]; norm_num
        rw [this, one_mul]; rfl
      rw [hminor]
      have h1 := IH (n + 1) σ hσ
      rw [Finset.prod_eq_zero (mem_univ p0) (by simp [hp0, hkF])] at h1
      have h2 := IH n (σ ∘ p0.succAbove) (hσ.comp Fin.succAbove_right_injective)
      rw [Fin.prod_univ_succAbove _ p0]
      have hrest : ∏ p', (if σ (p0.succAbove p') ∈ insert k F then c (σ (p0.succAbove p')) else 0) =
          ∏ p', (if (σ ∘ p0.succAbove) p' ∈ F then c ((σ ∘ p0.succAbove) p') else 0) := by
        refine prod_congr rfl fun p' _ => ?_
        have hne : σ (p0.succAbove p') ≠ k := by
          rw [← hp0]; exact fun h => Fin.succAbove_ne p0 p' (hσ h)
        simp [mem_insert, hne]
      rw [hrest, hp0]
      simp only [mem_insert, true_or, if_true]
      nlinarith [hc k]
    · push Not at hk
      have hrow : ∀ p, (σ p ∈ insert k F) ↔ σ p ∈ F := by
        intro p; simp [mem_insert, hk p]
      have : (M + diagonal (fun k' => if k' ∈ insert k F then c k' else 0)).submatrix σ σ =
          (M + diagonal (fun k => if k ∈ F then c k else 0)).submatrix σ σ := by
        ext a b
        simp [diagonal_apply, mem_insert, hk a]
      rw [this]
      simp only [hrow]
      exact IH n σ hσ

/-- For `M` P₀ and `c ≥ 0`: every principal minor of `M + diag(c)` is at least `∏_{k∈S} c_k`. -/
theorem det_principal_add_diagonal_ge (M : Matrix ι ι ℚ) (hM : IsP0Matrix M) (c : ι → ℚ)
    (hc : ∀ k, 0 ≤ c k) (S : Finset ι) : ∏ k ∈ S, c k ≤ (principal (M + diagonal c) S).det := by
  rw [principal_det_eq_fin]
  have := det_add_diag_ge_aux M hM c hc univ S.card (fun p => (S.equivFin.symm p).1)
    (fun a b h => S.equivFin.symm.injective (Subtype.ext h))
  simp only [mem_univ, if_true] at this
  refine le_trans (le_of_eq ?_) this
  rw [← Finset.prod_coe_sort S c]
  exact (Fintype.prod_equiv S.equivFin.symm _ _ (fun _ => rfl)).symm

theorem smul_one_eq_diag (δ : ℚ) : δ • (1 : Matrix ι ι ℚ) = diagonal (fun _ => δ) := by
  ext a b; by_cases h : a = b <;> simp [diagonal_apply, one_apply, h]

/-- [DL Lemma dl:lem:pmatrix, proof]: `det (M + δI)_{SS} ≥ δ^{|S|}` for `M` P₀, `δ ≥ 0`. -/
theorem det_principal_add_smul_ge (M : Matrix ι ι ℚ) (hM : IsP0Matrix M) (δ : ℚ) (hδ : 0 ≤ δ)
    (S : Finset ι) : δ ^ S.card ≤ (principal (M + δ • (1 : Matrix ι ι ℚ)) S).det := by
  rw [smul_one_eq_diag]
  have := det_principal_add_diagonal_ge M hM (fun _ => δ) (fun _ => hδ) S
  simpa [prod_const] using this

/-- [DL Lemma dl:lem:pmatrix]: `M` P₀ and `δ > 0` ⇒ `M + δ I` is a P-matrix. -/
theorem isP_add_smul (M : Matrix ι ι ℚ) (hM : IsP0Matrix M) (δ : ℚ) (hδ : 0 < δ) :
    IsPMatrix (M + δ • (1 : Matrix ι ι ℚ)) := fun S =>
  lt_of_lt_of_le (pow_pos hδ _) (det_principal_add_smul_ge M hM δ hδ.le S)

/-- `M` P₀ and `δ > 0` ⇒ `M + δ I` has no sign-reversing vector (no PV2 violation). -/
theorem no_signReversing_add_smul (M : Matrix ι ι ℚ) (hM : IsP0Matrix M) (δ : ℚ) (hδ : 0 < δ)
    (y : ι → ℚ) : ¬ IsSignReversing (M + δ • (1 : Matrix ι ι ℚ)) y := by
  rintro ⟨hy0, hy⟩
  set A := M + δ • (1 : Matrix ι ι ℚ) with hA
  set c : ι → ℚ := fun k => if y k = 0 then 0 else -(A *ᵥ y) k / y k with hcdef
  have hc : ∀ k, 0 ≤ c k := by
    intro k
    simp only [hcdef]
    split_ifs with h
    · exact le_rfl
    · have h1 := hy k
      have h2 : 0 < y k * y k := mul_self_pos.mpr h
      have : -(A *ᵥ y) k / y k = -(y k * (A *ᵥ y) k) / (y k * y k) := by field_simp
      rw [this]; exact div_nonneg (by linarith) h2.le
  set S : Finset ι := univ.filter fun k => y k ≠ 0 with hS
  have hpos : 0 < (principal (M + diagonal fun k => δ + c k) S).det :=
    lt_of_lt_of_le (prod_pos fun k _ => by linarith [hc k])
      (det_principal_add_diagonal_ge M hM _ (fun k => by linarith [hc k]) S)
  have hzero : (principal (M + diagonal fun k => δ + c k) S).det = 0 := by
    refine exists_mulVec_eq_zero_iff.mp ⟨fun k => y k, ?_, ?_⟩
    · intro h
      apply hy0
      ext k
      by_contra hk
      have := congrFun h ⟨k, by simp [hS]; simpa using hk⟩
      exact hk (by simpa using this)
    · ext ⟨k, hk⟩
      have hyk : y k ≠ 0 := by simpa [hS] using hk
      simp only [mulVec, dotProduct, principal, submatrix_apply, Pi.zero_apply]
      set N : Matrix ι ι ℚ := M + diagonal fun k => δ + c k with hN
      have e1 : ∑ i : S, N k i * y i = ∑ l, N k l * y l := by
        rw [Finset.sum_coe_sort S (fun l => N k l * y l)]
        exact Finset.sum_subset (subset_univ S) (fun l _ hl => by
          have : y l = 0 := by simpa [hS] using hl
          rw [this, mul_zero])
      rw [e1]
      have hsplit : ∀ l, N k l * y l =
          A k l * y l + (if k = l then c k * y l else 0) := by
        intro l
        rw [hN, hA]
        by_cases h : k = l
        · subst h; simp [diagonal_apply, one_apply]; ring
        · simp [diagonal_apply, one_apply, h]
      simp only [hsplit, sum_add_distrib, sum_ite_eq, mem_univ, if_true]
      have : ∑ l, A k l * y l = (A *ᵥ y) k := rfl
      rw [this]
      simp only [hcdef, hyk, if_false]
      field_simp
      ring
  linarith

/-- `M` P₀, `δ > 0` ⇒ `LCP(q, M + δ I)` has at most one solution. -/
theorem lcp_unique_add_smul (M : Matrix ι ι ℚ) (hM : IsP0Matrix M) (δ : ℚ) (hδ : 0 < δ)
    (q z z' : ι → ℚ) (hz : IsLCPSol q (M + δ • (1 : Matrix ι ι ℚ)) z)
    (hz' : IsLCPSol q (M + δ • (1 : Matrix ι ι ℚ)) z') : z = z' := by
  by_contra hne
  apply no_signReversing_add_smul M hM δ hδ (z - z')
  refine ⟨sub_ne_zero.mpr hne, fun k => ?_⟩
  have e : ((M + δ • (1 : Matrix ι ι ℚ)) *ᵥ (z - z')) k =
      slack q (M + δ • (1 : Matrix ι ι ℚ)) z k - slack q (M + δ • (1 : Matrix ι ι ℚ)) z' k := by
    simp only [slack, Pi.add_apply, mulVec_sub, Pi.sub_apply]; ring
  rw [e, Pi.sub_apply]
  have := hz.2.2 k; have := hz'.2.2 k
  nlinarith [hz.1 k, hz'.1 k, hz.2.1 k, hz'.2.1 k]

end Pmat

/-! ## The slack table and the LCP formulation lemma -/

section Formulation

variable {T Θ : Type*} [Fintype T] [DecidableEq T] [Fintype Θ] [DecidableEq Θ] [Nonempty T]
variable (G : BSSG T Θ)

/-- `q + M z` is exactly the slack table (dl:eq:lcp). -/
theorem slack_eq_table (z : Idx Θ T → ℚ) : slack (lcpq G) (lcpM G) z = slackTable G z := by
  ext k
  rcases k with ((⟨i, j⟩ | j | _) | (i | j))
  · simp [slack, lcpM, lcpq, slackTable, fromBlocks_mulVec, mulVec, dotProduct,
      Fintype.sum_sum_type, lcpB, incMat]
    ring
  · simp [slack, lcpM, lcpq, slackTable, fromBlocks_mulVec, mulVec, dotProduct,
      Fintype.sum_sum_type, lcpB, incMat]
    ring
  · simp [slack, lcpM, lcpq, slackTable, fromBlocks_mulVec, mulVec, dotProduct,
      Fintype.sum_sum_type, lcpB, incMat]
    ring
  · simp [slack, lcpM, lcpq, slackTable, fromBlocks_mulVec, mulVec, dotProduct,
      Fintype.sum_sum_type, lcpD, incMat, Fintype.sum_prod_type]
    rw [Finset.sum_comm]; simp; ring
  · simp [slack, lcpM, lcpq, slackTable, fromBlocks_mulVec, mulVec, dotProduct,
      Fintype.sum_sum_type, lcpD, incMat, Fintype.sum_prod_type, Finset.mul_sum]
    ring

theorem sl_f (z : Idx Θ T → ℚ) (i : Θ) (j : T) : slack (lcpq G) (lcpM G) z (Idx.f i j) =
    z (Idx.u i) + bb G i j * z (Idx.x j) - shiftA G i j := by rw [slack_eq_table]; rfl
theorem sl_t (z : Idx Θ T → ℚ) (j : T) : slack (lcpq G) (lcpM G) z (Idx.t j) =
    1 - z (Idx.x j) := by rw [slack_eq_table]; rfl
theorem sl_lam (z : Idx Θ T → ℚ) : slack (lcpq G) (lcpM G) z Idx.lam =
    (G.r : ℚ) - ∑ j, z (Idx.x j) := by rw [slack_eq_table]; rfl
theorem sl_u (z : Idx Θ T → ℚ) (i : Θ) : slack (lcpq G) (lcpM G) z (Idx.u i) =
    G.prior i - ∑ j, z (Idx.f i j) := by rw [slack_eq_table]; rfl
theorem sl_x (z : Idx Θ T → ℚ) (j : T) : slack (lcpq G) (lcpM G) z (Idx.x j) =
    z Idx.lam - 1 + z (Idx.t j) - dd G j * ∑ i, z (Idx.f i j) := by rw [slack_eq_table]; rfl

/-- The shift constant `c_i = 1 + max_k (b_ik − a_ik)`. -/
def shiftC (i : Θ) : ℚ := 1 + univ.sup' univ_nonempty (fun k => bb G i k - aa G i k)

theorem shiftA_eq (i : Θ) (j : T) : shiftA G i j = aa G i j + shiftC G i := by
  unfold shiftA shiftC; ring

/-- `A_ij − b_ij ≥ 1`. -/
theorem shiftA_sub_ge (i : Θ) (j : T) : 1 ≤ shiftA G i j - bb G i j := by
  have := le_sup' (fun k => bb G i k - aa G i k) (mem_univ j)
  unfold shiftA; linarith

theorem U_eq (i : Θ) (k : T) (x : T → ℚ) : G.U i k x = aa G i k - bb G i k * x k := by
  unfold BSSG.U aa bb; ring

end Formulation

/-! ### Cutoff form -/

section Cutoff

variable {T Θ : Type*} [Fintype T] [DecidableEq T] [Fintype Θ] [DecidableEq Θ]
variable (G : BSSG T Θ)

theorem exchange (π x : T → ℚ) (hx : IsFeasibleCov G x)
    (hopt : ∀ x', IsFeasibleCov G x' → ∑ j, π j * x' j ≤ ∑ j, π j * x j)
    (j k : T) (hj : 0 < x j) (hk : x k < 1) : π k ≤ π j := by
  by_cases hjk : j = k
  · subst hjk; exact le_rfl
  set ε := min (x j) (1 - x k) with hε
  have hεpos : 0 < ε := lt_min hj (by linarith)
  have hε1 : ε ≤ x j := min_le_left _ _
  have hε2 : ε ≤ 1 - x k := min_le_right _ _
  set x' : T → ℚ := fun t => x t - (if t = j then ε else 0) + (if t = k then ε else 0) with hx'
  have hfeas : IsFeasibleCov G x' := by
    refine ⟨fun t => ?_, ?_⟩
    · have := hx.1 t
      simp only [hx']
      by_cases htj : t = j
      · subst htj; simp [hjk]; constructor <;> linarith
      · by_cases htk : t = k
        · subst htk; simp [htj]; constructor <;> linarith
        · simp [htj, htk]; exact this
    · simp only [hx', sum_add_distrib, sum_sub_distrib, sum_ite_eq', mem_univ, if_true, hx.2]
      ring
  have := hopt x' hfeas
  simp only [hx', mul_add, mul_sub, sum_add_distrib, sum_sub_distrib, mul_ite, mul_zero,
    sum_ite_eq', mem_univ, if_true] at this
  nlinarith

/-- [DL Lemma dl:lem:cutoff] (cutoff form of the defender's best response). -/
theorem cutoff_form (π x : T → ℚ) (hx : IsFeasibleCov G x) :
    (∀ x', IsFeasibleCov G x' → ∑ j, π j * x' j ≤ ∑ j, π j * x j) ↔
      ∃ l0 : ℚ, ∀ j, (0 < x j → l0 ≤ π j) ∧ (x j < 1 → π j ≤ l0) := by
  constructor
  · intro hopt
    set A := univ.filter fun j => 0 < x j with hA
    by_cases hne : A.Nonempty
    · refine ⟨A.inf' hne π, fun j => ⟨fun hj => inf'_le _ (by simp [hA, hj]), fun hj => ?_⟩⟩
      refine le_inf' _ _ fun k hk => ?_
      have : 0 < x k := by simpa [hA] using hk
      exact exchange G π x hx hopt k j this hj
    · refine ⟨∑ k, |π k|, fun j => ⟨fun hj => absurd ⟨j, by simp [hA, hj]⟩ hne, fun _ => ?_⟩⟩
      exact le_trans (le_abs_self _) (single_le_sum (fun k _ => abs_nonneg (π k)) (mem_univ j))
  · rintro ⟨l0, hl0⟩ x' hx'
    have key : ∑ j, π j * x' j - ∑ j, π j * x j = ∑ j, (π j - l0) * (x' j - x j) := by
      have : ∑ j, (π j - l0) * (x' j - x j) =
          ∑ j, π j * x' j - ∑ j, π j * x j - l0 * (∑ j, x' j - ∑ j, x j) := by
        simp only [mul_sub, sub_mul, sum_sub_distrib, mul_sum]; ring
      rw [this, hx.2, hx'.2]; ring
    have : ∑ j, (π j - l0) * (x' j - x j) ≤ 0 := by
      refine sum_nonpos fun j _ => ?_
      rcases lt_trichotomy (x' j) (x j) with h | h | h
      · have h1 : 0 < x j := lt_of_le_of_lt (hx'.1 j).1 h
        have := (hl0 j).1 h1
        nlinarith
      · rw [h]; simp
      · have h1 : x j < 1 := lt_of_lt_of_le h (hx'.1 j).2
        have := (hl0 j).2 h1
        nlinarith
    linarith

end Cutoff

/-! ### LCP formulation lemma -/

section Formulation2

variable {T Θ : Type*} [Fintype T] [DecidableEq T] [Fintype Θ] [DecidableEq Θ] [Nonempty T]
variable (G : BSSG T Θ)

/-- [DL Lemma dl:lem:formulation (a)]. -/
theorem formulation_a (hwf : G.WellFormed) (hr0 : 0 < G.r) (hrn : G.r < Fintype.card T)
    (z : Idx Θ T → ℚ) (hz : IsLCPSol (lcpq G) (lcpM G) z) :
    0 < z Idx.lam ∧ ∑ j, zx z j = G.r ∧ IsMarginalBNE G (zx z) (zf z) := by
  obtain ⟨hz0, hw0, hc⟩ := hz
  have hb := bb_nonneg G hwf
  have hd := dd_nonneg G hwf
  -- caps
  have hx1 : ∀ j, z (Idx.x j) ≤ 1 := fun j => by have := hw0 (Idx.t j); rw [sl_t] at this; linarith
  -- types
  have hu : ∀ i j, shiftA G i j - bb G i j * z (Idx.x j) ≤ z (Idx.u i) := fun i j => by
    have := hw0 (Idx.f i j); rw [sl_f] at this; linarith
  have hupos : ∀ i, 0 < z (Idx.u i) := by
    intro i
    obtain ⟨j⟩ := (inferInstance : Nonempty T)
    have h1 := hu i j
    have h2 := shiftA_sub_ge G i j
    have h3 : bb G i j * z (Idx.x j) ≤ bb G i j := by
      nlinarith [hb i j, hx1 j, hz0 (Idx.x j)]
    linarith
  have hmass : ∀ i, ∑ j, z (Idx.f i j) = G.prior i := by
    intro i
    have := hc (Idx.u i); rw [sl_u] at this
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h (hupos i).ne'
    · linarith
  have hw : ∀ j, 0 ≤ ∑ i, z (Idx.f i j) := fun j => sum_nonneg fun i _ => hz0 _
  -- λ > 0
  have hlam : 0 < z Idx.lam := by
    rcases (hz0 Idx.lam).lt_or_eq with h | h
    · exact h
    exfalso
    have hall : ∀ j, z (Idx.x j) = 1 := by
      intro j
      have h1 := hw0 (Idx.x j); rw [sl_x, ← h] at h1
      have h2 : 0 < z (Idx.t j) := by nlinarith [hd j, hw j]
      have h3 := hc (Idx.t j); rw [sl_t] at h3
      rcases mul_eq_zero.mp h3 with h4 | h4
      · exact absurd h4 h2.ne'
      · linarith
    have h1 := hw0 Idx.lam; rw [sl_lam] at h1
    simp only [hall, sum_const, card_univ, nsmul_eq_mul, mul_one] at h1
    have : (G.r : ℚ) < Fintype.card T := by exact_mod_cast hrn
    linarith
  have hbudget : ∑ j, z (Idx.x j) = G.r := by
    have := hc Idx.lam; rw [sl_lam] at this
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hlam.ne'
    · linarith
  have hfeas : IsFeasibleCov G (zx z) := ⟨fun j => ⟨hz0 _, hx1 j⟩, hbudget⟩
  refine ⟨hlam, hbudget, hfeas, fun i j => hz0 _, hmass, ?_, ?_⟩
  · -- attacker best responses
    intro i j hf k
    have h1 := hc (Idx.f i j); rw [sl_f] at h1
    have h2 : z (Idx.u i) = shiftA G i j - bb G i j * z (Idx.x j) := by
      rcases mul_eq_zero.mp h1 with h | h
      · exact absurd h hf.ne'
      · linarith
    have h3 := hu i k
    rw [U_eq, U_eq]
    simp only [zx]
    have e1 := shiftA_eq G i j
    have e2 := shiftA_eq G i k
    linarith
  · -- defender optimality via the cutoff `λ − 1`
    refine (cutoff_form G (score G (zf z)) (zx z) hfeas).mpr ⟨z Idx.lam - 1, fun j => ⟨?_, ?_⟩⟩
    · intro hxj
      have h1 := hc (Idx.x j); rw [sl_x] at h1
      have h2 : z Idx.lam - 1 + z (Idx.t j) - dd G j * ∑ i, z (Idx.f i j) = 0 := by
        rcases mul_eq_zero.mp h1 with h | h
        · exact absurd h hxj.ne'
        · exact h
      simp only [score, wload, zf]
      linarith [hz0 (Idx.t j)]
    · intro hxj
      have h1 := hc (Idx.t j); rw [sl_t] at h1
      have h2 : z (Idx.t j) = 0 := by
        rcases mul_eq_zero.mp h1 with h | h
        · exact h
        · simp only [zx] at hxj; linarith
      have h3 := hw0 (Idx.x j); rw [sl_x, h2] at h3
      simp only [score, wload, zf]
      linarith

/-- The shifted best attacker utility `u_i = max_k (A_ik − b_ik x_k)`. -/
def uval (x : T → ℚ) (i : Θ) : ℚ := univ.sup' univ_nonempty fun k => shiftA G i k - bb G i k * x k

/-- The LCP vector built from `(x, f)` and a cutoff `λ₀` [DL Lemma dl:lem:formulation (b)]. -/
def extendZ (x : T → ℚ) (f : Θ → T → ℚ) (l0 : ℚ) : Idx Θ T → ℚ :=
  Sum.elim (Sum.elim (fun p => f p.1 p.2)
      (Sum.elim (fun j => max (score G f j - l0) 0) (fun _ => 1 + l0)))
    (Sum.elim (uval G x) x)

/-- [DL Lemma dl:lem:formulation (b)]. -/
theorem formulation_b (hwf : G.WellFormed) (hrn : G.r < Fintype.card T)
    (x : T → ℚ) (f : Θ → T → ℚ) (h : IsMarginalBNE G x f) :
    ∃ z, IsLCPSol (lcpq G) (lcpM G) z ∧ zx z = x ∧ zf z = f := by
  obtain ⟨hx, hf0, hmass, hatt, hopt⟩ := h
  obtain ⟨l0, hl0⟩ := (cutoff_form G (score G f) x hx).mp hopt
  have hb := bb_nonneg G hwf
  have hd := dd_nonneg G hwf
  have hscore : ∀ j, 0 ≤ score G f j := fun j =>
    mul_nonneg (hd j) (sum_nonneg fun i _ => hf0 i j)
  -- some target is unsaturated, so `λ₀ ≥ 0`
  have hl0pos : 0 ≤ l0 := by
    by_contra hneg
    push Not at hneg
    have hall : ∀ j, x j = 1 := by
      intro j
      by_contra hj
      have := (hl0 j).2 (lt_of_le_of_ne (hx.1 j).2 hj)
      linarith [hscore j]
    have := hx.2
    simp only [hall, sum_const, card_univ, nsmul_eq_mul, mul_one] at this
    have : (G.r : ℚ) < Fintype.card T := by exact_mod_cast hrn
    linarith
  set z := extendZ G x f l0 with hzdef
  have zf_eq : ∀ i j, z (Idx.f i j) = f i j := fun _ _ => rfl
  have zt_eq : ∀ j, z (Idx.t j) = max (score G f j - l0) 0 := fun _ => rfl
  have zl_eq : z Idx.lam = 1 + l0 := rfl
  have zu_eq : ∀ i, z (Idx.u i) = uval G x i := fun _ => rfl
  have zx_eq : ∀ j, z (Idx.x j) = x j := fun _ => rfl
  have hule : ∀ i k, shiftA G i k - bb G i k * x k ≤ uval G x i := fun i k =>
    le_sup' (fun k => shiftA G i k - bb G i k * x k) (mem_univ k)
  have hupos : ∀ i, 0 ≤ uval G x i := by
    intro i
    obtain ⟨k⟩ := (inferInstance : Nonempty T)
    have h1 := hule i k
    have h2 := shiftA_sub_ge G i k
    have h3 : bb G i k * x k ≤ bb G i k := by nlinarith [hb i k, (hx.1 k).2, (hx.1 k).1]
    linarith
  refine ⟨z, ⟨?_, ?_, ?_⟩, rfl, rfl⟩
  · rintro ((⟨i, j⟩ | j | _) | (i | j))
    · exact hf0 i j
    · exact le_max_right _ _
    · show 0 ≤ 1 + l0; linarith
    · exact hupos i
    · exact (hx.1 j).1
  · rintro ((⟨i, j⟩ | j | _) | (i | j))
    · show 0 ≤ slack (lcpq G) (lcpM G) z (Idx.f i j)
      rw [sl_f, zu_eq, zx_eq]; linarith [hule i j]
    · show 0 ≤ slack (lcpq G) (lcpM G) z (Idx.t j)
      rw [sl_t, zx_eq]; linarith [(hx.1 j).2]
    · show 0 ≤ slack (lcpq G) (lcpM G) z Idx.lam
      rw [sl_lam]; simp only [zx_eq, hx.2]; simp
    · show 0 ≤ slack (lcpq G) (lcpM G) z (Idx.u i)
      rw [sl_u]; simp only [zf_eq, hmass]; simp
    · show 0 ≤ slack (lcpq G) (lcpM G) z (Idx.x j)
      rw [sl_x, zl_eq, zt_eq]; simp only [zf_eq]
      have : score G f j = dd G j * ∑ i, f i j := rfl
      rw [← this]
      have := le_max_left (score G f j - l0) 0
      linarith
  · rintro ((⟨i, j⟩ | j | _) | (i | j))
    · show z (Idx.f i j) * slack (lcpq G) (lcpM G) z (Idx.f i j) = 0
      rw [sl_f, zu_eq, zx_eq, zf_eq]
      rcases (hf0 i j).lt_or_eq with hpos | hzero
      · have hbest := hatt i j hpos
        have : uval G x i = shiftA G i j - bb G i j * x j := by
          refine le_antisymm (sup'_le _ _ fun k _ => ?_) (hule i j)
          have := hbest k
          rw [U_eq, U_eq] at this
          rw [shiftA_eq, shiftA_eq]; linarith
        rw [this]; ring
      · rw [← hzero]; ring
    · show z (Idx.t j) * slack (lcpq G) (lcpM G) z (Idx.t j) = 0
      rw [sl_t, zx_eq, zt_eq]
      by_cases hs : score G f j - l0 ≤ 0
      · rw [max_eq_right hs]; ring
      · have hxj : x j = 1 := by
          by_contra hne
          have := (hl0 j).2 (lt_of_le_of_ne (hx.1 j).2 hne)
          exact hs (by linarith)
        rw [hxj]; ring
    · show z Idx.lam * slack (lcpq G) (lcpM G) z Idx.lam = 0
      rw [sl_lam]; simp only [zx_eq, hx.2]; ring
    · show z (Idx.u i) * slack (lcpq G) (lcpM G) z (Idx.u i) = 0
      rw [sl_u]; simp only [zf_eq, hmass]; ring
    · show z (Idx.x j) * slack (lcpq G) (lcpM G) z (Idx.x j) = 0
      rw [sl_x, zl_eq, zt_eq, zx_eq]; simp only [zf_eq]
      have : score G f j = dd G j * ∑ i, f i j := rfl
      rw [← this]
      rcases (hx.1 j).1.lt_or_eq with hpos | hzero
      · have := (hl0 j).1 hpos
        rw [max_eq_left (by linarith)]; ring
      · rw [← hzero]; ring

end Formulation2

/-! ## Uniform bound -/

section Bound

variable {T Θ : Type*} [Fintype T] [DecidableEq T] [Fintype Θ] [DecidableEq Θ] [Nonempty T]
variable (G : BSSG T Θ)

theorem slack_add_smul {ι : Type*} [Fintype ι] [DecidableEq ι] (q : ι → ℚ) (M : Matrix ι ι ℚ)
    (δ : ℚ) (z : ι → ℚ) (k : ι) :
    slack q (M + δ • (1 : Matrix ι ι ℚ)) z k = slack q M z k + δ * z k := by
  simp [slack, add_mulVec, smul_mulVec, one_mulVec]; ring

theorem exists_pos_of_sum_pos {α : Type*} [Fintype α] {g : α → ℚ} (h : 0 < ∑ a, g a) :
    ∃ a, a ∈ univ ∧ 0 < g a := by
  by_contra hne
  push Not at hne
  have : ∑ a, g a ≤ 0 := sum_nonpos fun a _ => hne a (mem_univ a)
  linarith

theorem one_le_cU : 1 ≤ cU G := (Finset.le_fold_max _).mpr (Or.inl le_rfl)

theorem shiftA_le_cU (i : Θ) (j : T) : shiftA G i j ≤ cU G :=
  (Finset.le_fold_max _).mpr (Or.inr ⟨(i, j), mem_univ _, le_rfl⟩)

theorem dd_le_cDstar (j : T) : dd G j ≤ cDstar G :=
  (Finset.le_fold_max _).mpr (Or.inr ⟨j, mem_univ _, le_rfl⟩)

theorem cK_ge : max (max 1 (cU G)) (max (cW G) (1 + cS G)) ≤ cK G := Int.le_ceil _

theorem one_le_cK : 1 ≤ cK G := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (cK_ge G)

/-- [DL Lemma dl:lem:bound]: for `0 < δ ≤ 1` every solution of `LCP(q, M + δI)` lies in `[0, K]^N`. -/
theorem uniform_bound (hwf : G.WellFormed) (δ : ℚ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (z : Idx Θ T → ℚ) (hz : IsLCPSol (lcpq G) (lcpMδ G δ) z) : ∀ k, 0 ≤ z k ∧ z k ≤ cK G := by
  obtain ⟨hz0, hw0, hc⟩ := hz
  have hb := bb_nonneg G hwf
  have hd := dd_nonneg G hwf
  have sl : ∀ k, slack (lcpq G) (lcpMδ G δ) z k = slack (lcpq G) (lcpM G) z k + δ * z k :=
    fun k => slack_add_smul _ _ δ z k
  -- vanishing perturbed slack where the variable is positive
  have hzero : ∀ k, 0 < z k → slack (lcpq G) (lcpM G) z k + δ * z k = 0 := by
    intro k hk
    have := hc k; rw [sl] at this
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hk.ne'
    · exact h
  have hnn : ∀ k, 0 ≤ slack (lcpq G) (lcpM G) z k + δ * z k := fun k => by rw [← sl]; exact hw0 k
  -- types
  have hu : ∀ i, z (Idx.u i) ≤ cU G := by
    intro i
    rcases (hz0 (Idx.u i)).lt_or_eq with hpos | h0
    · have h1 := hzero _ hpos; rw [sl_u] at h1
      have hsum : 0 < ∑ j, z (Idx.f i j) := by
        have := hwf.2.1 i; nlinarith
      obtain ⟨j, -, hj⟩ := exists_pos_of_sum_pos hsum
      have h2 := hzero _ hj; rw [sl_f] at h2
      have := shiftA_le_cU G i j
      nlinarith [hb i j, hz0 (Idx.x j), hz0 (Idx.f i j)]
    · rw [← h0]; linarith [one_le_cU G]
  -- flows
  have hrow : ∀ i, ∑ j, z (Idx.f i j) ≤ G.prior i + cU G := by
    intro i
    have h1 := hnn (Idx.u i); rw [sl_u] at h1
    nlinarith [hu i, hz0 (Idx.u i)]
  have htot : ∑ i, ∑ j, z (Idx.f i j) ≤ cW G := by
    calc ∑ i, ∑ j, z (Idx.f i j) ≤ ∑ i, (G.prior i + cU G) := sum_le_sum fun i _ => hrow i
      _ = cW G := by
        rw [sum_add_distrib, hwf.2.2.1]; simp [cW, sum_const, card_univ, nsmul_eq_mul]
  have hf : ∀ i j, z (Idx.f i j) ≤ cW G := by
    intro i j
    refine le_trans ?_ htot
    refine le_trans (single_le_sum (f := fun j => z (Idx.f i j)) (fun j _ => hz0 _) (mem_univ j)) ?_
    exact single_le_sum (f := fun i => ∑ j, z (Idx.f i j)) (fun i _ => sum_nonneg fun j _ => hz0 _)
      (mem_univ i)
  have hw : ∀ j, ∑ i, z (Idx.f i j) ≤ cW G := by
    intro j
    refine le_trans ?_ htot
    rw [Finset.sum_comm]
    exact single_le_sum (f := fun j => ∑ i, z (Idx.f i j)) (fun j _ => sum_nonneg fun i _ => hz0 _)
      (mem_univ j)
  have hW0 : 0 ≤ cW G := le_trans (sum_nonneg fun i _ => sum_nonneg fun j _ => hz0 _) htot
  have hdw : ∀ j, dd G j * ∑ i, z (Idx.f i j) ≤ cDstar G * cW G := fun j =>
    mul_le_mul (dd_le_cDstar G j) (hw j) (sum_nonneg fun i _ => hz0 _)
      (le_trans (hd j) (dd_le_cDstar G j))
  -- caps
  have ht : ∀ j, z (Idx.t j) ≤ cS G := by
    intro j
    rcases (hz0 (Idx.t j)).lt_or_eq with hpos | h0
    · have h1 := hzero _ hpos; rw [sl_t] at h1
      have hx : 0 < z (Idx.x j) := by nlinarith
      have h2 := hzero _ hx; rw [sl_x] at h2
      have := hdw j
      simp only [cS]; nlinarith [hz0 Idx.lam]
    · rw [← h0]; simp only [cS]; nlinarith [hdw j, hd j, sum_nonneg fun i (_ : i ∈ univ) => hz0 (Idx.f i j)]
  have hS0 : 0 ≤ cS G := le_trans (hz0 _) (ht (Classical.arbitrary T))
  have hx : ∀ j, z (Idx.x j) ≤ 1 + cS G := by
    intro j
    have h1 := hnn (Idx.t j); rw [sl_t] at h1
    nlinarith [ht j, hz0 (Idx.t j)]
  have hl : z Idx.lam ≤ cS G := by
    rcases (hz0 Idx.lam).lt_or_eq with hpos | h0
    · have h1 := hzero _ hpos; rw [sl_lam] at h1
      have hsum : 0 < ∑ j, z (Idx.x j) := by
        have : (0 : ℚ) ≤ G.r := Nat.cast_nonneg _
        nlinarith
      obtain ⟨j, -, hj⟩ := exists_pos_of_sum_pos hsum
      have h2 := hzero _ hj; rw [sl_x] at h2
      simp only [cS]; nlinarith [hdw j, hz0 (Idx.t j), hz0 (Idx.x j)]
    · rw [← h0]; exact hS0
  have hK := cK_ge G
  have hK1 : cU G ≤ cK G := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hK
  have hK2 : cW G ≤ cK G := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hK
  have hK3 : 1 + cS G ≤ cK G := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hK
  rintro ((⟨i, j⟩ | j | _) | (i | j))
  · exact ⟨hz0 _, le_trans (hf i j) hK2⟩
  · exact ⟨hz0 _, by linarith [ht j]⟩
  · exact ⟨hz0 _, by linarith⟩
  · exact ⟨hz0 _, le_trans (hu i) hK1⟩
  · exact ⟨hz0 _, le_trans (hx j) hK3⟩

end Bound

/-! ## Pattern LP, exact recovery, main theorem (modulo the gap lemma) -/

section Main

variable {T Θ : Type*} [Fintype T] [DecidableEq T] [Fintype Θ] [DecidableEq Θ] [Nonempty T]
variable (G : BSSG T Θ)

/-- [DL §4 "The pattern LP"]: every feasible point of a pattern LP solves `LCP(q, M)`. -/
theorem pattern_sol (P : Finset (Idx Θ T)) (z : Idx Θ T → ℚ) (h : IsPatternFeasible G P z) :
    IsLCPSol (lcpq G) (lcpM G) z := by
  obtain ⟨hbox, hpin, hsl, heq⟩ := h
  refine ⟨fun k => (hbox k).1, hsl, fun k => ?_⟩
  by_cases hk : k ∈ P
  · rw [heq k hk, mul_zero]
  · rw [hpin k hk, zero_mul]

/-- A relaxed-feasible point with `τ = 0` is pattern-feasible. -/
theorem pattern_of_relaxed_zero (P : Finset (Idx Θ T)) (z : Idx Θ T → ℚ)
    (h : IsRelaxedFeasible G P z 0) : IsPatternFeasible G P z := by
  obtain ⟨h1, h2, h3, h4, -, -⟩ := h
  refine ⟨h3, fun k hk => le_antisymm (h4 k hk) (h3 k).1, fun k => by simpa using h1 k,
    fun k hk => le_antisymm (by simpa using h2 k hk) (by simpa using h1 k)⟩

theorem one_le_cC : 1 ≤ cC G := le_max_left _ _

theorem one_le_cQ : (1 : ℚ) ≤ cQ G := by
  have : 1 ≤ cQ G := Nat.one_le_pow _ _ (Nat.mul_pos (Nat.succ_pos _) (one_le_cC G))
  exact_mod_cast this

theorem cδ_pos : 0 < cδ G := by
  have := one_le_cQ G; have := one_le_cK G
  unfold cδ; positivity

theorem cδ_le_one : cδ G ≤ 1 := by
  have := one_le_cQ G; have := one_le_cK G
  unfold cδ
  rw [div_le_one (by positivity)]; nlinarith

theorem cδ_mul_cK : cδ G * cK G = 1 / (2 * cQ G) := by
  have := one_le_cQ G; have := one_le_cK G
  unfold cδ; field_simp

/-- The perturbed solution, with `τ = δK`, is feasible for the relaxed pattern LP of its support
[DL Thm. dl:thm:main, "Exact recovery"]. -/
theorem relaxed_of_perturbed (hwf : G.WellFormed) (z : Idx Θ T → ℚ)
    (hz : IsLCPSol (lcpq G) (lcpMδ G (cδ G)) z) :
    IsRelaxedFeasible G (support z) z (cδ G * cK G) := by
  have hbox := uniform_bound G hwf (cδ G) (cδ_pos G) (cδ_le_one G) z hz
  obtain ⟨hz0, hw0, hc⟩ := hz
  have hδ := cδ_pos G
  have sl : ∀ k, slack (lcpq G) (lcpMδ G (cδ G)) z k = slack (lcpq G) (lcpM G) z k + cδ G * z k :=
    fun k => slack_add_smul _ _ _ z k
  have hK := one_le_cK G
  refine ⟨fun k => ?_, fun k hk => ?_, hbox, fun k hk => ?_, by positivity, ?_⟩
  · have := hw0 k; rw [sl] at this
    nlinarith [(hbox k).2]
  · have hpos : 0 < z k := by simpa [support] using hk
    have := hc k; rw [sl] at this
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hpos.ne'
    · nlinarith [(hbox k).2, hbox k]
  · have : ¬ 0 < z k := by simpa [support] using hk
    linarith
  · rw [cδ_mul_cK]
    have := one_le_cQ G
    rw [div_le_one (by positivity)]; linarith

/-- [DL Thm. dl:thm:main], `0 < r < n`, assuming the gap lemma: the query `M + δI` (`δ = 1/(2KQ)`)
is a P-matrix; for a solution `z*` of `LCP(q, M + δI)`, the pattern LP of `P = supp z*` is feasible,
and each of its solutions solves `LCP(q, M)` and gives a BNE in marginal coordinates. -/
theorem main_of_gap (hwf : G.WellFormed) (hr0 : 0 < G.r) (hrn : G.r < Fintype.card T)
    (hgap : GapLemma T Θ G) (z : Idx Θ T → ℚ) (hz : IsLCPSol (lcpq G) (lcpMδ G (cδ G)) z) :
    IsPMatrix (lcpMδ G (cδ G)) ∧ (∃ z', IsPatternFeasible G (support z) z') ∧
      ∀ z', IsPatternFeasible G (support z) z' →
        IsLCPSol (lcpq G) (lcpM G) z' ∧ IsMarginalBNE G (zx z') (zf z') := by
  refine ⟨isP_add_smul _ (lcpM_isP0 G hwf) _ (cδ_pos G), ?_, fun z' hz' => ?_⟩
  · have hrel := relaxed_of_perturbed G hwf z hz
    obtain ⟨z₀, τ₀, hfeas, hmin, hgap'⟩ := hgap (support z) ⟨z, _, hrel⟩
    have hle := hmin _ _ hrel
    rw [cδ_mul_cK] at hle
    have hQ := one_le_cQ G
    rcases hgap' with h0 | hge
    · subst h0; exact ⟨z₀, pattern_of_relaxed_zero G _ _ hfeas⟩
    · exfalso
      have : 1 / (cQ G : ℚ) ≤ 1 / (2 * cQ G) := le_trans hge hle
      rw [div_le_div_iff₀ (by positivity) (by positivity)] at this
      linarith
  · have hs := pattern_sol G _ z' hz'
    exact ⟨hs, (formulation_a G hwf hr0 hrn z' hs).2.2⟩

end Main

/-! ## The statements of `Statements.lean` -/

section Final

variable (T Θ : Type*) [Fintype T] [DecidableEq T] [Fintype Θ] [DecidableEq Θ]

theorem cutoffForm_proof : CutoffForm T Θ := fun G π x hx => cutoff_form G π x hx

theorem p0Core_proof : P0Core T Θ := fun β hβ d hd k ρ φ => p0core β hβ d hd k ρ φ

theorem p0_proof : P0 T Θ := fun G hb hd => incMat_isP0 (bb G) hb (dd G) hd

theorem diagPerturbation_proof : DiagPerturbation T Θ := by
  intro G hwf δ hδ
  have hM := lcpM_isP0 G hwf
  exact ⟨isP_add_smul _ hM δ hδ, det_principal_add_smul_ge _ hM δ hδ.le,
    no_signReversing_add_smul _ hM δ hδ, fun q z z' hz hz' => lcp_unique_add_smul _ hM δ hδ q z z' hz hz'⟩

theorem marginalIffCoverage_proof : MarginalIffCoverage T Θ := by
  intro G hr hd0 hd1 hp ξ σ hσ
  have hscore : ∀ j, score G (fun i j => G.prior i * σ i j) j = G.load σ j := by
    intro j; simp [score, wload, dd, hd0, hd1, BSSG.load]
  have hfeas : ∀ x, IsFeasibleCov G x ↔ BSSG.IsDist x := by
    intro x; constructor
    · rintro ⟨h1, h2⟩; exact ⟨fun j => (h1 j).1, by rw [h2, hr]; simp⟩
    · rintro ⟨h1, h2⟩
      refine ⟨fun j => ⟨h1 j, ?_⟩, by rw [h2, hr]; simp⟩
      rw [← h2]; exact single_le_sum (fun k _ => h1 k) (mem_univ j)
  have hsum : ∀ x : T → ℚ,
      ∑ j, score G (fun i j => G.prior i * σ i j) j * x j = ∑ t, x t * G.load σ t := by
    intro x; refine sum_congr rfl fun j _ => ?_; rw [hscore, mul_comm]
  have hopt : (∀ x', IsFeasibleCov G x' → ∑ j, score G (fun i j => G.prior i * σ i j) j * x' j ≤
      ∑ j, score G (fun i j => G.prior i * σ i j) j * ξ j) ↔
      (∀ y, BSSG.IsDist y → ∑ t, y t * G.load σ t ≤ ∑ t, ξ t * G.load σ t) := by
    simp only [hsum]; constructor
    · intro h y hy; exact h y ((hfeas y).mpr hy)
    · intro h x' hx'; exact h x' ((hfeas x').mp hx')
  constructor
  · rintro ⟨hx, -, -, hatt, hdef⟩
    have hξ := (hfeas ξ).mp hx
    exact ⟨hξ, hσ, fun θ k hk j => hatt θ k (mul_pos (hp θ) hk) j,
      (Emb.simplex_br (G.load σ) ξ hξ).mp (hopt.mp hdef)⟩
  · rintro ⟨hξ, -, hatt, hdef⟩
    refine ⟨(hfeas ξ).mpr hξ, fun i j => mul_nonneg (hp i).le ((hσ i).1 j),
      fun i => by rw [← mul_sum, (hσ i).2, mul_one], fun i j hf k => hatt i j ?_ k,
      hopt.mpr ((Emb.simplex_br _ ξ hξ).mpr hdef)⟩
    by_contra h; push Not at h; nlinarith [hp i]

theorem bneIffMarginal_proof : BNEIffMarginal T Θ := by
  intro G hr hd0 hd1 hp δ σ
  rw [Emb.fact0_main G hr hd0 hd1 δ σ]
  constructor
  · rintro ⟨hδ, hcov⟩
    exact ⟨hδ, hcov.2.1,
      (marginalIffCoverage_proof T Θ G hr hd0 hd1 hp _ σ hcov.2.1).mpr hcov⟩
  · rintro ⟨hδ, hσ, hm⟩
    exact ⟨hδ, (marginalIffCoverage_proof T Θ G hr hd0 hd1 hp _ σ hσ).mp hm⟩

variable [Nonempty T]

theorem slackTable_proof : SlackTable T Θ := fun G z => slack_eq_table G z

theorem formulationA_proof : FormulationA T Θ := fun G hwf hr0 hrn z hz =>
  formulation_a G hwf hr0 hrn z hz

theorem formulationB_proof : FormulationB T Θ := fun G hwf _ hrn x f h =>
  formulation_b G hwf hrn x f h

theorem uniformBound_proof : UniformBound T Θ := fun G hwf δ h0 h1 z hz =>
  uniform_bound G hwf δ h0 h1 z hz

theorem patternSol_proof : PatternSol T Θ := fun G P z h => pattern_sol G P z h

/-- [DL Thm. dl:thm:main] from the gap lemma (proved in `Gap.lean`). -/
theorem main_proof_of_gap (hgap : Gap T Θ) : MainTheorem T Θ := by
  intro G hwf hr0 hrn
  refine ⟨isP_add_smul _ (lcpM_isP0 G hwf) _ (cδ_pos G), cδ_pos G, cδ_le_one G, fun z hz => ?_⟩
  obtain ⟨-, h2, h3⟩ := main_of_gap G hwf hr0 hrn (hgap G) z hz
  exact ⟨h2, h3⟩

end Final

section Generic

variable (F R : Type*) [Fintype F] [Fintype R] [DecidableEq F] [DecidableEq R]

theorem blockDet_proof : BlockDet F R := fun B D S =>
  ⟨blockdet_card_ne B D S, fun _ e1 e2 => blockdet B D S e1 e2⟩

variable (ι : Type*) [Fintype ι] [DecidableEq ι]

theorem p0AddSmulIsP_proof : P0AddSmulIsP ι := fun M hM δ hδ => isP_add_smul M hM δ hδ

end Generic

end DirectLCP
end Bssg
