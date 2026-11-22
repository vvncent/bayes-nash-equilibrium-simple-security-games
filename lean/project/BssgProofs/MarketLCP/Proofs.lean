import BssgProofs.MarketLCP.Statements
import BssgProofs.DirectLCP.Gap

/-!
# The market (M1) reduces to one P-matrix LCP: proofs

Proofs of the statements in `Statements.lean`.  No `sorry`, `admit` or `axiom`.
Reused from `DirectLCP`: `blockdet`, `blockdet_card_ne`, `p0core` (P₀ core for incidence
matrices), `isP_add_smul`, `det_principal_add_smul_ge`, `lcp_unique_add_smul`, `slack_add_smul`,
and from `DirectLCP/Gap.lean` the LP machinery `abs_det_le`, `tightSpan`, `exists_perp`,
`vertex_value`.
-/

namespace Bssg
namespace MarketLCP

open Finset Matrix DirectLCP

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

/-! ## 1. The slack table and the LCP formulation -/

section Formulation

variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
variable (Mk : Market I J)

theorem zf_edge (z : Idx Mk → ℚ) (e : Edge Mk) : zf Mk z e.1 = z (.inl e) := by
  simp [zf, e.2]

theorem sum_edge (g : I × J → ℚ) : ∑ e : Edge Mk, g e.1 = ∑ e ∈ Mk.E, g e :=
  Finset.sum_coe_sort Mk.E g

theorem rowSum_eq (z : Idx Mk → ℚ) (i : I) :
    Mk.rowSum (zf Mk z) i = ∑ e : Edge Mk, if e.1.1 = i then z (.inl e) else 0 := by
  rw [Market.rowSum, sum_filter]
  rw [← sum_edge Mk (fun e => if e.1 = i then zf Mk z e else 0)]
  simp only [zf_edge]

theorem colSum_eq (z : Idx Mk → ℚ) (j : J) :
    Mk.colSum (zf Mk z) j = ∑ e : Edge Mk, if e.1.2 = j then z (.inl e) else 0 := by
  rw [Market.colSum, sum_filter]
  rw [← sum_edge Mk (fun e => if e.2 = j then zf Mk z e else 0)]
  simp only [zf_edge]

/-- `q + M z` is the slack table. -/
theorem slack_eq_table (z : Idx Mk → ℚ) : slack (lcpq Mk) (lcpM Mk) z = slackTable Mk z := by
  ext (e | i | j)
  · simp [slack, lcpM, lcpq, slackTable, fromBlocks_mulVec, mulVec, dotProduct, matB,
      Fintype.sum_sum_type]
    ring
  · simp [slack, lcpM, lcpq, slackTable, fromBlocks_mulVec, mulVec, dotProduct, matK,
      rowSum_eq]
    ring
  · simp [slack, lcpM, lcpq, slackTable, fromBlocks_mulVec, mulVec, dotProduct, matK,
      colSum_eq]
    ring


theorem sl_f (z : Idx Mk → ℚ) (e : Edge Mk) : slack (lcpq Mk) (lcpM Mk) z (.inl e) =
    z (Idx.u e.1.1) + Mk.b e.1 * z (Idx.P e.1.2) - Mk.a e.1 := by rw [slack_eq_table]; rfl
theorem sl_u (z : Idx Mk → ℚ) (i : I) : slack (lcpq Mk) (lcpM Mk) z (Idx.u i) =
    Mk.mass i - Mk.rowSum (zf Mk z) i := by rw [slack_eq_table]; rfl
theorem sl_P (z : Idx Mk → ℚ) (j : J) : slack (lcpq Mk) (lcpM Mk) z (Idx.P j) =
    Mk.cap j - Mk.colSum (zf Mk z) j := by rw [slack_eq_table]; rfl

theorem zero_of_compl {x w : ℚ} (h : x * w = 0) (hx : 0 < x) : w = 0 := by
  rcases mul_eq_zero.mp h with h | h
  · exact absurd h hx.ne'
  · exact h

/-- [PL Lemma plcp:lem:formulation], SOL ⇒ equilibrium. -/
theorem sol_to_eq (z : Idx Mk → ℚ) (hz : IsLCPSol (lcpq Mk) (lcpM Mk) z) :
    Mk.IsEquilibrium (zP Mk z) (zu Mk z) (zf Mk z) := by
  obtain ⟨hz0, hw0, hc⟩ := hz
  refine ⟨fun j => hz0 _, fun i => hz0 _, fun e he => ?_, fun e he => ?_, fun e he hpos => ?_,
    fun i => ?_, fun i hpos => ?_, fun j => ?_, fun j hpos => ?_⟩
  · simpa [zf, he] using hz0 (.inl ⟨e, he⟩)
  · have := hw0 (.inl ⟨e, he⟩); rw [sl_f] at this
    simp only [zu, zP]; linarith
  · have hpos' : 0 < z (.inl ⟨e, he⟩) := by simpa [zf, he] using hpos
    have := zero_of_compl (hc (.inl ⟨e, he⟩)) hpos'; rw [sl_f] at this
    simp only [zu, zP]; linarith
  · have := hw0 (Idx.u i); rw [sl_u] at this; linarith
  · have := zero_of_compl (hc (Idx.u i)) hpos; rw [sl_u] at this; linarith
  · have := hw0 (Idx.P j); rw [sl_P] at this; linarith
  · have := zero_of_compl (hc (Idx.P j)) hpos; rw [sl_P] at this; linarith

theorem zf_encode (P : J → ℚ) (v : I → ℚ) (f : I × J → ℚ) (e : I × J) (he : e ∈ Mk.E) :
    zf Mk (encode Mk P v f) e = f e := by
  simp [zf, he, encode]

theorem rowSum_encode (P : J → ℚ) (v : I → ℚ) (f : I × J → ℚ) (i : I) :
    Mk.rowSum (zf Mk (encode Mk P v f)) i = Mk.rowSum f i :=
  sum_congr rfl fun e he => zf_encode Mk P v f e (mem_filter.mp he).1

theorem colSum_encode (P : J → ℚ) (v : I → ℚ) (f : I × J → ℚ) (j : J) :
    Mk.colSum (zf Mk (encode Mk P v f)) j = Mk.colSum f j :=
  sum_congr rfl fun e he => zf_encode Mk P v f e (mem_filter.mp he).1

/-- [PL Lemma plcp:lem:formulation], equilibrium ⇒ SOL. -/
theorem eq_to_sol (P : J → ℚ) (v : I → ℚ) (f : I × J → ℚ) (h : Mk.IsEquilibrium P v f) :
    IsLCPSol (lcpq Mk) (lcpM Mk) (encode Mk P v f) := by
  refine ⟨fun k => ?_, fun k => ?_, fun k => ?_⟩
  · rcases k with e | i | j
    · exact h.f_nonneg e.1 e.2
    · exact h.v_nonneg i
    · exact h.P_nonneg j
  · rcases k with e | i | j
    · rw [sl_f]; have := h.cond_a e.1 e.2; simp only [encode, Sum.elim_inl, Sum.elim_inr]
      linarith
    · rw [sl_u, rowSum_encode]; linarith [h.cond_c_le i]
    · rw [sl_P, colSum_encode]; linarith [h.cond_d_le j]
  · rcases k with e | i | j
    · rw [sl_f]; simp only [encode, Sum.elim_inl, Sum.elim_inr]
      rcases (h.f_nonneg e.1 e.2).lt_or_eq with hp | h0
      · rw [h.cond_b e.1 e.2 hp]; ring
      · rw [← h0]; ring
    · rw [sl_u, rowSum_encode]; simp only [encode, Sum.elim_inl, Sum.elim_inr]
      rcases (h.v_nonneg i).lt_or_eq with hp | h0
      · rw [h.cond_c_eq i hp]; ring
      · rw [← h0]; ring
    · rw [sl_P, colSum_encode]; simp only [encode, Sum.elim_inl, Sum.elim_inr]
      rcases (h.P_nonneg j).lt_or_eq with hp | h0
      · rw [h.cond_d_eq j hp]; ring
      · rw [← h0]; ring

theorem encode_decode (z : Idx Mk → ℚ) : encode Mk (zP Mk z) (zu Mk z) (zf Mk z) = z := by
  ext (e | i | j)
  · exact zf_edge Mk z e
  · rfl
  · rfl

end Formulation

/-! ## 2. P₀ (via the DirectLCP incidence-matrix core) -/

section P0

variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
variable (Mk : Market I J)

/-- Slopes extended to all of `I × J` (`0` off `E`), as weights of DirectLCP's `incMat`. -/
def βof (i : I) (j : J) : ℚ := if (i, j) ∈ Mk.E then Mk.b (i, j) else 0

theorem βof_nonneg (hb : ∀ e ∈ Mk.E, 0 ≤ Mk.b e) (i : I) (j : J) : 0 ≤ βof Mk i j := by
  unfold βof; split_ifs with h
  · exact hb _ h
  · exact le_rfl

/-- `Bᵀ` is the restriction of DirectLCP's `incMat β` to the attack columns of edges in `E`. -/
theorem matB_eq : matB Mk =
    (incMat (βof Mk)).submatrix id (fun e : Edge Mk => (Sum.inl e.1 : FIdx I J)) := by
  ext (i | j) ⟨⟨i', j'⟩, he⟩
  · simp [matB, incMat, eq_comm]
  · by_cases h : j = j'
    · subst h; simp [matB, incMat, βof, he]
    · simp [matB, incMat, h, Ne.symm h]

/-- `Kᵀ` is the restriction of DirectLCP's `incMat 1` to the attack columns of edges in `E`. -/
theorem matK_eq : matK Mk =
    (incMat (fun (_ : I) (_ : J) => (1 : ℚ))).submatrix id
      (fun e : Edge Mk => (Sum.inl e.1 : FIdx I J)) := by
  ext (i | j) ⟨⟨i', j'⟩, he⟩
  · simp [matK, incMat, eq_comm]
  · simp [matK, incMat, eq_comm]

/-- [PL Lemma plcp:lem:p0]: `M` is P₀ for every market with slopes `b ≥ 0` on `E`. -/
theorem lcpM_isP0 (hb : ∀ e ∈ Mk.E, 0 ≤ Mk.b e) : IsP0Matrix (lcpM Mk) := by
  intro S
  unfold lcpM
  by_cases h : Fintype.card {a // Sum.inl a ∈ S} = Fintype.card {b // Sum.inr b ∈ S}
  · rw [blockdet _ _ S (Fintype.equivFin _).symm (Fintype.equivFinOfCardEq h.symm).symm,
      matB_eq, matK_eq, submatrix_submatrix, submatrix_submatrix]
    exact p0core (βof Mk) (βof_nonneg Mk hb) (fun _ => 1) (fun _ => zero_le_one) _ _ _
  · rw [blockdet_card_ne _ _ S h]

end P0

/-! ## 3. Diagonal perturbation and the uniform bound -/

section Bound

variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
variable (Mk : Market I J)

theorem b_nonneg (hwf : Mk.WellFormed) : ∀ e ∈ Mk.E, 0 ≤ Mk.b e := fun e he => (hwf.2.2 e he).le

/-- [PL Lemma plcp:lem:pmatrix] for the market matrix. -/
theorem pmatrix (hb : ∀ e ∈ Mk.E, 0 ≤ Mk.b e) (ε : ℚ) (hε : 0 < ε) :
    IsPMatrix (lcpMeps Mk ε) ∧ (∀ S, ε ^ S.card ≤ (principal (lcpMeps Mk ε) S).det) ∧
    ∀ q' z z', IsLCPSol q' (lcpMeps Mk ε) z → IsLCPSol q' (lcpMeps Mk ε) z' → z = z' :=
  ⟨isP_add_smul _ (lcpM_isP0 Mk hb) ε hε,
    fun S => det_principal_add_smul_ge _ (lcpM_isP0 Mk hb) ε hε.le S,
    fun q' z z' hz hz' => lcp_unique_add_smul _ (lcpM_isP0 Mk hb) ε hε q' z z' hz hz'⟩

theorem cH_nonneg : 0 ≤ cH Mk := (Finset.le_fold_max _).mpr (Or.inl le_rfl)

theorem a_le_cH (e : I × J) (he : e ∈ Mk.E) : Mk.a e ≤ cH Mk :=
  (Finset.le_fold_max _).mpr (Or.inr ⟨e, he, le_rfl⟩)

theorem muMax_nonneg : 0 ≤ muMax Mk := (Finset.le_fold_max _).mpr (Or.inl le_rfl)

theorem mass_le_muMax (i : I) : Mk.mass i ≤ muMax Mk :=
  (Finset.le_fold_max _).mpr (Or.inr ⟨i, mem_univ _, le_rfl⟩)

theorem bmin_le (e : I × J) (he : e ∈ Mk.E) : bmin Mk ≤ Mk.b e := by
  unfold bmin; rw [dite_eq_left_of_eq_true (eq_true ⟨e, he⟩)]; exact inf'_le _ he

theorem bmin_pos (hwf : Mk.WellFormed) : 0 < bmin Mk := by
  unfold bmin
  split_ifs with h
  · obtain ⟨e, he, heq⟩ := exists_mem_eq_inf' h Mk.b
    rw [heq]; exact hwf.2.2 e he
  · exact one_pos

theorem one_le_Zbar : 1 ≤ Zbar Mk := by
  unfold Zbar
  have := cH_nonneg Mk; have := muMax_nonneg Mk
  have : 0 ≤ muMax Mk + cH Mk := by linarith
  linarith [le_max_left (muMax Mk + cH Mk) (cH Mk / bmin Mk)]

theorem exists_pos_of_filter_sum_pos {s : Finset (I × J)} {g : I × J → ℚ}
    (h : 0 < ∑ e ∈ s, g e) : ∃ e ∈ s, 0 < g e := by
  by_contra hne
  push Not at hne
  have : ∑ e ∈ s, g e ≤ 0 := sum_nonpos hne
  linarith

theorem slack_eps (ε : ℚ) (z : Idx Mk → ℚ) (k : Idx Mk) :
    slack (lcpq Mk) (lcpMeps Mk ε) z k = slack (lcpq Mk) (lcpM Mk) z k + ε * z k :=
  slack_add_smul _ _ ε z k

/-- [PL Lemma plcp:lem:bound]. -/
theorem uniform_bound (hwf : Mk.WellFormed) (ε : ℚ) (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (z : Idx Mk → ℚ) (hz : IsLCPSol (lcpq Mk) (lcpMeps Mk ε) z) :
    ∀ k, 0 ≤ z k ∧ z k ≤ Zbar Mk - 1 := by
  obtain ⟨hz0, hw0, hc⟩ := hz
  have hzero : ∀ k, 0 < z k → slack (lcpq Mk) (lcpM Mk) z k + ε * z k = 0 := fun k hk => by
    have := zero_of_compl (hc k) hk; rwa [slack_eps] at this
  have hnn : ∀ k, 0 ≤ slack (lcpq Mk) (lcpM Mk) z k + ε * z k := fun k => by
    rw [← slack_eps]; exact hw0 k
  have hfnn : ∀ e ∈ Mk.E, 0 ≤ zf Mk z e := fun e he => by simpa [zf, he] using hz0 (.inl ⟨e, he⟩)
  -- a positive flow `f_e` makes `w^ε_e = 0`: `u_i + b P_j + ε f_e = a_e`
  have hedge : ∀ e ∈ Mk.E, 0 < zf Mk z e →
      z (Idx.u e.1) + Mk.b e * z (Idx.P e.2) + ε * zf Mk z e = Mk.a e := by
    intro e he hpos
    have hpos' : 0 < z (.inl ⟨e, he⟩) := by simpa [zf, he] using hpos
    have := hzero _ hpos'; rw [sl_f] at this
    simp only [zf, he, ↓reduceDIte]; simp only at this; linarith
  have hu : ∀ i, z (Idx.u i) ≤ cH Mk := by
    intro i
    rcases (hz0 (Idx.u i)).lt_or_eq with hpos | h0
    · have h1 := hzero _ hpos; rw [sl_u] at h1
      have hsum : 0 < Mk.rowSum (zf Mk z) i := by have := hwf.1 i; nlinarith
      obtain ⟨e, hef, hepos⟩ := exists_pos_of_filter_sum_pos hsum
      obtain ⟨he, rfl⟩ := mem_filter.mp hef
      have h2 := hedge e he hepos
      have := a_le_cH Mk e he
      nlinarith [hwf.2.2 e he, hz0 (Idx.P e.2), hfnn e he]
    · rw [← h0]; exact cH_nonneg Mk
  have hP : ∀ j, z (Idx.P j) ≤ cH Mk / bmin Mk := by
    intro j
    rcases (hz0 (Idx.P j)).lt_or_eq with hpos | h0
    · have h1 := hzero _ hpos; rw [sl_P] at h1
      have hsum : 0 < Mk.colSum (zf Mk z) j := by have := hwf.2.1 j; nlinarith
      obtain ⟨e, hef, hepos⟩ := exists_pos_of_filter_sum_pos hsum
      obtain ⟨he, rfl⟩ := mem_filter.mp hef
      have h2 := hedge e he hepos
      have ha := a_le_cH Mk e he
      have hbpos := hwf.2.2 e he
      have hbP : z (Idx.P e.2) * Mk.b e ≤ cH Mk := by
        nlinarith [hz0 (Idx.u e.1), hfnn e he]
      calc z (Idx.P e.2) ≤ cH Mk / Mk.b e := (le_div_iff₀ hbpos).mpr hbP
        _ ≤ cH Mk / bmin Mk :=
          div_le_div_of_nonneg_left (cH_nonneg Mk) (bmin_pos Mk hwf) (bmin_le Mk e he)
    · rw [← h0]; exact div_nonneg (cH_nonneg Mk) (bmin_pos Mk hwf).le
  have hf : ∀ e : Edge Mk, z (.inl e) ≤ muMax Mk + cH Mk := by
    intro e
    have h1 := hnn (Idx.u e.1.1); rw [sl_u] at h1
    have hle : zf Mk z e.1 ≤ Mk.rowSum (zf Mk z) e.1.1 :=
      single_le_sum (f := zf Mk z) (fun x hx => hfnn x (mem_filter.mp hx).1)
        (mem_filter.mpr ⟨e.2, rfl⟩)
    rw [zf_edge] at hle
    have := mass_le_muMax Mk e.1.1
    have := hu e.1.1
    nlinarith [hz0 (Idx.u e.1.1)]
  have hZ : Zbar Mk - 1 = max (muMax Mk + cH Mk) (cH Mk / bmin Mk) := by unfold Zbar; ring
  intro k
  refine ⟨hz0 k, ?_⟩
  rw [hZ]
  rcases k with e | i | j
  · exact le_trans (hf e) (le_max_left _ _)
  · exact le_trans (le_trans (hu i) (by linarith [muMax_nonneg Mk])) (le_max_left _ _)
  · exact le_trans (hP j) (le_max_right _ _)

end Bound

/-! ## 4. The generic gap lemma for `LP(A)` -/

section VertexPointed

variable {V Rw : Type*} [Fintype V] [DecidableEq V] [Fintype Rw] [DecidableEq Rw]

/-- Variant of DirectLCP's `exists_vertex` for a *pointed* polyhedron (trivial lineality space)
on which the objective `c` is bounded below along every recession direction: from any feasible
point one reaches a vertex (tight rows spanning everything) without increasing `c`. -/
theorem exists_vertex_pointed (a : Rw → V → ℚ) (b : Rw → ℚ)
    (hlin : ∀ d : V → ℚ, (∀ r, 0 ≤ a r ⬝ᵥ d) → (∀ r, 0 ≤ a r ⬝ᵥ (-d)) → d = 0) (c : V → ℚ)
    (hc : ∀ d : V → ℚ, (∀ r, 0 ≤ a r ⬝ᵥ d) → 0 ≤ c ⬝ᵥ d) :
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
  obtain ⟨d, hperp, hcd, hex⟩ : ∃ d : V → ℚ, (∀ w ∈ tightSpan a b y, w ⬝ᵥ d = 0) ∧
      c ⬝ᵥ d ≤ 0 ∧ ∃ r, a r ⬝ᵥ d < 0 := by
    have hperpn : ∀ w ∈ tightSpan a b y, w ⬝ᵥ (-d0) = 0 := fun w hw => by
      rw [dotProduct_neg, hperp0 w hw, neg_zero]
    by_cases h1 : c ⬝ᵥ d0 ≤ 0 ∧ ∃ r, a r ⬝ᵥ d0 < 0
    · exact ⟨d0, hperp0, h1.1, h1.2⟩
    by_cases h2 : c ⬝ᵥ (-d0) ≤ 0 ∧ ∃ r, a r ⬝ᵥ (-d0) < 0
    · exact ⟨-d0, hperpn, h2.1, h2.2⟩
    exfalso
    rw [not_and] at h1 h2
    have hcn : c ⬝ᵥ (-d0) = -(c ⬝ᵥ d0) := dotProduct_neg _ _
    by_cases hle : c ⬝ᵥ d0 ≤ 0
    · have hr1 : ∀ r, 0 ≤ a r ⬝ᵥ d0 := fun r => by
        by_contra hr; exact h1 hle ⟨r, by linarith [not_le.mp hr]⟩
      have := hc d0 hr1
      have hr2 : ∀ r, 0 ≤ a r ⬝ᵥ (-d0) := fun r => by
        by_contra hr; exact h2 (by linarith) ⟨r, by linarith [not_le.mp hr]⟩
      exact hd0 (hlin d0 hr1 hr2)
    · have hr2 : ∀ r, 0 ≤ a r ⬝ᵥ (-d0) := fun r => by
        by_contra hr; exact h2 (by linarith [not_le.mp hle]) ⟨r, by linarith [not_le.mp hr]⟩
      have := hc _ hr2
      linarith [not_le.mp hle]
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
    simp only [Set.mem_ofPred_eq] at hr ⊢
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

end VertexPointed

section GapGeneric

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (q : ι → ℚ) (M : Matrix ι ι ℚ)

/-- The `4N + 1` rows of `LP(A)` (before selecting the active ones), each `coef ⬝ (z, ρ) ≥ rhs`:
`D(q+Mz)_k + Dρ ≥ 0`, `−D(q+Mz)_k + Dρ ≥ 0`, `z_k ≥ 0`, `−z_k ≥ 0`, `ρ ≥ 0`. -/
abbrev LPRow (ι : Type*) := ι ⊕ ι ⊕ ι ⊕ ι ⊕ Unit

/-- Cleared (integer) coefficients over the variables `ι ⊕ Unit` (`inr ()` is `ρ`). -/
def lpCoef : LPRow ι → (ι ⊕ Unit) → ℚ
  | .inl k => Sum.elim (fun l => (lcmDen q M : ℚ) * M k l) (fun _ => (lcmDen q M : ℚ))
  | .inr (.inl k) => Sum.elim (fun l => -((lcmDen q M : ℚ) * M k l)) (fun _ => (lcmDen q M : ℚ))
  | .inr (.inr (.inl k)) => Sum.elim (fun l => if l = k then 1 else 0) (fun _ => 0)
  | .inr (.inr (.inr (.inl k))) => Sum.elim (fun l => if l = k then -1 else 0) (fun _ => 0)
  | .inr (.inr (.inr (.inr _))) => Sum.elim (fun _ => 0) (fun _ => 1)

/-- Cleared (integer) right sides. -/
def lpRhs : LPRow ι → ℚ
  | .inl k => -((lcmDen q M : ℚ) * q k)
  | .inr (.inl k) => (lcmDen q M : ℚ) * q k
  | _ => 0

/-- Which rows belong to `LP(A)`. -/
def lpActive (A : Finset ι) : LPRow ι → Bool
  | .inr (.inl k) => decide (k ∈ A)
  | .inr (.inr (.inr (.inl k))) => decide (k ∉ A)
  | _ => true

/-- `(z, ρ)` as one vector. -/
def zρ (z : ι → ℚ) (ρ : ℚ) : ι ⊕ Unit → ℚ := Sum.elim z (fun _ => ρ)

theorem zρ_eta (y : ι ⊕ Unit → ℚ) : zρ (fun k => y (.inl k)) (y (.inr ())) = y := by
  ext (k | u) <;> rfl

theorem lp_dot1 (k : ι) (z : ι → ℚ) (ρ : ℚ) :
    lpCoef q M (.inl k) ⬝ᵥ zρ z ρ = (lcmDen q M : ℚ) * (slack q M z k - q k) +
      (lcmDen q M : ℚ) * ρ := by
  simp [lpCoef, zρ, dotProduct, Fintype.sum_sum_type, slack, mulVec, mul_sum, mul_assoc]

theorem lp_dot2 (k : ι) (z : ι → ℚ) (ρ : ℚ) :
    lpCoef q M (.inr (.inl k)) ⬝ᵥ zρ z ρ = -((lcmDen q M : ℚ) * (slack q M z k - q k)) +
      (lcmDen q M : ℚ) * ρ := by
  simp [lpCoef, zρ, dotProduct, Fintype.sum_sum_type, slack, mulVec, mul_sum, mul_assoc]

theorem lp_dot3 (k : ι) (z : ι → ℚ) (ρ : ℚ) : lpCoef q M (.inr (.inr (.inl k))) ⬝ᵥ zρ z ρ = z k := by
  simp [lpCoef, zρ, dotProduct, Fintype.sum_sum_type]

theorem lp_dot4 (k : ι) (z : ι → ℚ) (ρ : ℚ) :
    lpCoef q M (.inr (.inr (.inr (.inl k)))) ⬝ᵥ zρ z ρ = -z k := by
  simp [lpCoef, zρ, dotProduct, Fintype.sum_sum_type]

theorem lp_dot5 (z : ι → ℚ) (ρ : ℚ) : lpCoef q M (.inr (.inr (.inr (.inr ())))) ⬝ᵥ zρ z ρ = ρ := by
  simp [lpCoef, zρ, dotProduct, Fintype.sum_sum_type]

theorem lcmDen_pos : 0 < lcmDen q M := by
  unfold lcmDen
  apply Nat.lcm_pos
  · apply Nat.pos_of_ne_zero
    rw [Ne, Finset.lcm_eq_zero_iff]; simp [Rat.den_ne_zero]
  · apply Nat.pos_of_ne_zero
    rw [Ne, Finset.lcm_eq_zero_iff]; simp [Rat.den_ne_zero]

theorem lcmDen_le_cC : lcmDen q M ≤ cC q M := le_max_left _ _

theorem one_le_cC : 1 ≤ cC q M := le_trans (lcmDen_pos q M) (lcmDen_le_cC q M)

/-- The rows of `LP(A)` are exactly the active rows. -/
theorem lp_feas_iff (A : Finset ι) (z : ι → ℚ) (ρ : ℚ) :
    IsLPFeasible q M A z ρ ↔
      ∀ r : {r : LPRow ι // lpActive A r = true}, lpRhs q M r.1 ≤ lpCoef q M r.1 ⬝ᵥ zρ z ρ := by
  have hD : (0 : ℚ) < lcmDen q M := by exact_mod_cast lcmDen_pos q M
  constructor
  · rintro ⟨h1, h2, h3, h4, h5⟩ ⟨r, hr⟩
    rcases r with k | k | k | k | u
    · rw [lp_dot1]; simp only [lpRhs]; nlinarith [h4 k]
    · have hk : k ∈ A := by simpa [lpActive] using hr
      rw [lp_dot2]; simp only [lpRhs]; nlinarith [h5 k hk]
    · rw [lp_dot3]; exact h1 k
    · have hk : k ∉ A := by simpa [lpActive] using hr
      rw [lp_dot4]; simp only [lpRhs]; rw [h3 k hk]; simp
    · rw [lp_dot5]; exact h2
  · intro h
    refine ⟨fun k => ?_, ?_, fun k hk => ?_, fun k => ?_, fun k hk => ?_⟩
    · have := h ⟨.inr (.inr (.inl k)), rfl⟩; rwa [lp_dot3] at this
    · have := h ⟨.inr (.inr (.inr (.inr ()))), rfl⟩; rwa [lp_dot5] at this
    · have a1 := h ⟨.inr (.inr (.inl k)), rfl⟩
      have a2 := h ⟨.inr (.inr (.inr (.inl k))), by simp [lpActive, hk]⟩
      rw [lp_dot3] at a1; rw [lp_dot4] at a2; simp only [lpRhs] at a1 a2; linarith
    · have := h ⟨.inl k, rfl⟩; rw [lp_dot1] at this; simp only [lpRhs] at this
      have : 0 ≤ (lcmDen q M : ℚ) * (slack q M z k + ρ) := by linarith
      have := (mul_nonneg_iff_of_pos_left hD).mp this; linarith
    · have := h ⟨.inr (.inl k), by simp [lpActive, hk]⟩; rw [lp_dot2] at this
      simp only [lpRhs] at this
      have : 0 ≤ (lcmDen q M : ℚ) * (ρ - slack q M z k) := by linarith
      have := (mul_nonneg_iff_of_pos_left hD).mp this; linarith

/-- A cleared entry `D x` (with `den x ∣ D`) is an integer bounded by `C` if its numerator is. -/
theorem cleared (x : ℚ) (hden : x.den ∣ lcmDen q M)
    (hle : ((lcmDen q M : ℚ) * x).num.natAbs ≤ cC q M) :
    ∃ m : ℤ, (lcmDen q M : ℚ) * x = m ∧ |m| ≤ (cC q M : ℕ) := by
  obtain ⟨m, hm⟩ := int_of_den_dvd x _ hden
  refine ⟨m, hm, ?_⟩
  rw [hm, Rat.num_intCast] at hle
  rw [← Int.natCast_natAbs]; exact_mod_cast hle

theorem M_int (k l : ι) : ∃ m : ℤ, (lcmDen q M : ℚ) * M k l = m ∧ |m| ≤ (cC q M : ℕ) := by
  refine cleared q M _ ((Finset.dvd_lcm (mem_univ (k, l))).trans (Nat.dvd_lcm_left _ _)) ?_
  refine le_trans ?_ (le_max_right _ _)
  exact le_trans (Finset.le_sup (f := fun p : ι × ι => ((lcmDen q M : ℚ) * M p.1 p.2).num.natAbs)
    (mem_univ (k, l))) le_sup_left

theorem q_int (k : ι) : ∃ m : ℤ, (lcmDen q M : ℚ) * q k = m ∧ |m| ≤ (cC q M : ℕ) := by
  refine cleared q M _ ((Finset.dvd_lcm (mem_univ k)).trans (Nat.dvd_lcm_right _ _)) ?_
  refine le_trans ?_ (le_max_right _ _)
  exact le_trans (Finset.le_sup (f := fun k => ((lcmDen q M : ℚ) * q k).num.natAbs)
    (mem_univ k)) le_sup_right

theorem small_int (x : ℤ) (hx : |x| ≤ 1) : ∃ m : ℤ, (x : ℚ) = m ∧ |m| ≤ (cC q M : ℕ) :=
  ⟨x, rfl, le_trans hx (by exact_mod_cast one_le_cC q M)⟩

theorem D_int : ∃ m : ℤ, (lcmDen q M : ℚ) = m ∧ |m| ≤ (cC q M : ℕ) :=
  ⟨lcmDen q M, by simp, by simp only [Nat.abs_cast]; exact_mod_cast lcmDen_le_cC q M⟩

theorem lpCoef_int (r : LPRow ι) (c : ι ⊕ Unit) :
    ∃ m : ℤ, lpCoef q M r c = m ∧ |m| ≤ (cC q M : ℕ) := by
  rcases r with k | k | k | k | u <;> rcases c with l | v
  · exact M_int q M k l
  · exact D_int q M
  · obtain ⟨m, hm, hb⟩ := M_int q M k l
    exact ⟨-m, by simp [lpCoef, hm], by rwa [abs_neg]⟩
  · exact D_int q M
  · simp only [lpCoef, Sum.elim_inl]
    split_ifs
    · exact ⟨1, by simp, by simpa using one_le_cC q M⟩
    · exact ⟨0, by simp, by simp⟩
  · exact ⟨0, by simp [lpCoef], by simp⟩
  · simp only [lpCoef, Sum.elim_inl]
    split_ifs
    · exact ⟨-1, by simp, by simpa using one_le_cC q M⟩
    · exact ⟨0, by simp, by simp⟩
  · exact ⟨0, by simp [lpCoef], by simp⟩
  · exact ⟨0, by simp [lpCoef], by simp⟩
  · exact ⟨1, by simp [lpCoef], by simpa using one_le_cC q M⟩

theorem lpRhs_int (r : LPRow ι) : ∃ m : ℤ, lpRhs q M r = m ∧ |m| ≤ (cC q M : ℕ) := by
  rcases r with k | k | k | k | u
  · obtain ⟨m, hm, hb⟩ := q_int q M k
    exact ⟨-m, by simp [lpRhs, hm], by rwa [abs_neg]⟩
  · exact q_int q M k
  · exact ⟨0, by simp [lpRhs], by simp⟩
  · exact ⟨0, by simp [lpRhs], by simp⟩
  · exact ⟨0, by simp [lpRhs], by simp⟩

theorem lp_zero_feasible (A : Finset ι) :
    IsLPFeasible q M A 0 (∑ k, |q k|) := by
  have hs : slack q M 0 = q := by simp [slack]
  have hle : ∀ k, |q k| ≤ ∑ k, |q k| := fun k =>
    single_le_sum (f := fun k => |q k|) (fun _ _ => abs_nonneg _) (mem_univ k)
  refine ⟨fun _ => le_rfl, sum_nonneg fun _ _ => abs_nonneg _, fun _ _ => rfl, fun k => ?_,
    fun k _ => ?_⟩
  · rw [hs]; linarith [neg_abs_le (q k), hle k]
  · rw [hs]; exact le_trans (le_abs_self _) (hle k)

/-- A vertex below any feasible point: its `ρ` is `p / q'` with `0 < |q'| ≤ d! C^d`. -/
theorem lp_vertex (A : Finset ι) (y : ι ⊕ Unit → ℚ)
    (hy : ∀ r : {r : LPRow ι // lpActive A r = true}, lpRhs q M r.1 ≤ lpCoef q M r.1 ⬝ᵥ y) :
    ∃ y', (∀ r : {r : LPRow ι // lpActive A r = true}, lpRhs q M r.1 ≤ lpCoef q M r.1 ⬝ᵥ y') ∧
      y' (.inr ()) ≤ y (.inr ()) ∧ ∃ p q' : ℤ, q' ≠ 0 ∧
        |q'| ≤ ((dimd ι).factorial * cC q M ^ dimd ι : ℕ) ∧ y' (.inr ()) = p / q' := by
  classical
  have hrow : ∀ (r : LPRow ι) (hr : lpActive A r = true) (d : ι ⊕ Unit → ℚ),
      (∀ r : {r : LPRow ι // lpActive A r = true}, 0 ≤ lpCoef q M r.1 ⬝ᵥ d) →
      0 ≤ lpCoef q M r ⬝ᵥ zρ (fun k => d (.inl k)) (d (.inr ())) := fun r hr d h => by
    rw [zρ_eta]; exact h ⟨r, hr⟩
  have hlin : ∀ d : ι ⊕ Unit → ℚ,
      (∀ r : {r : LPRow ι // lpActive A r = true}, 0 ≤ lpCoef q M r.1 ⬝ᵥ d) →
      (∀ r : {r : LPRow ι // lpActive A r = true}, 0 ≤ lpCoef q M r.1 ⬝ᵥ (-d)) → d = 0 := by
    intro d h1 h2
    ext (k | u)
    · have a1 := hrow (.inr (.inr (.inl k))) rfl d h1
      have a2 := hrow (.inr (.inr (.inl k))) rfl (-d) h2
      rw [lp_dot3] at a1 a2; simp only [Pi.neg_apply] at a2; simp only [Pi.zero_apply]; linarith
    · have a1 := hrow (.inr (.inr (.inr (.inr ())))) rfl d h1
      have a2 := hrow (.inr (.inr (.inr (.inr ())))) rfl (-d) h2
      rw [lp_dot5] at a1 a2; simp only [Pi.neg_apply] at a2; simp only [Pi.zero_apply]; linarith
  have hc : ∀ d : ι ⊕ Unit → ℚ,
      (∀ r : {r : LPRow ι // lpActive A r = true}, 0 ≤ lpCoef q M r.1 ⬝ᵥ d) →
      0 ≤ Pi.single (.inr ()) 1 ⬝ᵥ d := by
    intro d h
    have a1 := hrow (.inr (.inr (.inr (.inr ())))) rfl d h
    rw [lp_dot5] at a1; simpa [single_dotProduct] using a1
  obtain ⟨y', hf, hcy, htop⟩ := exists_vertex_pointed
    (fun r : {r : LPRow ι // lpActive A r = true} => lpCoef q M r.1)
    (fun r => lpRhs q M r.1) hlin (Pi.single (.inr ()) 1) hc _ y hy rfl
  simp only [single_dotProduct, one_mul] at hcy
  obtain ⟨p, q', hq, hqle, hval⟩ := vertex_value
    (fun r : {r : LPRow ι // lpActive A r = true} => lpCoef q M r.1)
    (fun r => lpRhs q M r.1) (cC q M) (fun r c => lpCoef_int q M r.1 c)
    (fun r => lpRhs_int q M r.1) y' htop (.inr ())
  refine ⟨y', hf, hcy, p, q', hq, ?_, hval⟩
  have hcard : Fintype.card (ι ⊕ Unit) = dimd ι := by simp [dimd]
  rw [hcard] at hqle
  exact_mod_cast hqle

/-- [PL Lemma plcp:lem:gap], generic. -/
theorem gap_lemma (A : Finset ι) :
    ∃ z₀ ρ₀, IsLPFeasible q M A z₀ ρ₀ ∧ (∀ z ρ, IsLPFeasible q M A z ρ → ρ₀ ≤ ρ) ∧
      (ρ₀ = 0 ∨ 1 / ((dimd ι * cC q M : ℕ) : ℚ) ^ dimd ι ≤ ρ₀) := by
  classical
  set R : ℚ := ∑ k, |q k| with hR
  set QN : ℕ := (dimd ι).factorial * cC q M ^ dimd ι with hQN
  set QZ : ℤ := (QN : ℤ) with hQZ
  set BZ : ℤ := ⌈R⌉ * QZ with hBZ
  set Cand : Finset ℚ :=
    ((Icc (-BZ) BZ) ×ˢ (Icc (-QZ) QZ)).image (fun pq : ℤ × ℤ => (pq.1 : ℚ) / pq.2) with hCand
  have hR0 : 0 ≤ R := sum_nonneg fun _ _ => abs_nonneg _
  have key : ∀ y : ι ⊕ Unit → ℚ,
      (∀ r : {r : LPRow ι // lpActive A r = true}, lpRhs q M r.1 ≤ lpCoef q M r.1 ⬝ᵥ y) →
      y (.inr ()) ≤ R →
      ∃ y', (∀ r : {r : LPRow ι // lpActive A r = true}, lpRhs q M r.1 ≤ lpCoef q M r.1 ⬝ᵥ y') ∧
        y' (.inr ()) ≤ y (.inr ()) ∧ y' (.inr ()) ∈ Cand := by
    intro y hy hyR
    obtain ⟨y', hy', hle, p, q', hq, hqle, hv⟩ := lp_vertex q M A y hy
    have hfe : IsLPFeasible q M A (fun k => y' (.inl k)) (y' (.inr ())) :=
      (lp_feas_iff q M A _ _).mpr (by rw [zρ_eta]; exact hy')
    have h0 : 0 ≤ y' (.inr ()) := hfe.2.1
    have hq0 : (q' : ℚ) ≠ 0 := by exact_mod_cast hq
    have hp : (p : ℚ) = y' (.inr ()) * q' := by rw [hv]; field_simp
    have hqQ : |(q' : ℚ)| ≤ (QZ : ℚ) := by rw [hQZ]; exact_mod_cast hqle
    have hpB : |(p : ℚ)| ≤ (BZ : ℚ) := by
      rw [hp, abs_mul, abs_of_nonneg h0, hBZ]; push_cast
      have hQ0 : (0 : ℚ) ≤ QZ := le_trans (abs_nonneg _) hqQ
      calc y' (.inr ()) * |(q' : ℚ)| ≤ R * QZ := by
            apply mul_le_mul (by linarith) hqQ (abs_nonneg _) hR0
        _ ≤ (⌈R⌉ : ℚ) * QZ := mul_le_mul_of_nonneg_right (Int.le_ceil R) hQ0
    have hpB' : |p| ≤ BZ := by exact_mod_cast hpB
    have hqQ' : |q'| ≤ QZ := by exact_mod_cast hqQ
    exact ⟨y', hy', hle, mem_image.mpr ⟨(p, q'),
      mem_product.mpr ⟨mem_Icc.mpr (abs_le.mp hpB'), mem_Icc.mpr (abs_le.mp hqQ')⟩, hv.symm⟩⟩
  set Vals := Cand.filter (fun v => ∃ y : ι ⊕ Unit → ℚ,
    (∀ r : {r : LPRow ι // lpActive A r = true}, lpRhs q M r.1 ≤ lpCoef q M r.1 ⬝ᵥ y) ∧
      y (.inr ()) = v) with hVals
  have hstart := (lp_feas_iff q M A 0 R).mp (lp_zero_feasible q M A)
  obtain ⟨y1, hy1, hy1R, hc1⟩ := key _ hstart le_rfl
  have hne : Vals.Nonempty := ⟨_, mem_filter.mpr ⟨hc1, y1, hy1, rfl⟩⟩
  obtain ⟨hcand, y₀, hy₀, hy₀ρ⟩ := mem_filter.mp (Vals.min'_mem hne)
  have hfe0 : IsLPFeasible q M A (fun k => y₀ (.inl k)) (y₀ (.inr ())) :=
    (lp_feas_iff q M A _ _).mpr (by rw [zρ_eta]; exact hy₀)
  have hminR : Vals.min' hne ≤ R :=
    le_trans (Vals.min'_le _ (mem_filter.mpr ⟨hc1, y1, hy1, rfl⟩)) hy1R
  refine ⟨fun k => y₀ (.inl k), Vals.min' hne, by rw [← hy₀ρ]; exact hfe0, ?_, ?_⟩
  · intro z ρ h
    by_cases hρ : ρ ≤ R
    · obtain ⟨y', hy', hle, hc'⟩ := key _ ((lp_feas_iff q M A z ρ).mp h) hρ
      have h1 : Vals.min' hne ≤ y' (.inr ()) :=
        Vals.min'_le _ (mem_filter.mpr ⟨hc', y', hy', rfl⟩)
      have h2 : zρ z ρ (.inr ()) = ρ := rfl
      linarith
    · linarith [not_le.mp hρ]
  · have h0 : 0 ≤ Vals.min' hne := hy₀ρ ▸ hfe0.2.1
    rcases h0.lt_or_eq with hpos | hzero
    · right
      obtain ⟨⟨p, q'⟩, hpq, hval⟩ := mem_image.mp hcand
      simp only [mem_product, mem_Icc] at hpq
      simp only at hval
      have hq0 : (q' : ℚ) ≠ 0 := by intro h; rw [h, div_zero] at hval; linarith
      have hp0 : p ≠ 0 := by intro h; rw [h, Int.cast_zero, zero_div] at hval; linarith
      have habs : Vals.min' hne = |(p : ℚ)| / |(q' : ℚ)| := by
        rw [← abs_div, hval, abs_of_pos hpos]
      have hp1 : (1 : ℚ) ≤ |(p : ℚ)| := by
        have : (1 : ℤ) ≤ |p| := Int.one_le_abs hp0
        exact_mod_cast this
      have hqQ : |(q' : ℚ)| ≤ (QN : ℚ) := by
        have : |q'| ≤ QZ := abs_le.mpr hpq.2
        rw [hQZ] at this; exact_mod_cast this
      have hNat : QN ≤ (dimd ι * cC q M) ^ dimd ι := by
        rw [hQN, mul_pow]; exact Nat.mul_le_mul_right _ (Nat.factorial_le_pow _)
      have hQle : (QN : ℚ) ≤ ((dimd ι * cC q M : ℕ) : ℚ) ^ dimd ι := by exact_mod_cast hNat
      have hq1 : 0 < |(q' : ℚ)| := abs_pos.mpr hq0
      have hdC : 0 < dimd ι * cC q M := Nat.mul_pos (Nat.succ_pos _) (one_le_cC q M)
      have hpow : (0 : ℚ) < ((dimd ι * cC q M : ℕ) : ℚ) ^ dimd ι := by positivity
      rw [habs, div_le_div_iff₀ hpow hq1]
      nlinarith
    · left; exact hzero.symm

/-- Every feasible point of `(∗)` solves `LCP(q, M)`. -/
theorem star_sol (A : Finset ι) (z : ι → ℚ) (h : IsStarFeasible q M A z) : IsLCPSol q M z := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨h1, h3, fun k => ?_⟩
  by_cases hk : k ∈ A
  · rw [h4 k hk, mul_zero]
  · rw [h2 k hk, zero_mul]

/-- A feasible point of `LP(A)` with `ρ = 0` is a feasible point of `(∗)`. -/
theorem star_of_lp_zero (A : Finset ι) (z : ι → ℚ) (h : IsLPFeasible q M A z 0) :
    IsStarFeasible q M A z := by
  obtain ⟨h1, -, h3, h4, h5⟩ := h
  refine ⟨h1, h3, fun k => by simpa using h4 k, fun k hk => ?_⟩
  have := h4 k; have := h5 k hk; linarith

end GapGeneric

/-! ## 4b. `C` agrees with the book's formula -/

section BookC

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (q : ι → ℚ) (M : Matrix ι ι ℚ)

theorem natAbs_cleared (x : ℚ) (hden : x.den ∣ lcmDen q M) :
    ((((lcmDen q M : ℚ) * x).num.natAbs : ℕ) : ℚ) = (lcmDen q M : ℚ) * |x| := by
  obtain ⟨m, hm⟩ := int_of_den_dvd x _ hden
  rw [hm, Rat.num_intCast, Nat.cast_natAbs, Int.cast_abs, ← hm, abs_mul, Nat.abs_cast]

theorem M_den (k l : ι) : (M k l).den ∣ lcmDen q M :=
  (Finset.dvd_lcm (mem_univ (k, l))).trans (Nat.dvd_lcm_left _ _)

theorem q_den (k : ι) : (q k).den ∣ lcmDen q M :=
  (Finset.dvd_lcm (mem_univ k)).trans (Nat.dvd_lcm_right _ _)

theorem cast_sup_le {α : Type*} (s : Finset α) (g : α → ℕ) (B : ℚ) (hB : 0 ≤ B)
    (h : ∀ a ∈ s, (g a : ℚ) ≤ B) : ((s.sup g : ℕ) : ℚ) ≤ B := by
  refine Finset.sup_induction (p := fun n : ℕ => (n : ℚ) ≤ B) (by simpa using hB) ?_ h
  intro a ha b hb
  rcases le_total a b with hab | hab
  · rw [sup_of_le_right hab]; exact hb
  · rw [sup_of_le_left hab]; exact ha

/-- `C = D · max(1, max_{kl} |M_kl|, max_k |q_k|)`, the book's formula. -/
theorem cC_eq : (cC q M : ℚ) = (lcmDen q M : ℚ) *
    max 1 (max (univ.fold max 0 fun p : ι × ι => |M p.1 p.2|) (univ.fold max 0 fun k => |q k|)) := by
  have hD : (0 : ℚ) < lcmDen q M := by exact_mod_cast lcmDen_pos q M
  set F1 := univ.fold max 0 fun p : ι × ι => |M p.1 p.2|
  set F2 := univ.fold max 0 fun k => |q k|
  have hF1 : 0 ≤ F1 := (Finset.le_fold_max _).mpr (Or.inl le_rfl)
  have hF2 : 0 ≤ F2 := (Finset.le_fold_max _).mpr (Or.inl le_rfl)
  set B := (lcmDen q M : ℚ) * max 1 (max F1 F2)
  have hB0 : 0 ≤ B := by positivity
  apply le_antisymm
  · unfold cC
    rw [Nat.cast_max]
    refine max_le (le_mul_of_one_le_right hD.le (le_max_left _ _)) ?_
    rcases le_total (univ.sup fun p : ι × ι => ((lcmDen q M : ℚ) * M p.1 p.2).num.natAbs)
      (univ.sup fun k => ((lcmDen q M : ℚ) * q k).num.natAbs) with h | h
    · rw [sup_of_le_right h]
      refine cast_sup_le _ _ _ hB0 fun k _ => ?_
      rw [natAbs_cleared q M _ (q_den q M k)]
      refine mul_le_mul_of_nonneg_left ?_ hD.le
      exact le_trans ((Finset.le_fold_max _).mpr (Or.inr ⟨k, mem_univ _, le_rfl⟩))
        (le_trans (le_max_right _ _) (le_max_right _ _))
    · rw [sup_of_le_left h]
      refine cast_sup_le _ _ _ hB0 fun p _ => ?_
      rw [natAbs_cleared q M _ (M_den q M p.1 p.2)]
      refine mul_le_mul_of_nonneg_left ?_ hD.le
      exact le_trans ((Finset.le_fold_max _).mpr (Or.inr ⟨p, mem_univ _, le_rfl⟩))
        (le_trans (le_max_left _ _) (le_max_right _ _))
  · have hC1 : ((univ.sup fun p : ι × ι => ((lcmDen q M : ℚ) * M p.1 p.2).num.natAbs : ℕ) : ℚ) ≤
        cC q M := by exact_mod_cast le_trans le_sup_left (le_max_right _ _)
    have hC2 : ((univ.sup fun k => ((lcmDen q M : ℚ) * q k).num.natAbs : ℕ) : ℚ) ≤ cC q M := by
      exact_mod_cast le_trans le_sup_right (le_max_right _ _)
    have hCD : (lcmDen q M : ℚ) ≤ cC q M := by exact_mod_cast lcmDen_le_cC q M
    have hC0 : (0 : ℚ) ≤ cC q M / lcmDen q M := by positivity
    simp only [B]
    rw [mul_max_of_nonneg _ _ hD.le, mul_max_of_nonneg _ _ hD.le, mul_one]
    refine max_le hCD (max_le ?_ ?_)
    · rw [← le_div_iff₀' hD]
      refine (Finset.fold_max_le _).mpr ⟨hC0, fun p _ => ?_⟩
      rw [le_div_iff₀' hD, ← natAbs_cleared q M _ (M_den q M p.1 p.2)]
      exact le_trans (by exact_mod_cast Finset.le_sup (f := fun p : ι × ι =>
        ((lcmDen q M : ℚ) * M p.1 p.2).num.natAbs) (mem_univ p)) hC1
    · rw [← le_div_iff₀' hD]
      refine (Finset.fold_max_le _).mpr ⟨hC0, fun k _ => ?_⟩
      rw [le_div_iff₀' hD, ← natAbs_cleared q M _ (q_den q M k)]
      exact le_trans (by exact_mod_cast Finset.le_sup (f := fun k =>
        ((lcmDen q M : ℚ) * q k).num.natAbs) (mem_univ k)) hC2

end BookC

/-! ## 5. The main theorem -/

section Main

variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
variable (Mk : Market I J)

theorem one_le_dC : (1 : ℚ) ≤ ((md Mk * mC Mk : ℕ) : ℚ) := by
  have : 1 ≤ md Mk * mC Mk := Nat.mul_pos (Nat.succ_pos _) (one_le_cC _ _)
  exact_mod_cast this

theorem one_le_Q : (1 : ℚ) ≤ ((md Mk * mC Mk : ℕ) : ℚ) ^ md Mk := one_le_pow₀ (one_le_dC Mk)

theorem one_le_ceilZ : (1 : ℚ) ≤ (⌈Zbar Mk⌉ : ℚ) := by
  have : (1 : ℤ) ≤ ⌈Zbar Mk⌉ := Int.one_le_ceil_iff.mpr (by linarith [one_le_Zbar Mk])
  exact_mod_cast this

theorem eps_pos : 0 < eps Mk := by
  unfold eps
  have := one_le_Q Mk; have := one_le_ceilZ Mk
  positivity

theorem eps_le_one : eps Mk ≤ 1 := by
  unfold eps
  have := one_le_Q Mk; have := one_le_ceilZ Mk
  rw [div_le_one (by positivity)]
  nlinarith

/-- `ε Z̄ ≤ 1 / (2 (dC)^d) < (dC)^{−d}`. -/
theorem eps_mul_Zbar_lt : eps Mk * Zbar Mk < 1 / ((md Mk * mC Mk : ℕ) : ℚ) ^ md Mk := by
  unfold eps
  have hQ := one_le_Q Mk; have hc := one_le_ceilZ Mk
  have hZ : Zbar Mk ≤ (⌈Zbar Mk⌉ : ℚ) := Int.le_ceil _
  set Q := ((md Mk * mC Mk : ℕ) : ℚ) ^ md Mk
  set c := (⌈Zbar Mk⌉ : ℚ)
  rw [div_mul_eq_mul_div, one_mul, div_lt_div_iff₀ (by positivity) (by positivity)]
  nlinarith

/-- [PL Thm. plcp:thm:main]. -/
theorem main_theorem (hwf : Mk.WellFormed) :
    IsPMatrix (lcpMeps Mk (eps Mk)) ∧ 0 < eps Mk ∧ eps Mk ≤ 1 ∧
    (∀ z z', IsLCPSol (lcpq Mk) (lcpMeps Mk (eps Mk)) z →
      IsLCPSol (lcpq Mk) (lcpMeps Mk (eps Mk)) z' → z = z') ∧
    ∀ zε : Idx Mk → ℚ, IsLCPSol (lcpq Mk) (lcpMeps Mk (eps Mk)) zε →
      (∃ z, IsStarFeasible (lcpq Mk) (lcpM Mk) (support zε) z) ∧
      ∀ z, IsStarFeasible (lcpq Mk) (lcpM Mk) (support zε) z →
        IsLCPSol (lcpq Mk) (lcpM Mk) z ∧ Mk.IsEquilibrium (zP Mk z) (zu Mk z) (zf Mk z) := by
  have hb := b_nonneg Mk hwf
  have hε := eps_pos Mk
  obtain ⟨hP, -, huniq⟩ := pmatrix Mk hb (eps Mk) hε
  refine ⟨hP, hε, eps_le_one Mk, fun z z' => huniq _ z z', fun zε hzε => ⟨?_, fun z hz => ?_⟩⟩
  · -- feasibility of `(∗)` via the gap lemma
    have hbd := uniform_bound Mk hwf (eps Mk) hε (eps_le_one Mk) zε hzε
    obtain ⟨hz0, hw0, hc⟩ := hzε
    have hLP : IsLPFeasible (lcpq Mk) (lcpM Mk) (support zε) zε (eps Mk * Zbar Mk) := by
      refine ⟨hz0, by nlinarith [one_le_Zbar Mk], fun k hk => ?_, fun k => ?_, fun k hk => ?_⟩
      · have : ¬ 0 < zε k := by simpa [support] using hk
        exact le_antisymm (not_lt.mp this) (hz0 k)
      · have := hw0 k; rw [slack_eps] at this
        have := (hbd k).2
        nlinarith
      · have hpos : 0 < zε k := by simpa [support] using hk
        have := zero_of_compl (hc k) hpos; rw [slack_eps] at this
        nlinarith [one_le_Zbar Mk]
    obtain ⟨z₀, ρ₀, h0, hmin, hgap⟩ := gap_lemma (lcpq Mk) (lcpM Mk) (support zε)
    have hle := hmin _ _ hLP
    have hlt := eps_mul_Zbar_lt Mk
    have hρ0 : ρ₀ = 0 := by
      rcases hgap with h | h
      · exact h
      · exfalso
        have : 1 / ((md Mk * mC Mk : ℕ) : ℚ) ^ md Mk ≤ eps Mk * Zbar Mk := le_trans h hle
        unfold md mC at hlt this
        linarith
    rw [hρ0] at h0
    exact ⟨z₀, star_of_lp_zero _ _ _ _ h0⟩
  · have := star_sol _ _ _ _ hz
    exact ⟨this, sol_to_eq Mk z this⟩

end Main

/-! ## 6. The statements of `Statements.lean` -/

section Final

variable (I J : Type*) [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

theorem slackTable_proof : SlackTable I J := fun Mk z => slack_eq_table Mk z

theorem formulationSolEq_proof : FormulationSolEq I J := fun Mk z hz => sol_to_eq Mk z hz

theorem formulationEqSol_proof : FormulationEqSol I J := fun Mk P v f h =>
  ⟨eq_to_sol Mk P v f h, rfl, rfl, fun e he => zf_encode Mk P v f e he⟩

theorem formulation_proof : Formulation I J := by
  intro Mk z
  refine ⟨⟨sol_to_eq Mk z, fun h => ?_⟩, encode_decode Mk z⟩
  have := eq_to_sol Mk _ _ _ h
  rwa [encode_decode] at this

theorem p0_proof : P0 I J := fun Mk hb => lcpM_isP0 Mk hb

theorem pMatrix_proof : PMatrix I J := fun Mk hb ε hε => pmatrix Mk hb ε hε

theorem uniformBound_proof : UniformBound I J := fun Mk hwf ε h0 h1 z hz =>
  uniform_bound Mk hwf ε h0 h1 z hz

theorem main_proof : MainTheorem I J := fun Mk hwf => main_theorem Mk hwf

variable (ι : Type*) [Fintype ι] [DecidableEq ι]

theorem gap_proof : Gap ι := fun q M A => gap_lemma q M A

theorem starSol_proof : StarSol ι := fun q M A z h => star_sol q M A z h

end Final


/-! ## 7. Example plcp:ex:negative (`ε = 1` fails, small `ε` works) -/

section Example

theorem ex_edge_eq (e : Edge exMarket) : e = exEdge := Subsingleton.elim _ _

theorem ex_sl_f (z : Idx exMarket → ℚ) (e : Edge exMarket) :
    slack (lcpq exMarket) (lcpM exMarket) z (.inl e) = z (Idx.u ()) + z (Idx.P ()) - 1 := by
  rw [sl_f]; simp [exMarket]

theorem ex_sl_u (z : Idx exMarket → ℚ) :
    slack (lcpq exMarket) (lcpM exMarket) z (Idx.u ()) = 1 - z (.inl exEdge) := by
  rw [sl_u, ← zf_edge exMarket z exEdge]; simp [Market.rowSum, exMarket, exEdge]

theorem ex_sl_P (z : Idx exMarket → ℚ) :
    slack (lcpq exMarket) (lcpM exMarket) z (Idx.P ()) = 2 - z (.inl exEdge) := by
  rw [sl_P, ← zf_edge exMarket z exEdge]; simp [Market.colSum, exMarket, exEdge]

theorem exZ_sol (ε f u P : ℚ) :
    IsLCPSol (lcpq exMarket) (lcpMeps exMarket ε) (exZ f u P) ↔
      (0 ≤ f ∧ 0 ≤ u ∧ 0 ≤ P) ∧ (0 ≤ u + P - 1 + ε * f ∧ 0 ≤ 1 - f + ε * u ∧ 0 ≤ 2 - f + ε * P) ∧
        (f * (u + P - 1 + ε * f) = 0 ∧ u * (1 - f + ε * u) = 0 ∧ P * (2 - f + ε * P) = 0) := by
  unfold IsLCPSol
  simp only [slack_eps]
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨⟨h1 (.inl exEdge), h1 (Idx.u ()), h1 (Idx.P ())⟩,
      ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩
    · have := h2 (.inl exEdge); rwa [ex_sl_f] at this
    · have := h2 (Idx.u ()); rwa [ex_sl_u] at this
    · have := h2 (Idx.P ()); rwa [ex_sl_P] at this
    · have := h3 (.inl exEdge); rwa [ex_sl_f] at this
    · have := h3 (Idx.u ()); rwa [ex_sl_u] at this
    · have := h3 (Idx.P ()); rwa [ex_sl_P] at this
  · rintro ⟨⟨a1, a2, a3⟩, ⟨b1, b2, b3⟩, ⟨c1, c2, c3⟩⟩
    have hf : ∀ e : Edge exMarket, exZ f u P (.inl e) = f := fun _ => rfl
    have hu : exZ f u P (Idx.u ()) = u := rfl
    have hP : exZ f u P (Idx.P ()) = P := rfl
    have hfe : exZ f u P (.inl exEdge) = f := rfl
    refine ⟨?_, ?_, ?_⟩ <;> rintro (e | ⟨⟩ | ⟨⟩)
    · exact a1
    · exact a2
    · exact a3
    · rw [ex_sl_f, hu, hP, hf]; exact b1
    · rw [ex_sl_u, hu, hfe]; exact b2
    · rw [ex_sl_P, hP, hfe]; exact b3
    · rw [ex_sl_f, hu, hP, hf]; exact c1
    · rw [ex_sl_u, hu, hfe]; exact c2
    · rw [ex_sl_P, hP, hfe]; exact c3

/-- At `ε = 1`, `(f, u, P) = (1, 0, 0)` solves `LCP(q, M + I)`. -/
theorem ex_one_sol : IsLCPSol (lcpq exMarket) (lcpMeps exMarket 1) (exZ 1 0 0) := by
  rw [exZ_sol]; norm_num

/-- ... and it is the only solution. -/
theorem ex_one_unique (z : Idx exMarket → ℚ) (hz : IsLCPSol (lcpq exMarket) (lcpMeps exMarket 1) z) :
    z = exZ 1 0 0 :=
  (pmatrix exMarket (fun _ _ => zero_le_one) 1 one_pos).2.2 _ _ _ hz ex_one_sol

theorem ex_one_support : support (exZ 1 0 0) = {.inl exEdge} := by
  ext (e | ⟨⟩ | ⟨⟩) <;> simp [support, exZ, ex_edge_eq]

/-- At `ε = 1` the system `(∗)` for the support `{f}` is infeasible. -/
theorem ex_one_star_infeasible :
    ¬ ∃ z, IsStarFeasible (lcpq exMarket) (lcpM exMarket) (support (exZ 1 0 0)) z := by
  rintro ⟨z, -, h2, h3, -⟩
  rw [ex_one_support] at h2
  have hu := h2 (Idx.u ()) (by simp)
  have hP := h2 (Idx.P ()) (by simp)
  have := h3 (.inl exEdge)
  rw [ex_sl_f, hu, hP] at this
  norm_num at this

/-- `(P, v, f) = (0, 1, 1)` is an equilibrium of the example ... -/
theorem ex_eq : exMarket.IsEquilibrium (fun _ => 0) (fun _ => 1) (fun _ => 1) := by
  refine ⟨fun _ => le_rfl, fun _ => zero_le_one, fun _ _ => zero_le_one, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    intros <;> simp_all [exMarket, Market.rowSum, Market.colSum]

/-- ... and the only one. -/
theorem ex_eq_unique (P : Unit → ℚ) (v : Unit → ℚ) (f : Unit × Unit → ℚ)
    (h : exMarket.IsEquilibrium P v f) : P () = 0 ∧ v () = 1 ∧ f ((), ()) = 1 := by
  have he : ((), ()) ∈ exMarket.E := mem_singleton_self _
  have hrow : exMarket.rowSum f () = f ((), ()) := by simp [Market.rowSum, exMarket]
  have hcol : exMarket.colSum f () = f ((), ()) := by simp [Market.colSum, exMarket]
  have hc := h.cond_c_le (); rw [hrow] at hc; simp only [exMarket] at hc
  have hP : P () = 0 := by
    rcases (h.P_nonneg ()).lt_or_eq with hp | hp
    · have := h.cond_d_eq () hp; rw [hcol] at this; simp only [exMarket] at this; linarith
    · exact hp.symm
  have ha := h.cond_a _ he; simp only [exMarket, hP] at ha
  have hf := h.cond_c_eq () (by linarith); rw [hrow] at hf; simp only [exMarket] at hf
  have hb := h.cond_b _ he (by rw [hf]; norm_num); simp only [exMarket, hP] at hb
  refine ⟨hP, by linarith, hf⟩

/-- For `0 < ε < 1` the perturbed solution is `u = (1−ε)/(1+ε²)`, `f = 1 + εu`, `P = 0`; its
support is `{f, u}`, and `(∗)` for this support has exactly one feasible point, the equilibrium
`(f, u, P) = (1, 1, 0)`. -/
theorem ex_small (ε : ℚ) (h0 : 0 < ε) (h1 : ε < 1) :
    IsLCPSol (lcpq exMarket) (lcpMeps exMarket ε)
        (exZ (1 + ε * ((1 - ε) / (1 + ε ^ 2))) ((1 - ε) / (1 + ε ^ 2)) 0) ∧
      support (exZ (1 + ε * ((1 - ε) / (1 + ε ^ 2))) ((1 - ε) / (1 + ε ^ 2)) 0) =
        {.inl exEdge, Idx.u ()} ∧
      IsStarFeasible (lcpq exMarket) (lcpM exMarket) {.inl exEdge, Idx.u ()} (exZ 1 1 0) ∧
      ∀ z, IsStarFeasible (lcpq exMarket) (lcpM exMarket) {.inl exEdge, Idx.u ()} z →
        z = exZ 1 1 0 := by
  have hd : 0 < 1 + ε ^ 2 := by positivity
  set u := (1 - ε) / (1 + ε ^ 2) with hu
  have hu0 : 0 < u := div_pos (by linarith) hd
  have hu1 : u ≤ 1 := (div_le_one hd).mpr (by nlinarith)
  have hkey : u + 0 - 1 + ε * (1 + ε * u) = 0 := by
    rw [hu]; field_simp; ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [exZ_sol]
    refine ⟨⟨by positivity, hu0.le, le_rfl⟩, ⟨by linarith, by linarith, by nlinarith⟩,
      ⟨by rw [hkey, mul_zero], by ring, by ring⟩⟩
  · have hf0 : 0 < 1 + ε * u := by positivity
    ext k
    simp only [support, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    rcases k with e | ⟨⟩ | ⟨⟩
    · simp [exZ, ex_edge_eq e, hf0]
    · simp [exZ, hu0]
    · simp [exZ]
  · refine ⟨?_, ?_, ?_, ?_⟩
    · rintro (e | ⟨⟩ | ⟨⟩) <;> simp [exZ]
    · rintro (e | ⟨⟩ | ⟨⟩) hk <;> simp_all [exZ, ex_edge_eq]
    · rintro (e | ⟨⟩ | ⟨⟩)
      · rw [ex_sl_f]; simp [exZ]
      · rw [ex_sl_u]; simp [exZ]
      · rw [ex_sl_P]; simp [exZ]
    · rintro (e | ⟨⟩ | ⟨⟩) hk
      · rw [ex_sl_f]; simp [exZ]
      · rw [ex_sl_u]; simp [exZ]
      · simp at hk
  · rintro z ⟨-, h2, -, h4⟩
    have hP := h2 (Idx.P ()) (by simp)
    have hf := h4 (.inl exEdge) (by simp)
    have hu' := h4 (Idx.u ()) (by simp)
    rw [ex_sl_f, hP] at hf
    rw [ex_sl_u] at hu'
    ext (e | ⟨⟩ | ⟨⟩)
    · rw [ex_edge_eq e]; simp [exZ]; linarith
    · simp [exZ]; linarith
    · simpa [exZ] using hP


theorem eps_le_half {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (Mk : Market I J) : eps Mk ≤ 1 / 2 := by
  unfold eps
  have := one_le_Q Mk; have := one_le_ceilZ Mk
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  nlinarith

/-- With the book's `ε` (Thm. plcp:thm:main) the example decodes: `0 < ε < 1`, so `ex_small` applies. -/
theorem ex_book_eps : 0 < eps exMarket ∧ eps exMarket < 1 :=
  ⟨eps_pos exMarket, lt_of_le_of_lt (eps_le_half exMarket) (by norm_num)⟩

theorem negativeExample_proof : NegativeExample :=
  ⟨ex_eq, ex_eq_unique, ex_one_sol, ex_one_unique, ex_one_support, ex_one_star_infeasible,
    fun ε h0 h1 => ex_small ε h0 h1, ex_book_eps⟩

end Example

end MarketLCP
end Bssg
