import Mathlib
import BssgProofs.Statements

/-!
# Proofs of Lemma 2 (Disser–Skutella counting network) and Lemma 3 (alternation)

Each target of `Statements.lean` is restated verbatim as `<name>_proof`.
Proof plan: `pwl D` is rewritten as a clipped sum `cs D y = Σ D_i · clip(y - i)`; a flow of
`G_k` is reduced to the level values `v_j` (flow through the inner `G_j`), giving
`cost ≥ F_k(y)` by the recursion `F_{j+1}(x) ≤ F_j(y) + 3^{j+1}(x - y)`; an explicit optimal
flow attains it.  Lemma 3 splits a splitter flow into two `G_m` flows and uses slope bounds of
`cs` with gaps `≥ 6`.
-/

namespace Bssg

open Finset

namespace L23

/-! ### Index formula for `countD` -/

theorem countD_len (k : ℕ) : (countD k).length = 2 ^ k := lemma2_length k

theorem countD_getD_succ (k i : ℕ) (hi : i < 2 * 2 ^ k) :
    (countD (k + 1)).getD i 0 =
      if i < 2 ^ k then (countD k).getD i 0
      else 2 * 3 ^ (k + 1) - (countD k).getD (2 * 2 ^ k - 1 - i) 0 := by
  have hl := countD_len k
  show (countD k ++ (countD k).reverse.map fun d => 2 * 3 ^ (k + 1) - d).getD i 0 = _
  split_ifs with h
  · exact List.getD_append _ _ _ _ (by omega)
  · rw [List.getD_append_right _ _ _ _ (by omega)]
    rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_map, List.getElem_reverse,
      List.getD_eq_getElem _ _ (by omega)]
    congr 2
    omega

theorem first (k : ℕ) : (countD k).getD 0 0 = 0 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [countD_getD_succ k 0 (by positivity), if_pos (by positivity), ih]

theorem getD_last (k : ℕ) : (countD (k + 1)).getD (2 * 2 ^ k - 1) 0 = 2 * 3 ^ (k + 1) := by
  have h1 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  rw [countD_getD_succ k _ (by omega), if_neg (by omega), Nat.sub_self, first]
  ring

theorem mem_bounds (k : ℕ) : ∀ d ∈ countD k, 0 ≤ d ∧ d ≤ 2 * 3 ^ k := by
  induction k with
  | zero => intro d hd; simp [countD] at hd; subst hd; norm_num
  | succ k ih =>
    intro d hd
    simp only [countD, List.mem_append, List.mem_map, List.mem_reverse] at hd
    have h3 : (3 : ℚ) ^ k ≤ 3 ^ (k + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
    rcases hd with hd | ⟨a, ha, rfl⟩
    · obtain ⟨h0, h1⟩ := ih d hd; exact ⟨h0, by linarith⟩
    · obtain ⟨h0, h1⟩ := ih a ha
      constructor
      · rw [pow_succ] at h3 ⊢; nlinarith
      · linarith

theorem gaps (k : ℕ) (hk : 1 ≤ k) (i : ℕ) (hi : i + 1 < 2 ^ k) :
    (countD k).getD i 0 + 6 ≤ (countD k).getD (i + 1) 0 := by
  induction k, hk using Nat.le_induction generalizing i with
  | base =>
    have : i = 0 := by omega
    subst this; simp [countD]; norm_num
  | succ k hk ih =>
    rw [pow_succ] at hi
    rw [countD_getD_succ k i (by omega), countD_getD_succ k (i + 1) (by omega)]
    have hc : 2 ≤ 2 ^ k := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
    by_cases h1 : i + 1 < 2 ^ k
    · rw [if_pos (by omega), if_pos h1]; exact ih i h1
    by_cases h2 : i + 1 = 2 ^ k
    · rw [if_pos (by omega), if_neg (by omega)]
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      have hl := getD_last k'
      have e1 : i = 2 * 2 ^ k' - 1 := by rw [pow_succ] at h2; omega
      have e2 : 2 * 2 ^ (k' + 1) - 1 - (i + 1) = 2 * 2 ^ k' - 1 := by rw [pow_succ] at h2 ⊢; omega
      rw [e2, e1, hl]
      have : (3 : ℚ) ≤ 3 ^ (k' + 1) := by
        calc (3 : ℚ) = 3 ^ 1 := by norm_num
          _ ≤ 3 ^ (k' + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
      rw [pow_succ 3 (k' + 1)]
      linarith
    · rw [if_neg (by omega), if_neg (by omega)]
      have := ih (2 * 2 ^ k - 1 - (i + 1)) (by omega)
      rw [show 2 * 2 ^ k - 1 - (i + 1) + 1 = 2 * 2 ^ k - 1 - i by omega] at this
      linarith

/-! ### Clipped-sum form of `pwl` -/

def clip (t : ℚ) : ℚ := min 1 (max 0 t)

def cs : List ℚ → ℚ → ℚ
  | [], _ => 0
  | d :: D, y => d * clip y + cs D (y - 1)

theorem clip_of_nonpos {t : ℚ} (h : t ≤ 0) : clip t = 0 := by
  unfold clip; rw [max_eq_left h]; simp

theorem clip_of_one_le {t : ℚ} (h : 1 ≤ t) : clip t = 1 := by
  unfold clip; rw [max_eq_right (by linarith)]; exact min_eq_left h

theorem clip_of_mem {t : ℚ} (h0 : 0 ≤ t) (h1 : t ≤ 1) : clip t = t := by
  unfold clip; rw [max_eq_right h0]; exact min_eq_right h1

theorem clip_nonneg (t : ℚ) : 0 ≤ clip t := by
  unfold clip; exact le_min (by norm_num) (le_max_left _ _)

theorem clip_mono {s t : ℚ} (h : s ≤ t) : clip s ≤ clip t := by
  unfold clip; exact min_le_min_left _ (max_le_max_left _ h)

theorem clip_add_clip (t : ℚ) : clip t + clip (1 - t) = 1 := by
  rcases le_total t 0 with h | h
  · rw [clip_of_nonpos h, clip_of_one_le (by linarith)]; ring
  rcases le_total t 1 with h' | h'
  · rw [clip_of_mem h h', clip_of_mem (by linarith) (by linarith)]; ring
  · rw [clip_of_one_le h', clip_of_nonpos (by linarith)]; ring

theorem cs_nonpos (D : List ℚ) {y : ℚ} (hy : y ≤ 0) : cs D y = 0 := by
  induction D generalizing y with
  | nil => rfl
  | cons d D ih => simp only [cs]; rw [clip_of_nonpos hy, ih (by linarith)]; ring

theorem cs_ge_len (D : List ℚ) {y : ℚ} (hy : (D.length : ℚ) ≤ y) : cs D y = D.sum := by
  induction D generalizing y with
  | nil => rfl
  | cons d D ih =>
    simp only [List.length_cons, Nat.cast_add, Nat.cast_one] at hy
    have h0 : (0 : ℚ) ≤ D.length := Nat.cast_nonneg _
    simp only [cs, List.sum_cons]
    rw [clip_of_one_le (by linarith), ih (by linarith)]; ring

theorem pwl_eq_cs (D : List ℚ) {y : ℚ} (hy : 0 ≤ y) : pwl D y = cs D y := by
  induction D generalizing y with
  | nil => simp [pwl, cs]
  | cons d D ih =>
    simp only [cs]
    rcases lt_or_ge y 1 with h | h
    · have hf : ⌊y⌋₊ = 0 := Nat.floor_eq_zero.mpr h
      rw [cs_nonpos D (by linarith), clip_of_mem hy h.le]
      simp [pwl, hf]; ring
    · have hf : ⌊y⌋₊ = ⌊y - 1⌋₊ + 1 := by
        rw [← Nat.floor_add_one (by linarith)]; ring_nf
      rw [← ih (by linarith), clip_of_one_le h]
      simp only [pwl, hf, List.take_succ_cons, List.sum_cons, List.getD_cons_succ]
      push_cast; ring

theorem cs_append (D E : List ℚ) (y : ℚ) : cs (D ++ E) y = cs D y + cs E (y - D.length) := by
  induction D generalizing y with
  | nil => simp [cs]
  | cons d D ih =>
    simp only [List.cons_append, cs, ih, List.length_cons]; push_cast; ring_nf

theorem cs_reverse (D : List ℚ) (u : ℚ) : cs D.reverse u = D.sum - cs D (D.length - u) := by
  induction D generalizing u with
  | nil => simp [cs]
  | cons d D ih =>
    simp only [List.reverse_cons, cs_append, ih, List.length_reverse, cs, List.sum_cons,
      List.length_cons]
    push_cast
    have := clip_add_clip (u - D.length)
    rw [show (D.length : ℚ) + 1 - u - 1 = D.length - u by ring,
      show (D.length : ℚ) + 1 - u = 1 - (u - D.length) by ring]
    linear_combination d * this

theorem cs_map_sub (E : List ℚ) (a u : ℚ) :
    cs (E.map fun d => a - d) u = a * cs (E.map fun _ => 1) u - cs E u := by
  induction E generalizing u with
  | nil => simp [cs]
  | cons d E ih => simp only [List.map_cons, cs, ih]; ring

theorem cs_ones (E : List ℚ) {u : ℚ} (h0 : 0 ≤ u) (h1 : u ≤ E.length) :
    cs (E.map fun _ => 1) u = u := by
  induction E generalizing u with
  | nil => simp at h1; simp [cs]; linarith
  | cons d E ih =>
    simp only [List.length_cons, Nat.cast_add, Nat.cast_one] at h1
    simp only [List.map_cons, cs]
    rcases le_total u 1 with h | h
    · rw [clip_of_mem h0 h, cs_nonpos _ (by linarith)]; ring
    · rw [clip_of_one_le h, ih (by linarith) (by linarith)]; ring

theorem cs_lip (D : List ℚ) (L : ℚ) (hD : ∀ d ∈ D, 0 ≤ d ∧ d ≤ L) {y y' : ℚ} (h : y ≤ y') :
    cs D y' - cs D y ≤ L * (cs (D.map fun _ => 1) y' - cs (D.map fun _ => 1) y) := by
  induction D generalizing y y' with
  | nil => simp [cs]
  | cons d D ih =>
    simp only [List.map_cons, cs]
    have h1 := ih (fun e he => hD e (List.mem_cons_of_mem _ he)) (show y - 1 ≤ y' - 1 by linarith)
    obtain ⟨hd0, hdL⟩ := hD d List.mem_cons_self
    have hc := clip_mono h
    have : d * (clip y' - clip y) ≤ L * (clip y' - clip y) :=
      mul_le_mul_of_nonneg_right hdL (by linarith)
    nlinarith

/-- The numeric content of `F_k`: `F_k := cs (countD k)` on `[0, 2^k]`. -/
theorem F_lip (k : ℕ) {y y' : ℚ} (h0 : 0 ≤ y) (h : y ≤ y') (h1 : y' ≤ 2 ^ k) :
    cs (countD k) y' - cs (countD k) y ≤ 2 * 3 ^ k * (y' - y) := by
  have hl : ((countD k).length : ℚ) = 2 ^ k := by rw [countD_len]; push_cast; rfl
  have := cs_lip (countD k) _ (mem_bounds k) h
  rwa [cs_ones _ (by linarith) (by simp only [hl]; linarith),
    cs_ones _ h0 (by simp only [hl]; linarith)] at this

theorem F_succ_lo (k : ℕ) {x : ℚ} (hx : x ≤ 2 ^ k) :
    cs (countD (k + 1)) x = cs (countD k) x := by
  have hl : ((countD k).length : ℚ) = 2 ^ k := by rw [countD_len]; push_cast; rfl
  show cs (countD k ++ _) x = _
  rw [cs_append, hl, cs_nonpos (y := x - 2 ^ k) _ (by linarith)]; ring

theorem F_succ_hi (k : ℕ) {x : ℚ} (hx0 : 2 ^ k ≤ x) (hx : x ≤ 2 * 2 ^ k) :
    cs (countD (k + 1)) x =
      2 * 3 ^ (k + 1) * (x - 2 ^ k) + cs (countD k) (2 * 2 ^ k - x) := by
  have hl : ((countD k).length : ℚ) = 2 ^ k := by rw [countD_len]; push_cast; rfl
  show cs (countD k ++ _) x = _
  rw [cs_append, hl, cs_map_sub, cs_reverse, cs_ones _ (by linarith)
    (by rw [List.length_reverse, hl]; linarith), cs_ge_len _ (by rw [hl]; exact hx0), hl]
  rw [show (2 : ℚ) ^ k - (x - 2 ^ k) = 2 * 2 ^ k - x by ring]
  ring

/-- Recursion, equality case: `F_{k+1}(x) = F_k(y*) + 3^{k+1}(x - y*)`, `y* = min(x, 2^{k+1} - x)`. -/
theorem F_succ_eq (k : ℕ) {x : ℚ} (_hx0 : 0 ≤ x) (hx : x ≤ 2 * 2 ^ k) :
    cs (countD (k + 1)) x = cs (countD k) (min x (2 * 2 ^ k - x)) +
      3 ^ (k + 1) * (x - min x (2 * 2 ^ k - x)) := by
  rcases le_total x (2 ^ k) with h | h
  · rw [min_eq_left (by linarith), F_succ_lo k h]; ring
  · rw [min_eq_right (by linarith), F_succ_hi k h hx]; ring

/-- Recursion, inequality case. -/
theorem F_succ_le (k : ℕ) {x y : ℚ} (hy0 : 0 ≤ y) (hyx : y ≤ x) (hyx' : y ≤ 2 * 2 ^ k - x) :
    cs (countD (k + 1)) x ≤ cs (countD k) y + 3 ^ (k + 1) * (x - y) := by
  have hx : x ≤ 2 * 2 ^ k := by linarith
  rw [F_succ_eq k (by linarith) hx]
  set y' := min x (2 * 2 ^ k - x)
  have h1 : y ≤ y' := le_min hyx hyx'
  have h2 : y' ≤ 2 ^ k := by
    rcases le_total x (2 ^ k) with h | h
    · exact (min_le_left _ _).trans h
    · exact (min_le_right _ _).trans (by linarith)
  have := F_lip k hy0 h1 h2
  have h3 : (2 : ℚ) * 3 ^ k ≤ 3 ^ (k + 1) := by rw [pow_succ]; nlinarith [pow_pos (show (0:ℚ) < 3 by norm_num) k]
  nlinarith

/-! ### Flows in `G_k`: per-node formulas -/

section G

variable {k : ℕ}

/-- Flow on arc `r` of level `j + 1` (zero if `j ≥ k`). -/
def A (φ : GArc k → ℚ) (j : ℕ) (r : Fin 4) : ℚ := if h : j < k then φ (some (⟨j, h⟩, r)) else 0

theorem A_zero (φ : GArc k → ℚ) {j : ℕ} (h : k ≤ j) (r : Fin 4) : A φ j r = 0 := by
  simp [A]; omega

theorem sum_cast (φ : GArc k → ℚ) (i : Fin (k + 1)) (r : Fin 4) :
    (∑ j : Fin k, if j.castSucc = i then φ (some (j, r)) else 0) = A φ i r := by
  calc (∑ j : Fin k, if j.castSucc = i then φ (some (j, r)) else 0)
      = ∑ j : Fin k, (fun n : ℕ => if n = (i : ℕ) then A φ n r else 0) j :=
        Finset.sum_congr rfl (fun j _ => by simp [A, Fin.ext_iff])
    _ = ∑ n ∈ range k, (if n = (i : ℕ) then A φ n r else 0) 
        := Fin.sum_univ_eq_sum_range (fun n : ℕ => if n = (i : ℕ) then A φ n r else 0) k
    _ = A φ i r := by
        rw [Finset.sum_ite_eq']
        split_ifs with h
        · rfl
        · rw [A_zero φ (by simpa using h)]

theorem sum_succ (φ : GArc k → ℚ) (i : Fin (k + 1)) (r : Fin 4) :
    (∑ j : Fin k, if j.succ = i then φ (some (j, r)) else 0) =
      if (i : ℕ) = 0 then 0 else A φ (i - 1) r := by
  calc (∑ j : Fin k, if j.succ = i then φ (some (j, r)) else 0)
      = ∑ j : Fin k, (fun n : ℕ => if n + 1 = (i : ℕ) then A φ n r else 0) j :=
        Finset.sum_congr rfl (fun j _ => by simp [A, Fin.ext_iff])
    _ = ∑ n ∈ range k, (if n + 1 = (i : ℕ) then A φ n r else 0) 
        := Fin.sum_univ_eq_sum_range (fun n : ℕ => if n + 1 = (i : ℕ) then A φ n r else 0) k
    _ = _ := by
        split_ifs with h0
        · exact Finset.sum_eq_zero (fun n _ => by rw [if_neg (by omega)])
        · rw [Finset.sum_congr rfl (g := fun n => if n = (i : ℕ) - 1 then A φ n r else 0)
            (fun n _ => by congr 1; apply propext; omega), Finset.sum_ite_eq']
          split_ifs with h
          · rfl
          · rw [A_zero φ (by simpa using h)]

theorem outflow_inl (φ : GArc k → ℚ) (i : Fin (k + 1)) :
    (countingNetwork k).outflow φ (.inl i) =
      (if (i : ℕ) = 0 then φ none else A φ (i - 1) 0 + A φ (i - 1) 2) + A φ i 3 := by
  unfold Network.outflow
  rw [Finset.sum_filter, Fintype.sum_option, Fintype.sum_prod_type]
  simp only [Fin.sum_univ_four, countingNetwork, gTail]
  simp
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, sum_succ, sum_succ, sum_cast]
  by_cases h : i = 0
  · subst h; simp
  · have h' : (i : ℕ) ≠ 0 := fun h' => h (Fin.ext h')
    simp [h, h', Ne.symm h]

theorem inflow_inl (φ : GArc k → ℚ) (i : Fin (k + 1)) :
    (countingNetwork k).inflow φ (.inl i) = A φ i 0 := by
  unfold Network.inflow
  rw [Finset.sum_filter, Fintype.sum_option, Fintype.sum_prod_type]
  simp only [Fin.sum_univ_four, countingNetwork, gHead]
  simp
  rw [sum_cast]

theorem outflow_inr (φ : GArc k → ℚ) (i : Fin (k + 1)) :
    (countingNetwork k).outflow φ (.inr i) = A φ i 1 := by
  unfold Network.outflow
  rw [Finset.sum_filter, Fintype.sum_option, Fintype.sum_prod_type]
  simp only [Fin.sum_univ_four, countingNetwork, gTail]
  simp
  rw [sum_cast]

theorem inflow_inr (φ : GArc k → ℚ) (i : Fin (k + 1)) :
    (countingNetwork k).inflow φ (.inr i) =
      (if (i : ℕ) = 0 then φ none else A φ (i - 1) 1 + A φ (i - 1) 3) + A φ i 2 := by
  unfold Network.inflow
  rw [Finset.sum_filter, Fintype.sum_option, Fintype.sum_prod_type]
  simp only [Fin.sum_univ_four, countingNetwork, gHead]
  simp
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, sum_succ, sum_succ, sum_cast]
  by_cases h : i = 0
  · subst h; simp
  · have h' : (i : ℕ) ≠ 0 := fun h' => h (Fin.ext h')
    simp [h, h', Ne.symm h]; ring

theorem totalCost_eq (φ : GArc k → ℚ) :
    (countingNetwork k).totalCost φ = ∑ j ∈ range k, 3 ^ (j + 1) * (A φ j 2 + A φ j 3) := by
  unfold Network.totalCost
  rw [Fintype.sum_option, Fintype.sum_prod_type]
  simp only [Fin.sum_univ_four, countingNetwork, gCost]
  simp
  rw [← Fin.sum_univ_eq_sum_range (fun j => 3 ^ (j + 1) * (A φ j 2 + A φ j 3)) k]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  simp [A]; ring

/-- `v j` = value of the flow through the inner copy of `G_j`. -/
def vv (φ : GArc k → ℚ) : ℕ → ℚ
  | 0 => φ none
  | j + 1 => A φ j 0 + A φ j 2

def ww (φ : GArc k → ℚ) : ℕ → ℚ
  | 0 => φ none
  | j + 1 => A φ j 1 + A φ j 3

theorem ite_vv (φ : GArc k → ℚ) (j : ℕ) :
    (if j = 0 then φ none else A φ (j - 1) 0 + A φ (j - 1) 2) = vv φ j := by
  cases j <;> simp [vv]

theorem ite_ww (φ : GArc k → ℚ) (j : ℕ) :
    (if j = 0 then φ none else A φ (j - 1) 1 + A φ (j - 1) 3) = ww φ j := by
  cases j <;> simp [ww]

theorem netOut_inl (φ : GArc k → ℚ) (i : Fin (k + 1)) :
    (countingNetwork k).netOut φ (.inl i) = vv φ i + A φ i 3 - A φ i 0 := by
  rw [Network.netOut, outflow_inl, inflow_inl, ite_vv]

theorem netOut_inr (φ : GArc k → ℚ) (i : Fin (k + 1)) :
    (countingNetwork k).netOut φ (.inr i) = A φ i 1 - ww φ i - A φ i 2 := by
  rw [Network.netOut, outflow_inr, inflow_inr, ite_ww]; ring

/-- Lower bound and value facts for any `s_k → t_k` flow of `G_k`. -/
theorem flow_lower (y : ℚ) (φ : GArc k → ℚ)
    (hφ : (countingNetwork k).IsFlow (gSource k) (gSink k) y φ) :
    cs (countD k) y ≤ (countingNetwork k).totalCost φ ∧
      (countingNetwork k).inflow φ (gSink k) = y ∧ 0 ≤ y ∧ y ≤ 2 ^ k := by
  obtain ⟨hfeas, hsrc, hcons⟩ := hφ
  have hA : ∀ j r, 0 ≤ A φ j r ∧ A φ j r ≤ 2 ^ j := by
    intro j r
    by_cases h : j < k
    · have := hfeas (some (⟨j, h⟩, r))
      simpa [A, h, countingNetwork, gCap] using this
    · rw [A_zero φ (by omega)]; exact ⟨le_refl _, by positivity⟩
  have hnone := hfeas none
  simp only [countingNetwork, gCap] at hnone
  -- conservation at `s_j`, `t_j` for `j < k`
  have hs : ∀ j, j < k → A φ j 0 = vv φ j + A φ j 3 := by
    intro j hj
    have := hcons (.inl ⟨j, by omega⟩) (by simp [gSource, Fin.ext_iff]; omega)
      (by simp [gSink])
    rw [netOut_inl] at this; simp at this; linarith
  have ht : ∀ j, j < k → A φ j 1 = ww φ j + A φ j 2 := by
    intro j hj
    have := hcons (.inr ⟨j, by omega⟩) (by simp [gSource]) (by simp [gSink, Fin.ext_iff]; omega)
    rw [netOut_inr] at this; simp at this; linarith
  have hvw : ∀ j, j ≤ k → ww φ j = vv φ j := by
    intro j hj
    induction j with
    | zero => rfl
    | succ j ih =>
      simp only [ww, vv]
      rw [ht j (by omega), hs j (by omega), ih (by omega)]; ring
  have hval : vv φ k = y := by
    have := hsrc
    rw [gSource, netOut_inl] at this
    simp only [Fin.val_last] at this
    rw [A_zero φ le_rfl, A_zero φ le_rfl] at this; linarith
  have hv0 : ∀ j, 0 ≤ vv φ j := by
    intro j; cases j with
    | zero => exact hnone.1
    | succ j => simp only [vv]; linarith [hA j 0, hA j 2]
  have hstep : ∀ j, j < k → vv φ j ≤ vv φ (j + 1) ∧ vv φ j + vv φ (j + 1) ≤ 2 * 2 ^ j ∧
      vv φ (j + 1) - vv φ j = A φ j 2 + A φ j 3 := by
    intro j hj
    have h1 := hs j hj; have h2 := ht j hj; rw [hvw j hj.le] at h2
    have e : vv φ (j + 1) = A φ j 0 + A φ j 2 := rfl
    rw [e]
    refine ⟨by linarith [hA j 2, hA j 3], by linarith [hA j 0, hA j 1], by linarith⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [totalCost_eq, ← hval]
    have key : ∀ i, i ≤ k → cs (countD i) (vv φ i) ≤
        ∑ j ∈ range i, 3 ^ (j + 1) * (A φ j 2 + A φ j 3) := by
      intro i hi
      induction i with
      | zero => simp [countD, cs]
      | succ i ih =>
        rw [Finset.sum_range_succ]
        obtain ⟨h1, h2, h3⟩ := hstep i (by omega)
        have := F_succ_le i (hv0 i) h1 (by linarith)
        rw [← h3]; linarith [ih (by omega)]
    exact key k le_rfl
  · rw [gSink, inflow_inr, ite_ww, Fin.val_last, hvw k le_rfl, A_zero φ (by simp)]; simpa using hval
  · rw [← hval]; exact hv0 k
  · rw [← hval]
    cases k with
    | zero => simpa [vv] using hnone.2
    | succ k =>
      obtain ⟨_, h2, _⟩ := hstep k (by omega)
      have := hv0 k
      rw [pow_succ]; linarith

/-- Top-down levels of the optimal flow: `uu 0 = y`, `uu (n+1) = min(x, 2^{k-n} - x)`. -/
def uu (k : ℕ) (y : ℚ) : ℕ → ℚ
  | 0 => y
  | n + 1 => min (uu k y n) (2 ^ (k - n) - uu k y n)

/-- The optimal flow of value `y`. -/
def optFlow (k : ℕ) (y : ℚ) : GArc k → ℚ
  | none => uu k y k
  | some (j, r) =>
    if r.val ≤ 1 then (uu k y (k - j) + uu k y (k - (j + 1))) / 2
    else (uu k y (k - (j + 1)) - uu k y (k - j)) / 2

theorem uu_bounds (k : ℕ) {y : ℚ} (h0 : 0 ≤ y) (h1 : y ≤ 2 ^ k) :
    ∀ n, n ≤ k → 0 ≤ uu k y n ∧ uu k y n ≤ 2 ^ (k - n) := by
  intro n hn
  induction n with
  | zero => simpa [uu] using ⟨h0, h1⟩
  | succ n ih =>
    obtain ⟨a, b⟩ := ih (by omega)
    have e : (2 : ℚ) ^ (k - n) = 2 * 2 ^ (k - (n + 1)) := by
      rw [← pow_succ']; congr 1; omega
    simp only [uu]
    refine ⟨le_min a (by linarith), ?_⟩
    rcases le_total (uu k y n) (2 ^ (k - (n + 1))) with h | h
    · exact (min_le_left _ _).trans h
    · exact (min_le_right _ _).trans (by linarith)

theorem uu_step (k : ℕ) (y : ℚ) (j : ℕ) (hj : j < k) :
    uu k y (k - j) = min (uu k y (k - (j + 1))) (2 * 2 ^ j - uu k y (k - (j + 1))) := by
  rw [show k - j = (k - (j + 1)) + 1 by omega, uu, show k - (k - (j + 1)) = j + 1 by omega,
    pow_succ']

theorem A_optFlow (k : ℕ) (y : ℚ) (j : ℕ) (hj : j < k) (r : Fin 4) :
    A (optFlow k y) j r = if r.val ≤ 1 then (uu k y (k - j) + uu k y (k - (j + 1))) / 2
      else (uu k y (k - (j + 1)) - uu k y (k - j)) / 2 := by
  simp [A, hj, optFlow]

theorem vv_optFlow (k : ℕ) (y : ℚ) (j : ℕ) (hj : j ≤ k) :
    vv (optFlow k y) j = uu k y (k - j) := by
  cases j with
  | zero => rfl
  | succ j =>
    simp only [vv]; rw [A_optFlow k y j (by omega), A_optFlow k y j (by omega)]
    simp; ring

theorem ww_optFlow (k : ℕ) (y : ℚ) (j : ℕ) (hj : j ≤ k) :
    ww (optFlow k y) j = uu k y (k - j) := by
  cases j with
  | zero => rfl
  | succ j =>
    simp only [ww]; rw [A_optFlow k y j (by omega), A_optFlow k y j (by omega)]
    simp; ring

theorem optFlow_spec (k : ℕ) {y : ℚ} (h0 : 0 ≤ y) (h1 : y ≤ 2 ^ k) :
    (countingNetwork k).IsFlow (gSource k) (gSink k) y (optFlow k y) ∧
      (countingNetwork k).totalCost (optFlow k y) = cs (countD k) y := by
  have hb := uu_bounds k h0 h1
  have hlev : ∀ j, j < k → 0 ≤ uu k y (k - j) ∧ uu k y (k - j) ≤ uu k y (k - (j + 1)) ∧
      uu k y (k - j) + uu k y (k - (j + 1)) ≤ 2 * 2 ^ j := by
    intro j hj
    have := hb (k - j) (by omega)
    rw [uu_step k y j hj]
    refine ⟨?_, min_le_left _ _, ?_⟩
    · rw [← uu_step k y j hj]; exact this.1
    · linarith [min_le_right (uu k y (k - (j + 1))) (2 * 2 ^ j - uu k y (k - (j + 1)))]
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · intro a
    rcases a with _ | ⟨j, r⟩
    · have := hb k le_rfl
      simp only [optFlow, countingNetwork, gCap]; simpa using this
    · obtain ⟨a1, a2, a3⟩ := hlev j j.isLt
      simp only [optFlow, countingNetwork, gCap]
      split_ifs
      · constructor <;> linarith
      · constructor <;> linarith
  · rw [gSource, netOut_inl, Fin.val_last, A_zero _ le_rfl, A_zero _ le_rfl,
      vv_optFlow k y k le_rfl, Nat.sub_self]; simp [uu]
  · intro u hu1 hu2
    rcases u with ⟨j, hj⟩ | ⟨j, hj⟩
    · have hjk : j < k := by
        by_contra h; apply hu1; simp [gSource, Fin.ext_iff]; omega
      rw [netOut_inl]; simp only
      rw [vv_optFlow k y j (by omega), A_optFlow k y j hjk, A_optFlow k y j hjk]
      simp; ring
    · have hjk : j < k := by
        by_contra h; apply hu2; simp [gSink, Fin.ext_iff]; omega
      rw [netOut_inr]; simp only
      rw [ww_optFlow k y j (by omega), A_optFlow k y j hjk, A_optFlow k y j hjk]
      simp; ring
  · rw [totalCost_eq]
    have key : ∀ i, i ≤ k → cs (countD i) (uu k y (k - i)) =
        ∑ j ∈ range i, 3 ^ (j + 1) * (A (optFlow k y) j 2 + A (optFlow k y) j 3) := by
      intro i hi
      induction i with
      | zero => simp [countD, cs]
      | succ i ih =>
        rw [Finset.sum_range_succ, ← ih (by omega), A_optFlow k y i (by omega),
          A_optFlow k y i (by omega)]
        have hx := hb (k - (i + 1)) (by omega)
        rw [show k - (k - (i + 1)) = i + 1 by omega, pow_succ'] at hx
        rw [F_succ_eq i hx.1 hx.2, ← uu_step k y i (by omega)]
        simp
    have := key k le_rfl
    rw [Nat.sub_self] at this
    simpa [uu] using this.symm

end G

end L23

/-! ## Lemma 2 -/

theorem lemma2_first_proof (k : ℕ) : (countD k).getD 0 0 = 0 := L23.first k

theorem lemma2_last_proof (k : ℕ) (hk : 1 ≤ k) : (countD k).getLast? = some (2 * 3 ^ k) := by
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  have hl := L23.countD_len (k + 1)
  have h1 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  rw [List.getLast?_eq_getElem?, hl, List.getElem?_eq_getElem (by rw [hl]; rw [pow_succ]; omega),
    ← List.getD_eq_getElem _ 0, show 2 ^ (k + 1) - 1 = 2 * 2 ^ k - 1 by rw [pow_succ]; omega,
    L23.getD_last]

theorem lemma2_gaps_proof (k : ℕ) (hk : 1 ≤ k) (i : ℕ) (hi : i + 1 < (countD k).length) :
    (countD k).getD i 0 + 6 ≤ (countD k).getD (i + 1) 0 :=
  L23.gaps k hk i (by rwa [L23.countD_len] at hi)

theorem lemma2_minCost_proof (k : ℕ) (y : ℚ) (hy0 : 0 ≤ y) (hy : y ≤ 2 ^ k) :
    (∃ φ, (countingNetwork k).IsMinCostFlow (gSource k) (gSink k) y φ) ∧
    ∀ φ, (countingNetwork k).IsMinCostFlow (gSource k) (gSink k) y φ →
      (countingNetwork k).totalCost φ = pwl (countD k) y := by
  obtain ⟨hf, hc⟩ := L23.optFlow_spec k hy0 hy
  refine ⟨⟨L23.optFlow k y, hf, fun ψ hψ => ?_⟩, fun φ hφ => ?_⟩
  · rw [hc]; exact (L23.flow_lower y ψ hψ).1
  · rw [L23.pwl_eq_cs _ hy0]
    have h1 := hφ.2 _ hf
    have h2 := (L23.flow_lower y φ hφ.1).1
    linarith

theorem lemma2_maxFlow_proof (k : ℕ) (y : ℚ) (hy : 2 ^ k < y) :
    ¬ ∃ φ, (countingNetwork k).IsFlow (gSource k) (gSink k) y φ := by
  rintro ⟨φ, hφ⟩
  have := (L23.flow_lower y φ hφ).2.2.2
  linarith

example (k : ℕ) : (countD k).getD 0 0 = 0 := lemma2_first_proof k
example (k : ℕ) (hk : 1 ≤ k) : (countD k).getLast? = some (2 * 3 ^ k) := lemma2_last_proof k hk


/-! ## Lemma 3 -/

namespace L23

/-! ### Slope bounds for `cs` (index form) -/

theorem cs_sum (D : List ℚ) (y : ℚ) :
    cs D y = ∑ i ∈ range D.length, D.getD i 0 * clip (y - i) := by
  induction D generalizing y with
  | nil => simp [cs]
  | cons d D ih =>
    rw [List.length_cons, Finset.sum_range_succ', cs, ih]
    simp only [List.getD_cons_succ, List.getD_cons_zero, Nat.cast_add, Nat.cast_one,
      Nat.cast_zero, sub_zero]
    rw [add_comm]
    congr 1
    refine Finset.sum_congr rfl (fun i _ => ?_)
    ring_nf

theorem clip_sum (n : ℕ) {y : ℚ} (h0 : 0 ≤ y) (h1 : y ≤ n) :
    ∑ i ∈ range n, clip (y - i) = y := by
  induction n generalizing y with
  | zero => simp at h1 ⊢; linarith
  | succ n ih =>
    rw [Finset.sum_range_succ']
    push_cast at h1
    rcases le_total y 1 with h | h
    · rw [Finset.sum_eq_zero (fun i _ => clip_of_nonpos (by
        have : (0 : ℚ) ≤ i := Nat.cast_nonneg i
        push_cast; linarith))]
      simp [clip_of_mem h0 h]
    · have := ih (y := y - 1) (by linarith) (by linarith)
      rw [Finset.sum_congr rfl (g := fun i : ℕ => clip (y - 1 - i)) (fun i _ => by
        push_cast; ring_nf), this]
      simp [clip_of_one_le h]

theorem diff_sum (D : List ℚ) (y1 y2 : ℚ) :
    cs D y2 - cs D y1 = ∑ i ∈ range D.length, D.getD i 0 * (clip (y2 - i) - clip (y1 - i)) := by
  rw [cs_sum, cs_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl (fun i _ => by ring)

theorem mul_diff_sum (n : ℕ) {c y1 y2 : ℚ} (h0 : 0 ≤ y1) (h12 : y1 ≤ y2) (h2 : y2 ≤ n) :
    c * (y2 - y1) = ∑ i ∈ range n, c * (clip (y2 - i) - clip (y1 - i)) := by
  rw [← Finset.mul_sum, Finset.sum_sub_distrib, clip_sum n (by linarith) h2,
    clip_sum n h0 (by linarith)]

theorem slope_lo (D : List ℚ) (i0 : ℕ) (L : ℚ)
    (hL : ∀ i, i0 ≤ i → i < D.length → L ≤ D.getD i 0)
    {y1 y2 : ℚ} (h1 : (i0 : ℚ) ≤ y1) (h12 : y1 ≤ y2) (h2 : y2 ≤ D.length) :
    L * (y2 - y1) ≤ cs D y2 - cs D y1 := by
  have hi0 : (0 : ℚ) ≤ i0 := Nat.cast_nonneg _
  rw [diff_sum, mul_diff_sum D.length (by linarith) h12 h2]
  refine Finset.sum_le_sum (fun i hi => ?_)
  rw [Finset.mem_range] at hi
  by_cases h : i0 ≤ i
  · have := clip_mono (show y1 - i ≤ y2 - i by linarith)
    exact mul_le_mul_of_nonneg_right (hL i h hi) (by linarith)
  · have hi' : (i : ℚ) + 1 ≤ i0 := by exact_mod_cast (show i + 1 ≤ i0 by omega)
    rw [clip_of_one_le (show 1 ≤ y1 - i by linarith), clip_of_one_le (show 1 ≤ y2 - i by linarith)]
    simp

theorem slope_hi (D : List ℚ) (j : ℕ) (U : ℚ)
    (hU : ∀ i, i ≤ j → i < D.length → D.getD i 0 ≤ U)
    {y1 y2 : ℚ} (h0 : 0 ≤ y1) (h12 : y1 ≤ y2) (h2 : y2 ≤ (j : ℚ) + 1) (h2' : y2 ≤ D.length) :
    cs D y2 - cs D y1 ≤ U * (y2 - y1) := by
  rw [diff_sum, mul_diff_sum D.length h0 h12 h2']
  refine Finset.sum_le_sum (fun i hi => ?_)
  rw [Finset.mem_range] at hi
  by_cases h : i ≤ j
  · have := clip_mono (show y1 - i ≤ y2 - i by linarith)
    exact mul_le_mul_of_nonneg_right (hU i h hi) (by linarith)
  · have hi' : (j : ℚ) + 1 ≤ i := by exact_mod_cast (show j + 1 ≤ i by omega)
    rw [clip_of_nonpos (show y1 - i ≤ 0 by linarith), clip_of_nonpos (show y2 - i ≤ 0 by linarith)]
    simp

/-- The numeric core of Lemma 3: `h₀(x)` is the unique minimiser of
`Φ(A) = F(A) + F(x - A) + θ (x - A)` over the feasible `A`. -/
theorem split_unique (N : ℕ) (D : List ℚ) (hlen : D.length = N)
    (hgap : ∀ i, i + 1 < N → D.getD i 0 + 6 ≤ D.getD (i + 1) 0)
    {θ x A : ℚ} (hθ0 : 0 < θ) (hθ6 : θ < 6) (hx0 : 0 ≤ x)
    (hA0 : 0 ≤ A) (hAN : A ≤ N) (hB0 : 0 ≤ x - A) (hBN : x - A ≤ N)
    (hle : cs D A + cs D (x - A) + θ * (x - A) ≤
      cs D (h0 x) + cs D (x - h0 x) + θ * (x - h0 x)) : A = h0 x := by
  have mono : ∀ i j, i ≤ j → j < N → D.getD i 0 ≤ D.getD j 0 := by
    intro i j hij hj
    induction j with
    | zero => have : i = 0 := by omega
              subst this; exact le_rfl
    | succ j ih =>
      rcases Nat.lt_or_ge i (j + 1) with h | h
      · have := ih (by omega) (by omega); have := hgap j hj; linarith
      · have : i = j + 1 := by omega
        subst this; exact le_rfl
  set z : ℤ := ⌊x / 2⌋ with hz
  have hz0 : 0 ≤ z := Int.floor_nonneg.mpr (by linarith)
  have hzl : (z : ℚ) ≤ x / 2 := Int.floor_le _
  have hzu : x / 2 < (z : ℚ) + 1 := Int.lt_floor_add_one _
  set zn : ℕ := z.toNat with hzn
  have hzq : (zn : ℚ) = (z : ℚ) := by
    rw [hzn]; exact_mod_cast Int.toNat_of_nonneg hz0
  set ρ := x - 2 * (z : ℚ) with hρ
  have hρ0 : 0 ≤ ρ := by linarith
  have hρ2 : ρ < 2 := by linarith
  set a0 := h0 x with ha0
  have ha0' : a0 = zn + min ρ 1 := by rw [ha0, hzq]; rfl
  have hb0' : x - a0 = zn + max (ρ - 1) 0 := by
    have := h0_add_h1 x
    have e : h1 x = zn + max (ρ - 1) 0 := by rw [hzq]; rfl
    linarith
  set F := cs D
  have hN : ((D.length : ℕ) : ℚ) = N := by rw [hlen]
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · -- `A < a0`: compare slopes at index `zn`
    set d := a0 - A
    have hd : 0 < d := by simp only [d]; linarith
    have hzb : (zn : ℚ) ≤ x - a0 := by rw [hb0']; linarith [le_max_right (ρ - 1) 0]
    have hza : a0 ≤ (zn : ℚ) + 1 := by rw [ha0']; linarith [min_le_right ρ 1]
    have hzN : zn < N := by
      have : (zn : ℚ) < N := by linarith
      exact_mod_cast this
    have lo := slope_lo D zn (D.getD zn 0) (fun i hi hi' => mono _ _ hi (by omega))
      hzb (show x - a0 ≤ x - A by linarith) (by rw [hN]; exact hBN)
    have hzN' : (zn : ℚ) + 1 ≤ N := by exact_mod_cast hzN
    have hi := slope_hi D zn (D.getD zn 0) (fun i hi hi' => mono _ _ hi hzN)
      hA0 hlt.le hza (by rw [hN]; linarith)
    have e1 : x - A - (x - a0) = d := by simp only [d]; ring
    rw [e1] at lo
    have : θ * (x - A) - θ * (x - a0) = θ * d := by simp only [d]; ring
    nlinarith
  · -- `A > a0`
    set d := A - a0
    have hd : 0 < d := by simp only [d]; linarith
    have hb0pos : 0 < x - a0 := by linarith
    obtain ⟨j, hja, hjb⟩ : ∃ j : ℕ, (j : ℚ) + 1 ≤ a0 ∧ x - a0 ≤ (j : ℚ) + 1 := by
      rcases le_or_gt ρ 1 with hρ1 | hρ1
      · have hb : x - a0 = zn := by rw [hb0', max_eq_right (by linarith)]; ring
        have hzpos : 1 ≤ zn := by
          have : (0 : ℚ) < zn := by linarith
          exact_mod_cast this
        refine ⟨zn - 1, ?_, ?_⟩
        · have : ((zn - 1 : ℕ) : ℚ) + 1 = zn := by
            rw [Nat.cast_sub hzpos]; push_cast; ring
          rw [this, ha0']; linarith [le_min hρ0 (show (0:ℚ) ≤ 1 by norm_num)]
        · have : ((zn - 1 : ℕ) : ℚ) + 1 = zn := by
            rw [Nat.cast_sub hzpos]; push_cast; ring
          rw [this, hb]
      · refine ⟨zn, ?_, ?_⟩
        · rw [ha0', min_eq_right hρ1.le]
        · rw [hb0', max_eq_left (by linarith)]; linarith
    have hjN : j + 1 < N := by
      have : (j : ℚ) + 1 < N := by linarith
      exact_mod_cast this
    have lo := slope_lo D (j + 1) (D.getD (j + 1) 0)
      (fun i hi hi' => mono _ _ hi (by omega)) (by push_cast; exact hja) hgt.le
      (by rw [hN]; exact hAN)
    have hi := slope_hi D j (D.getD j 0) (fun i hi hi' => mono _ _ hi (by omega))
      hB0 (show x - A ≤ x - a0 by linarith) hjb (by rw [hN]; linarith)
    have e1 : x - a0 - (x - A) = d := by simp only [d]; ring
    rw [e1] at hi
    have hg := hgap j hjN
    have : θ * (x - A) - θ * (x - a0) = -(θ * d) := by simp only [d]; ring
    nlinarith

/-! ### The splitter as two copies of `G_m` -/

section Split

variable {m : ℕ}

theorem embed_eq_src (c : Bool) (x : GNode m) : embed c x = sSource m ↔ x = gSource m := by
  rcases x with ⟨i, hi⟩ | ⟨i, hi⟩
  · simp only [embed, sSource, gSource, Sum.inl.injEq, Fin.ext_iff, Fin.val_last]
    split_ifs with h
    · simp; omega
    · simp; omega
  · simp [embed, sSource, gSource]

theorem embed_eq_embed (c c' : Bool) (x u : GNode m) (hu : u ≠ gSource m) :
    embed c' x = embed c u ↔ c' = c ∧ x = u := by
  rcases u with ⟨j, hj⟩ | ⟨j, hj⟩
  · have hjm : j < m := by
      by_contra h; apply hu; simp [gSource, Fin.ext_iff]; omega
    rcases x with ⟨i, hi⟩ | ⟨i, hi⟩
    · simp only [embed, hjm, dite_true]
      split_ifs with h
      · simp
      · simp; omega
    · simp [embed, hjm]
  · rcases x with ⟨i, hi⟩ | ⟨i, hi⟩
    · simp only [embed]; split_ifs <;> simp
    · simp [embed]

/-- Copy `c` of a splitter flow, as a flow on `G_m`. -/
def cp (φ : SArc m → ℚ) (c : Bool) : GArc m → ℚ := fun a => φ (c, a)

theorem s_outflow (φ : SArc m → ℚ) (c : Bool) (u : GNode m) (hu : u ≠ gSource m) :
    (splitter m).outflow φ (embed c u) = (countingNetwork m).outflow (cp φ c) u := by
  unfold Network.outflow
  rw [Finset.sum_filter, Finset.sum_filter, Fintype.sum_prod_type, Fintype.sum_bool]
  simp only [splitter, countingNetwork, cp]
  simp_rw [embed_eq_embed _ _ _ _ hu]
  cases c <;> simp <;> congr

theorem s_inflow (φ : SArc m → ℚ) (c : Bool) (u : GNode m) (hu : u ≠ gSource m) :
    (splitter m).inflow φ (embed c u) = (countingNetwork m).inflow (cp φ c) u := by
  unfold Network.inflow
  rw [Finset.sum_filter, Finset.sum_filter, Fintype.sum_prod_type, Fintype.sum_bool]
  simp only [splitter, countingNetwork, cp]
  simp_rw [embed_eq_embed _ _ _ _ hu]
  cases c <;> simp <;> congr

theorem s_netOut (φ : SArc m → ℚ) (c : Bool) (u : GNode m) (hu : u ≠ gSource m) :
    (splitter m).netOut φ (embed c u) = (countingNetwork m).netOut (cp φ c) u := by
  rw [Network.netOut, Network.netOut, s_outflow φ c u hu, s_inflow φ c u hu]

theorem s_outflow_src (φ : SArc m → ℚ) :
    (splitter m).outflow φ (sSource m) = (countingNetwork m).outflow (cp φ false) (gSource m) +
      (countingNetwork m).outflow (cp φ true) (gSource m) := by
  unfold Network.outflow
  rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_filter, Fintype.sum_prod_type,
    Fintype.sum_bool, add_comm]
  simp only [splitter, countingNetwork, cp]
  simp_rw [embed_eq_src]
  congr

theorem s_inflow_src (φ : SArc m → ℚ) :
    (splitter m).inflow φ (sSource m) = (countingNetwork m).inflow (cp φ false) (gSource m) +
      (countingNetwork m).inflow (cp φ true) (gSource m) := by
  unfold Network.inflow
  rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_filter, Fintype.sum_prod_type,
    Fintype.sum_bool, add_comm]
  simp only [splitter, countingNetwork, cp]
  simp_rw [embed_eq_src]
  congr

theorem s_netOut_src (φ : SArc m → ℚ) :
    (splitter m).netOut φ (sSource m) = (countingNetwork m).netOut (cp φ false) (gSource m) +
      (countingNetwork m).netOut (cp φ true) (gSource m) := by
  simp only [Network.netOut, s_outflow_src, s_inflow_src]
  ring

theorem s_totalCost (φ : SArc m → ℚ) :
    (splitter m).totalCost φ = (countingNetwork m).totalCost (cp φ false) +
      (countingNetwork m).totalCost (cp φ true) := by
  simp only [Network.totalCost, Fintype.sum_prod_type, Fintype.sum_bool, splitter,
    countingNetwork, cp]
  ring

theorem gSink_ne_gSource : gSink m ≠ gSource m := by simp [gSink, gSource]

theorem sinkOf_eq (c : Bool) : sinkOf m c = embed c (gSink m) := by
  cases c <;> rfl

theorem snode_cases (v : SNode m) : v = sSource m ∨ ∃ c u, u ≠ gSource m ∧ v = embed c u := by
  rcases v with ⟨⟩ | ⟨c, ⟨i, hi⟩ | ⟨i, hi⟩⟩
  · exact Or.inl rfl
  · right; refine ⟨c, .inl ⟨i, by omega⟩, by simp [gSource, Fin.ext_iff]; omega, ?_⟩
    simp [embed, hi]
  · right; exact ⟨c, .inr ⟨i, hi⟩, by simp [gSource], rfl⟩

/-- Each copy of a split flow is an `s_m → t_m` flow of `G_m`. -/
theorem split_copy (x : ℚ) (φ : SArc m → ℚ) (hφ : IsSplitFlow m x φ) (c : Bool) :
    (countingNetwork m).IsFlow (gSource m) (gSink m)
      ((countingNetwork m).netOut (cp φ c) (gSource m)) (cp φ c) := by
  obtain ⟨hfeas, _, hcons⟩ := hφ
  refine ⟨fun a => hfeas (c, a), rfl, fun u hu1 hu2 => ?_⟩
  rw [← s_netOut φ c u hu1]
  apply hcons
  · rw [Ne, embed_eq_src]; exact hu1
  · rw [show sinkA m = embed false (gSink m) from rfl, Ne,
      embed_eq_embed _ _ _ _ gSink_ne_gSource]
    rintro ⟨rfl, rfl⟩; exact hu2 rfl
  · rw [show sinkB m = embed true (gSink m) from rfl, Ne,
      embed_eq_embed _ _ _ _ gSink_ne_gSource]
    rintro ⟨rfl, rfl⟩; exact hu2 rfl

/-- Glue two `G_m` flows into a split flow. -/
def glue (ψA ψB : GArc m → ℚ) : SArc m → ℚ := fun p => if p.1 then ψB p.2 else ψA p.2

theorem cp_glue_false (ψA ψB : GArc m → ℚ) : cp (glue ψA ψB) false = ψA := by
  funext a; simp [cp, glue]

theorem cp_glue_true (ψA ψB : GArc m → ℚ) : cp (glue ψA ψB) true = ψB := by
  funext a; simp [cp, glue]

theorem glue_split {a b : ℚ} (ψA ψB : GArc m → ℚ)
    (hA : (countingNetwork m).IsFlow (gSource m) (gSink m) a ψA)
    (hB : (countingNetwork m).IsFlow (gSource m) (gSink m) b ψB) :
    IsSplitFlow m (a + b) (glue ψA ψB) := by
  refine ⟨fun p => ?_, ?_, fun v hv1 hv2 hv3 => ?_⟩
  · rcases p with ⟨_ | _, e⟩
    · exact hA.1 e
    · exact hB.1 e
  · rw [s_netOut_src, cp_glue_false, cp_glue_true, hA.2.1, hB.2.1]
  · rcases snode_cases v with rfl | ⟨c, u, hu, rfl⟩
    · exact absurd rfl hv1
    rw [s_netOut _ c u hu]
    have hu2 : u ≠ gSink m := by
      rintro rfl
      cases c
      · exact hv2 rfl
      · exact hv3 rfl
    cases c
    · rw [cp_glue_false]; exact hA.2.2 u hu hu2
    · rw [cp_glue_true]; exact hB.2.2 u hu hu2

end Split

theorem h0_bounds (N : ℕ) {x : ℚ} (hx0 : 0 ≤ x) (hxN : x ≤ 2 * N) :
    0 ≤ h0 x ∧ h0 x ≤ N ∧ 0 ≤ x - h0 x ∧ x - h0 x ≤ N := by
  have hz0 : 0 ≤ ⌊x / 2⌋ := Int.floor_nonneg.mpr (by linarith)
  have hzl : ((⌊x / 2⌋ : ℤ) : ℚ) ≤ x / 2 := Int.floor_le _
  have hzu : x / 2 < ((⌊x / 2⌋ : ℤ) : ℚ) + 1 := Int.lt_floor_add_one _
  have hz0' : (0 : ℚ) ≤ ((⌊x / 2⌋ : ℤ) : ℚ) := by exact_mod_cast hz0
  have hb : x - h0 x = h1 x := by linarith [h0_add_h1 x]
  rw [hb]
  unfold h0 h1
  set z : ℤ := ⌊x / 2⌋
  have hzN : z ≤ (N : ℤ) := by
    have : (z : ℚ) ≤ N := by linarith
    exact_mod_cast this
  rcases lt_or_eq_of_le hzN with h | h
  · have : (z : ℚ) + 1 ≤ N := by exact_mod_cast h
    refine ⟨by linarith [le_min (show 0 ≤ x - 2 * (z : ℚ) by linarith) zero_le_one], ?_, ?_, ?_⟩
    · linarith [min_le_right (x - 2 * (z : ℚ)) 1]
    · linarith [le_max_right (x - 2 * (z : ℚ) - 1) 0]
    · rcases le_total (x - 2 * (z : ℚ) - 1) 0 with h' | h'
      · rw [max_eq_right h']; linarith
      · rw [max_eq_left h']; linarith
  · have hzq : (z : ℚ) = N := by exact_mod_cast h
    have hρ : x - 2 * (z : ℚ) = 0 := by linarith
    rw [hρ, hzq]; norm_num

end L23

theorem lemma3_proof (m : ℕ) (hm : 1 ≤ m) (θ : ℚ) (hθ0 : 0 < θ) (hθ6 : θ < 6) (x : ℚ) (hx0 : 0 ≤ x)
    (hxK : x ≤ bigK m) (φ : SArc m → ℚ) (hφ : IsSplitFlow m x φ)
    (hmin : ∀ ψ, IsSplitFlow m x ψ → splitObjective m θ φ ≤ splitObjective m θ ψ) :
    (splitter m).inflow φ (sinkA m) = h0 x ∧ (splitter m).inflow φ (sinkB m) = h1 x := by
  have hN : (((2 ^ m : ℕ) : ℕ) : ℚ) = 2 ^ m := by push_cast; rfl
  have hxN : x ≤ 2 * ((2 ^ m : ℕ) : ℚ) := by
    rw [hN]; unfold bigK at hxK; rw [pow_succ] at hxK; linarith
  set A := (countingNetwork m).netOut (L23.cp φ false) (gSource m)
  set B := (countingNetwork m).netOut (L23.cp φ true) (gSource m)
  have hfA := L23.split_copy x φ hφ false
  have hfB := L23.split_copy x φ hφ true
  obtain ⟨cA, iA, A0, AN⟩ := L23.flow_lower A _ hfA
  obtain ⟨cB, iB, B0, BN⟩ := L23.flow_lower B _ hfB
  have hsum : A + B = x := by rw [← L23.s_netOut_src]; exact hφ.2.1
  have hinA : (splitter m).inflow φ (sinkA m) = A := by
    rw [show sinkA m = embed false (gSink m) from rfl, L23.s_inflow _ _ _ L23.gSink_ne_gSource, iA]
  have hinB : (splitter m).inflow φ (sinkB m) = B := by
    rw [show sinkB m = embed true (gSink m) from rfl, L23.s_inflow _ _ _ L23.gSink_ne_gSource, iB]
  have hobj : splitObjective m θ φ = (countingNetwork m).totalCost (L23.cp φ false) +
      (countingNetwork m).totalCost (L23.cp φ true) + θ * B := by
    rw [splitObjective, L23.s_totalCost, hinB]
  -- comparison flow at `h₀(x)`
  obtain ⟨a1, a2, a3, a4⟩ := L23.h0_bounds (2 ^ m) hx0 hxN
  rw [hN] at a2 a4
  obtain ⟨fa, ca⟩ := L23.optFlow_spec m a1 a2
  obtain ⟨fb, cb⟩ := L23.optFlow_spec m a3 a4
  have hψ := L23.glue_split _ _ fa fb
  rw [show h0 x + (x - h0 x) = x by ring] at hψ
  have hcmp := hmin _ hψ
  have hobjψ : splitObjective m θ (L23.glue (L23.optFlow m (h0 x)) (L23.optFlow m (x - h0 x))) =
      L23.cs (countD m) (h0 x) + L23.cs (countD m) (x - h0 x) + θ * (x - h0 x) := by
    rw [splitObjective, L23.s_totalCost, L23.cp_glue_false, L23.cp_glue_true, ca, cb,
      show sinkB m = embed true (gSink m) from rfl, L23.s_inflow _ _ _ L23.gSink_ne_gSource,
      L23.cp_glue_true, (L23.flow_lower _ _ fb).2.1]
  have hB : B = x - A := by linarith
  have key : A = h0 x := by
    refine L23.split_unique (2 ^ m) (countD m) (L23.countD_len m) (L23.gaps m hm) hθ0 hθ6 hx0
      A0 (by rw [hN]; exact AN) (by rw [← hB]; exact B0) (by rw [hN, ← hB]; exact BN) ?_
    rw [← hB]
    have := hobj ▸ hobjψ ▸ hcmp
    linarith
  refine ⟨by rw [hinA, key], ?_⟩
  rw [hinB, hB, key]; linarith [h0_add_h1 x]

/-! Checks: each proof has exactly the type of the corresponding statement in `Statements.lean`. -/

example : type_of% lemma2_first := lemma2_first_proof
example : type_of% lemma2_last := lemma2_last_proof
example : type_of% lemma2_gaps := lemma2_gaps_proof
example : type_of% lemma2_minCost := lemma2_minCost_proof
example : type_of% lemma2_maxFlow := lemma2_maxFlow_proof
example : type_of% lemma3 := lemma3_proof

#print axioms lemma2_first_proof
#print axioms lemma2_last_proof
#print axioms lemma2_gaps_proof
#print axioms lemma2_minCost_proof
#print axioms lemma2_maxFlow_proof
#print axioms lemma3_proof

end Bssg
