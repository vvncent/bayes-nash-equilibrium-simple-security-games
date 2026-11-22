import Mathlib
import BssgProofs.Statements
import BssgProofs.Proofs.Lemma23

/-!
# Lemmas 4, 5, 6 of simple-proof.md (LP facts and one gadget)
-/

set_option linter.unusedSectionVars false
set_option linter.deprecated false
set_option linter.style.longLine false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace Bssg

open Finset

namespace Gadget

/-! ## Lemma 4 -/

section L4

variable {I J : Type*} [DecidableEq I] [DecidableEq J] (L : AllocLP I J)

theorem split_sum (g : I × J → ℚ) (v : I → ℚ) (π : J → ℚ) :
    ∑ e ∈ L.E, (v e.1 + π e.2) * g e =
      (∑ i ∈ L.E.image Prod.fst, v i * L.rowSum g i) +
        ∑ j ∈ L.E.image Prod.snd, π j * L.colSum g j := by
  simp only [add_mul, sum_add_distrib, AllocLP.rowSum, AllocLP.colSum, mul_sum]
  congr 1
  · rw [← sum_fiberwise_of_maps_to (s := L.E) (t := L.E.image Prod.fst) (g := Prod.fst)
      (fun e he => mem_image_of_mem _ he)]
    refine sum_congr rfl fun i _ => sum_congr rfl fun e he => ?_
    rw [(mem_filter.1 he).2]
  · rw [← sum_fiberwise_of_maps_to (s := L.E) (t := L.E.image Prod.snd) (g := Prod.snd)
      (fun e he => mem_image_of_mem _ he)]
    refine sum_congr rfl fun i _ => sum_congr rfl fun e he => ?_
    rw [(mem_filter.1 he).2]

end L4

/-! ## Circulations and conformal cycles (for Lemma 5) -/

section Circ

variable {V α : Type*} [DecidableEq V] [DecidableEq α] (A : Finset α) (tl hd : α → V)

/-- Circulation on the arcs `A`: conservation at every node. -/
def IsCirc (x : α → ℚ) : Prop :=
  ∀ v, ∑ a ∈ A, (if tl a = v then x a else 0) = ∑ a ∈ A, (if hd a = v then x a else 0)

/-- Tail of a signed arc (`true` = forward). -/
def stl (s : α × Bool) : V := if s.2 then tl s.1 else hd s.1

/-- Head of a signed arc. -/
def shd (s : α × Bool) : V := if s.2 then hd s.1 else tl s.1

/-- Positive signed arcs of `x`. -/
def Pos (x : α → ℚ) : Finset (α × Bool) :=
  (A ×ˢ (univ : Finset Bool)).filter fun s => if s.2 then 0 < x s.1 else x s.1 < 0

/-- Signed indicator. -/
def sgn (s : α × Bool) (a : α) : ℤ := if a = s.1 then (if s.2 then 1 else -1) else 0

variable {A tl hd}

theorem mem_Pos {x : α → ℚ} {s : α × Bool} :
    s ∈ Pos A x ↔ s.1 ∈ A ∧ (if s.2 then 0 < x s.1 else x s.1 < 0) := by
  simp [Pos]

theorem pos_out {x : α → ℚ} (hx : IsCirc A tl hd x) {s : α × Bool} (hs : s ∈ Pos A x) :
    ∃ s' ∈ Pos A x, stl tl hd s' = shd tl hd s := by
  by_contra H
  push Not at H
  set v := shd tl hd s
  have h1 : ∀ a ∈ A, tl a = v → x a ≤ 0 := by
    intro a ha hta
    by_contra hlt; push Not at hlt
    exact H (a, true) (mem_Pos.2 ⟨ha, by simpa using hlt⟩) (by simp [stl, hta])
  have h2 : ∀ a ∈ A, hd a = v → 0 ≤ x a := by
    intro a ha hha
    by_contra hlt; push Not at hlt
    exact H (a, false) (mem_Pos.2 ⟨ha, by simpa using hlt⟩) (by simp [stl, hha])
  have hL : ∑ a ∈ A, (if tl a = v then x a else 0) ≤ 0 :=
    sum_nonpos fun a ha => by split_ifs with h <;> [exact h1 a ha h; exact le_rfl]
  have hR : 0 ≤ ∑ a ∈ A, (if hd a = v then x a else 0) :=
    sum_nonneg fun a ha => by split_ifs with h <;> [exact h2 a ha h; exact le_rfl]
  have hc := hx v
  have hL0 : ∑ a ∈ A, (if tl a = v then x a else 0) = 0 := by linarith
  have hR0 : ∑ a ∈ A, (if hd a = v then x a else 0) = 0 := by linarith
  obtain ⟨hsA, hsx⟩ := mem_Pos.1 hs
  rcases s with ⟨b, _ | _⟩
  · simp only [Bool.false_eq_true, ↓reduceIte] at hsx
    have hv : tl b = v := by simp [v, shd]
    have := (sum_eq_zero_iff_of_nonpos fun a ha => by
      split_ifs with h <;> [exact h1 a ha h; exact le_rfl]).1 hL0 b hsA
    rw [if_pos hv] at this; linarith
  · simp only [↓reduceIte] at hsx
    have hv : hd b = v := by simp [v, shd]
    have := (sum_eq_zero_iff_of_nonneg fun a ha => by
      split_ifs with h <;> [exact h2 a ha h; exact le_rfl]).1 hR0 b hsA
    rw [if_pos hv] at this; linarith

/-- A nonempty balanced set of positive signed arcs. -/
theorem exists_balanced {x : α → ℚ} (hx : IsCirc A tl hd x) (hne : ∃ a ∈ A, x a ≠ 0) :
    ∃ S : Finset (α × Bool), S.Nonempty ∧ S ⊆ Pos A x ∧ ∀ v,
      ∑ s ∈ S, (if stl tl hd s = v then (1 : ℤ) else 0) =
        ∑ s ∈ S, (if shd tl hd s = v then (1 : ℤ) else 0) := by
  classical
  set P := Pos A x
  obtain ⟨a0, ha0, hx0⟩ := hne
  obtain ⟨s0, hs0⟩ : ∃ s0, s0 ∈ P := by
    rcases lt_or_gt_of_ne hx0 with h | h
    · exact ⟨(a0, false), mem_Pos.2 ⟨ha0, by simpa using h⟩⟩
    · exact ⟨(a0, true), mem_Pos.2 ⟨ha0, by simpa using h⟩⟩
  let next : V → α × Bool := fun v =>
    if h : ∃ s ∈ P, stl tl hd s = v then h.choose else s0
  let succ : V → V := fun v => shd tl hd (next v)
  let RF : Finset V := P.image (shd tl hd)
  have hR : ∀ v ∈ RF, next v ∈ P ∧ stl tl hd (next v) = v := by
    intro v hv
    obtain ⟨s, hs, rfl⟩ := mem_image.1 hv
    have h := pos_out hx hs
    simp only [next]
    rw [dif_pos h]
    exact h.choose_spec
  have hRs : ∀ v ∈ RF, succ v ∈ RF := fun v hv => mem_image_of_mem _ (hR v hv).1
  have hv0 : shd tl hd s0 ∈ RF := mem_image_of_mem _ hs0
  have hit : ∀ k, succ^[k] (shd tl hd s0) ∈ RF := by
    intro k
    induction k with
    | zero => exact hv0
    | succ k ih => rw [Function.iterate_succ_apply']; exact hRs _ ih
  obtain ⟨i, hi, j, hj, hij, heq⟩ := exists_ne_map_eq_of_card_lt_of_maps_to
    (s := range (RF.card + 1)) (t := RF) (f := fun k => succ^[k] (shd tl hd s0))
    (by simp) (fun k _ => hit k)
  have hper : ∃ p ∈ RF, p ∈ Function.periodicPts succ := by
    rcases lt_or_gt_of_ne hij with h | h
    · refine ⟨succ^[i] (shd tl hd s0), hit i, Function.mk_mem_periodicPts (n := j - i)
        (by omega) ?_⟩
      show succ^[j - i] (succ^[i] _) = _
      rw [← Function.iterate_add_apply, Nat.sub_add_cancel h.le]; exact heq.symm
    · refine ⟨succ^[j] (shd tl hd s0), hit j, Function.mk_mem_periodicPts (n := i - j)
        (by omega) ?_⟩
      show succ^[i - j] (succ^[j] _) = _
      rw [← Function.iterate_add_apply, Nat.sub_add_cancel h.le]; exact heq
  obtain ⟨p, hpR, hpP⟩ := hper
  let C : Finset V := RF.filter (· ∈ Function.periodicPts succ)
  have hpC : p ∈ C := mem_filter.2 ⟨hpR, hpP⟩
  have hCmaps : ∀ u ∈ C, succ u ∈ C := by
    intro u hu
    obtain ⟨huR, huP⟩ := mem_filter.1 hu
    obtain ⟨n, hn, hpn⟩ := huP
    exact mem_filter.2 ⟨hRs u huR, n, hn, hpn.apply⟩
  have hCinj : Set.InjOn succ C := fun u hu w hw h =>
    (Function.bijOn_periodicPts succ).injOn (mem_filter.1 hu).2 (mem_filter.1 hw).2 h
  have hCsurj : Set.SurjOn succ C C := by
    intro w hw
    obtain ⟨u, hu, rfl⟩ := surj_on_of_inj_on_of_card_le (s := C) (t := C) (fun u _ => succ u)
      (fun u hu => hCmaps u hu) (fun u w hu hw h => hCinj hu hw h) le_rfl w hw
    exact ⟨u, hu, rfl⟩
  have hnextinj : Set.InjOn next C := by
    intro u hu w hw h
    have h1 := (hR u (mem_filter.1 hu).1).2
    have h2 := (hR w (mem_filter.1 hw).1).2
    rw [← h1, ← h2, h]
  refine ⟨C.image next, ⟨next p, mem_image_of_mem _ hpC⟩, ?_, ?_⟩
  · intro s hs
    obtain ⟨u, hu, rfl⟩ := mem_image.1 hs
    exact (hR u (mem_filter.1 hu).1).1
  · intro v
    rw [sum_image hnextinj, sum_image hnextinj]
    have e1 : ∀ u ∈ C, (if stl tl hd (next u) = v then (1 : ℤ) else 0) =
        if u = v then 1 else 0 := by
      intro u hu; rw [(hR u (mem_filter.1 hu).1).2]
    rw [sum_congr rfl e1]
    symm
    exact sum_nbij succ hCmaps hCinj hCsurj (fun u _ => rfl)


/-- The `±1` vector of a balanced positive set. -/
theorem exists_cycle {x : α → ℚ} (hx : IsCirc A tl hd x) (hne : ∃ a ∈ A, x a ≠ 0) :
    ∃ d : α → ℤ, (∀ a, |d a| ≤ 1) ∧ (∀ a ∈ A, d a ≠ 0 → 0 < (d a : ℚ) * x a) ∧
      IsCirc A tl hd (fun a => (d a : ℚ)) ∧ ∃ a ∈ A, d a ≠ 0 := by
  classical
  obtain ⟨S, hSne, hSP, hbal⟩ := exists_balanced hx hne
  let d : α → ℤ := fun a => ∑ s ∈ S, sgn s a
  have hval : ∀ a, d a = (if (a, true) ∈ S then 1 else 0) + (if (a, false) ∈ S then -1 else 0) := by
    intro a
    have : ∀ s : α × Bool, sgn s a = (if s = (a, true) then 1 else 0) +
        (if s = (a, false) then -1 else 0) := by
      rintro ⟨b, _ | _⟩ <;> by_cases h : a = b <;> simp [sgn, h, eq_comm]
    simp only [d, this, sum_add_distrib, sum_ite_eq']
  have hnot : ∀ a, ¬ ((a, true) ∈ S ∧ (a, false) ∈ S) := by
    rintro a ⟨h1, h2⟩
    have := (mem_Pos.1 (hSP h1)).2; have := (mem_Pos.1 (hSP h2)).2
    simp at *; linarith
  have hcases : ∀ a, (d a = 1 ∧ (a, true) ∈ S) ∨ (d a = -1 ∧ (a, false) ∈ S) ∨ d a = 0 := by
    intro a
    rw [hval a]
    by_cases h1 : (a, true) ∈ S <;> by_cases h2 : (a, false) ∈ S
    · exact absurd ⟨h1, h2⟩ (hnot a)
    · simp [h1, h2]
    · simp [h1, h2]
    · simp [h1, h2]
  refine ⟨d, ?_, ?_, ?_, ?_⟩
  · intro a
    rcases hcases a with ⟨h, _⟩ | ⟨h, _⟩ | h <;> rw [h] <;> norm_num
  · intro a _ ha
    rcases hcases a with ⟨h, hS⟩ | ⟨h, hS⟩ | h
    · have := (mem_Pos.1 (hSP hS)).2; simp at this; rw [h]; simpa using this
    · have := (mem_Pos.1 (hSP hS)).2; simp at this; rw [h]; push_cast; linarith
    · exact absurd h ha
  · intro v
    have key : ∀ s ∈ S, ∀ w : V,
        ∑ a ∈ A, (if tl a = w then (sgn s a : ℚ) else 0) -
          ∑ a ∈ A, (if hd a = w then (sgn s a : ℚ) else 0) =
        ((if stl tl hd s = w then 1 else 0 : ℤ) : ℚ) - ((if shd tl hd s = w then 1 else 0 : ℤ) : ℚ) := by
      rintro ⟨b, c⟩ hs w
      have hb : b ∈ A := (mem_Pos.1 (hSP hs)).1
      have e : ∀ P : α → Prop, [DecidablePred P] → ∑ a ∈ A, (if P a then (sgn (b, c) a : ℚ) else 0) =
          if P b then (if c then 1 else -1) else 0 := by
        intro P _
        have h0 := sum_ite_eq' A b (fun a => if P a then (if c then (1 : ℚ) else -1) else 0)
        rw [if_pos hb] at h0
        rw [← h0]
        refine sum_congr rfl fun a _ => ?_
        by_cases h : a = b
        · subst h; simp [sgn]
        · simp [sgn, h]
      rw [e (fun a => tl a = w), e (fun a => hd a = w)]
      cases c <;> simp [stl, shd] <;> split_ifs <;> norm_num
    have h1 : ∑ a ∈ A, (if tl a = v then ((d a : ℤ) : ℚ) else 0) -
        ∑ a ∈ A, (if hd a = v then ((d a : ℤ) : ℚ) else 0) =
        ∑ s ∈ S, (∑ a ∈ A, (if tl a = v then (sgn s a : ℚ) else 0) -
          ∑ a ∈ A, (if hd a = v then (sgn s a : ℚ) else 0)) := by
      simp only [d, Int.cast_sum, sum_sub_distrib]
      rw [sum_comm (s := S), sum_comm (s := S)]
      congr 1 <;> refine sum_congr rfl fun a _ => ?_ <;> split_ifs <;> simp
    have h2 := congrArg (fun z : ℤ => (z : ℚ)) (hbal v)
    simp only [Int.cast_sum] at h2
    rw [sum_congr rfl fun s hs => key s hs v, sum_sub_distrib, h2, sub_self] at h1
    linarith
  · obtain ⟨⟨b, c⟩, hs⟩ := hSne
    refine ⟨b, (mem_Pos.1 (hSP hs)).1, ?_⟩
    rcases hcases b with ⟨h, _⟩ | ⟨h, _⟩ | h
    · rw [h]; norm_num
    · rw [h]; norm_num
    · rw [hval b] at h
      have hn := hnot b
      cases c
      · by_cases h2 : (b, true) ∈ S <;> simp [hs, h2] at h hn
      · by_cases h2 : (b, false) ∈ S <;> simp [hs, h2] at h hn

/-- Conformal `±1` circulation with positive weight: by induction on the support. -/
theorem exists_good_cycle (w : α → ℤ) : ∀ (n : ℕ) (x : α → ℚ), (A.filter (x · ≠ 0)).card = n →
    IsCirc A tl hd x → 0 < ∑ a ∈ A, (w a : ℚ) * x a →
    ∃ d : α → ℤ, (∀ a, |d a| ≤ 1) ∧ (∀ a ∈ A, d a ≠ 0 → 0 < (d a : ℚ) * x a) ∧
      IsCirc A tl hd (fun a => (d a : ℚ)) ∧ 1 ≤ ∑ a ∈ A, w a * d a := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro x hn hx hT
  have hne : ∃ a ∈ A, x a ≠ 0 := by
    by_contra H; push Not at H
    rw [sum_eq_zero fun a ha => by rw [H a ha, mul_zero]] at hT
    exact lt_irrefl _ hT
  obtain ⟨d, hd1, hdc, hdcirc, a1, ha1, hda1⟩ := exists_cycle hx hne
  by_cases hTd : 1 ≤ ∑ a ∈ A, w a * d a
  · exact ⟨d, hd1, hdc, hdcirc, hTd⟩
  push Not at hTd
  have hTd' : (∑ a ∈ A, (w a : ℚ) * (d a : ℚ)) ≤ 0 := by
    have : ∑ a ∈ A, w a * d a ≤ 0 := by omega
    exact_mod_cast this
  have hsupp : (A.filter (d · ≠ 0)).Nonempty := ⟨a1, mem_filter.2 ⟨ha1, hda1⟩⟩
  set t := (A.filter (d · ≠ 0)).inf' hsupp (fun a => |x a|) with ht_def
  have hxpos : ∀ a ∈ A, d a ≠ 0 → 0 < |x a| := by
    intro a ha hda
    have := hdc a ha hda
    exact abs_pos.2 fun h => by rw [h, mul_zero] at this; exact lt_irrefl _ this
  have ht0 : 0 < t := (lt_inf'_iff _).2 fun a ha => hxpos a (mem_filter.1 ha).1 (mem_filter.1 ha).2
  have htle : ∀ a ∈ A, d a ≠ 0 → t ≤ |x a| := fun a ha hda => inf'_le _ (mem_filter.2 ⟨ha, hda⟩)
  obtain ⟨astar, hastar, hteq⟩ := exists_mem_eq_inf' hsupp (fun a => |x a|)
  let x' : α → ℚ := fun a => x a - t * d a
  have hdcases : ∀ a, d a = 1 ∨ d a = -1 ∨ d a = 0 := by
    intro a; have := abs_le.1 (hd1 a); omega
  -- sign transfer
  have htrans : ∀ a ∈ A, ∀ q : ℚ, 0 < q * x' a → 0 < q * x a := by
    intro a ha q hq
    rcases hdcases a with h | h | h
    · have hp := hdc a ha (by rw [h]; norm_num)
      rw [h] at hp; push_cast at hp
      have hle := htle a ha (by rw [h]; norm_num)
      rw [abs_of_pos (by linarith)] at hle
      simp only [x', h] at hq; push_cast at hq
      rcases lt_or_ge q 0 with hq0 | hq0
      · nlinarith
      · nlinarith
    · have hp := hdc a ha (by rw [h]; norm_num)
      rw [h] at hp; push_cast at hp
      have hle := htle a ha (by rw [h]; norm_num)
      rw [abs_of_neg (by linarith)] at hle
      simp only [x', h] at hq; push_cast at hq
      rcases lt_or_ge q 0 with hq0 | hq0
      · nlinarith
      · nlinarith
    · simpa [x', h] using hq
  have hcirc' : IsCirc A tl hd x' := by
    intro v
    have e : ∀ P : Prop, [Decidable P] → ∀ a, (if P then x' a else 0) =
        (if P then x a else 0) - t * (if P then (d a : ℚ) else 0) := by
      intro P _ a; split_ifs <;> simp [x']
    simp only [e, sum_sub_distrib, ← mul_sum]
    rw [hx v, hdcirc v]
  have hT' : 0 < ∑ a ∈ A, (w a : ℚ) * x' a := by
    have : ∑ a ∈ A, (w a : ℚ) * x' a =
        ∑ a ∈ A, (w a : ℚ) * x a - t * ∑ a ∈ A, (w a : ℚ) * (d a : ℚ) := by
      simp only [x', mul_sub, sum_sub_distrib, mul_sum]
      congr 1; refine sum_congr rfl fun a _ => by ring
    rw [this]; nlinarith
  have hlt : (A.filter (x' · ≠ 0)).card < n := by
    rw [← hn]
    apply card_lt_card
    rw [ssubset_iff_of_subset]
    · refine ⟨astar, ?_, ?_⟩
      · obtain ⟨hA, hdn⟩ := mem_filter.1 hastar
        exact mem_filter.2 ⟨hA, fun h => (hxpos astar hA hdn).ne' (by rw [h, abs_zero])⟩
      · intro h
        obtain ⟨hA, hdn⟩ := mem_filter.1 hastar
        apply (mem_filter.1 h).2
        have hp := hdc astar hA hdn
        show x astar - t * d astar = 0
        rw [← ht_def] at hteq
        rcases hdcases astar with h1 | h1 | h1
        · rw [h1] at hp ⊢; push_cast at hp ⊢
          rw [hteq, abs_of_pos (by linarith)]; ring
        · rw [h1] at hp ⊢; push_cast at hp ⊢
          rw [hteq, abs_of_neg (by linarith)]; ring
        · exact absurd h1 hdn
    · intro a ha
      obtain ⟨hA, hx'a⟩ := mem_filter.1 ha
      refine mem_filter.2 ⟨hA, fun h => hx'a ?_⟩
      have : d a = 0 := by
        by_contra hda; have := hxpos a hA hda; rw [h, abs_zero] at this; exact lt_irrefl _ this
      simp [x', h, this]
  obtain ⟨d', hd'1, hd'c, hd'circ, hd'T⟩ := ih _ hlt x' rfl hcirc' hT'
  exact ⟨d', hd'1, fun a ha hda => htrans a ha _ (hd'c a ha hda), hd'circ, hd'T⟩

end Circ

end Gadget


open Gadget in
theorem lemma4_proof {I J : Type*} [DecidableEq I] [DecidableEq J]
    (L : AllocLP I J) (f : I × J → ℚ) (hf : L.Feasible f) (v : I → ℚ) (π : J → ℚ)
    (hv : ∀ i, 0 ≤ v i) (hπ : ∀ j, 0 ≤ π j) (hπinf : ∀ j, L.cap j = none → π j = 0)
    (hdual : ∀ e ∈ L.E, L.coef e ≤ v e.1 + π e.2)
    (htight : ∀ e ∈ L.E, 0 < f e → L.coef e = v e.1 + π e.2)
    (hrow : ∀ i, 0 < v i → L.rowSum f i = L.mass i)
    (hcol : ∀ j c, L.cap j = some c → 0 < π j → L.colSum f j = c) :
    L.IsOptimal f := by
  classical
  let B : J → ℚ := fun j => match L.cap j with
    | some c => π j * c
    | none => 0
  let U : ℚ := (∑ i ∈ L.E.image Prod.fst, v i * L.mass i) + ∑ j ∈ L.E.image Prod.snd, B j
  have hle : ∀ g, L.Feasible g → L.objective g ≤ U := by
    intro g hg
    have h1 : L.objective g ≤ ∑ e ∈ L.E, (v e.1 + π e.2) * g e :=
      sum_le_sum fun e he => mul_le_mul_of_nonneg_right (hdual e he) (hg.1 e he)
    rw [split_sum] at h1
    refine h1.trans (add_le_add (sum_le_sum fun i _ => ?_) (sum_le_sum fun j _ => ?_))
    · exact mul_le_mul_of_nonneg_left (hg.2.1 i) (hv i)
    · simp only [B]
      rcases hc : L.cap j with _ | c
      · simp [hπinf j hc]
      · exact mul_le_mul_of_nonneg_left (hg.2.2 j c hc) (hπ j)
  have heq : L.objective f = U := by
    have h1 : L.objective f = ∑ e ∈ L.E, (v e.1 + π e.2) * f e := by
      refine sum_congr rfl fun e he => ?_
      rcases (hf.1 e he).lt_or_eq with h | h
      · rw [htight e he h]
      · rw [← h]; simp
    rw [h1, split_sum]
    congr 1
    · refine sum_congr rfl fun i _ => ?_
      rcases (hv i).lt_or_eq with h | h
      · rw [hrow i h]
      · rw [← h]; simp
    · refine sum_congr rfl fun j _ => ?_
      simp only [B]
      rcases hc : L.cap j with _ | c
      · simp [hπinf j hc]
      · rcases (hπ j).lt_or_eq with h | h
        · rw [hcol j c hc h]
        · rw [← h]; simp
  exact ⟨hf, fun g hg => (hle g hg).trans heq.ge⟩


namespace Gadget

/-! ## The network `D` of Lemma 5 -/

/-- Nodes of the network `D` of Lemma 5. -/
inductive DNode (I J : Type*)
  | r
  | q
  | buyer (i : I)
  | good (j : J)
  deriving DecidableEq

/-- Arcs of `D`. -/
inductive DArc (I J : Type*)
  | ra (i : I)
  | opt (e : I × J)
  | qa (j : J)
  | back
  deriving DecidableEq

section D

variable {I J : Type*} [DecidableEq I] [DecidableEq J] (L : AllocLP I J)

def dtl : DArc I J → DNode I J
  | .ra _ => .r
  | .opt e => .buyer e.1
  | .qa j => .good j
  | .back => .q

def dhd : DArc I J → DNode I J
  | .ra i => .buyer i
  | .opt e => .good e.2
  | .qa _ => .q
  | .back => .r

def arcs : Finset (DArc I J) :=
  (L.E.image Prod.fst).image DArc.ra ∪ L.E.image DArc.opt ∪ (L.E.image Prod.snd).image DArc.qa ∪
    {DArc.back}

theorem sum_arcs (F : DArc I J → ℚ) :
    ∑ a ∈ arcs L, F a = (∑ i ∈ L.E.image Prod.fst, F (.ra i)) + (∑ e ∈ L.E, F (.opt e)) +
      (∑ j ∈ L.E.image Prod.snd, F (.qa j)) + F .back := by
  unfold arcs
  have d3 : Disjoint ((L.E.image Prod.fst).image DArc.ra) (L.E.image DArc.opt) := by
    rw [disjoint_left]; intro a ha; simp only [mem_image] at ha ⊢; aesop
  have d2 : Disjoint ((L.E.image Prod.fst).image DArc.ra ∪ L.E.image DArc.opt)
      ((L.E.image Prod.snd).image DArc.qa) := by
    rw [disjoint_left]; intro a ha; simp only [mem_union, mem_image] at ha ⊢; aesop
  have d1 : Disjoint ((L.E.image Prod.fst).image DArc.ra ∪ L.E.image DArc.opt ∪
      (L.E.image Prod.snd).image DArc.qa) {DArc.back} := by
    rw [disjoint_left]; intro a ha; simp only [mem_union, mem_image, mem_singleton] at ha ⊢; aesop
  rw [sum_union d1, sum_union d2, sum_union d3, sum_singleton,
    sum_image (s := L.E.image Prod.fst) (g := DArc.ra) (fun a _ b _ h => by cases h; rfl),
    sum_image (s := L.E) (g := DArc.opt) (fun a _ b _ h => by cases h; rfl),
    sum_image (s := L.E.image Prod.snd) (g := DArc.qa) (fun a _ b _ h => by cases h; rfl)]

variable {L}

theorem rowSum_eq_ite (z : I × J → ℚ) (i : I) :
    L.rowSum z i = if i ∈ L.E.image Prod.fst then L.rowSum z i else 0 := by
  split_ifs with h
  · rfl
  · refine sum_eq_zero fun e he => absurd ?_ h
    obtain ⟨he2, rfl⟩ := mem_filter.1 he
    exact mem_image_of_mem _ he2

theorem colSum_eq_ite (z : I × J → ℚ) (j : J) :
    L.colSum z j = if j ∈ L.E.image Prod.snd then L.colSum z j else 0 := by
  split_ifs with h
  · rfl
  · refine sum_eq_zero fun e he => absurd ?_ h
    obtain ⟨he2, rfl⟩ := mem_filter.1 he
    exact mem_image_of_mem _ he2

/-- The circulation induced by a vector on the options. -/
def lift (z : I × J → ℚ) : DArc I J → ℚ
  | .ra i => L.rowSum z i
  | .opt e => z e
  | .qa j => L.colSum z j
  | .back => ∑ e ∈ L.E, z e

theorem sum_rows (z : I × J → ℚ) : ∑ i ∈ L.E.image Prod.fst, L.rowSum z i = ∑ e ∈ L.E, z e :=
  sum_fiberwise_of_maps_to (fun e he => mem_image_of_mem _ he) z

theorem sum_cols (z : I × J → ℚ) : ∑ j ∈ L.E.image Prod.snd, L.colSum z j = ∑ e ∈ L.E, z e :=
  sum_fiberwise_of_maps_to (fun e he => mem_image_of_mem _ he) z

theorem lift_circ (z : I × J → ℚ) : IsCirc (arcs L) dtl dhd (lift (L := L) z) := by
  intro v
  rw [sum_arcs, sum_arcs]
  cases v with
  | r => simp [dtl, dhd, lift, sum_rows]
  | q => simp [dtl, dhd, lift, sum_cols]
  | buyer i =>
    simp only [dtl, dhd, lift, reduceCtorEq, if_false, sum_const_zero, add_zero, zero_add,
      DNode.buyer.injEq, sum_ite_eq']
    rw [← rowSum_eq_ite]; rw [AllocLP.rowSum, sum_filter]
  | good j =>
    simp only [dtl, dhd, lift, reduceCtorEq, if_false, sum_const_zero, add_zero, zero_add,
      DNode.good.injEq, sum_ite_eq']
    rw [← colSum_eq_ite]; rw [AllocLP.colSum, sum_filter]

theorem circ_buyer {y : DArc I J → ℚ} (hy : IsCirc (arcs L) dtl dhd y) (i : I)
    (hi : i ∈ L.E.image Prod.fst) : y (.ra i) = ∑ e ∈ L.E.filter (fun e => e.1 = i), y (.opt e) := by
  have := hy (.buyer i)
  rw [sum_arcs, sum_arcs] at this
  simp only [dtl, dhd, reduceCtorEq, if_false, sum_const_zero, add_zero, zero_add,
      DNode.buyer.injEq, sum_ite_eq', if_pos hi] at this
  rw [sum_filter, this]

theorem circ_good {y : DArc I J → ℚ} (hy : IsCirc (arcs L) dtl dhd y) (j : J)
    (hj : j ∈ L.E.image Prod.snd) : y (.qa j) = ∑ e ∈ L.E.filter (fun e => e.2 = j), y (.opt e) := by
  have := hy (.good j)
  rw [sum_arcs, sum_arcs] at this
  simp only [dtl, dhd, reduceCtorEq, if_false, sum_const_zero, add_zero, zero_add,
      DNode.good.injEq, sum_ite_eq', if_pos hj] at this
  rw [sum_filter, ← this]

/-- Trade weights. -/
def tw : DArc I J → ℤ
  | .ra _ => 1
  | .qa j => if (L.cap j).isSome then 1 else 0
  | _ => 0

theorem weight_circ {y : DArc I J → ℚ} (hy : IsCirc (arcs L) dtl dhd y) :
    ∑ a ∈ arcs L, ((tw (L := L) a : ℤ) : ℚ) * y a =
      ∑ e ∈ L.E, (1 + if (L.cap e.2).isSome then 1 else 0) * y (.opt e) := by
  rw [sum_arcs]
  simp only [tw, Int.cast_one, one_mul, Int.cast_zero, zero_mul, sum_const_zero, add_zero]
  rw [sum_congr rfl fun i hi => circ_buyer hy i hi,
    sum_congr rfl fun j hj => congrArg (_ * ·) (circ_good hy j hj)]
  rw [sum_fiberwise_of_maps_to (fun e he => mem_image_of_mem _ he) (fun e => y (.opt e))]
  have : ∑ j ∈ L.E.image Prod.snd, ((if (L.cap j).isSome then 1 else 0 : ℤ) : ℚ) *
      ∑ e ∈ L.E.filter (fun e => e.2 = j), y (.opt e) =
      ∑ e ∈ L.E, (if (L.cap e.2).isSome then 1 else 0) * y (.opt e) := by
    rw [← sum_fiberwise_of_maps_to (s := L.E) (t := L.E.image Prod.snd) (g := Prod.snd)
      (fun e he => mem_image_of_mem _ he)]
    refine sum_congr rfl fun j _ => ?_
    rw [mul_sum]
    refine sum_congr rfl fun e he => ?_
    rw [(mem_filter.1 he).2]; push_cast; rfl
  rw [this, ← sum_add_distrib]
  refine sum_congr rfl fun e _ => by ring

theorem mem_arcs_ra {i : I} (h : i ∈ L.E.image Prod.fst) : DArc.ra i ∈ arcs L := by
  simp only [arcs, mem_union, mem_image, mem_singleton]; left; left; left; exact ⟨i, mem_image.1 h, rfl⟩

theorem mem_arcs_opt {e : I × J} (h : e ∈ L.E) : DArc.opt e ∈ arcs L := by
  simp only [arcs, mem_union, mem_image, mem_singleton]; left; left; right; exact ⟨e, h, rfl⟩

theorem mem_arcs_qa {j : J} (h : j ∈ L.E.image Prod.snd) : DArc.qa j ∈ arcs L := by
  simp only [arcs, mem_union, mem_image, mem_singleton]; left; right; exact ⟨j, mem_image.1 h, rfl⟩

theorem step_le {F G t hi : ℚ} {dd : ℤ} (hd : |dd| ≤ 1) (hc : dd ≠ 0 → 0 < (dd : ℚ) * (G - F))
    (ht : dd ≠ 0 → t ≤ |G - F|) (ht0 : 0 ≤ t) (hF : F ≤ hi) (hG : G ≤ hi) : F + t * dd ≤ hi := by
  have : dd = 1 ∨ dd = -1 ∨ dd = 0 := by have := abs_le.1 hd; omega
  rcases this with h | h | h
  · have h1 := hc (by rw [h]; norm_num); have h2 := ht (by rw [h]; norm_num)
    rw [h] at h1 ⊢; push_cast at h1 ⊢; rw [abs_of_pos (by linarith)] at h2; linarith
  · have h1 := hc (by rw [h]; norm_num); have h2 := ht (by rw [h]; norm_num)
    rw [h] at h1 ⊢; push_cast at h1 ⊢; rw [abs_of_neg (by linarith)] at h2; linarith
  · rw [h]; simpa using hF

theorem step_ge {F G t lo : ℚ} {dd : ℤ} (hd : |dd| ≤ 1) (hc : dd ≠ 0 → 0 < (dd : ℚ) * (G - F))
    (ht : dd ≠ 0 → t ≤ |G - F|) (ht0 : 0 ≤ t) (hF : lo ≤ F) (hG : lo ≤ G) : lo ≤ F + t * dd := by
  have : dd = 1 ∨ dd = -1 ∨ dd = 0 := by have := abs_le.1 hd; omega
  rcases this with h | h | h
  · have h1 := hc (by rw [h]; norm_num); have h2 := ht (by rw [h]; norm_num)
    rw [h] at h1 ⊢; push_cast at h1 ⊢; rw [abs_of_pos (by linarith)] at h2; nlinarith
  · have h1 := hc (by rw [h]; norm_num); have h2 := ht (by rw [h]; norm_num)
    rw [h] at h1 ⊢; push_cast at h1 ⊢; rw [abs_of_neg (by linarith)] at h2; linarith
  · rw [h]; simpa using hF

end D

end Gadget

open Gadget in
theorem lemma5_proof {I J : Type*} [DecidableEq I] [DecidableEq J]
    (L : AllocLP I J) (M : ℚ) (κ : I × J → ℚ) (hκ0 : ∀ e ∈ L.E, 0 ≤ κ e)
    (hcoef : ∀ e ∈ L.E, L.coef e = M * (1 + if (L.cap e.2).isSome then 1 else 0) - κ e)
    (hM : (∑ e ∈ L.E, κ e) < M) (f : I × J → ℚ) (hf : L.IsOptimal f) :
    ∀ g, L.Feasible g → L.trade g ≤ L.trade f := by
  classical
  intro g hg
  by_contra hlt
  push Not at hlt
  let z : I × J → ℚ := fun e => g e - f e
  let x := lift (L := L) z
  have hx : IsCirc (arcs L) dtl dhd x := lift_circ z
  have hxra : ∀ i, x (.ra i) = L.rowSum g i - L.rowSum f i := by
    intro i; simp [x, lift, z, AllocLP.rowSum, sum_sub_distrib]
  have hxqa : ∀ j, x (.qa j) = L.colSum g j - L.colSum f j := by
    intro j; simp [x, lift, z, AllocLP.colSum, sum_sub_distrib]
  have hT : 0 < ∑ a ∈ arcs L, ((tw (L := L) a : ℤ) : ℚ) * x a := by
    rw [weight_circ hx]
    have : ∑ e ∈ L.E, (1 + if (L.cap e.2).isSome then 1 else 0) * x (.opt e) =
        L.trade g - L.trade f := by
      simp only [AllocLP.trade, x, lift, z, add_mul, one_mul, sum_add_distrib, ite_mul, zero_mul,
        sum_filter, mul_sub, sum_sub_distrib]
    rw [this]; linarith
  obtain ⟨d, hd1, hdc, hdcirc, hdT⟩ := exists_good_cycle (tw (L := L)) _ x rfl hx hT
  have hsupp : ((arcs L).filter (d · ≠ 0)).Nonempty := by
    by_contra H
    rw [not_nonempty_iff_eq_empty, filter_eq_empty_iff] at H
    rw [sum_eq_zero fun a ha => by rw [not_not.1 (H ha), mul_zero]] at hdT
    exact absurd hdT (by norm_num)
  set t := ((arcs L).filter (d · ≠ 0)).inf' hsupp (fun a => |x a|) with ht_def
  have hxpos : ∀ a ∈ arcs L, d a ≠ 0 → 0 < |x a| := by
    intro a ha hda
    have := hdc a ha hda
    exact abs_pos.2 fun h => by rw [h, mul_zero] at this; exact lt_irrefl _ this
  have ht0 : 0 < t := (lt_inf'_iff _).2 fun a ha => hxpos a (mem_filter.1 ha).1 (mem_filter.1 ha).2
  have htle : ∀ a ∈ arcs L, d a ≠ 0 → t ≤ |x a| := fun a ha hda =>
    inf'_le _ (mem_filter.2 ⟨ha, hda⟩)
  let f' : I × J → ℚ := fun e => f e + t * d (.opt e)
  have hrow' : ∀ i, L.rowSum f' i = L.rowSum f i + t * ∑ e ∈ L.E.filter (fun e => e.1 = i),
      (d (.opt e) : ℚ) := by
    intro i; simp [f', AllocLP.rowSum, sum_add_distrib, mul_sum]
  have hcol' : ∀ j, L.colSum f' j = L.colSum f j + t * ∑ e ∈ L.E.filter (fun e => e.2 = j),
      (d (.opt e) : ℚ) := by
    intro j; simp [f', AllocLP.colSum, sum_add_distrib, mul_sum]
  have hfeas : L.Feasible f' := by
    refine ⟨fun e he => ?_, fun i => ?_, fun j c hc => ?_⟩
    · have ha := mem_arcs_opt he
      exact step_ge (hd1 _) (hdc _ ha) (htle _ ha) ht0.le (hf.1.1 e he) (hg.1 e he)
    · by_cases hi : i ∈ L.E.image Prod.fst
      · have ha := mem_arcs_ra hi
        have e1 := circ_buyer hdcirc i hi
        rw [hrow', ← e1]
        refine step_le (hd1 _) ?_ ?_ ht0.le (hf.1.2.1 i) (hg.2.1 i)
        · intro h; rw [← hxra]; exact hdc _ ha h
        · intro h; rw [← hxra]; exact htle _ ha h
      · rw [hrow']
        have : L.E.filter (fun e => e.1 = i) = ∅ := by
          rw [filter_eq_empty_iff]; intro e he h; exact hi (h ▸ mem_image_of_mem _ he)
        rw [this, sum_empty, mul_zero, add_zero]; exact hf.1.2.1 i
    · by_cases hj : j ∈ L.E.image Prod.snd
      · have ha := mem_arcs_qa hj
        have e1 := circ_good hdcirc j hj
        rw [hcol', ← e1]
        refine step_le (hd1 _) ?_ ?_ ht0.le (hf.1.2.2 j c hc) (hg.2.2 j c hc)
        · intro h; rw [← hxqa]; exact hdc _ ha h
        · intro h; rw [← hxqa]; exact htle _ ha h
      · rw [hcol']
        have : L.E.filter (fun e => e.2 = j) = ∅ := by
          rw [filter_eq_empty_iff]; intro e he h; exact hj (h ▸ mem_image_of_mem _ he)
        rw [this, sum_empty, mul_zero, add_zero]; exact hf.1.2.2 j c hc
  have hobj : L.objective f' = L.objective f + t * ∑ e ∈ L.E, L.coef e * (d (.opt e) : ℚ) := by
    simp [AllocLP.objective, f', mul_add, sum_add_distrib, mul_sum]
    refine sum_congr rfl fun e _ => by ring
  have hW : (1 : ℚ) ≤ ∑ e ∈ L.E, (1 + if (L.cap e.2).isSome then 1 else 0) * (d (.opt e) : ℚ) := by
    rw [← weight_circ hdcirc]; exact_mod_cast hdT
  have hK : ∑ e ∈ L.E, κ e * (d (.opt e) : ℚ) ≤ ∑ e ∈ L.E, κ e := by
    refine sum_le_sum fun e he => ?_
    have := (abs_le.1 (hd1 (.opt e))).2
    have : (d (.opt e) : ℚ) ≤ 1 := by exact_mod_cast this
    nlinarith [hκ0 e he]
  have hsum : ∑ e ∈ L.E, L.coef e * (d (.opt e) : ℚ) =
      M * ∑ e ∈ L.E, (1 + if (L.cap e.2).isSome then 1 else 0) * (d (.opt e) : ℚ) -
        ∑ e ∈ L.E, κ e * (d (.opt e) : ℚ) := by
    rw [mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun e he => ?_
    rw [hcoef e he]; ring
  have hM0 : 0 ≤ ∑ e ∈ L.E, κ e := sum_nonneg hκ0
  have hgain : 0 < ∑ e ∈ L.E, L.coef e * (d (.opt e) : ℚ) := by
    rw [hsum]; nlinarith
  have := hf.2 f' hfeas
  rw [hobj] at this
  nlinarith


/-! ## Lemma 6 (one gadget) -/

namespace Gadget

section Splitter
variable (m : ℕ)

theorem tail_ne_head (e : SArc m) : (splitter m).tail e ≠ (splitter m).head e := by
  rcases e with ⟨c, _ | ⟨j, r⟩⟩
  · simp [splitter, embed, gTail, gHead]; by_cases h : 0 < m <;> simp [h]
  · fin_cases r <;> simp [splitter, embed, gTail, gHead] <;> (try split) <;> simp [Fin.ext_iff]

theorem head_ne_source (e : SArc m) : (splitter m).head e ≠ sSource m := by
  rcases e with ⟨c, _ | ⟨j, r⟩⟩
  · simp [splitter, embed, gTail, gHead, sSource]
  · fin_cases r <;> simp [splitter, embed, gTail, gHead, sSource]

theorem tail_ne_sink (e : SArc m) :
    (splitter m).tail e ≠ sinkA m ∧ (splitter m).tail e ≠ sinkB m := by
  rcases e with ⟨c, _ | ⟨j, r⟩⟩
  · simp [splitter, embed, gTail, gHead, sinkA, sinkB]; by_cases h : 0 < m <;> simp [h]
  · fin_cases r <;> simp [splitter, embed, gTail, gHead, sinkA, sinkB] <;> (try split) <;>
      simp

theorem source_ne_sinkA : sSource m ≠ sinkA m := by simp [sSource, sinkA]
theorem source_ne_sinkB : sSource m ≠ sinkB m := by simp [sSource, sinkB]
theorem sinkA_ne_sinkB : sinkA m ≠ sinkB m := by simp [sinkA, sinkB]

abbrev Opt (m : ℕ) := SNode m × (SArc m ⊕ GadgetPort)

theorem sum_gadgetE (F : Opt m → ℚ) :
    ∑ o ∈ gadgetE m, F o = (∑ e, F ((splitter m).tail e, .inl e)) +
      (∑ e, F ((splitter m).head e, .inl e)) + F (sSource m, .inr .p) +
      F (sinkA m, .inr .πa) + F (sinkB m, .inr .πb) := by
  unfold gadgetE
  have d2 : Disjoint (univ.image fun e : SArc m => ((splitter m).tail e, (Sum.inl e : SArc m ⊕ GadgetPort)))
      (univ.image fun e : SArc m => ((splitter m).head e, (Sum.inl e : SArc m ⊕ GadgetPort))) := by
    rw [disjoint_left]
    intro o h1 h2
    simp only [mem_image, mem_univ, true_and] at h1 h2
    obtain ⟨e, rfl⟩ := h1
    obtain ⟨e', h⟩ := h2
    simp only [Prod.mk.injEq, Sum.inl.injEq] at h
    obtain ⟨h1, h2⟩ := h
    subst h2
    exact tail_ne_head m _ h1.symm
  have d1 : Disjoint ((univ.image fun e : SArc m => ((splitter m).tail e, (Sum.inl e : SArc m ⊕ GadgetPort))) ∪
      (univ.image fun e : SArc m => ((splitter m).head e, (Sum.inl e : SArc m ⊕ GadgetPort))))
      {(sSource m, .inr .p), (sinkA m, .inr .πa), (sinkB m, .inr .πb)} := by
    rw [disjoint_left]
    intro o h1 h2
    simp only [mem_union, mem_image, mem_univ, true_and] at h1
    simp only [mem_insert, mem_singleton] at h2
    rcases h1 with ⟨e, rfl⟩ | ⟨e, rfl⟩ <;> rcases h2 with h | h | h <;> simp at h
  rw [sum_union d1, sum_union d2, sum_image (fun a _ b _ h => by simp at h; exact h.2),
    sum_image (fun a _ b _ h => by simp at h; exact h.2), sum_insert (by simp), sum_insert (by simp),
    sum_singleton]
  ring

theorem tail_mem (e : SArc m) : ((splitter m).tail e, (.inl e : SArc m ⊕ GadgetPort)) ∈ gadgetE m := by
  simp [gadgetE]

theorem head_mem (e : SArc m) : ((splitter m).head e, (.inl e : SArc m ⊕ GadgetPort)) ∈ gadgetE m := by
  simp [gadgetE]

theorem p_mem : (sSource m, (.inr .p : SArc m ⊕ GadgetPort)) ∈ gadgetE m := by simp [gadgetE]
theorem πa_mem : (sinkA m, (.inr .πa : SArc m ⊕ GadgetPort)) ∈ gadgetE m := by simp [gadgetE]
theorem πb_mem : (sinkB m, (.inr .πb : SArc m ⊕ GadgetPort)) ∈ gadgetE m := by simp [gadgetE]

theorem forall_gadgetE {P : Opt m → Prop} (h1 : ∀ e, P ((splitter m).tail e, .inl e))
    (h2 : ∀ e, P ((splitter m).head e, .inl e)) (h3 : P (sSource m, .inr .p))
    (h4 : P (sinkA m, .inr .πa)) (h5 : P (sinkB m, .inr .πb)) : ∀ o ∈ gadgetE m, P o := by
  intro o ho
  simp only [gadgetE, mem_union, mem_image, mem_univ, true_and, mem_insert, mem_singleton] at ho
  rcases ho with (⟨e, rfl⟩ | ⟨e, rfl⟩) | rfl | rfl | rfl
  exacts [h1 e, h2 e, h3, h4, h5]

end Splitter

section GLP
variable (m : ℕ) (c x αa αb : ℚ)


theorem g_rowSum (g : Opt m → ℚ) (u : SNode m) :
    (gadgetLP m c x αa αb).rowSum g u = (splitter m).outflow (fun e => g ((splitter m).tail e, .inl e)) u +
      (∑ e ∈ univ.filter (fun e => (splitter m).head e = u), g ((splitter m).head e, .inl e)) +
      (if sSource m = u then g (sSource m, .inr .p) else 0) +
      (if sinkA m = u then g (sinkA m, .inr .πa) else 0) +
      (if sinkB m = u then g (sinkB m, .inr .πb) else 0) := by
  unfold AllocLP.rowSum Network.outflow
  rw [sum_filter, sum_filter, sum_filter]
  exact sum_gadgetE m (fun o => if o.1 = u then g o else 0)

theorem g_colSum_arc (g : Opt m → ℚ) (e0 : SArc m) :
    (gadgetLP m c x αa αb).colSum g (.inl e0) = g ((splitter m).tail e0, .inl e0) + g ((splitter m).head e0, .inl e0) := by
  unfold AllocLP.colSum
  rw [sum_filter]
  rw [show (gadgetLP m c x αa αb).E = gadgetE m from rfl, sum_gadgetE]
  simp

theorem g_colSum_p (g : Opt m → ℚ) :
    (gadgetLP m c x αa αb).colSum g (.inr .p) = g (sSource m, .inr .p) := by
  unfold AllocLP.colSum
  rw [sum_filter]
  rw [show (gadgetLP m c x αa αb).E = gadgetE m from rfl, sum_gadgetE]
  simp

theorem g_objective (g : Opt m → ℚ) :
    (gadgetLP m c x αa αb).objective g = (∑ e, (2 * bigM m - gCost e.2) * g ((splitter m).tail e, .inl e)) +
      (∑ e, 2 * bigM m * g ((splitter m).head e, .inl e)) + 2 * bigM m * g (sSource m, .inr .p) +
      αa * g (sinkA m, .inr .πa) + αb * g (sinkB m, .inr .πb) := by
  unfold AllocLP.objective
  rw [show (gadgetLP m c x αa αb).E = gadgetE m from rfl, sum_gadgetE]
  have h2 : ∀ e : SArc m, (gadgetLP m c x αa αb).coef ((splitter m).head e, .inl e) = 2 * bigM m := by
    intro e
    show gadgetCoef m αa αb ((splitter m).head e, .inl e) = _
    simp only [gadgetCoef]; rw [if_neg (tail_ne_head m e)]
  have h1 : ∀ e : SArc m, (gadgetLP m c x αa αb).coef ((splitter m).tail e, .inl e) = 2 * bigM m - gCost e.2 := by
    intro e
    show gadgetCoef m αa αb ((splitter m).tail e, .inl e) = _
    simp only [gadgetCoef]; simp
  simp only [h1, h2]
  rfl

theorem g_trade (g : Opt m → ℚ) :
    (gadgetLP m c x αa αb).trade g = (∑ u, (gadgetLP m c x αa αb).rowSum g u) + (∑ e, (gadgetLP m c x αa αb).colSum g (.inl e)) +
      (gadgetLP m c x αa αb).colSum g (.inr .p) := by
  unfold AllocLP.trade
  have hr : ∑ u, (gadgetLP m c x αa αb).rowSum g u = ∑ o ∈ (gadgetLP m c x αa αb).E, g o := by
    unfold AllocLP.rowSum
    exact sum_fiberwise _ _ _
  rw [hr, sum_filter]
  simp only [g_colSum_arc, g_colSum_p]
  rw [show (gadgetLP m c x αa αb).E = gadgetE m from rfl, sum_gadgetE m (fun o => if ((gadgetLP m c x αa αb).cap o.2).isSome then g o else 0)]
  simp only [sum_add_distrib]
  simp [gadgetLP]
  ring

end GLP
theorem outCap_source (k : ℕ) : ∑ e : SArc (k+1), (if (splitter (k+1)).tail e = sSource (k+1) then gCap e.2 else 0) = bigK (k+1) := by
  simp only [Fintype.sum_prod_type, Fintype.sum_option, Fin.sum_univ_four, Fintype.sum_bool]
  simp [splitter, embed, gTail, sSource, gCap]
  rw [Fin.sum_univ_castSucc]
  have h1 : ∀ x : Fin k, ¬ k ≤ (x : ℕ) := fun x => not_le.2 x.isLt
  have h2 : ∀ x : Fin k, ¬ k < (x : ℕ) := fun x => not_lt.2 x.isLt.le
  simp [bigK, h1, h2]
  ring

theorem sum_three_pow (k : ℕ) : 2 * ∑ x : Fin k, (3 : ℚ) ^ ((x : ℕ) + 1) = 3 ^ (k + 1) - 3 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Fin.sum_univ_castSucc, mul_add]
    simp only [Fin.coe_castSucc, Fin.val_last]
    rw [ih, pow_succ (3 : ℚ) (k + 1)]; ring

theorem sum_gCost (k : ℕ) : ∑ e : SArc k, gCost e.2 = 2 * 3 ^ (k+1) - 6 := by
  simp only [Fintype.sum_prod_type, Fintype.sum_option, Fin.sum_univ_four, Fintype.sum_bool]
  simp [gCost]
  have := sum_three_pow k
  simp only [← two_mul, ← mul_sum] 
  linarith
def flow0 (k : ℕ) (y : ℚ) (e : SArc (k+1)) : ℚ :=
  match e.2 with
  | none => 0
  | some (j, _) => if j = Fin.last k then y / 4 else 0

theorem flow0_netOut (k : ℕ) (y : ℚ) (u : SNode (k+1)) : (splitter (k+1)).netOut (flow0 k y) u =
    (if sSource (k+1) = u then y else 0) - (if sinkA (k+1) = u then y / 2 else 0) -
      (if sinkB (k+1) = u then y / 2 else 0) := by
  simp only [Network.netOut, Network.outflow, Network.inflow, sum_filter]
  simp only [Fintype.sum_prod_type, Fintype.sum_option, Fin.sum_univ_four, Fintype.sum_bool]
  simp only [Fin.sum_univ_castSucc]
  have hne : ∀ i : Fin k, Fin.castSucc i ≠ Fin.last k := fun i => Fin.castSucc_ne_last i
  simp [splitter, embed, gTail, gHead, flow0, hne, sSource, sinkA, sinkB]
  rcases u with _ | ⟨_ | _, _ | i⟩ <;> simp <;> ring_nf <;> split_ifs <;> ring

section Struct
variable (m : ℕ)

theorem inflow_source (φ : SArc m → ℚ) : (splitter m).inflow φ (sSource m) = 0 :=
  sum_eq_zero fun e he => absurd (mem_filter.1 he).2 (head_ne_source m e)

theorem outflow_sinkA (φ : SArc m → ℚ) : (splitter m).outflow φ (sinkA m) = 0 :=
  sum_eq_zero fun e he => absurd (mem_filter.1 he).2 (tail_ne_sink m e).1

theorem outflow_sinkB (φ : SArc m → ℚ) : (splitter m).outflow φ (sinkB m) = 0 :=
  sum_eq_zero fun e he => absurd (mem_filter.1 he).2 (tail_ne_sink m e).2

theorem inCap_source : inCap m (sSource m) = 0 := inflow_source m _

theorem sum_netOut (φ : SArc m → ℚ) : ∑ u, (splitter m).netOut φ u = 0 := by
  simp only [Network.netOut, sum_sub_distrib, Network.outflow, Network.inflow]
  rw [sum_fiberwise, sum_fiberwise, sub_self]

theorem split_AB {y : ℚ} {φ : SArc m → ℚ} (h : IsSplitFlow m y φ) :
    (splitter m).inflow φ (sinkA m) + (splitter m).inflow φ (sinkB m) = y := by
  have hs := sum_netOut m φ
  have e : ∀ u, (splitter m).netOut φ u = (if u = sSource m then y else 0) -
      (if u = sinkA m then (splitter m).inflow φ (sinkA m) else 0) -
      (if u = sinkB m then (splitter m).inflow φ (sinkB m) else 0) := by
    intro u
    by_cases h1 : u = sSource m
    · subst h1; simp [source_ne_sinkA, source_ne_sinkB, h.2.1]
    by_cases h2 : u = sinkA m
    · subst h2
      simp [h1, sinkA_ne_sinkB, Network.netOut, outflow_sinkA]
    by_cases h3 : u = sinkB m
    · subst h3
      simp [h1, h2, Network.netOut, outflow_sinkB]
    simp [h1, h2, h3, h.2.2 u h1 h2 h3]
  rw [sum_congr rfl fun u _ => e u] at hs
  simp only [sum_sub_distrib, sum_ite_eq', mem_univ, if_true] at hs
  linarith

variable (c x αa αb : ℚ)

theorem rowSum_struct (g : Opt m → ℚ) (φ : SArc m → ℚ)
    (h1 : ∀ e, g ((splitter m).tail e, .inl e) = φ e)
    (h2 : ∀ e, g ((splitter m).head e, .inl e) = gCap e.2 - φ e) (u : SNode m) :
    (gadgetLP m c x αa αb).rowSum g u = (splitter m).netOut φ u + inCap m u +
      (if sSource m = u then g (sSource m, .inr .p) else 0) +
      (if sinkA m = u then g (sinkA m, .inr .πa) else 0) +
      (if sinkB m = u then g (sinkB m, .inr .πb) else 0) := by
  rw [g_rowSum]
  have e1 : (fun e => g ((splitter m).tail e, .inl e)) = φ := funext h1
  rw [e1, sum_congr rfl fun e _ => h2 e, sum_sub_distrib]
  simp only [Network.netOut, inCap, Network.inflow]
  have : ∑ a ∈ univ.filter (fun a => (splitter m).head a = u), (splitter m).cap a =
      ∑ a ∈ univ.filter (fun a => (splitter m).head a = u), gCap a.2 := rfl
  rw [this]; ring

theorem coef_tail (e : SArc m) :
    (gadgetLP m c x αa αb).coef ((splitter m).tail e, .inl e) = 2 * bigM m - gCost e.2 := by
  show gadgetCoef m αa αb ((splitter m).tail e, .inl e) = _
  simp [gadgetCoef]

theorem coef_head (e : SArc m) :
    (gadgetLP m c x αa αb).coef ((splitter m).head e, .inl e) = 2 * bigM m := by
  show gadgetCoef m αa αb ((splitter m).head e, .inl e) = _
  simp only [gadgetCoef]; rw [if_neg (tail_ne_head m e)]

theorem objective_struct (P' P'' y : ℚ) (g : Opt m → ℚ) (φ : SArc m → ℚ)
    (hφ : IsSplitFlow m y φ)
    (h1 : ∀ e, g ((splitter m).tail e, .inl e) = φ e)
    (h2 : ∀ e, g ((splitter m).head e, .inl e) = gCap e.2 - φ e)
    (hp : g (sSource m, .inr .p) = c - x)
    (ha : g (sinkA m, .inr .πa) = (splitter m).inflow φ (sinkA m))
    (hb : g (sinkB m, .inr .πb) = (splitter m).inflow φ (sinkB m)) :
    (gadgetLP m c x (bigM m - P') (bigM m - epsC - P'')).objective g =
      2 * bigM m * (∑ e : SArc m, gCap e.2) + 2 * bigM m * (c - x) + (bigM m - P') * y -
        splitObjective m (epsC + P'' - P') φ := by
  rw [g_objective]
  have hAB := split_AB m hφ
  simp only [h1, h2, hp, ha, hb, splitObjective, Network.totalCost]
  have e1 : ∑ e : SArc m, (2 * bigM m - gCost e.2) * φ e =
      2 * bigM m * ∑ e : SArc m, φ e - ∑ e : SArc m, (splitter m).cost e * φ e := by
    rw [mul_sum, ← sum_sub_distrib]; refine sum_congr rfl fun e _ => ?_
    simp only [splitter]; ring
  have e2 : ∑ e : SArc m, 2 * bigM m * (gCap e.2 - φ e) =
      2 * bigM m * ∑ e : SArc m, gCap e.2 - 2 * bigM m * ∑ e : SArc m, φ e := by
    rw [mul_sum, mul_sum, ← sum_sub_distrib]; refine sum_congr rfl fun e _ => by ring
  rw [e1, e2]
  have : (splitter m).inflow φ (sinkA m) = y - (splitter m).inflow φ (sinkB m) := by linarith
  rw [this]; ring

end Struct

end Gadget
open Gadget in
theorem lemma6_proof (m : ℕ) (hm : 1 ≤ m) (c x P' P'' : ℚ) (hc : 0 < c) (hx0 : 0 ≤ x) (hxc : x < c)
    (hP'0 : 0 ≤ P') (hP'1 : P' ≤ 1) (hP''0 : 0 ≤ P'') (hP''1 : P'' ≤ 1) (f : _ → ℚ)
    (hf : (gadgetLP m c x (bigM m - P') (bigM m - epsC - P'')).IsOptimal f) :
    f (sinkA m, .inr .πa) = h0 (min x (bigK m)) ∧ f (sinkB m, .inr .πb) = h1 (min x (bigK m)) := by
  classical
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  have hK : 0 < (bigK (k+1)) := by unfold bigK; positivity
  have hy0 : 0 ≤ min x (bigK (k+1)) := le_min hx0 hK.le
  have hyx : min x (bigK (k+1)) ≤ x := min_le_left _ _
  have hyK : min x (bigK (k+1)) ≤ (bigK (k+1)) := min_le_right _ _
  have hSA : (sSource (k+1)) ≠ (sinkA (k+1)) := source_ne_sinkA _
  have hSB : (sSource (k+1)) ≠ (sinkB (k+1)) := source_ne_sinkB _
  have hAB : (sinkA (k+1)) ≠ (sinkB (k+1)) := sinkA_ne_sinkB _
  let bnd : SNode (k+1) → ℚ := fun u => if u = (sSource (k+1)) then c - x + min x (bigK (k+1)) else inCap (k+1) u
  have hmass : ∀ u, (gadgetLP (k+1) c x (bigM (k+1) - P') (bigM (k+1) - epsC - P'')).mass u = if u = (sSource (k+1)) then c else inCap (k+1) u := fun u => rfl
  -- upper bounds for feasible points
  have hcolle : ∀ g, (gadgetLP (k+1) c x (bigM (k+1) - P') (bigM (k+1) - epsC - P'')).Feasible g → ∀ e : SArc (k+1), (gadgetLP (k+1) c x (bigM (k+1) - P') (bigM (k+1) - epsC - P'')).colSum g (.inl e) ≤ gCap e.2 :=
    fun g hg e => hg.2.2 (.inl e) _ rfl
  have hple : ∀ g, (gadgetLP (k+1) c x (bigM (k+1) - P') (bigM (k+1) - epsC - P'')).Feasible g → (gadgetLP (k+1) c x (bigM (k+1) - P') (bigM (k+1) - epsC - P'')).colSum g (.inr .p) ≤ c - x :=
    fun g hg => hg.2.2 (.inr .p) _ rfl
  have hrowle : ∀ g, (gadgetLP (k+1) c x (bigM (k+1) - P') (bigM (k+1) - epsC - P'')).Feasible g → ∀ u, (gadgetLP (k+1) c x (bigM (k+1) - P') (bigM (k+1) - epsC - P'')).rowSum g u ≤ bnd u := by
    intro g hg u
    by_cases hu : u = (sSource (k+1))
    · subst hu
      simp only [bnd, if_true]
      have hr1 : (gadgetLP (k+1) c x (bigM (k+1) - P') (bigM (k+1) - epsC - P'')).rowSum g (sSource (k+1)) ≤ c := by
        have := hg.2.1 (sSource (k+1)); rwa [hmass, if_pos rfl] at this
      have hr2 : (gadgetLP (k+1) c x (bigM (k+1) - P') (bigM (k+1) - epsC - P'')).rowSum g (sSource (k+1)) ≤ (bigK (k+1)) + (c - x) := by
        rw [g_rowSum]
        have hh : ∑ e ∈ univ.filter (fun e => (splitter (k+1)).head e = (sSource (k+1))), g ((splitter (k+1)).head e, .inl e) = 0 :=
          sum_eq_zero fun e he => absurd (mem_filter.1 he).2 (head_ne_source _ e)
        rw [hh, if_pos rfl, if_neg hSA.symm, if_neg hSB.symm]
        have hp := hple g hg
        rw [g_colSum_p] at hp
        have ho : (splitter (k+1)).outflow (fun e => g ((splitter (k+1)).tail e, .inl e)) (sSource (k+1)) ≤ (bigK (k+1)) := by
          rw [← outCap_source k]
          unfold Network.outflow
          rw [sum_filter]
          refine sum_le_sum fun e _ => ?_
          split_ifs
          · have h1 := hcolle g hg e
            rw [g_colSum_arc] at h1
            have h2 := hg.1 _ (head_mem _ e)
            linarith
          · exact le_rfl
        linarith
      rcases le_total x (bigK (k+1)) with h | h
      · rw [min_eq_left h]; linarith
      · rw [min_eq_right h]; linarith
    · simp only [bnd, if_neg hu]
      have := hg.2.1 u; rwa [hmass, if_neg hu] at this
  have htrade_le : ∀ g, (gadgetLP (k+1) c x (bigM (k+1) - P') (bigM (k+1) - epsC - P'')).Feasible g →
      (gadgetLP (k+1) c x (bigM (k+1) - P') (bigM (k+1) - epsC - P'')).trade g ≤ ∑ u, bnd u + ∑ e : SArc (k+1), gCap e.2 + (c - x) := by
    intro g hg
    rw [g_trade]
    exact add_le_add (add_le_add (sum_le_sum fun u _ => hrowle g hg u)
      (sum_le_sum fun e _ => hcolle g hg e)) (hple g hg)
  -- the solution built from a flow
  let build : (SArc (k+1) → ℚ) → Opt (k+1) → ℚ := fun ψ o => match o with
    | (u, .inl e) => if (splitter (k+1)).tail e = u then ψ e else gCap e.2 - ψ e
    | (_, .inr .p) => c - x
    | (_, .inr .πa) => (splitter (k+1)).inflow ψ (sinkA (k+1))
    | (_, .inr .πb) => (splitter (k+1)).inflow ψ (sinkB (k+1))
  have hb1 : ∀ ψ e, build ψ ((splitter (k+1)).tail e, .inl e) = ψ e := by intro ψ e; simp [build]
  have hb2 : ∀ ψ e, build ψ ((splitter (k+1)).head e, .inl e) = gCap e.2 - ψ e := by
    intro ψ e; simp [build, tail_ne_head _ e]
  have hbp : ∀ ψ, build ψ ((sSource (k+1)), .inr .p) = c - x := fun ψ => rfl
  have hba : ∀ ψ, build ψ ((sinkA (k+1)), .inr .πa) = (splitter (k+1)).inflow ψ (sinkA (k+1)) := fun ψ => rfl
  have hbb : ∀ ψ, build ψ ((sinkB (k+1)), .inr .πb) = (splitter (k+1)).inflow ψ (sinkB (k+1)) := fun ψ => rfl
  have hbrow : ∀ ψ, IsSplitFlow (k+1) (min x (bigK (k+1))) ψ → ∀ u, (gadgetLP (k+1) c x (bigM (k+1) - P') (bigM (k+1) - epsC - P'')).rowSum (build ψ) u = bnd u := by
    intro ψ hψ u
    rw [rowSum_struct _ _ _ _ _ _ ψ (hb1 ψ) (hb2 ψ), hbp ψ, hba ψ, hbb ψ]
    by_cases h1 : u = (sSource (k+1))
    · subst h1
      simp only [bnd, if_true, hψ.2.1, inCap_source, if_neg hSA.symm, if_neg hSB.symm]
      ring
    by_cases h2 : u = (sinkA (k+1))
    · subst h2
      simp only [bnd, if_neg h1, if_neg hSA, if_true, if_neg hAB.symm, Network.netOut,
        outflow_sinkA]
      ring
    by_cases h3 : u = (sinkB (k+1))
    · subst h3
      simp only [bnd, if_neg h1, if_neg hSB, if_true, if_neg hAB, Network.netOut,
        outflow_sinkB]
      ring
    simp only [bnd, if_neg h1, if_neg (Ne.symm h1), if_neg (Ne.symm h2), if_neg (Ne.symm h3),
      hψ.2.2 u h1 h2 h3]
    ring
  have hbcol : ∀ ψ (e : SArc (k+1)), (gadgetLP (k+1) c x (bigM (k+1) - P') (bigM (k+1) - epsC - P'')).colSum (build ψ) (.inl e) = gCap e.2 := by
    intro ψ e; rw [g_colSum_arc, hb1, hb2]; ring
  have hbfeas : ∀ ψ, IsSplitFlow (k+1) (min x (bigK (k+1))) ψ → (gadgetLP (k+1) c x (bigM (k+1) - P') (bigM (k+1) - epsC - P'')).Feasible (build ψ) := by
    intro ψ hψ
    refine ⟨forall_gadgetE _ ?_ ?_ ?_ ?_ ?_, fun u => ?_, fun j cj hj => ?_⟩
    · intro e; rw [hb1]; exact (hψ.1 e).1
    · intro e; rw [hb2]; have := (hψ.1 e).2; simp only [splitter] at this; linarith
    · rw [hbp ψ]; linarith
    · rw [hba]; exact sum_nonneg fun e _ => (hψ.1 e).1
    · rw [hbb]; exact sum_nonneg fun e _ => (hψ.1 e).1
    · rw [hbrow ψ hψ u, hmass]
      simp only [bnd]
      split_ifs
      · linarith
      · exact le_rfl
    · rcases j with e | _ | _ | _
      · have : cj = gCap e.2 := by
          have h' : (some (gCap e.2) : Option ℚ) = some cj := hj
          exact (Option.some_injective _ h').symm
        rw [this, hbcol]
      · have : cj = c - x := by
          have h' : (some (c - x) : Option ℚ) = some cj := hj
          exact (Option.some_injective _ h').symm
        rw [this, g_colSum_p, hbp ψ]
      · exact absurd hj (by simp [gadgetLP])
      · exact absurd hj (by simp [gadgetLP])
  have hbtrade : ∀ ψ, IsSplitFlow (k+1) (min x (bigK (k+1))) ψ →
      (gadgetLP (k+1) c x (bigM (k+1) - P') (bigM (k+1) - epsC - P'')).trade (build ψ) = ∑ u, bnd u + ∑ e : SArc (k+1), gCap e.2 + (c - x) := by
    intro ψ hψ
    rw [g_trade, sum_congr rfl fun u _ => hbrow ψ hψ u, sum_congr rfl fun e _ => hbcol ψ e,
      g_colSum_p, hbp ψ]
  -- an explicit flow of value `min x K`
  have hflow0 : IsSplitFlow (k+1) (min x (bigK (k+1))) (flow0 k (min x (bigK (k+1)))) := by
    refine ⟨fun e => ?_, ?_, fun u h1 h2 h3 => ?_⟩
    · rcases e with ⟨c', _ | ⟨j, r⟩⟩
      · simp [flow0, splitter, gCap]
      · simp only [flow0, splitter, gCap]
        split_ifs with hj
        · subst hj
          have : ((bigK (k+1))) = 4 * 2 ^ k := by unfold bigK; ring
          simp only [Fin.val_last]
          constructor <;> linarith
        · simp
    · rw [flow0_netOut]; simp [hSA.symm, hSB.symm]
    · rw [flow0_netOut]; simp [Ne.symm h1, Ne.symm h2, Ne.symm h3]
  -- Lemma 5
  let κ : Opt (k+1) → ℚ := fun o => (bigM (k+1)) * (1 + if ((gadgetLP (k+1) c x (bigM (k+1) - P') (bigM (k+1) - epsC - P'')).cap o.2).isSome then 1 else 0) - (gadgetLP (k+1) c x (bigM (k+1) - P') (bigM (k+1) - epsC - P'')).coef o
  have hcp : (gadgetLP (k+1) c x (bigM (k+1) - P') (bigM (k+1) - epsC - P'')).coef ((sSource (k+1)), .inr .p) = 2 * (bigM (k+1)) := rfl
  have hca : (gadgetLP (k+1) c x (bigM (k+1) - P') (bigM (k+1) - epsC - P'')).coef ((sinkA (k+1)), .inr .πa) = (bigM (k+1)) - P' := rfl
  have hcb : (gadgetLP (k+1) c x (bigM (k+1) - P') (bigM (k+1) - epsC - P'')).coef ((sinkB (k+1)), .inr .πb) = (bigM (k+1)) - epsC - P'' := rfl
  have hκt : ∀ e : SArc (k+1), κ ((splitter (k+1)).tail e, .inl e) = gCost e.2 := by
    intro e; simp only [κ, coef_tail]; simp [gadgetLP]; ring
  have hκh : ∀ e : SArc (k+1), κ ((splitter (k+1)).head e, .inl e) = 0 := by
    intro e; simp only [κ, coef_head]; simp [gadgetLP]; ring
  have hκp : κ ((sSource (k+1)), .inr .p) = 0 := by simp only [κ, hcp]; simp [gadgetLP]; ring
  have hκa : κ ((sinkA (k+1)), .inr .πa) = P' := by simp only [κ, hca]; simp [gadgetLP]
  have hκb : κ ((sinkB (k+1)), .inr .πb) = epsC + P'' := by simp only [κ, hcb]; simp [gadgetLP]; ring
  have hκ0 : ∀ o ∈ (gadgetLP (k+1) c x (bigM (k+1) - P') (bigM (k+1) - epsC - P'')).E, 0 ≤ κ o := by
    refine forall_gadgetE _ (fun e => ?_) (fun e => ?_) ?_ ?_ ?_
    · rw [hκt]; rcases e with ⟨_, _ | ⟨j, r⟩⟩ <;> simp only [gCost] <;> (try split_ifs) <;> positivity
    · rw [hκh]
    · rw [hκp]
    · rw [hκa]; exact hP'0
    · rw [hκb]; unfold epsC; linarith
  have hM : (∑ o ∈ (gadgetLP (k+1) c x (bigM (k+1) - P') (bigM (k+1) - epsC - P'')).E, κ o) < (bigM (k+1)) := by
    show (∑ o ∈ gadgetE (k+1), κ o) < (bigM (k+1))
    rw [sum_gadgetE, sum_congr rfl fun e _ => hκt e, sum_congr rfl fun e _ => hκh e, hκp, hκa, hκb,
      sum_gCost]
    unfold bigM epsC
    simp only [sum_const_zero]
    linarith
  have h5 := lemma5_proof (gadgetLP (k+1) c x (bigM (k+1) - P') (bigM (k+1) - epsC - P'')) (bigM (k+1)) κ hκ0 (fun o _ => by simp only [κ]; ring) hM f hf
  -- tightness
  have hTf := h5 _ (hbfeas _ hflow0)
  rw [hbtrade _ hflow0, g_trade] at hTf
  have hR := sum_le_sum fun u (_ : u ∈ univ) => hrowle f hf.1 u
  have hC := sum_le_sum fun e (_ : e ∈ univ) => hcolle f hf.1 e
  have hP := hple f hf.1
  have hrow_eq : ∀ u, (gadgetLP (k+1) c x (bigM (k+1) - P') (bigM (k+1) - epsC - P'')).rowSum f u = bnd u := fun u =>
    (sum_eq_sum_iff_of_le (fun u _ => hrowle f hf.1 u)).1 (by linarith) u (mem_univ u)
  have hcol_eq : ∀ e : SArc (k+1), (gadgetLP (k+1) c x (bigM (k+1) - P') (bigM (k+1) - epsC - P'')).colSum f (.inl e) = gCap e.2 := fun e =>
    (sum_eq_sum_iff_of_le (fun e _ => hcolle f hf.1 e)).1 (by linarith) e (mem_univ e)
  have hfp : f ((sSource (k+1)), .inr .p) = c - x := by
    have := g_colSum_p (k+1) c x (bigM (k+1) - P') (bigM (k+1) - epsC - P'') f; linarith
  -- the flow of `f`
  let φ : SArc (k+1) → ℚ := fun e => f ((splitter (k+1)).tail e, .inl e)
  have hf2 : ∀ e, f ((splitter (k+1)).head e, .inl e) = gCap e.2 - φ e := by
    intro e; have := hcol_eq e; rw [g_colSum_arc] at this; simp only [φ]; linarith
  have hrow' := rowSum_struct (k+1) c x (bigM (k+1) - P') (bigM (k+1) - epsC - P'') f φ (fun e => rfl) hf2
  have hφ : IsSplitFlow (k+1) (min x (bigK (k+1))) φ := by
    refine ⟨fun e => ⟨hf.1.1 _ (tail_mem _ e), ?_⟩, ?_, fun u h1 h2 h3 => ?_⟩
    · have := hf.1.1 _ (head_mem _ e); rw [hf2] at this; show φ e ≤ gCap e.2; linarith
    · have := hrow_eq (sSource (k+1))
      rw [hrow', hfp, inCap_source, if_pos rfl, if_neg hSA.symm, if_neg hSB.symm] at this
      simp only [bnd, if_true] at this
      linarith
    · have := hrow_eq u
      rw [hrow', if_neg (Ne.symm h1), if_neg (Ne.symm h2), if_neg (Ne.symm h3)] at this
      simp only [bnd, if_neg h1] at this
      linarith
  have hfa : f ((sinkA (k+1)), .inr .πa) = (splitter (k+1)).inflow φ (sinkA (k+1)) := by
    have := hrow_eq (sinkA (k+1))
    rw [hrow', if_neg hSA, if_pos rfl, if_neg hAB.symm] at this
    simp only [bnd, if_neg hSA.symm, Network.netOut, outflow_sinkA] at this
    linarith
  have hfb : f ((sinkB (k+1)), .inr .πb) = (splitter (k+1)).inflow φ (sinkB (k+1)) := by
    have := hrow_eq (sinkB (k+1))
    rw [hrow', if_neg hSB, if_neg hAB, if_pos rfl] at this
    simp only [bnd, if_neg hSB.symm, Network.netOut, outflow_sinkB] at this
    linarith
  -- minimality and Lemma 3
  have hmin : ∀ ψ, IsSplitFlow (k+1) (min x (bigK (k+1))) ψ →
      splitObjective (k+1) (epsC + P'' - P') φ ≤ splitObjective (k+1) (epsC + P'' - P') ψ := by
    intro ψ hψ
    have h := hf.2 (build ψ) (hbfeas ψ hψ)
    rw [objective_struct _ _ _ _ _ _ (build ψ) ψ hψ (hb1 ψ) (hb2 ψ) (hbp ψ) (hba ψ) (hbb ψ),
      objective_struct _ _ _ _ _ _ f φ hφ (fun e => rfl) hf2 hfp hfa hfb] at h
    linarith
  have hθ0 : 0 < epsC + P'' - P' := by unfold epsC; linarith
  have hθ6 : epsC + P'' - P' < 6 := by unfold epsC; linarith
  obtain ⟨hA, hB⟩ := lemma3_proof (k+1) hm _ hθ0 hθ6 _ hy0 hyK φ hφ hmin
  exact ⟨hfa.trans hA, hfb.trans hB⟩


end Bssg

