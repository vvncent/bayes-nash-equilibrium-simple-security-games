import Mathlib
import BssgProofs.Statements
import BssgProofs.Proofs.Decoder
import BssgProofs.Proofs.Embedding
import BssgProofs.Proofs.Gadget

namespace Bssg

open Finset

namespace Comp

/-! ### The switch map: lower bounds -/

theorem h0_ge (ξ : ℚ) : (ξ - 1) / 2 ≤ h0 ξ := by
  unfold h0
  have h1 := Int.floor_le (ξ / 2)
  have h2 := Int.lt_floor_add_one (ξ / 2)
  rcases le_total (ξ - 2 * ((⌊ξ / 2⌋ : ℤ) : ℚ)) 1 with h | h
  · rw [min_eq_left h]; linarith
  · rw [min_eq_right h]; linarith

theorem h1_ge (ξ : ℚ) : (ξ - 1) / 2 ≤ h1 ξ := by
  unfold h1
  rcases le_total (ξ - 2 * ((⌊ξ / 2⌋ : ℤ) : ℚ) - 1) 0 with h | h
  · rw [max_eq_right h]; linarith
  · rw [max_eq_left h]; linarith

theorem h_ge (i : Bool) (ξ : ℚ) : (ξ - 1) / 2 ≤ h i ξ := by
  cases i
  · exact h0_ge ξ
  · exact h1_ge ξ

/-! ### Splitter facts -/

theorem sSource_ne_sinkA (m : ℕ) : sSource m ≠ sinkA m := by simp [sSource, sinkA]
theorem sSource_ne_sinkB (m : ℕ) : sSource m ≠ sinkB m := by simp [sSource, sinkB]
theorem sinkA_ne_sinkB (m : ℕ) : sinkA m ≠ sinkB m := by simp [sinkA, sinkB]

theorem sinkOf_ne_sSource (m : ℕ) (i : Bool) : sinkOf m i ≠ sSource m := by
  cases i
  · exact (sSource_ne_sinkA m).symm
  · exact (sSource_ne_sinkB m).symm

theorem sinkOf_inj (m : ℕ) {i j : Bool} (h : sinkOf m i = sinkOf m j) : i = j := by
  cases i <;> cases j <;> simp_all [sinkOf, sinkA, sinkB]

theorem inCap_sink (n : ℕ) (hn : 1 ≤ n) (c : Bool) :
    inCap n (.inr (c, .inr (Fin.last n))) = 2 ^ n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  unfold inCap Network.inflow
  rw [Finset.sum_filter]
  have key : ∀ (p : Prop) [Decidable p] (b : Bool) (x : Fin (k + 1)),
      ((if p then (Sum.inr (b, Sum.inl x) : SNode (k + 1)) else Sum.inl ()) =
        Sum.inr (c, Sum.inr (Fin.last (k + 1)))) ↔ False := by
    intro p _ b x; split <;> simp
  simp [Fintype.sum_prod_type, Fintype.sum_option, Fin.sum_univ_four, splitter, embed, gHead,
    gCap, key]
  cases c <;> simp [Finset.sum_ite_eq', ← two_mul, pow_succ] <;> ring

/-! ### Generic sums over filtered option sets -/

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

/-! ### The gadget of switch `v` inside the market -/

/-- Goods of the gadget LP as goods of the market (gadget of switch `v`). -/
def gmap (v : Fin n) : SArc n ⊕ GadgetPort → RGood n
  | .inl e => .inr (.inl (v, e))
  | .inr .p => .inl v
  | .inr .πa => I.portGood v false
  | .inr .πb => I.portGood v true

/-- The purchases of the buyers `(v, ·)`, as a solution of the gadget LP. -/
def fv (v : Fin n) (x : SNode n × (SArc n ⊕ GadgetPort)) : ℚ := f ((v, x.1), gmap I v x.2)

theorem gadget_rowSum (c x αa αb : ℚ) (v : Fin n) (u : SNode n) :
    (gadgetLP n c x αa αb).rowSum (fv I f v) u = I.redMarket.rowSum f (v, u) := by
  rw [rowSum_market]
  unfold AllocLP.rowSum
  rw [sum_filter_fst, Fintype.sum_sum_type, sum_gadgetPort]
  simp only [gadgetLP, mem_gadgetE_arc, mem_gadgetE_p, mem_gadgetE_πa, mem_gadgetE_πb, fv, gmap]

theorem gadget_colSum_arc (c x αa αb : ℚ) (v : Fin n) (e : SArc n) :
    (gadgetLP n c x αa αb).colSum (fv I f v) (.inl e) =
      I.redMarket.colSum f (.inr (.inl (v, e))) := by
  rw [colSum_arc]
  unfold AllocLP.colSum
  rw [sum_filter_snd]
  simp only [gadgetLP, mem_gadgetE_arc, fv, gmap]

theorem gadget_colSum_p (c x αa αb : ℚ) (v : Fin n) :
    (gadgetLP n c x αa αb).colSum (fv I f v) (.inr .p) = f ((v, sSource n), .inl v) := by
  unfold AllocLP.colSum
  rw [sum_filter_snd]
  simp only [gadgetLP, mem_gadgetE_p, fv, gmap]
  simp

end Market

/-! ### Counting labelled edges -/

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

/-- Every labelled edge has a head: a switch or one of the two terminals. -/
theorem sum_split_heads (g : Fin n → Bool → ℚ) :
    (∑ u : Fin n, ∑ i : Bool, g u i) =
      (∑ w : Fin n, ∑ u : Fin n, ∑ i : Bool, if I.succ u i = .inl w then g u i else 0) +
      (∑ u : Fin n, ∑ i : Bool, if I.succ u i = .inr .yes then g u i else 0) +
      (∑ u : Fin n, ∑ i : Bool, if I.succ u i = .inr .no then g u i else 0) := by
  have hA : (∑ w : Fin n, ∑ u : Fin n, ∑ i : Bool, if I.succ u i = .inl w then g u i else 0) =
      ∑ u : Fin n, ∑ i : Bool, ∑ w : Fin n, if I.succ u i = .inl w then g u i else 0 := by
    rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun u _ => Finset.sum_comm
  rw [hA, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rcases hs : I.succ u i with w | t
  · simp
  · cases t <;> simp

theorem state_stay (k j : ℕ) (t : Terminal) (h : (I.state k).1 = .inr t) :
    I.state (j + k) = I.state k := by
  have hfix : I.step (I.state k) = I.state k := by
    rcases hst : I.state k with ⟨a, b⟩
    rw [hst] at h
    simp only at h
    subst h
    rfl
  unfold ArrivalInstance.state at *
  rw [Function.iterate_add_apply]
  exact Function.iterate_fixed hfix j

theorem reaches_unique' {t t' : Terminal} (ht : I.Reaches t) (ht' : I.Reaches t') : t = t' := by
  obtain ⟨k, hk⟩ := ht
  obtain ⟨k', hk'⟩ := ht'
  have h1 := state_stay I k k' t hk
  have h2 := state_stay I k' k t' hk'
  rw [add_comm, h2] at h1
  rw [h1, hk] at hk'
  simpa using hk'

end Counting

end Comp

end Bssg

namespace Bssg
namespace Comp

open Finset

/-! ### Intercepts and slopes -/

section Coef

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

theorem bigM_pos (m : ℕ) : 0 < bigM m := by unfold bigM; positivity

/-- The capacity `c_v + [v = o]` of the gadget LP of `v`. -/
def gc (w : Fin n) : ℚ := I.capV w + (if w = I.origin then 1 else 0)

theorem gadget_mass (x αa αb : ℚ) (w : Fin n) (u : SNode n) :
    (gadgetLP n (gc I w) x αa αb).mass u = I.redMarket.mass (w, u) := by
  simp only [gadgetLP, ArrivalInstance.redMarket, gc]

theorem redX_eq (f : RBuyer n × RGood n → ℚ) (w : Fin n) : I.redX f w = (if w = I.origin then 1 else 0) +
    ∑ u : Fin n, ∑ i : Bool, if I.succ u i = .inl w then I.portPurchase f u i else 0 := rfl


end Coef

/-! ### Step 1: port prices -/

section Step1

variable {n : ℕ} (I : ArrivalInstance n) {P : RGood n → ℚ} {util : RBuyer n → ℚ}
  {f : RBuyer n × RGood n → ℚ} (heq : I.redMarket.IsEquilibrium P util f)
include heq

theorem pp_nonneg (u : Fin n) (i : Bool) : 0 ≤ I.portPurchase f u i :=
  heq.f_nonneg _ ((mem_E I _).2 (opt_port I u i))

theorem pp_le (u : Fin n) (i : Bool) : I.portPurchase f u i ≤ 2 ^ n := by
  have hn : 1 ≤ n := Fin.pos u
  have h1 : I.portPurchase f u i ≤ I.redMarket.rowSum f (u, sinkOf n i) := by
    unfold Market.rowSum ArrivalInstance.portPurchase
    refine Finset.single_le_sum (f := f) (fun e he => heq.f_nonneg e (Finset.mem_filter.1 he).1) ?_
    exact Finset.mem_filter.2 ⟨(mem_E I _).2 (opt_port I u i), rfl⟩
  have h2 := heq.cond_c_le (u, sinkOf n i)
  have h3 : I.redMarket.mass (u, sinkOf n i) = 2 ^ n := by
    simp only [ArrivalInstance.redMarket, sinkOf_ne_sSource, ite_false]
    cases i
    · exact inCap_sink n hn false
    · exact inCap_sink n hn true
  linarith

theorem others_le (w : Node n) :
    (∑ u : Fin n, ∑ i : Bool, if I.succ u i = w then I.portPurchase f u i else 0) ≤
      2 ^ n * (I.indeg w : ℚ) :=
  sum_ite_succ_le I w _ _ fun u i _ => pp_le I heq u i

theorem others_nonneg (w : Node n) :
    0 ≤ ∑ u : Fin n, ∑ i : Bool, if I.succ u i = w then I.portPurchase f u i else 0 := by
  refine Finset.sum_nonneg fun u _ => Finset.sum_nonneg fun i _ => ?_
  split_ifs
  · exact pp_nonneg I heq u i
  · exact le_rfl

theorem P_inl_le (w : Fin n) : P (.inl w) ≤ 1 := by
  by_contra hP
  replace hP := not_le.1 hP
  have hcol := heq.cond_d_eq (.inl w) (by linarith)
  rw [colSum_inl] at hcol
  have hcap : I.redMarket.cap (.inl w) = 1 + 2 ^ n * (I.indeg (.inl w) : ℚ) := rfl
  have hoth := others_le I heq (.inl w)
  have hy : 0 < f ((w, sSource n), .inl w) := by linarith
  have hb := heq.cond_b _ ((mem_E I _).2 (opt_src I w)) hy
  have hv := heq.v_nonneg (w, sSource n)
  rw [a_nonarc I _ _ (by simp), b_nonarc I _ _ (by simp)] at hb
  simp only [ite_true] at hb
  have hM := bigM_pos n
  unfold lam at hb
  nlinarith

theorem P_exit : P (.inr (.inr ())) = 0 := by
  by_contra hP
  have hP' : 0 < P (.inr (.inr ())) := lt_of_le_of_ne (heq.P_nonneg _) (Ne.symm hP)
  have hcol := heq.cond_d_eq _ hP'
  rw [colSum_exit] at hcol
  have hcap : I.redMarket.cap (.inr (.inr ())) =
      1 + 2 ^ n * ((I.indeg (.inr .yes) : ℚ) + (I.indeg (.inr .no) : ℚ)) := rfl
  have h1 := others_le I heq (.inr .yes)
  have h2 := others_le I heq (.inr .no)
  unfold ArrivalInstance.exitLoad at hcol
  linarith

theorem P_port (u : Fin n) (i : Bool) :
    0 ≤ P (I.portGood u i) ∧ P (I.portGood u i) ≤ 1 := by
  refine ⟨heq.P_nonneg _, ?_⟩
  unfold ArrivalInstance.portGood
  split
  · exact P_inl_le I heq _
  · rw [P_exit I heq]; norm_num

/-! ### Step 2: each gadget solves its gadget LP -/

theorem gadget_optimal (w : Fin n) :
    (gadgetLP n (gc I w) (I.redX f w) (bigM n - P (I.portGood w false))
      (bigM n - epsC - P (I.portGood w true))).IsOptimal (fv I f w) := by
  set L := gadgetLP n (gc I w) (I.redX f w) (bigM n - P (I.portGood w false))
      (bigM n - epsC - P (I.portGood w true)) with hL
  have hcolw := colSum_inl I f w
  have hrx := redX_eq I f w
  have hcapw : I.redMarket.cap (.inl w) = I.capV w := rfl
  have hgc : gc I w = I.capV w + (if w = I.origin then 1 else 0) := rfl
  -- dual variables
  let π : SArc n ⊕ GadgetPort → ℚ := fun j => match j with
    | .inl e => P (.inr (.inl (w, e)))
    | .inr .p => lam n * P (.inl w)
    | .inr .πa => 0
    | .inr .πb => 0
  have hM := bigM_pos n
  apply lemma4_proof L (fv I f w) ?feas (fun u => util (w, u)) π (fun u => heq.v_nonneg _) ?πnn ?πinf
    ?dual ?tight ?row ?col
  case feas =>
    refine ⟨?_, ?_, ?_⟩
    · rintro ⟨u, j⟩ hj
      rcases j with e | (⟨⟩ | ⟨⟩ | ⟨⟩)
      · exact heq.f_nonneg _ ((mem_E I _).2 ((opt_arc I w u w e).2 ⟨rfl,
          (mem_gadgetE_arc n u e).1 hj⟩))
      · obtain rfl := (mem_gadgetE_p n u).1 hj
        exact heq.f_nonneg _ ((mem_E I _).2 (opt_src I w))
      · obtain rfl := (mem_gadgetE_πa n u).1 hj
        exact heq.f_nonneg _ ((mem_E I _).2 (opt_port I w false))
      · obtain rfl := (mem_gadgetE_πb n u).1 hj
        exact heq.f_nonneg _ ((mem_E I _).2 (opt_port I w true))
    · intro u
      rw [gadget_rowSum, hL, gadget_mass]
      exact heq.cond_c_le _
    · rintro (e | (⟨⟩ | ⟨⟩ | ⟨⟩)) c hc
      · simp only [L, gadgetLP, Option.some.injEq] at hc
        subst hc
        rw [gadget_colSum_arc]
        exact heq.cond_d_le _
      · simp only [L, gadgetLP, Option.some.injEq] at hc
        subst hc
        rw [gadget_colSum_p]
        have := heq.cond_d_le (.inl w)
        rw [hcolw, hcapw] at this
        rw [hgc, hrx]
        linarith
      · simp [L, gadgetLP] at hc
      · simp [L, gadgetLP] at hc
  case πnn =>
    rintro (e | (⟨⟩ | ⟨⟩ | ⟨⟩))
    · exact heq.P_nonneg _
    · have := heq.P_nonneg (.inl w)
      show 0 ≤ lam n * P (.inl w)
      unfold lam; positivity
    · exact le_rfl
    · exact le_rfl
  case πinf =>
    rintro (e | (⟨⟩ | ⟨⟩ | ⟨⟩)) hj <;> simp_all [L, gadgetLP, π]
  case dual =>
    rintro ⟨u, j⟩ hj
    rcases j with e | (⟨⟩ | ⟨⟩ | ⟨⟩)
    · have hopt := (mem_E I _).2 ((opt_arc I w u w e).2 ⟨rfl, (mem_gadgetE_arc n u e).1 hj⟩)
      have ha := heq.cond_a _ hopt
      rw [a_arc, b_arc] at ha
      simp only [L, gadgetLP, gadgetCoef, π]
      dsimp only at ha
      split_ifs at ha ⊢ <;> linarith
    · obtain rfl := (mem_gadgetE_p n u).1 hj
      have ha := heq.cond_a _ ((mem_E I _).2 (opt_src I w))
      rw [a_nonarc I _ _ (by simp), b_nonarc I _ _ (by simp)] at ha
      simp only [ite_true] at ha
      simp only [L, gadgetLP, gadgetCoef, π]
      linarith
    · obtain rfl := (mem_gadgetE_πa n u).1 hj
      have ha := heq.cond_a _ ((mem_E I _).2 (opt_port I w false))
      rw [a_nonarc I _ _ (portGood_nonarc I w false),
        b_nonarc I _ _ (portGood_nonarc I w false)] at ha
      simp only [sinkOf, (sSource_ne_sinkA n).symm, ite_false, ite_true] at ha
      simp only [L, gadgetLP, gadgetCoef, π]
      linarith
    · obtain rfl := (mem_gadgetE_πb n u).1 hj
      have ha := heq.cond_a _ ((mem_E I _).2 (opt_port I w true))
      rw [a_nonarc I _ _ (portGood_nonarc I w true),
        b_nonarc I _ _ (portGood_nonarc I w true)] at ha
      simp only [sinkOf, (sSource_ne_sinkB n).symm, sinkA_ne_sinkB n |>.symm, ite_false] at ha
      simp only [L, gadgetLP, gadgetCoef, π]
      linarith
  case tight =>
    rintro ⟨u, j⟩ hj hpos
    rcases j with e | (⟨⟩ | ⟨⟩ | ⟨⟩)
    · have hopt := (mem_E I _).2 ((opt_arc I w u w e).2 ⟨rfl, (mem_gadgetE_arc n u e).1 hj⟩)
      have ha := heq.cond_b _ hopt hpos
      rw [a_arc, b_arc] at ha
      simp only [L, gadgetLP, gadgetCoef, π]
      dsimp only at ha
      split_ifs at ha ⊢ <;> linarith
    · obtain rfl := (mem_gadgetE_p n u).1 hj
      have ha := heq.cond_b _ ((mem_E I _).2 (opt_src I w)) hpos
      rw [a_nonarc I _ _ (by simp), b_nonarc I _ _ (by simp)] at ha
      simp only [ite_true] at ha
      simp only [L, gadgetLP, gadgetCoef, π]
      linarith
    · obtain rfl := (mem_gadgetE_πa n u).1 hj
      have ha := heq.cond_b _ ((mem_E I _).2 (opt_port I w false)) hpos
      rw [a_nonarc I _ _ (portGood_nonarc I w false),
        b_nonarc I _ _ (portGood_nonarc I w false)] at ha
      simp only [sinkOf, (sSource_ne_sinkA n).symm, ite_false, ite_true] at ha
      simp only [L, gadgetLP, gadgetCoef, π]
      linarith
    · obtain rfl := (mem_gadgetE_πb n u).1 hj
      have ha := heq.cond_b _ ((mem_E I _).2 (opt_port I w true)) hpos
      rw [a_nonarc I _ _ (portGood_nonarc I w true),
        b_nonarc I _ _ (portGood_nonarc I w true)] at ha
      simp only [sinkOf, (sSource_ne_sinkB n).symm, sinkA_ne_sinkB n |>.symm, ite_false] at ha
      simp only [L, gadgetLP, gadgetCoef, π]
      linarith
  case row =>
    intro u hu
    rw [gadget_rowSum, hL, gadget_mass]
    exact heq.cond_c_eq _ hu
  case col =>
    rintro (e | (⟨⟩ | ⟨⟩ | ⟨⟩)) c hc hπ
    · simp only [L, gadgetLP, Option.some.injEq] at hc
      subst hc
      rw [gadget_colSum_arc]
      exact heq.cond_d_eq _ hπ
    · simp only [L, gadgetLP, Option.some.injEq] at hc
      subst hc
      rw [gadget_colSum_p]
      have hP : 0 < P (.inl w) := by
        have : 0 < lam n * P (.inl w) := hπ
        have hl : 0 < lam n := by unfold lam; linarith
        exact pos_of_mul_pos_right this hl.le
      have := heq.cond_d_eq (.inl w) hP
      rw [hcolw, hcapw] at this
      rw [hgc, hrx]
      linarith
    · simp [L, gadgetLP] at hc
    · simp [L, gadgetLP] at hc

theorem redX_nonneg (w : Fin n) : 0 ≤ I.redX f w := by
  rw [redX_eq]
  have := others_nonneg I heq (.inl w)
  split_ifs <;> linarith

theorem redX_lt (w : Fin n) : I.redX f w < gc I w := by
  rw [redX_eq, gc]
  have := others_le I heq (.inl w)
  unfold ArrivalInstance.capV
  linarith

/-- **Step 2.** `(A_w, B_w) = (h̄₀(x_w), h̄₁(x_w))`. -/
theorem gadget_ports (w : Fin n) (i : Bool) :
    I.portPurchase f w i = h i (min (I.redX f w) (bigK n)) := by
  have hn : 1 ≤ n := Fin.pos w
  have hc : 0 < gc I w := lt_of_le_of_lt (redX_nonneg I heq w) (redX_lt I heq w)
  have h6 := lemma6_proof n hn (gc I w) (I.redX f w) (P (I.portGood w false)) (P (I.portGood w true))
    hc (redX_nonneg I heq w) (redX_lt I heq w) (P_port I heq w false).1 (P_port I heq w false).2
    (P_port I heq w true).1 (P_port I heq w true).2 (fv I f w) (gadget_optimal I heq w)
  cases i
  · exact h6.1
  · exact h6.2

/-! ### Step 3: the load bound -/

theorem exitLoad_nonneg (t : Terminal) : 0 ≤ I.exitLoad f t := others_nonneg I heq (.inr t)

theorem exitLoad_sum_le : I.exitLoad f .yes + I.exitLoad f .no ≤ 1 := by
  have hsplit := sum_split_heads I (I.portPurchase f)
  have hpair : ∀ u, I.portPurchase f u false + I.portPurchase f u true ≤ I.redX f u := by
    intro u
    rw [gadget_ports I heq u false, gadget_ports I heq u true]
    show h0 _ + h1 _ ≤ _
    rw [h0_add_h1]
    exact min_le_left _ _
  have hA : (∑ u : Fin n, ∑ i : Bool, I.portPurchase f u i) ≤ ∑ u : Fin n, I.redX f u := by
    refine Finset.sum_le_sum fun u _ => ?_
    rw [Fintype.sum_bool]
    linarith [hpair u]
  have hX : (∑ u : Fin n, I.redX f u) = 1 +
      ∑ w : Fin n, ∑ u : Fin n, ∑ i : Bool,
        if I.succ u i = .inl w then I.portPurchase f u i else 0 := by
    simp only [redX_eq, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  unfold ArrivalInstance.exitLoad
  linarith

theorem pp_le_exit (u : Fin n) (i : Bool) (t : Terminal) (hs : I.succ u i = .inr t) :
    I.portPurchase f u i ≤ I.exitLoad f t := by
  unfold ArrivalInstance.exitLoad
  have hnn : ∀ u' ∈ (univ : Finset (Fin n)), 0 ≤ ∑ i' : Bool,
      if I.succ u' i' = .inr t then I.portPurchase f u' i' else 0 := fun u' _ =>
    Finset.sum_nonneg fun i' _ => by split_ifs; exacts [pp_nonneg I heq u' i', le_rfl]
  refine le_trans ?_ (Finset.single_le_sum hnn (Finset.mem_univ u))
  refine le_trans ?_ (Finset.single_le_sum (f := fun i' =>
    if I.succ u i' = .inr t then I.portPurchase f u i' else 0)
    (fun i' _ => by split_ifs; exacts [pp_nonneg I heq u i', le_rfl])
    (Finset.mem_univ i))
  simp [hs]

theorem pp_le_term (u : Fin n) (i : Bool) (t : Terminal) (hs : I.succ u i = .inr t) :
    I.portPurchase f u i ≤ 1 := by
  have h1 := pp_le_exit I heq u i t hs
  have h2 := exitLoad_sum_le I heq
  have h3 := exitLoad_nonneg I heq .yes
  have h4 := exitLoad_nonneg I heq .no
  cases t <;> linarith

theorem pp_le_switch (u : Fin n) (i : Bool) (w : Fin n) (hs : I.succ u i = .inl w) :
    I.portPurchase f u i ≤ I.redX f w := by
  rw [redX_eq]
  have hnn : ∀ u' ∈ (univ : Finset (Fin n)), 0 ≤ ∑ i' : Bool,
      if I.succ u' i' = .inl w then I.portPurchase f u' i' else 0 := fun u' _ =>
    Finset.sum_nonneg fun i' _ => by split_ifs; exacts [pp_nonneg I heq u' i', le_rfl]
  have : I.portPurchase f u i ≤ ∑ u : Fin n, ∑ i : Bool,
      if I.succ u i = .inl w then I.portPurchase f u i else 0 := by
    refine le_trans ?_ (Finset.single_le_sum hnn (Finset.mem_univ u))
    refine le_trans ?_ (Finset.single_le_sum (f := fun i' =>
      if I.succ u i' = .inl w then I.portPurchase f u i' else 0)
      (fun i' _ => by split_ifs; exacts [pp_nonneg I heq u i', le_rfl])
      (Finset.mem_univ i))
    simp [hs]
  have h0 : (0 : ℚ) ≤ if w = I.origin then 1 else 0 := by split_ifs <;> norm_num
  linarith

/-- Halving: every port purchase is at least `min((x_u − 1)/2, (K − 1)/2)`. -/
theorem pp_ge (u : Fin n) (i : Bool) :
    min ((I.redX f u + 1) / 2) ((bigK n + 1) / 2) ≤ I.portPurchase f u i + 1 := by
  rw [gadget_ports I heq u i]
  have := h_ge i (min (I.redX f u) (bigK n))
  rcases le_total (I.redX f u) (bigK n) with hle | hle
  · rw [min_eq_left hle] at this ⊢
    exact le_trans (min_le_left _ _) (by linarith)
  · rw [min_eq_right hle] at this ⊢
    exact le_trans (min_le_right _ _) (by linarith)

/-- **The load bound** (induction along a path to a terminal). -/
theorem load_bound (k : ℕ) (u : Fin n) (hu : I.liveWithin k u = true) :
    min (I.redX f u + 1) (bigK n + 1) ≤ 2 ^ (k + 1) := by
  induction k generalizing u with
  | zero => simp [ArrivalInstance.liveWithin] at hu
  | succ k ih =>
    have hK : (0 : ℚ) ≤ bigK n := by unfold bigK; positivity
    have hpow : (4 : ℚ) ≤ 2 ^ (k + 1 + 1) := by
      rw [pow_succ, pow_succ]; nlinarith [one_le_pow₀ (M₀ := ℚ) (a := 2) (n := k) (by norm_num)]
    simp only [ArrivalInstance.liveWithin, List.any_cons, List.any_nil, Bool.or_false,
      Bool.or_eq_true] at hu
    obtain ⟨i, hi⟩ : ∃ i, (match I.succ u i with
        | .inr _ => true
        | .inl w => I.liveWithin k w) = true := by
      rcases hu with h | h
      · exact ⟨false, h⟩
      · exact ⟨true, h⟩
    have hge := pp_ge I heq u i
    rcases hs : I.succ u i with w | t
    · rw [hs] at hi
      have ih' := ih w hi
      have hsw := pp_le_switch I heq u i w hs
      rw [pow_succ]
      rcases min_le_iff.1 hge with h | h
      all_goals
        rcases min_le_iff.1 ih' with h' | h'
      all_goals
        first
        | exact le_trans (min_le_left _ _) (by linarith)
        | exact le_trans (min_le_right _ _) (by linarith)
    · have ht := pp_le_term I heq u i t hs
      rcases min_le_iff.1 hge with h | h
      · exact le_trans (min_le_left _ _) (by linarith)
      · exact le_trans (min_le_right _ _) (by linarith)

theorem redX_le_K (hI : I.Preprocessed) (u : Fin n) : I.redX f u ≤ bigK n := by
  have := load_bound I heq n u (hI u)
  have hK : bigK n = 2 ^ (n + 1) := rfl
  rcases min_le_iff.1 this with h | h <;> linarith

end Step1

end Comp
end Bssg

namespace Bssg

open Finset

namespace Comp

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

end Comp

/-- `redMarket_wellFormed`, restated verbatim from `Statements.lean`. -/
theorem redMarket_wellFormed_proof {n : ℕ} (I : ArrivalInstance n) :
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
    · exact le_of_eq (Comp.b_arc I b q).symm
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
    · exact Comp.inCap_pos n u hu
  · rintro (w | ⟨v, a⟩ | ⟨⟩)
    · exact lt_of_lt_of_le one_pos (hcapV w)
    · exact Comp.gCap_pos a.2
    · show (0 : ℚ) < 1 + 2 ^ n * ((I.indeg (.inr .yes) : ℚ) + (I.indeg (.inr .no) : ℚ))
      positivity

/-- **Theorem 7** (composition), restated verbatim from `Statements.lean`. -/
theorem theorem7_proof {n : ℕ} (I : ArrivalInstance n) (hI : I.Preprocessed) (P : RGood n → ℚ)
    (v : RBuyer n → ℚ) (f : RBuyer n × RGood n → ℚ) (heq : I.redMarket.IsEquilibrium P v f) :
    I.IsFixedPoint (I.redX f) ∧
    ∀ t, I.exitLoad f t = I.termInflow (I.redX f) t ∧
      (I.Reaches t → I.exitLoad f t = 1) ∧ (¬ I.Reaches t → I.exitLoad f t = 0) := by
  -- Step 4: the port purchases are `h_i(x_u)`
  have hpp : ∀ u i, I.portPurchase f u i = h i (I.redX f u) := fun u i => by
    rw [Comp.gadget_ports I heq u i, min_eq_left (Comp.redX_le_K I heq hI u)]
  have hsum : ∀ w : Node n, (∑ u : Fin n, ∑ i : Bool,
      if I.succ u i = w then I.portPurchase f u i else 0) = I.inflow (I.redX f) w := by
    intro w
    unfold ArrivalInstance.inflow
    simp only [hpp]
  have hfp : I.IsFixedPoint (I.redX f) :=
    ⟨Comp.redX_nonneg I heq, fun w => by rw [Comp.redX_eq, hsum]⟩
  have hex : ∀ t, I.exitLoad f t = I.termInflow (I.redX f) t := fun t => hsum (.inr t)
  refine ⟨hfp, fun t => ⟨hex t, ?_, ?_⟩⟩
  · intro ht
    obtain ⟨t', ht', h1, _⟩ := lemma1_proof I (I.redX f) hfp
    rw [Comp.reaches_unique' I ht ht', hex]
    exact h1
  · intro ht
    obtain ⟨t', ht', _, h0⟩ := lemma1_proof I (I.redX f) hfp
    have hne : t ≠ t' := fun h => ht (h ▸ ht')
    have : t = t'.other := by cases t <;> cases t' <;> simp_all [Terminal.other]
    rw [this, hex]
    exact h0

/-- **Main theorem, coverage form**, restated verbatim from `Statements.lean`. -/
theorem main_coverage_proof {n : ℕ} (I : ArrivalInstance n) (ξ : RTarget n → ℚ)
    (σ : RType n → RTarget n → ℚ) (h : (Red I).IsCoverageBNE ξ σ) :
    Dec I σ = true ↔ I.Reaches .yes := by
  set J := I.preprocess with hJ
  have hwf := redMarket_wellFormed_proof J
  have heq := lemma8_proof J.redMarket hwf.1 hwf.2 ξ σ h
  have h7 := (theorem7_proof J (preprocess_preprocessed_proof I) _ _ _ heq).2 .yes
  have hdec : (∑ u : Fin n, ∑ i : Bool,
      if J.succ u i = .inr .yes then
        (J.redMarket.gW + J.redMarket.mass (u, sinkOf n i)) *
          σ (.inl (u, sinkOf n i)) (.inl (.inr (.inr ())))
      else 0) = J.exitLoad (J.redMarket.decF σ) .yes := by
    unfold ArrivalInstance.exitLoad
    refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun i _ => ?_
    split_ifs with hs
    · have hpg : J.portGood u i = .inr (.inr ()) := by
        unfold ArrivalInstance.portGood; rw [hs]
      simp only [ArrivalInstance.portPurchase, Market.decF, hpg]
    · rfl
  have hDec : Dec I σ = true ↔ J.exitLoad (J.redMarket.decF σ) .yes = 1 := by
    unfold Dec
    rw [← hdec]
    simp only [decide_eq_true_eq]
    exact Iff.rfl
  rw [hDec, ← preprocess_reaches_yes_proof I]
  constructor
  · intro h1
    by_contra hn
    rw [h7.2.2 hn] at h1
    exact zero_ne_one h1
  · exact h7.2.1

/-- **Main theorem**, restated verbatim from `Statements.lean`. -/
theorem main_proof {n : ℕ} (I : ArrivalInstance n) (δ : Finset (RTarget n) → ℚ)
    (σ : RType n → RTarget n → ℚ) (h : (Red I).IsBNE δ σ) :
    Dec I σ = true ↔ I.Reaches .yes := by
  have h0 := (fact0_proof (Red I) rfl (fun _ => rfl) (fun _ => rfl) δ σ).1 h
  exact main_coverage_proof I _ σ h0.2

end Bssg

#print axioms Bssg.theorem7_proof
#print axioms Bssg.main_coverage_proof
#print axioms Bssg.main_proof
#print axioms Bssg.redMarket_wellFormed_proof
