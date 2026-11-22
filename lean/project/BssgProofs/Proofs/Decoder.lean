import Mathlib
import BssgProofs.Statements

/-!
# Decoder: Dohrau et al. Lemma 1, the run bridges, preprocessing, and simple-proof Lemma 1
-/

namespace Bssg

open Finset

namespace Decoder

set_option linter.unusedSectionVars false
set_option linter.deprecated false

/-! ## Dohrau et al., Lemma 1 (pebble argument) -/

section Dohrau

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SwitchGraph V)

theorem traversed_mem_E (st : V × (V → Bool)) : G.traversed st ∈ G.E := by
  unfold SwitchGraph.traversed SwitchGraph.E
  split_ifs
  · exact mem_union_right _ (mem_image.2 ⟨st.1, mem_univ _, rfl⟩)
  · exact mem_union_left _ (mem_image.2 ⟨st.1, mem_univ _, rfl⟩)

theorem runState_succ (o d : V) (k : ℕ) :
    G.runState o d (k + 1) = G.runStep d (G.runState o d k) := by
  unfold SwitchGraph.runState
  rw [Function.iterate_succ_apply']

theorem runProfile_zero (o d : V) (e : V × V) : G.runProfile o d 0 e = 0 := by
  simp [SwitchGraph.runProfile]

theorem runProfile_succ (o d : V) (k : ℕ) (e : V × V) :
    G.runProfile o d (k + 1) e = G.runProfile o d k e +
      if (G.runState o d k).1 ≠ d ∧ G.traversed (G.runState o d k) = e then 1 else 0 := by
  unfold SwitchGraph.runProfile
  rw [range_add_one, filter_insert]
  split_ifs with h
  · rw [card_insert_of_notMem]
    simp
  · rfl

theorem mem_outE {v : V} {e : V × V} : e ∈ G.outE v ↔ e ∈ G.E ∧ e.1 = v := mem_filter

theorem mem_inE {v : V} {e : V × V} : e ∈ G.inE v ↔ e ∈ G.E ∧ e.2 = v := mem_filter

theorem sum_outE_indicator (st : V × (V → Bool)) (v : V) :
    (∑ e ∈ G.outE v, (if G.traversed st = e then (1 : ℤ) else 0)) =
      if st.1 = v then 1 else 0 := by
  rw [sum_ite_eq]
  simp only [mem_outE, traversed_mem_E, true_and]
  rfl

theorem sum_inE_indicator (st : V × (V → Bool)) (v : V) :
    (∑ e ∈ G.inE v, (if G.traversed st = e then (1 : ℤ) else 0)) =
      if (G.traversed st).2 = v then 1 else 0 := by
  rw [sum_ite_eq]
  simp only [mem_inE, traversed_mem_E, true_and]

/-- Conservation invariant of the run profile. -/
theorem runProfile_conservation (o d : V) (k : ℕ) (v : V) :
    (∑ e ∈ G.outE v, (G.runProfile o d k e : ℤ)) - (∑ e ∈ G.inE v, (G.runProfile o d k e : ℤ)) =
      (if v = o then 1 else 0) - (if v = (G.runState o d k).1 then 1 else 0) := by
  induction k with
  | zero =>
    have h0 : G.runState o d 0 = (o, fun _ => false) := rfl
    rw [h0]; simp [runProfile_zero]
  | succ k ih =>
    simp only [runProfile_succ, Nat.cast_add, sum_add_distrib]
    rw [runState_succ]
    by_cases hd : (G.runState o d k).1 = d
    · simp only [hd, ne_eq, not_true_eq_false, false_and, if_false, Nat.cast_zero, sum_const_zero,
        add_zero]
      rw [ih]
      unfold SwitchGraph.runStep
      rw [if_pos hd]
    · have h1 : ∀ e, ((if (G.runState o d k).1 ≠ d ∧ G.traversed (G.runState o d k) = e
          then 1 else 0 : ℕ) : ℤ) = if G.traversed (G.runState o d k) = e then 1 else 0 := by
        intro e
        split_ifs <;> simp_all
      simp only [h1, sum_outE_indicator, sum_inE_indicator]
      have hstep : (G.runStep d (G.runState o d k)).1 = (G.traversed (G.runState o d k)).2 := by
        unfold SwitchGraph.runStep SwitchGraph.traversed
        rw [if_neg hd]
      rw [hstep]
      have e1 : (if (G.runState o d k).1 = v then (1:ℤ) else 0) =
          if v = (G.runState o d k).1 then 1 else 0 := by
        rcases eq_or_ne v (G.runState o d k).1 with h | h
        · simp [h]
        · simp [h, Ne.symm h]
      have e2 : (if (G.traversed (G.runState o d k)).2 = v then (1:ℤ) else 0) =
          if v = (G.traversed (G.runState o d k)).2 then 1 else 0 := by
        rcases eq_or_ne v (G.traversed (G.runState o d k)).2 with h | h
        · simp [h]
        · simp [h, Ne.symm h]
      rw [e1, e2]
      linarith

/-- Alternation invariant at a vertex with two distinct successors. -/
theorem runProfile_alternation (o d : V) (k : ℕ) (v : V) (hv : G.s0 v ≠ G.s1 v) :
    G.runProfile o d k (v, G.s0 v) =
      G.runProfile o d k (v, G.s1 v) + if (G.runState o d k).2 v then 1 else 0 := by
  induction k with
  | zero => simp [runProfile_zero, SwitchGraph.runState]
  | succ k ih =>
    rw [runProfile_succ, runProfile_succ, runState_succ]
    generalize G.runState o d k = st at ih ⊢
    obtain ⟨u, sw⟩ := st
    by_cases hd : u = d
    · simp only [hd, ne_eq, not_true_eq_false, false_and, if_false, add_zero] at ih ⊢
      unfold SwitchGraph.runStep
      simp only [if_true]
      exact ih
    · unfold SwitchGraph.runStep SwitchGraph.traversed
      simp only [ne_eq, hd, not_false_eq_true, true_and, if_false] at ih ⊢
      by_cases huv : u = v
      · subst huv
        cases hsw : sw u
        · simp only [hsw, Bool.false_eq_true, if_false, add_zero, Prod.mk.injEq, true_and,
            Function.update_self, Bool.not_false, if_true] at ih ⊢
          rw [if_neg hv]
          simp [ih]
        · simp only [hsw, if_true, Prod.mk.injEq, true_and, Function.update_self, Bool.not_true,
            Bool.false_eq_true, if_false, add_zero] at ih ⊢
          rw [if_neg (Ne.symm hv)]
          simp [ih]
      · have hne : ∀ w, ((u, if sw u = true then G.s1 u else G.s0 u) = (v, w)) = False := by
          intro w; simp [huv]
        simp only [hne, if_false, add_zero, Function.update_of_ne (Ne.symm huv)]
        exact ih

theorem sum_outE_pair (f : V × V → ℕ) (v : V) (hv : G.s0 v ≠ G.s1 v) :
    ∑ e ∈ G.outE v, f e = f (v, G.s0 v) + f (v, G.s1 v) := by
  have : G.outE v = {(v, G.s0 v), (v, G.s1 v)} := by
    ext ⟨a, b⟩
    simp only [mem_outE, SwitchGraph.E, mem_union, mem_image, mem_univ, true_and, Prod.mk.injEq,
      mem_insert, mem_singleton]
    constructor
    · rintro ⟨h | h, rfl⟩ <;> obtain ⟨c, rfl, rfl⟩ := h <;> simp
    · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · exact ⟨Or.inl ⟨a, rfl, rfl⟩, rfl⟩
      · exact ⟨Or.inr ⟨a, rfl, rfl⟩, rfl⟩
  rw [this, sum_pair]
  simp [hv]

theorem sum_outE_single (f : V × V → ℕ) (v : V) (hv : G.s0 v = G.s1 v) :
    ∑ e ∈ G.outE v, f e = f (v, G.s0 v) := by
  have : G.outE v = {(v, G.s0 v)} := by
    ext ⟨a, b⟩
    simp only [mem_outE, SwitchGraph.E, mem_union, mem_image, mem_univ, true_and, Prod.mk.injEq,
      mem_singleton]
    constructor
    · rintro ⟨h | h, rfl⟩ <;> obtain ⟨c, rfl, rfl⟩ := h <;> simp [hv]
    · rintro ⟨rfl, rfl⟩
      exact ⟨Or.inl ⟨a, rfl, rfl⟩, rfl⟩
  rw [this, sum_singleton]

theorem runProfile_le (o d : V) (_hod : o ≠ d) (x : V × V → ℕ) (hx : G.IsSwitchingFlow o d x) :
    ∀ k, ∀ e ∈ G.E, G.runProfile o d k e ≤ x e := by
  intro k
  induction k with
  | zero => intro e _; simp [runProfile_zero]
  | succ k ih =>
    intro e he
    rw [runProfile_succ]
    split_ifs with hc
    swap
    · simpa using ih e he
    obtain ⟨hvd, htr⟩ := hc
    rcases (ih e he).lt_or_eq with hlt | heq
    · omega
    exfalso
    set v := (G.runState o d k).1 with hvdef
    set sw := (G.runState o d k).2 with hswdef
    have hR := runProfile_conservation G o d k v
    rw [← hvdef, if_pos rfl] at hR
    have hX := hx.conservation v
    rw [if_neg hvd] at hX
    have hin : (∑ e ∈ G.inE v, (G.runProfile o d k e : ℤ)) ≤ ∑ e ∈ G.inE v, (x e : ℤ) :=
      sum_le_sum fun e he' => by exact_mod_cast ih e (mem_inE G |>.1 he').1
    have hout : (∑ e ∈ G.outE v, (x e : ℤ)) ≤ ∑ e ∈ G.outE v, (G.runProfile o d k e : ℤ) := by
      have htr' : e = (v, if sw v then G.s1 v else G.s0 v) := htr.symm
      push_cast [← Nat.cast_sum]
      by_cases hs : G.s0 v = G.s1 v
      · rw [sum_outE_single G _ v hs, sum_outE_single G _ v hs]
        have : e = (v, G.s0 v) := by rw [htr']; split_ifs <;> simp [hs]
        rw [this] at heq
        exact_mod_cast heq.ge
      · rw [sum_outE_pair G _ v hs, sum_outE_pair G _ v hs]
        have halt := runProfile_alternation G o d k v hs
        have hsw := hx.switching v
        rw [← hswdef] at halt
        cases hb : sw v
        · rw [hb] at htr' halt
          simp only [Bool.false_eq_true, if_false] at htr' halt
          rw [htr'] at heq
          have : (x (v, G.s0 v) + x (v, G.s1 v) : ℕ) ≤
              G.runProfile o d k (v, G.s0 v) + G.runProfile o d k (v, G.s1 v) := by omega
          exact_mod_cast this
        · rw [hb] at htr' halt
          simp only [if_true] at htr' halt
          rw [htr'] at heq
          have : (x (v, G.s0 v) + x (v, G.s1 v) : ℕ) ≤
              G.runProfile o d k (v, G.s0 v) + G.runProfile o d k (v, G.s1 v) := by omega
          exact_mod_cast this
    split_ifs at hR hX <;> omega

theorem sum_runProfile_E (o d : V) (hnt : ∀ k, (G.runState o d k).1 ≠ d) (k : ℕ) :
    ∑ e ∈ G.E, G.runProfile o d k e = k := by
  induction k with
  | zero => simp [runProfile_zero]
  | succ k ih =>
    simp only [runProfile_succ, sum_add_distrib, ih, ne_eq, hnt k, not_false_eq_true, true_and]
    rw [sum_ite_eq, if_pos (traversed_mem_E G _)]

/-! ### Switching flows from labelled-edge weights -/

/-- The edge carried by the labelled edge `(v, b)`. -/
def lab (p : V × Bool) : V × V := (p.1, if p.2 then G.s1 p.1 else G.s0 p.1)

/-- Edge values from labelled-edge weights `F`. -/
def chi (F : V × Bool → ℕ) (e : V × V) : ℕ := ∑ p, if lab G p = e then F p else 0

theorem lab_mem_E (p : V × Bool) : lab G p ∈ G.E := traversed_mem_E G (p.1, fun _ => p.2)

theorem sum_outE_chi (F : V × Bool → ℕ) (w : V) :
    ∑ e ∈ G.outE w, (chi G F e : ℤ) = ∑ b, (F (w, b) : ℤ) := by
  unfold chi
  push_cast
  rw [sum_comm]
  simp only [sum_ite_eq, mem_outE, lab_mem_E, true_and]
  rw [Fintype.sum_prod_type]
  simp [lab]

theorem sum_inE_chi (F : V × Bool → ℕ) (w : V) :
    ∑ e ∈ G.inE w, (chi G F e : ℤ) = ∑ p, if (lab G p).2 = w then (F p : ℤ) else 0 := by
  unfold chi
  push_cast
  rw [sum_comm]
  simp only [sum_ite_eq, mem_inE, lab_mem_E, true_and]

theorem chi_eq_of_ne (F : V × Bool → ℕ) (v : V) (hv : G.s0 v ≠ G.s1 v) (b : Bool) :
    chi G F (v, if b then G.s1 v else G.s0 v) = F (v, b) := by
  unfold chi
  rw [Fintype.sum_eq_single (v, b)]
  · simp [lab]
  · rintro ⟨u, c⟩ hp
    rw [if_neg]
    intro h
    simp only [lab, Prod.mk.injEq] at h
    obtain ⟨rfl, h⟩ := h
    apply hp
    cases b <;> cases c <;> simp_all [eq_comm]

theorem chi_switching (F : V × Bool → ℕ) (v : V) (h1 : F (v, true) ≤ F (v, false))
    (h2 : F (v, false) ≤ F (v, true) + 1) :
    chi G F (v, G.s1 v) ≤ chi G F (v, G.s0 v) ∧ chi G F (v, G.s0 v) ≤ chi G F (v, G.s1 v) + 1 := by
  by_cases hs : G.s0 v = G.s1 v
  · rw [hs]; omega
  · have e0 := chi_eq_of_ne G F v hs false
    have e1 := chi_eq_of_ne G F v hs true
    simp only [Bool.false_eq_true, if_false, if_true] at e0 e1
    rw [e0, e1]; omega

end Dohrau

end Decoder

open Decoder in
theorem dohrau_lemma1_proof {V : Type*} [Fintype V] [DecidableEq V] (G : SwitchGraph V) (o d : V)
    (hod : o ≠ d) (x : V × V → ℕ) (hx : G.IsSwitchingFlow o d x) :
    G.RunTerminates o d ∧ ∀ k, ∀ e ∈ G.E, G.runProfile o d k e ≤ x e := by
  refine ⟨?_, runProfile_le G o d hod x hx⟩
  by_contra hnt
  have hnt' : ∀ k, (G.runState o d k).1 ≠ d := fun k hk => hnt ⟨k, hk⟩
  have h1 := sum_runProfile_E G o d hnt' (∑ e ∈ G.E, x e + 1)
  have h2 : ∑ e ∈ G.E, G.runProfile o d (∑ e ∈ G.E, x e + 1) e ≤ ∑ e ∈ G.E, x e :=
    sum_le_sum fun e he => runProfile_le G o d hod x hx _ e he
  omega



namespace Decoder

/-! ## Runs of ARRIVAL instances -/

section Arrival

variable {n : ℕ} (I : ArrivalInstance n)

theorem state_succ (k : ℕ) : I.state (k + 1) = I.step (I.state k) := by
  unfold ArrivalInstance.state
  rw [Function.iterate_succ_apply']

theorem state_add (k j : ℕ) : I.state (k + j) = I.step^[j] (I.state k) := by
  unfold ArrivalInstance.state
  rw [add_comm, Function.iterate_add_apply]

theorem iterate_step_inr (j : ℕ) (t : Terminal) (sw : Fin n → Bool) :
    I.step^[j] (.inr t, sw) = (.inr t, sw) :=
  Function.iterate_fixed (f := I.step) rfl j

theorem state_absorb {k : ℕ} {t : Terminal} (h : (I.state k).1 = .inr t) (j : ℕ) :
    I.state (k + j) = I.state k := by
  rw [state_add]
  rcases hs : I.state k with ⟨p, sw⟩
  rw [hs] at h
  simp only at h
  subst h
  exact iterate_step_inr I j t sw

theorem reaches_unique' {t t' : Terminal} (ht : I.Reaches t) (ht' : I.Reaches t') : t = t' := by
  obtain ⟨k, hk⟩ := ht
  obtain ⟨k', hk'⟩ := ht'
  have h1 := state_absorb I hk k'
  have h2 := state_absorb I hk' k
  rw [add_comm, h2] at h1
  have := congrArg Prod.fst h1
  rw [hk, hk'] at this
  exact (Sum.inr_injective this).symm

/-- The run on `G′` simulates the instance's run. -/
theorem sim (t : Terminal) (k : ℕ) :
    (I.toSwitchGraph.runState (.inl I.origin) (.inr t) k).1 = (I.state k).1 ∧
    ∀ v, (I.toSwitchGraph.runState (.inl I.origin) (.inr t) k).2 (.inl v) = (I.state k).2 v := by
  induction k with
  | zero => exact ⟨rfl, fun _ => rfl⟩
  | succ k ih =>
    rw [runState_succ, state_succ]
    generalize I.toSwitchGraph.runState (.inl I.origin) (.inr t) k = st at ih ⊢
    generalize I.state k = st' at ih ⊢
    obtain ⟨p, sw⟩ := st
    obtain ⟨q, sw'⟩ := st'
    obtain ⟨h1, h2⟩ := ih
    simp only at h1 h2
    subst h1
    cases p with
    | inl v =>
      have hne : (Sum.inl v : Node n) ≠ .inr t := Sum.inl_ne_inr
      simp only [SwitchGraph.runStep, hne, if_false, ArrivalInstance.step]
      refine ⟨?_, fun u => ?_⟩
      · rw [h2]; cases sw' v <;> rfl
      · by_cases huv : u = v
        · subst huv; simp [h2]
        · rw [Function.update_of_ne (by simpa using huv), Function.update_of_ne huv, h2]
    | inr t' =>
      simp only [SwitchGraph.runStep, ArrivalInstance.step]
      by_cases htt : (Sum.inr t' : Node n) = .inr t
      · rw [if_pos htt]; exact ⟨rfl, h2⟩
      · rw [if_neg htt]
        refine ⟨?_, fun u => ?_⟩
        · dsimp only; split <;> rfl
        · dsimp only; rw [Function.update_of_ne Sum.inl_ne_inr, h2]

theorem terminates_iff (t : Terminal) :
    I.Reaches t ↔ I.toSwitchGraph.RunTerminates (.inl I.origin) (.inr t) := by
  unfold ArrivalInstance.Reaches SwitchGraph.RunTerminates
  simp only [(sim I t _).1]

theorem reaches_iff_outcomeWithin' (t : Terminal) :
    I.Reaches t ↔ I.outcomeWithin (n * 2 ^ n) = some t := by
  constructor
  · intro hr
    classical
    let k := Nat.find hr
    have hk : (I.state k).1 = .inr t := Nat.find_spec hr
    have hmin : ∀ j < k, (I.state j).1 ≠ .inr t := fun j hj => Nat.find_min hr hj
    -- before `k` the token is at a switch
    have hsw : ∀ j < k, ∃ v, (I.state j).1 = .inl v := by
      intro j hj
      rcases hs : (I.state j).1 with v | t'
      · exact ⟨v, rfl⟩
      · exfalso
        have h1 := state_absorb I hs (k - j)
        rw [Nat.add_sub_cancel' hj.le] at h1
        rw [h1, hs] at hk
        rw [Sum.inr_injective hk] at hs
        exact hmin j hj hs
    -- states before `k` are distinct
    have hinj : ∀ i < k, ∀ j < k, I.state i = I.state j → i = j := by
      intro i hi j hj hij
      by_contra hne
      wlog hlt : i < j generalizing i j
      · exact this j hj i hi hij.symm (Ne.symm hne) (by omega)
      have h1 : I.state (i + (k - j)) = I.state k := by
        rw [state_add, hij, ← state_add, Nat.add_sub_cancel' hj.le]
      exact hmin (i + (k - j)) (by omega) (by rw [h1]; exact hk)
    let g : ℕ → Fin n × (Fin n → Bool) := fun j =>
      match (I.state j).1 with
      | .inl v => (v, (I.state j).2)
      | .inr _ => (I.origin, (I.state j).2)
    have hg : ∀ j < k, I.state j = (.inl (g j).1, (g j).2) := by
      intro j hj
      obtain ⟨v, hv⟩ := hsw j hj
      simp only [g, hv]
      rw [← hv]
    have hcard : k ≤ n * 2 ^ n := by
      have := Finset.card_le_card_of_injOn g (s := range k) (t := univ)
        (fun _ _ => mem_coe.2 (mem_univ _)) (by
          intro i hi j hj hij
          simp only [coe_range, Set.mem_Iio] at hi hj
          apply hinj i hi j hj
          rw [hg i hi, hg j hj, hij])
      simpa [Fintype.card_prod, Fintype.card_fun] using this
    have := state_absorb I hk (n * 2 ^ n - k)
    rw [Nat.add_sub_cancel' hcard] at this
    unfold ArrivalInstance.outcomeWithin
    rw [this, hk]
  · intro h
    unfold ArrivalInstance.outcomeWithin at h
    refine ⟨n * 2 ^ n, ?_⟩
    rcases hs : (I.state (n * 2 ^ n)).1 with v | t'
    · rw [hs] at h; simp at h
    · rw [hs] at h; simp at h; rw [h]

/-! ### `liveWithin` and preprocessing -/

/-- One-step liveness of a node given liveness of switches within `k`. -/
def gl (k : ℕ) : Node n → Bool
  | .inl w => I.liveWithin k w
  | .inr _ => true

theorem liveWithin_succ (k : ℕ) (v : Fin n) :
    I.liveWithin (k + 1) v = (gl I k (I.succ v false) || gl I k (I.succ v true)) := by
  simp only [ArrivalInstance.liveWithin, List.any_cons, List.any_nil, Bool.or_false]
  rcases I.succ v false <;> rcases I.succ v true <;> rfl

theorem liveWithin_mono_succ (k : ℕ) : ∀ v, I.liveWithin k v = true → I.liveWithin (k + 1) v = true := by
  induction k with
  | zero => intro v h; simp [ArrivalInstance.liveWithin] at h
  | succ k ih =>
    intro v h
    have hg : ∀ u, gl I k u = true → gl I (k + 1) u = true := by
      intro u; cases u with
      | inl w => exact ih w
      | inr _ => intro _; rfl
    rw [liveWithin_succ] at h ⊢
    simp only [Bool.or_eq_true] at h ⊢
    rcases h with h | h
    · exact Or.inl (hg _ h)
    · exact Or.inr (hg _ h)

theorem liveWithin_mono {k m : ℕ} (hkm : k ≤ m) (v : Fin n) (h : I.liveWithin k v = true) :
    I.liveWithin m v = true := by
  induction m, hkm using Nat.le_induction with
  | base => exact h
  | succ m _ ih => exact liveWithin_mono_succ I m v ih

def Stable (k : ℕ) : Prop := ∀ v, I.liveWithin k v = I.liveWithin (k + 1) v

theorem stable_succ {k : ℕ} (h : Stable I k) : Stable I (k + 1) := by
  intro v
  have hg : ∀ u, gl I k u = gl I (k + 1) u := by
    intro u; cases u with
    | inl w => exact h w
    | inr _ => rfl
  rw [liveWithin_succ, liveWithin_succ, hg, hg]

theorem stable_le {k m : ℕ} (hkm : k ≤ m) (h : Stable I k) : Stable I m := by
  induction m, hkm using Nat.le_induction with
  | base => exact h
  | succ m _ ih => exact stable_succ I ih

theorem card_live_ge (m : ℕ) (h : ∀ j < m, ¬ Stable I j) :
    m ≤ (univ.filter fun v => I.liveWithin m v = true).card := by
  induction m with
  | zero => exact Nat.zero_le _
  | succ m ih =>
    have ih' := ih fun j hj => h j (by omega)
    have hlt : (univ.filter fun v => I.liveWithin m v = true) ⊂
        (univ.filter fun v => I.liveWithin (m + 1) v = true) := by
      rw [Finset.ssubset_iff_subset_ne]
      refine ⟨fun v hv => ?_, fun heq => h m (by omega) fun v => ?_⟩
      · simp only [mem_filter, mem_univ, true_and] at hv ⊢
        exact liveWithin_mono_succ I m v hv
      · have := congrArg (v ∈ ·) heq
        simp only [mem_filter, mem_univ, true_and, eq_iff_iff] at this
        cases h1 : I.liveWithin m v <;> cases h2 : I.liveWithin (m + 1) v <;> simp_all
    have := Finset.card_lt_card hlt
    omega

theorem stable_n : Stable I n := by
  by_contra hns
  have h : ∀ j < n + 1, ¬ Stable I j := fun j hj hs => hns (stable_le I (by omega) hs)
  have h1 := card_live_ge I (n + 1) h
  have h2 := Finset.card_le_univ (univ.filter fun v => I.liveWithin (n + 1) v = true)
  simp only [Fintype.card_fin] at h2
  omega

theorem liveWithin_n_add (m : ℕ) (v : Fin n) : I.liveWithin (n + m) v = I.liveWithin n v := by
  induction m with
  | zero => rfl
  | succ m ih => rw [← add_assoc, ← stable_le I (by omega : n ≤ n + m) (stable_n I) v, ih]

theorem liveWithin_le_n {k : ℕ} (v : Fin n) (h : I.liveWithin k v = true) :
    I.liveWithin n v = true := by
  rcases le_total k n with hk | hk
  · exact liveWithin_mono I hk v h
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk
    rwa [liveWithin_n_add] at h

/-- A dead switch only leads to dead switches. -/
theorem dead_succ (u : Fin n) (hu : I.liveWithin n u = false) (i : Bool) :
    ∃ w, I.succ u i = .inl w ∧ I.liveWithin n w = false := by
  have h1 : I.liveWithin (n + 1) u = false := by rw [← stable_n I u]; exact hu
  rw [liveWithin_succ] at h1
  simp only [Bool.or_eq_false_iff] at h1
  have hg : gl I n (I.succ u i) = false := by cases i <;> simp [h1.1, h1.2]
  rcases hs : I.succ u i with w | t
  · rw [hs] at hg; exact ⟨w, rfl, hg⟩
  · rw [hs] at hg; simp [gl] at hg

theorem preprocess_succ (v : Fin n) (i : Bool) :
    I.preprocess.succ v i = I.redirect (I.succ v i) := by
  cases i <;> rfl

theorem redirect_live (w : Fin n) (hw : I.liveWithin n w = true) :
    I.redirect (.inl w) = .inl w := by
  simp [ArrivalInstance.redirect, hw]

theorem redirect_dead (w : Fin n) (hw : I.liveWithin n w = false) :
    I.redirect (.inl w) = .inr .no := by
  simp [ArrivalInstance.redirect, hw]

theorem liveWithin_preprocess (k : ℕ) : ∀ v, I.liveWithin k v = true →
    I.preprocess.liveWithin k v = true := by
  induction k with
  | zero => intro v h; simp [ArrivalInstance.liveWithin] at h
  | succ k ih =>
    intro v h
    have hg : ∀ u, gl I k u = true → gl I.preprocess k (I.redirect u) = true := by
      intro u; cases u with
      | inl w =>
        intro hw
        rw [redirect_live I w (liveWithin_le_n I w hw)]
        exact ih w hw
      | inr _ => intro _; rfl
    rw [liveWithin_succ] at h ⊢
    simp only [Bool.or_eq_true, preprocess_succ] at h ⊢
    rcases h with h | h
    · exact Or.inl (hg _ h)
    · exact Or.inr (hg _ h)

theorem preprocess_preprocessed' : I.preprocess.Preprocessed := by
  intro v
  cases hv : I.liveWithin n v
  · obtain ⟨w, hw, hwd⟩ := dead_succ I v hv false
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := v.pos; omega⟩
    rw [liveWithin_succ, preprocess_succ, hw, redirect_dead I w hwd]
    rfl
  · exact liveWithin_preprocess I n v hv

/-- Simulation invariant between the original run and the preprocessed run. -/
def Inv (k : ℕ) : Prop :=
  (I.preprocess.state k = I.state k ∧
      ∀ u, (I.state k).1 = .inl u → I.liveWithin n u = true) ∨
    ((∃ u, (I.state k).1 = .inl u ∧ I.liveWithin n u = false) ∧
      ((I.preprocess.state k).1 = .inr .no ∨
        ∃ u, (I.preprocess.state k).1 = .inl u ∧ I.liveWithin n u = false))

theorem inv_all (k : ℕ) : Inv I k := by
  induction k with
  | zero =>
    cases h : I.liveWithin n I.origin
    · exact Or.inr ⟨⟨I.origin, rfl, h⟩, Or.inr ⟨I.origin, rfl, h⟩⟩
    · refine Or.inl ⟨rfl, fun u hu => ?_⟩
      have : u = I.origin := (Sum.inl_injective hu).symm
      rw [this]; exact h
  | succ k ih =>
    unfold Inv
    rw [state_succ, state_succ]
    rcases ih with ⟨heq, hlive⟩ | ⟨⟨u, hu, hud⟩, hp⟩
    · rw [heq]
      rcases hs : I.state k with ⟨p, sw⟩
      rw [hs] at hlive
      cases p with
      | inr t => exact Or.inl ⟨rfl, fun u hu => by simp [ArrivalInstance.step] at hu⟩
      | inl v =>
        simp only [ArrivalInstance.step]
        rw [preprocess_succ]
        rcases hsv : I.succ v (sw v) with w | t
        · cases hw : I.liveWithin n w
          · rw [redirect_dead I w hw]
            exact Or.inr ⟨⟨w, rfl, hw⟩, Or.inl rfl⟩
          · rw [redirect_live I w hw]
            refine Or.inl ⟨rfl, fun u hu => ?_⟩
            rw [← Sum.inl_injective hu]; exact hw
        · exact Or.inl ⟨rfl, fun u hu => by simp at hu⟩
    · refine Or.inr ⟨?_, ?_⟩
      · rcases hs : I.state k with ⟨p, sw⟩
        rw [hs] at hu
        simp only at hu
        subst hu
        obtain ⟨w, hw, hwd⟩ := dead_succ I u hud (sw u)
        exact ⟨w, by simp [ArrivalInstance.step, ArrivalInstance.succ] at hw ⊢; exact hw, hwd⟩
      · rcases hs : I.preprocess.state k with ⟨p, sw⟩
        rw [hs] at hp
        rcases hp with hp | ⟨u', hu', hu'd⟩
        · simp only at hp; subst hp; exact Or.inl rfl
        · simp only at hu'; subst hu'
          obtain ⟨w, hw, hwd⟩ := dead_succ I u' hu'd (sw u')
          refine Or.inl ?_
          show I.preprocess.succ u' (sw u') = _
          rw [preprocess_succ, hw, redirect_dead I w hwd]

theorem preprocess_reaches_yes' : I.preprocess.Reaches .yes ↔ I.Reaches .yes := by
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    rcases inv_all I k with ⟨heq, _⟩ | ⟨_, hp | ⟨u, hu, _⟩⟩
    · rw [← heq]; exact hk
    · rw [hp] at hk; cases hk
    · rw [hu] at hk; cases hk
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    rcases inv_all I k with ⟨heq, _⟩ | ⟨⟨u, hu, _⟩, _⟩
    · rw [heq]; exact hk
    · rw [hu] at hk; cases hk

end Arrival

/-! ## The floor trick -/

/-- `h_i` on naturals: `h₀(m) = ⌈m/2⌉`, `h₁(m) = ⌊m/2⌋`. -/
def hN (i : Bool) (m : ℕ) : ℕ := if i then m / 2 else (m + 1) / 2

theorem floor_h (i : Bool) (x : ℚ) (hx : 0 ≤ x) :
    0 ≤ h i x ∧ ⌊h i x⌋₊ = hN i ⌊x⌋₊ := by
  have hm1 : ((⌊x⌋₊ : ℕ) : ℚ) ≤ x := Nat.floor_le hx
  have hm2 : x < (⌊x⌋₊ : ℚ) + 1 := Nat.lt_floor_add_one x
  obtain ⟨q, hq | hq⟩ : ∃ q, ⌊x⌋₊ = 2 * q ∨ ⌊x⌋₊ = 2 * q + 1 := ⟨⌊x⌋₊ / 2, by omega⟩
  · rw [hq] at hm1 hm2
    push_cast at hm1 hm2
    have hz : ⌊x / 2⌋ = (q : ℤ) := by
      rw [Int.floor_eq_iff]; push_cast; constructor <;> linarith
    rw [hq]
    cases i
    · have : h false x = q + (x - 2 * q) := by
        simp only [h, Bool.false_eq_true, if_false, h0, hz]
        push_cast
        rw [min_eq_left (by linarith)]
      rw [this]
      refine ⟨by positivity, ?_⟩
      rw [Nat.floor_eq_iff (by positivity)]
      simp only [hN, Bool.false_eq_true, if_false]
      rw [show (2 * q + 1) / 2 = q by omega]
      constructor <;> linarith
    · have : h true x = q := by
        simp only [h, if_true, h1, hz]
        push_cast
        rw [max_eq_right (by linarith)]
        ring
      rw [this]
      refine ⟨by positivity, ?_⟩
      simp only [hN, if_true, Nat.floor_natCast]
      omega
  · rw [hq] at hm1 hm2
    push_cast at hm1 hm2
    have hz : ⌊x / 2⌋ = (q : ℤ) := by
      rw [Int.floor_eq_iff]; push_cast; constructor <;> linarith
    rw [hq]
    cases i
    · have : h false x = q + 1 := by
        simp only [h, Bool.false_eq_true, if_false, h0, hz]
        push_cast
        rw [min_eq_right (by linarith)]
      rw [this]
      refine ⟨by positivity, ?_⟩
      simp only [hN, Bool.false_eq_true, if_false]
      rw [show (2 * q + 1 + 1) / 2 = q + 1 by omega]
      exact_mod_cast Nat.floor_natCast (q + 1)
    · have : h true x = q + (x - 2 * q - 1) := by
        simp only [h, if_true, h1, hz]
        push_cast
        rw [max_eq_left (by linarith)]
      rw [this]
      refine ⟨by nlinarith, ?_⟩
      rw [Nat.floor_eq_iff (by linarith)]
      simp only [hN, if_true]
      rw [show (2 * q + 1) / 2 = q by omega]
      constructor <;> linarith

section Decode

variable {n : ℕ} (I : ArrivalInstance n)

theorem sum_terminal {M : Type*} [AddCommMonoid M] (g : Terminal → M) :
    ∑ t, g t = g .yes + g .no := by
  rw [show (univ : Finset Terminal) = {.yes, .no} from rfl, sum_pair (by decide)]

/-- Counting labelled edges by their heads. -/
theorem sum_heads {M : Type*} [AddCommMonoid M] (F : Fin n → Bool → M) :
    (∑ v : Fin n, ∑ u, ∑ i, if I.succ u i = .inl v then F u i else 0) +
      ((∑ u, ∑ i, if I.succ u i = .inr .yes then F u i else 0) +
        (∑ u, ∑ i, if I.succ u i = .inr .no then F u i else 0)) = ∑ u, ∑ i, F u i := by
  have h : ∑ w : Node n, ∑ u, ∑ i, (if I.succ u i = w then F u i else 0) = ∑ u, ∑ i, F u i := by
    rw [sum_comm]
    refine sum_congr rfl fun u _ => ?_
    rw [sum_comm]
    refine sum_congr rfl fun i _ => ?_
    rw [sum_ite_eq]; simp
  rw [← h, Fintype.sum_sum_type, sum_terminal]

theorem fp_sum (x : Fin n → ℚ) (hx : I.IsFixedPoint x) :
    I.termInflow x .yes + I.termInflow x .no = 1 := by
  have key := sum_heads I (fun u i => h i (x u))
  have hsum : ∑ u, ∑ i : Bool, h i (x u) = ∑ u, x u := by
    refine sum_congr rfl fun u _ => ?_
    rw [Fintype.sum_bool]
    simp only [h, if_true, Bool.false_eq_true, if_false]
    rw [add_comm, h0_add_h1]
  have hfp : ∑ v, x v = ∑ v, ((if v = I.origin then 1 else 0) + I.inflow x (.inl v)) :=
    sum_congr rfl fun v _ => hx.2 v
  rw [sum_add_distrib, sum_ite_eq' univ I.origin (fun _ => (1 : ℚ)), if_pos (mem_univ _)] at hfp
  unfold ArrivalInstance.termInflow ArrivalInstance.inflow
  unfold ArrivalInstance.inflow at hfp
  linarith

theorem lemma1' (x : Fin n → ℚ) (hx : I.IsFixedPoint x) :
    ∃ t, I.Reaches t ∧ I.termInflow x t = 1 ∧ I.termInflow x t.other = 0 := by
  have hy := fp_sum I x hx
  obtain ⟨hx0, hxfp⟩ := hx
  -- (ii) the floor of a fixed point
  let X : Fin n → ℕ := fun u => ⌊x u⌋₊
  let A : Fin n → Bool → ℕ := fun u i => hN i (X u)
  have hA : ∀ u i, (A u i : ℚ) ≤ h i (x u) := by
    intro u i
    have := floor_h i (x u) (hx0 u)
    show ((hN i ⌊x u⌋₊ : ℕ) : ℚ) ≤ _
    rw [← this.2]; exact Nat.floor_le this.1
  let In : Node n → ℕ := fun w => ∑ u, ∑ i, if I.succ u i = w then A u i else 0
  have hInle : ∀ w, (In w : ℚ) ≤ I.inflow x w := by
    intro w
    simp only [In, ArrivalInstance.inflow]; push_cast
    refine sum_le_sum fun u _ => sum_le_sum fun i _ => ?_
    split_ifs
    · exact hA u i
    · exact le_refl _
  have hXge : ∀ v, (if v = I.origin then 1 else 0) + In (.inl v) ≤ X v := by
    intro v
    apply Nat.le_floor
    rw [hxfp v]; push_cast
    have := hInle (.inl v)
    linarith
  have hXsum : ∑ u, X u = ∑ u, ∑ i, A u i := by
    refine sum_congr rfl fun u _ => ?_
    rw [Fintype.sum_bool]; simp only [A, hN, if_true, Bool.false_eq_true, if_false]; omega
  have key : ∑ v, In (.inl v) + (In (.inr .yes) + In (.inr .no)) = ∑ u, ∑ i, A u i :=
    sum_heads I A
  have hsumle : ∑ v, ((if v = I.origin then 1 else 0) + In (.inl v)) ≤ ∑ v, X v :=
    sum_le_sum fun v _ => hXge v
  have hone : ∑ v, ((if v = I.origin then 1 else 0) + In (.inl v)) = 1 + ∑ v, In (.inl v) := by
    rw [sum_add_distrib, sum_ite_eq' univ I.origin (fun _ => 1), if_pos (mem_univ _)]
  have hup : (In (.inr .yes) : ℚ) + In (.inr .no) ≤ 1 := by
    have := hInle (.inr .yes); have := hInle (.inr .no)
    unfold ArrivalInstance.termInflow at hy; linarith
  have hY : In (.inr .yes) + In (.inr .no) = 1 := by
    have : In (.inr .yes) + In (.inr .no) ≤ 1 := by exact_mod_cast hup
    omega
  have hXeq : ∀ v, X v = (if v = I.origin then 1 else 0) + In (.inl v) := by
    have heq : ∑ v, ((if v = I.origin then 1 else 0) + In (.inl v)) = ∑ v, X v := by omega
    have := (Finset.sum_eq_sum_iff_of_le fun v _ => hXge v).1 heq
    exact fun v => (this v (mem_univ _)).symm
  have hyeq : ∀ t, I.termInflow x t = In (.inr t) := by
    have h1 := hInle (.inr .yes); have h2 := hInle (.inr .no)
    have h3 : (In (.inr .yes) : ℚ) + In (.inr .no) = 1 := by exact_mod_cast hY
    unfold ArrivalInstance.termInflow at hy ⊢
    intro t; cases t <;> linarith
  obtain ⟨ts, h1, h0⟩ : ∃ ts : Terminal, In (.inr ts) = 1 ∧ In (.inr ts.other) = 0 := by
    rcases Nat.eq_zero_or_pos (In (.inr .yes)) with h | h
    · exact ⟨.no, by omega, h⟩
    · exact ⟨.yes, by omega, by show In (.inr .no) = 0; omega⟩
  -- (iii) the switching flow on `G′`
  let G' := I.toSwitchGraph
  let F : Node n × Bool → ℕ := fun p => Sum.elim (fun u => A u p.2) (fun _ => 0) p.1
  have hin : ∀ w, ∑ p : Node n × Bool, (if (lab G' p).2 = w then (F p : ℤ) else 0) = In w := by
    intro w
    simp only [Fintype.sum_prod_type, Fintype.sum_sum_type, F, Sum.elim_inl, Sum.elim_inr,
      Nat.cast_zero, ite_self, sum_const_zero, add_zero, In]
    push_cast
    refine sum_congr rfl fun u _ => sum_congr rfl fun b _ => ?_
    cases b <;> rfl
  have hsf : G'.IsSwitchingFlow (.inl I.origin) (.inr ts) (chi G' F) := by
    constructor
    · intro w
      rw [sum_outE_chi, sum_inE_chi, hin, Fintype.sum_bool]
      cases w with
      | inl v =>
        simp only [F, Sum.elim_inl]
        have hv := hXeq v
        have hXv : A v true + A v false = X v := by simp only [A, hN]; simp; omega
        simp only [Sum.inl.injEq, reduceCtorEq, if_false, sub_zero]
        rw [← hXv] at hv
        split_ifs at hv ⊢ <;> omega
      | inr t =>
        simp only [F, Sum.elim_inr, Nat.cast_zero, add_zero, zero_sub, reduceCtorEq, if_false,
          Sum.inr.injEq]
        by_cases ht : t = ts
        · subst ht; rw [if_pos rfl, h1]; rfl
        · have : t = ts.other := by cases t <;> cases ts <;> simp_all [Terminal.other]
          subst this; rw [if_neg ht, h0]; rfl
    · intro w
      apply chi_switching
      · cases w with
        | inl v => simp only [F, Sum.elim_inl, A, hN]; simp; omega
        | inr _ => exact le_refl _
      · cases w with
        | inl v => simp only [F, Sum.elim_inl, A, hN]; simp; omega
        | inr _ => exact Nat.zero_le _
  have hterm := (dohrau_lemma1_proof G' _ _ Sum.inl_ne_inr _ hsf).1
  refine ⟨ts, (terminates_iff I ts).2 hterm, ?_, ?_⟩
  · rw [hyeq, h1]; rfl
  · rw [hyeq, h0]; rfl

end Decode

end Decoder

namespace Decoder

theorem h_nat (i : Bool) (m : ℕ) : h i (m : ℚ) = (hN i m : ℚ) := by
  obtain ⟨q, hq | hq⟩ : ∃ q, m = 2 * q ∨ m = 2 * q + 1 := ⟨m / 2, by omega⟩ <;> subst hq
  · have hz : ⌊((2 * q : ℕ) : ℚ) / 2⌋ = (q : ℤ) := by
      rw [Int.floor_eq_iff]; push_cast; constructor <;> linarith
    cases i
    · simp only [h, Bool.false_eq_true, if_false, h0, hz, hN]
      rw [show (2 * q + 1) / 2 = q by omega]; push_cast
      rw [min_eq_left (by linarith)]; ring
    · simp only [h, if_true, h1, hz, hN]
      rw [show (2 * q) / 2 = q by omega]; push_cast
      rw [max_eq_right (by linarith)]; ring
  · have hz : ⌊((2 * q + 1 : ℕ) : ℚ) / 2⌋ = (q : ℤ) := by
      rw [Int.floor_eq_iff]; push_cast; constructor <;> linarith
    cases i
    · simp only [h, Bool.false_eq_true, if_false, h0, hz, hN]
      rw [show (2 * q + 1 + 1) / 2 = q + 1 by omega]; push_cast
      rw [min_eq_right (by linarith)]
    · simp only [h, if_true, h1, hz, hN]
      rw [show (2 * q + 1) / 2 = q by omega]; push_cast
      rw [max_eq_left (by linarith)]; ring

end Decoder

open Decoder

/-! ## The target statements (verbatim from `Statements.lean`) -/

theorem toSwitchGraph_terminates_iff_proof {n : ℕ} (I : ArrivalInstance n) (t : Terminal) :
    I.Reaches t ↔ I.toSwitchGraph.RunTerminates (.inl I.origin) (.inr t) :=
  terminates_iff I t

theorem reaches_unique_proof {n : ℕ} (I : ArrivalInstance n) {t t' : Terminal}
    (ht : I.Reaches t) (ht' : I.Reaches t') : t = t' :=
  reaches_unique' I ht ht'

theorem reaches_iff_outcomeWithin_proof {n : ℕ} (I : ArrivalInstance n) (t : Terminal) :
    I.Reaches t ↔ I.outcomeWithin (n * 2 ^ n) = some t :=
  reaches_iff_outcomeWithin' I t

theorem preprocess_reaches_yes_proof {n : ℕ} (I : ArrivalInstance n) :
    I.preprocess.Reaches .yes ↔ I.Reaches .yes :=
  preprocess_reaches_yes' I

theorem preprocess_preprocessed_proof {n : ℕ} (I : ArrivalInstance n) :
    I.preprocess.Preprocessed :=
  preprocess_preprocessed' I

theorem h_floor_proof (i : Bool) (x : ℚ) (hx : 0 ≤ x) :
    h i ((⌊x⌋ : ℤ) : ℚ) = ((⌊h i x⌋ : ℤ) : ℚ) := by
  obtain ⟨hpos, hfl⟩ := floor_h i x hx
  rw [← Int.natCast_floor_eq_floor hx, ← Int.natCast_floor_eq_floor hpos, hfl]
  push_cast
  exact h_nat i _

theorem fixedPoint_termInflow_sum_proof {n : ℕ} (I : ArrivalInstance n) (x : Fin n → ℚ)
    (hx : I.IsFixedPoint x) : I.termInflow x .yes + I.termInflow x .no = 1 :=
  fp_sum I x hx

theorem lemma1_proof {n : ℕ} (I : ArrivalInstance n) (x : Fin n → ℚ) (hx : I.IsFixedPoint x) :
    ∃ t, I.Reaches t ∧ I.termInflow x t = 1 ∧ I.termInflow x t.other = 0 :=
  lemma1' I x hx

#print axioms dohrau_lemma1_proof
#print axioms toSwitchGraph_terminates_iff_proof
#print axioms reaches_unique_proof
#print axioms reaches_iff_outcomeWithin_proof
#print axioms preprocess_reaches_yes_proof
#print axioms preprocess_preprocessed_proof
#print axioms h_floor_proof
#print axioms fixedPoint_termInflow_sum_proof
#print axioms lemma1_proof

end Bssg
