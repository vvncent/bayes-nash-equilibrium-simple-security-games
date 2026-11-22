import Mathlib
import BssgProofs.Statements
import BssgProofs.Proofs.Embedding

/-!
# Bit-length bounds for `Red` (simple-proof, "Sizes" paragraph of the proof of the Theorem)

`ratBits q = Nat.size |num q| + Nat.size (den q)` is the binary length of a rational in lowest
terms (`Nat.size k` = number of binary digits of `k`, `Nat.size 0 = 0`).

Main results (for every ARRIVAL instance `I` with `n` switches; `N := n + 1`):

* `redMarket_bits`: every mass, capacity, intercept and slope of the §5 market (of any instance,
  in particular of `I.preprocess`, the one used by `Red`) has `ratBits ≤ 6 N`.
* `red_bits`: every prior and every attacker payoff entry `u₂⁰(θ,t)`, `u₂¹(θ,t)` of `Red I` has
  `ratBits ≤ 28 N`; the defender payoffs `0, 1` have `ratBits ≤ 2`; `r = 1`.
* `red_descBits`: the total description length `descBits (Red I)` (sum of `ratBits` over all
  numbers of the explicit game, plus `Nat.size r`) is `≤ 8500 N⁵`.
* `red_descBits_product`: the coarser count `(#types)(#targets)(2·28N) + (#types)(28N)
  + (#targets)(2·2) + 1` (every entry charged the maximal bound) is `≤ 8500 N⁵`.

Method: every market number is a natural number `≤ R²` with `R = 4^{n+1}`; then `W, A, S` and the
type weights are naturals bounded by powers of `R`, priors are `weight/total`, payoffs `x/S` with
`|x| ≤ R⁸`, `S ≤ R⁵`; and `Nat.size (R^k) = 2k(n+1) + 1`.
-/

namespace Bssg

open Finset

set_option linter.unusedSectionVars false

/-- Binary length of a rational: bits of `|numerator|` plus bits of the denominator
(`q` is stored in lowest terms, `den ≥ 1`). -/
def ratBits (q : ℚ) : ℕ := Nat.size q.num.natAbs + Nat.size q.den

/-- Total binary description length of an explicit Bayesian simple security game: the number of
resources, every prior, every defender payoff `u₁⁰(t), u₁¹(t)` and every attacker payoff
`u₂⁰(θ,t), u₂¹(θ,t)`. -/
def BSSG.descBits {T Θ : Type*} [Fintype T] [Fintype Θ] (G : BSSG T Θ) : ℕ :=
  Nat.size G.r + (∑ θ, ratBits (G.prior θ)) + (∑ t, (ratBits (G.ud0 t) + ratBits (G.ud1 t))) +
    ∑ θ, ∑ t, (ratBits (G.ua0 θ t) + ratBits (G.ua1 θ t))

namespace Size

/-! ### Rationals given as bounded fractions -/

/-- `q = x / y` with `|x| ≤ X`, `0 < y ≤ Y`. -/
def Small (q : ℚ) (X Y : ℕ) : Prop :=
  ∃ x : ℤ, ∃ y : ℕ, 0 < y ∧ q = (x : ℚ) / (y : ℚ) ∧ x.natAbs ≤ X ∧ y ≤ Y

theorem ratBits_div (x : ℤ) (y : ℕ) (hy : 0 < y) :
    ratBits ((x : ℚ) / (y : ℚ)) ≤ Nat.size x.natAbs + Nat.size y := by
  have hq : (x : ℚ) / (y : ℚ) = Rat.divInt x y := by rw [Rat.divInt_eq_div]; simp
  rw [ratBits, hq]
  have hy0 : (y : ℤ) ≠ 0 := by exact_mod_cast hy.ne'
  apply add_le_add
  · apply Nat.size_le_size
    by_cases hx : x = 0
    · subst hx; simp
    · exact Int.natAbs_le_of_dvd_ne_zero (Rat.num_dvd x hy0) hx
  · apply Nat.size_le_size
    have h := Int.le_of_dvd (by exact_mod_cast hy) (Rat.den_dvd x y)
    exact_mod_cast h

theorem Small.bits {q : ℚ} {X Y : ℕ} (h : Small q X Y) : ratBits q ≤ Nat.size X + Nat.size Y := by
  obtain ⟨x, y, hy, rfl, hx, hyY⟩ := h
  exact (ratBits_div x y hy).trans (add_le_add (Nat.size_le_size hx) (Nat.size_le_size hyY))

theorem Small.congr {q q' : ℚ} {X Y : ℕ} (h : Small q X Y) (e : q = q') : Small q' X Y := e ▸ h

/-! ### Rationals that are bounded naturals -/

/-- `q` is a natural number `≤ B`. -/
def NatLe (q : ℚ) (B : ℕ) : Prop := ∃ k : ℕ, q = k ∧ k ≤ B

theorem NatLe.mono {q : ℚ} {B B' : ℕ} (h : NatLe q B) (hB : B ≤ B') : NatLe q B' := by
  obtain ⟨k, rfl, hk⟩ := h; exact ⟨k, rfl, hk.trans hB⟩

theorem NatLe.nonneg {q : ℚ} {B : ℕ} (h : NatLe q B) : 0 ≤ q := by
  obtain ⟨k, rfl, -⟩ := h; positivity

theorem NatLe.le {q : ℚ} {B : ℕ} (h : NatLe q B) : q ≤ B := by
  obtain ⟨k, rfl, hk⟩ := h; exact_mod_cast hk

theorem NatLe.congr' {p q : ℚ} {b : ℕ} (h : NatLe p b) (e : p = q) : NatLe q b := e ▸ h

theorem natLe_nat (k : ℕ) {B : ℕ} (h : k ≤ B) : NatLe (k : ℚ) B := ⟨k, rfl, h⟩

theorem NatLe.add {p q : ℚ} {a b : ℕ} (hp : NatLe p a) (hq : NatLe q b) : NatLe (p + q) (a + b) := by
  obtain ⟨k, rfl, hk⟩ := hp; obtain ⟨l, rfl, hl⟩ := hq
  exact ⟨k + l, by push_cast; ring, add_le_add hk hl⟩

theorem NatLe.mul {p q : ℚ} {a b : ℕ} (hp : NatLe p a) (hq : NatLe q b) : NatLe (p * q) (a * b) := by
  obtain ⟨k, rfl, hk⟩ := hp; obtain ⟨l, rfl, hl⟩ := hq
  exact ⟨k * l, by push_cast; ring, Nat.mul_le_mul hk hl⟩

theorem NatLe.sub {p q : ℚ} {a b : ℕ} (hp : NatLe p a) (hq : NatLe q b) (h : q ≤ p) :
    NatLe (p - q) a := by
  obtain ⟨k, rfl, hk⟩ := hp; obtain ⟨l, rfl, hl⟩ := hq
  have hlk : l ≤ k := by exact_mod_cast h
  exact ⟨k - l, by rw [Nat.cast_sub hlk], (Nat.sub_le k l).trans hk⟩

theorem natLe_sum {ι : Type*} (s : Finset ι) (f : ι → ℚ) (B : ℕ) (h : ∀ i ∈ s, NatLe (f i) B) :
    NatLe (∑ i ∈ s, f i) (s.card * B) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simp, by simp⟩
  | insert a s ha ih =>
    rw [sum_insert ha, card_insert_of_notMem ha, Nat.succ_mul, add_comm (s.card * B)]
    exact (h a (mem_insert_self a s)).add (ih fun i hi => h i (mem_insert_of_mem hi))

theorem natLe_fold_max {ι : Type*} (s : Finset ι) (f : ι → ℚ) (B : ℕ)
    (h : ∀ i ∈ s, NatLe (f i) B) : NatLe (s.fold max 0 f) B := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simp, Nat.zero_le _⟩
  | insert a s ha ih =>
    rw [fold_insert ha]
    obtain ⟨k, hk, hkB⟩ := h a (mem_insert_self a s)
    obtain ⟨l, hl, hlB⟩ := ih fun i hi => h i (mem_insert_of_mem hi)
    exact ⟨max k l, by rw [hk, hl, Nat.cast_max], max_le hkB hlB⟩

theorem NatLe.small {q : ℚ} {B : ℕ} (h : NatLe q B) : Small q B 1 := by
  obtain ⟨k, rfl, hk⟩ := h
  exact ⟨k, 1, one_pos, by simp, by simpa using hk, le_rfl⟩

/-- A small integer constant. -/
theorem small_const {q : ℚ} {X Y : ℕ} (z : ℤ) (hq : q = z) (hz : z.natAbs ≤ X) (hY : 1 ≤ Y) :
    Small q X Y := ⟨z, 1, one_pos, by simp [hq], hz, hY⟩

/-! ### `Nat.size` of powers of `R = 4^{n+1}` -/

theorem size_le_R (n k x : ℕ) (hx : x ≤ (4 ^ (n + 1)) ^ k) :
    Nat.size x ≤ 2 * k * (n + 1) + 1 := by
  have : (4 ^ (n + 1)) ^ k = 2 ^ (2 * k * (n + 1)) := by
    rw [← pow_mul, show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul]; ring_nf
  rw [this] at hx
  exact (Nat.size_le_size hx).trans (by rw [Nat.size_pow])

/-! ### Generic bounds for the game Γ built from a market (§6) -/

section Game

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
  (Mk : Market I J) (B : ℕ)
  (hm : ∀ i, NatLe (Mk.mass i) B) (hc : ∀ j, NatLe (Mk.cap j) B)
  (ha : ∀ e, NatLe (Mk.a e) B) (hb : ∀ e, NatLe (Mk.b e) B)

include hm hc in
theorem gW_natLe : NatLe Mk.gW (1 + Fintype.card I * B + B) := by
  unfold Market.gW
  refine ((natLe_nat 1 le_rfl).add ?_).add (natLe_fold_max _ _ _ fun j _ => hc j)
  simpa [card_univ] using natLe_sum univ Mk.mass B fun i _ => hm i

include hm in
theorem cap_add_one_le_gW (j : J) : Mk.cap j + 1 ≤ Mk.gW := by
  unfold Market.gW
  have h1 : Mk.cap j ≤ univ.fold max 0 Mk.cap := (le_fold_max _).2 (Or.inr ⟨j, mem_univ _, le_rfl⟩)
  have h2 : 0 ≤ ∑ i, Mk.mass i := sum_nonneg fun i _ => (hm i).nonneg
  linarith

include hm hc in
theorem one_le_gW : 1 ≤ Mk.gW := by
  unfold Market.gW
  have h1 : (0 : ℚ) ≤ univ.fold max 0 Mk.cap := (le_fold_max _).2 (Or.inl le_rfl)
  have h2 : 0 ≤ ∑ i, Mk.mass i := sum_nonneg fun i _ => (hm i).nonneg
  linarith

include hm hc in
theorem weight_natLe (θ : MType I J) :
    NatLe (Mk.gWeight θ) (1 + Fintype.card I * B + B + B) ∧ 1 ≤ Mk.gWeight θ := by
  have hW := gW_natLe Mk B hm hc
  have hW1 := one_le_gW Mk B hm hc
  rcases θ with i | j | u
  · exact ⟨hW.add (hm i), by simp only [Market.gWeight]; linarith [(hm i).nonneg]⟩
  · have := cap_add_one_le_gW Mk B hm j
    exact ⟨(hW.sub (hc j) (by linarith)).mono (Nat.le_add_right _ _),
      by simp only [Market.gWeight]; linarith⟩
  · exact ⟨hW.mono (Nat.le_add_right _ _), hW1⟩

include hm hc in
theorem prior_small (θ : MType I J) :
    Small (Mk.toGame.prior θ) (1 + Fintype.card I * B + B + B)
      (Fintype.card (MType I J) * (1 + Fintype.card I * B + B + B)) := by
  obtain ⟨k, hk, hkB⟩ := (weight_natLe Mk B hm hc θ).1
  obtain ⟨t, ht, htB⟩ := natLe_sum univ Mk.gWeight _ fun θ' _ => (weight_natLe Mk B hm hc θ').1
  have hpos : (1 : ℚ) ≤ ∑ θ', Mk.gWeight θ' :=
    (weight_natLe Mk B hm hc (.inr (.inr ()))).2.trans
      (single_le_sum (f := Mk.gWeight) (fun θ' _ => (zero_le_one.trans (weight_natLe Mk B hm hc θ').2))
        (mem_univ _))
  have htpos : 0 < t := by
    have : (1 : ℚ) ≤ t := ht ▸ hpos
    exact_mod_cast this
  refine ⟨k, t, htpos, ?_, by simpa using hkB, by simpa [card_univ] using htB⟩
  show Mk.gWeight θ / ∑ θ', Mk.gWeight θ' = _
  rw [hk, ht]; simp

include ha in
theorem gA_natLe : NatLe Mk.gA (1 + B) :=
  (natLe_nat 1 le_rfl).add (natLe_fold_max _ _ _ fun e _ => ha e)

include ha in
theorem gS_natLe :
    NatLe Mk.gS (1 + (Fintype.card I + Fintype.card J) * (1 + B)) ∧ 1 ≤ Mk.gS := by
  have hA := gA_natLe Mk B ha
  refine ⟨?_, ?_⟩
  · unfold Market.gS
    refine (natLe_nat 1 le_rfl).add
      (((natLe_nat (Fintype.card I + Fintype.card J) le_rfl).mul hA).congr' ?_)
    push_cast; ring
  · unfold Market.gS
    have : 0 ≤ ((Fintype.card I : ℚ) + Fintype.card J) * Mk.gA :=
      mul_nonneg (by positivity) hA.nonneg
    linarith

/-- Numerator bound for payoff entries. -/
def payX (BS : ℕ) : ℕ := 4 + 2 * B + BS + B * BS

include ha hb in
theorem pay_small (θ : MType I J) (k : MTarget I J) :
    Small (Mk.gPay θ k).1 (payX B (1 + (Fintype.card I + Fintype.card J) * (1 + B)))
        (1 + (Fintype.card I + Fintype.card J) * (1 + B)) ∧
      Small ((Mk.gPay θ k).1 - (Mk.gPay θ k).2)
        (payX B (1 + (Fintype.card I + Fintype.card J) * (1 + B)))
        (1 + (Fintype.card I + Fintype.card J) * (1 + B)) := by
  set BS := 1 + (Fintype.card I + Fintype.card J) * (1 + B)
  obtain ⟨⟨s, hs, hsB⟩, hS1⟩ := gS_natLe Mk B ha
  have hspos : 0 < s := by
    have : (1 : ℚ) ≤ s := hs ▸ hS1
    exact_mod_cast this
  have hBS : 1 ≤ BS := Nat.le_add_right _ _
  have hX3 : (3 : ℕ) ≤ payX B BS := by unfold payX; omega
  have frac : ∀ (x : ℚ) (bx : ℕ) (y : ℚ) (by_ : ℕ), NatLe x bx → NatLe y by_ →
      bx + by_ * BS ≤ payX B BS →
      Small (x / Mk.gS) (payX B BS) BS ∧ Small (x / Mk.gS - y) (payX B BS) BS := by
    intro x bx y by_ hx hy hle
    obtain ⟨kx, rfl, hkx⟩ := hx
    obtain ⟨ky, rfl, hky⟩ := hy
    refine ⟨⟨kx, s, hspos, by rw [hs]; simp, ?_, hsB⟩,
      ⟨(kx : ℤ) - (ky : ℤ) * s, s, hspos, ?_, ?_, hsB⟩⟩
    · rw [Int.natAbs_natCast]
      exact le_trans hkx (le_trans (Nat.le_add_right _ _) hle)
    · rw [hs]; push_cast; field_simp
    · calc ((kx : ℤ) - (ky : ℤ) * s).natAbs ≤ ((kx : ℤ)).natAbs + ((ky : ℤ) * s).natAbs :=
            Int.natAbs_sub_le _ _
        _ = kx + ky * s := by simp [Int.natAbs_mul]
        _ ≤ bx + by_ * BS := add_le_add hkx (Nat.mul_le_mul hky hsB)
        _ ≤ payX B BS := hle
  have cst : ∀ (c d : ℤ), c.natAbs ≤ 3 → (c - d).natAbs ≤ 3 →
      Small (c : ℚ) (payX B BS) BS ∧ Small ((c : ℚ) - (d : ℚ)) (payX B BS) BS := fun c d h1 h2 =>
    ⟨small_const c rfl (h1.trans hX3) hBS,
      small_const (c - d) (by push_cast; ring) (h2.trans hX3) hBS⟩
  have hA := gA_natLe Mk B ha
  rcases θ with i | j | u <;> rcases k with j' | i' | u' | u' <;> (try cases u) <;> (try cases u') <;>
    simp only [Market.gPay] <;> (try split_ifs) <;>
    first
    | exact frac _ _ _ _ (ha _) (hb _) (by unfold payX; nlinarith)
    | exact frac _ _ _ _ hA (natLe_nat 1 le_rfl) (by unfold payX; nlinarith)
    | (have h := cst (-2) 1 (by decide) (by decide); norm_num at h ⊢; exact h)
    | (have h := cst 2 1 (by decide) (by decide); norm_num at h ⊢; exact h)
    | (have h := cst 0 1 (by decide) (by decide); norm_num at h ⊢; exact h)

end Game

/-! ### Arithmetic on `R = 4^{n+1}` -/

theorem R_facts (n : ℕ) : 4 ≤ 4 ^ (n + 1) ∧ 4 * 2 ^ n ≤ 4 ^ (n + 1) ∧ 4 * (n + 1) ≤ 4 ^ (n + 1) ∧
    3 ^ (n + 1) ≤ 4 ^ (n + 1) := by
  have h1 : 2 ^ n ≤ 4 ^ n := Nat.pow_le_pow_left (by norm_num) n
  have h2 : n + 1 ≤ 2 ^ n := Nat.lt_two_pow_self
  have h3 : 1 ≤ 4 ^ n := Nat.one_le_pow _ _ (by norm_num)
  refine ⟨?_, ?_, ?_, Nat.pow_le_pow_left (by norm_num) _⟩ <;> rw [pow_succ] <;> omega

theorem poly (R a b : ℕ) (hR : 4 ≤ R) (hab : a + b + 3 ≤ R ^ 2) :
    1 + a * R ^ 2 + R ^ 2 + R ^ 2 ≤ R ^ 4 ∧
    (a + (b + 1)) * (1 + a * R ^ 2 + R ^ 2 + R ^ 2) ≤ R ^ 6 ∧
    1 + (a + b) * (1 + R ^ 2) ≤ R ^ 5 ∧
    payX (R ^ 2) (1 + (a + b) * (1 + R ^ 2)) ≤ R ^ 8 := by
  set Q := R ^ 2 with hQ
  have hQ16 : 16 ≤ Q := by rw [hQ]; nlinarith
  have e4 : R ^ 4 = Q * Q := by rw [hQ]; ring
  have e5 : R ^ 5 = R * (Q * Q) := by rw [hQ]; ring
  have e6 : R ^ 6 = Q * (Q * Q) := by rw [hQ]; ring
  have e8 : R ^ 8 = Q * (Q * (Q * Q)) := by rw [hQ]; ring
  have A1 : 1 + a * Q + Q + Q ≤ Q * Q := by nlinarith
  have A2 : (a + (b + 1)) * (1 + a * Q + Q + Q) ≤ Q * (Q * Q) :=
    Nat.mul_le_mul (by omega) A1
  have A3 : 1 + (a + b) * (1 + Q) ≤ R * (Q * Q) := by
    have : 1 + (a + b) * (1 + Q) ≤ Q * (1 + Q) := by nlinarith
    have : Q * (1 + Q) ≤ 4 * (Q * Q) := by nlinarith
    have : 4 * (Q * Q) ≤ R * (Q * Q) := Nat.mul_le_mul_right _ hR
    omega
  refine ⟨e4 ▸ A1, e6 ▸ A2, e5 ▸ A3, ?_⟩
  rw [e8]
  set BS := 1 + (a + b) * (1 + Q)
  have hRQ : R ≤ Q := by rw [hQ]; nlinarith
  have hB1 : BS ≤ Q * (Q * Q) := A3.trans (Nat.mul_le_mul_right _ hRQ)
  have hB2 : Q * BS ≤ Q * (Q * (Q * Q)) / 2 := by
    have : Q * BS ≤ Q * (Q * (Q * Q)) := Nat.mul_le_mul_left _ hB1
    have h4 : 4 * (Q * BS) ≤ R * (Q * BS) := Nat.mul_le_mul_right _ hR
    have h5 : R * (Q * BS) ≤ Q * (Q * (Q * Q)) := by
      calc R * (Q * BS) = Q * (R * BS) := by ring
        _ ≤ Q * (R * (R * (Q * Q))) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ A3)
        _ = Q * (Q * (Q * Q)) := by rw [hQ]; ring
    omega
  have hQQ : Q * (Q * Q) * 16 ≤ Q * (Q * (Q * Q)) := by
    have := Nat.mul_le_mul_left (Q * (Q * Q)) hQ16; linarith
  have hQ2 : Q * 16 ≤ Q * Q := Nat.mul_le_mul_left Q hQ16
  have hQ3 : Q * Q * 16 ≤ Q * (Q * Q) := by have := Nat.mul_le_mul_left (Q * Q) hQ16; linarith
  unfold payX; omega

/-! ### The §5 market of an arbitrary instance -/

section Market

variable {n : ℕ} (I : ArrivalInstance n)

theorem indeg_le (w : Node n) : I.indeg w ≤ 2 * n := by
  unfold ArrivalInstance.indeg
  refine (card_filter_le _ _).trans ?_
  simp [card_univ, mul_comm]

theorem gCap_natLe (a : GArc n) : NatLe (gCap a) (2 ^ n) := by
  rcases a with _ | ⟨j, r⟩
  · exact ⟨1, by simp [gCap], Nat.one_le_two_pow⟩
  · exact ⟨2 ^ (j : ℕ), by simp [gCap], Nat.pow_le_pow_right (by norm_num) j.isLt.le⟩

theorem gCost_natLe (a : GArc n) : NatLe (gCost a) (3 ^ n) := by
  rcases a with _ | ⟨j, r⟩
  · exact ⟨0, by simp [gCost], Nat.zero_le _⟩
  · simp only [gCost]
    split_ifs
    · exact ⟨0, by simp, Nat.zero_le _⟩
    · exact ⟨3 ^ ((j : ℕ) + 1), by simp, Nat.pow_le_pow_right (by norm_num) j.isLt⟩

theorem inCap_natLe (u : SNode n) : NatLe (inCap n u) ((8 * n + 2) * 2 ^ n) := by
  unfold inCap Network.inflow
  refine (natLe_sum _ _ _ fun a _ => gCap_natLe a.2).mono (Nat.mul_le_mul_right _ ?_)
  exact (card_filter_le _ _).trans (by rw [card_univ, Emb.card_SArc])

theorem capV_natLe (v : Fin n) : NatLe (I.capV v) (1 + 2 ^ n * (2 * n)) :=
  ⟨1 + 2 ^ n * I.indeg (.inl v), by simp [ArrivalInstance.capV],
    Nat.add_le_add_left (Nat.mul_le_mul_left _ (indeg_le I _)) _⟩

theorem market_natLe :
    (∀ i, NatLe (I.redMarket.mass i) ((4 ^ (n + 1)) ^ 2)) ∧
    (∀ j, NatLe (I.redMarket.cap j) ((4 ^ (n + 1)) ^ 2)) ∧
    (∀ e, NatLe (I.redMarket.a e) ((4 ^ (n + 1)) ^ 2)) ∧
    (∀ e, NatLe (I.redMarket.b e) ((4 ^ (n + 1)) ^ 2)) := by
  obtain ⟨hR4, hP, hN, hT⟩ := R_facts n
  set R := 4 ^ (n + 1)
  have hP1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  have key : 2 + 2 ^ n * (4 * n) + (8 * n + 2) * 2 ^ n ≤ R ^ 2 := by
    have := Nat.mul_le_mul hP hN
    nlinarith
  have k4 : 4 * 3 ^ (n + 1) ≤ R ^ 2 := by nlinarith
  have h2M : NatLe (2 * bigM n) (4 * 3 ^ (n + 1)) :=
    ⟨4 * 3 ^ (n + 1), by simp only [bigM]; push_cast; ring, le_rfl⟩
  have hM : NatLe (bigM n) (4 * 3 ^ (n + 1)) :=
    ⟨2 * 3 ^ (n + 1), by simp only [bigM]; push_cast; ring, by omega⟩
  have h3n : 3 ^ n ≤ 3 ^ (n + 1) := Nat.pow_le_pow_right (by norm_num) (Nat.le_succ n)
  have hM6 : (6 : ℚ) ≤ bigM n := by
    have : (3 : ℚ) ≤ 3 ^ (n + 1) := le_self_pow₀ (by norm_num) (Nat.succ_ne_zero n)
    simp only [bigM]; linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i
    simp only [ArrivalInstance.redMarket]
    by_cases h1 : i.2 = sSource n
    · simp only [h1, ↓reduceIte]
      have : NatLe (if i.1 = I.origin then (1 : ℚ) else 0) 1 := by
        split_ifs
        · exact ⟨1, by simp, le_rfl⟩
        · exact ⟨0, by simp, Nat.zero_le _⟩
      refine ((capV_natLe I i.1).add this).mono (by nlinarith)
    · simp only [h1, ↓reduceIte]
      exact (inCap_natLe i.2).mono (by nlinarith)
  · intro j
    rcases j with v | ⟨v, a⟩ | u
    · exact (capV_natLe I v).mono (by nlinarith)
    · exact (gCap_natLe a.2).mono (by nlinarith)
    · cases u
      refine ⟨1 + 2 ^ n * (I.indeg (.inr .yes) + I.indeg (.inr .no)), by simp [ArrivalInstance.redMarket, ArrivalInstance.capV], ?_⟩
      have := indeg_le I (.inr .yes); have := indeg_le I (.inr .no)
      have : 2 ^ n * (I.indeg (.inr .yes) + I.indeg (.inr .no)) ≤ 2 ^ n * (4 * n) :=
        Nat.mul_le_mul_left _ (by omega)
      omega
  · rintro ⟨⟨v, u⟩, g⟩
    show NatLe (ArrivalInstance.redA _) _
    rcases g with w | ⟨v', a⟩ | u'
    · simp only [ArrivalInstance.redA]
      split_ifs
      · exact h2M.mono k4
      · exact hM.mono k4
      · exact ((hM.sub (natLe_nat 3 le_rfl) (by push_cast; linarith)).mono k4).congr' (by simp [epsC])
    · simp only [ArrivalInstance.redA]
      split_ifs
      · have hc3 : gCost a.2 ≤ 2 * bigM n := by
          have e : (2 : ℚ) * bigM n = ((4 * 3 ^ (n + 1) : ℕ) : ℚ) := by
            simp only [bigM]; push_cast; ring
          rw [e]
          exact (gCost_natLe a.2).le.trans (by exact_mod_cast (by omega))
        exact (h2M.sub (gCost_natLe a.2) hc3).mono k4
      · exact h2M.mono k4
    · simp only [ArrivalInstance.redA]
      split_ifs
      · exact h2M.mono k4
      · exact hM.mono k4
      · exact ((hM.sub (natLe_nat 3 le_rfl) (by push_cast; linarith)).mono k4).congr' (by simp [epsC])
  · rintro ⟨⟨v, u⟩, g⟩
    show NatLe (ArrivalInstance.redB _) _
    rcases g with w | ⟨v', a⟩ | u'
    · simp only [ArrivalInstance.redB]
      split_ifs
      · exact (h2M.mono k4).congr' (by simp [lam])
      · exact natLe_nat 1 (by nlinarith)
    · exact natLe_nat 1 (by nlinarith) |>.congr' (by simp [ArrivalInstance.redB])
    · simp only [ArrivalInstance.redB]
      split_ifs
      · exact (h2M.mono k4).congr' (by simp [lam])
      · exact natLe_nat 1 (by nlinarith)

end Market

end Size

/-! ### Main results -/

open Size in
/-- **Market bit bound.** Every number of the §5 market of an instance with `n` switches (masses,
capacities, and the intercept and slope of every buyer–good pair) has `ratBits ≤ 6(n+1)`.
Applies in particular to `I.preprocess.redMarket`, the market inside `Red I`. -/
theorem redMarket_bits {n : ℕ} (I : ArrivalInstance n) :
    (∀ i, ratBits (I.redMarket.mass i) ≤ 6 * (n + 1)) ∧
    (∀ j, ratBits (I.redMarket.cap j) ≤ 6 * (n + 1)) ∧
    (∀ e, ratBits (I.redMarket.a e) ≤ 6 * (n + 1)) ∧
    (∀ e, ratBits (I.redMarket.b e) ≤ 6 * (n + 1)) := by
  obtain ⟨h1, h2, h3, h4⟩ := market_natLe I
  have key : ∀ q : ℚ, NatLe q ((4 ^ (n + 1)) ^ 2) → ratBits q ≤ 6 * (n + 1) := fun q hq => by
    have h5 := hq.small.bits
    have h6 := size_le_R n 2 _ le_rfl
    rw [Nat.size_one] at h5; omega
  exact ⟨fun i => key _ (h1 i), fun j => key _ (h2 j), fun e => key _ (h3 e), fun e => key _ (h4 e)⟩

open Size in
/-- **Entry bit bound for `Red`.** For every ARRIVAL instance with `n` switches, `Red I` has one
resource, every prior and every attacker payoff entry (uncovered `u₂⁰` and covered `u₂¹`, for all
types × targets) has `ratBits ≤ 28(n+1)`, and the defender payoffs (`0` and `1`) have
`ratBits ≤ 2`. -/
theorem red_bits {n : ℕ} (I : ArrivalInstance n) :
    (Red I).r = 1 ∧
    (∀ θ, ratBits ((Red I).prior θ) ≤ 28 * (n + 1)) ∧
    (∀ θ t, ratBits ((Red I).ua0 θ t) ≤ 28 * (n + 1) ∧ ratBits ((Red I).ua1 θ t) ≤ 28 * (n + 1)) ∧
    (∀ t, ratBits ((Red I).ud0 t) ≤ 2 ∧ ratBits ((Red I).ud1 t) ≤ 2) := by
  obtain ⟨hm, hc, ha, hb⟩ := market_natLe I.preprocess
  obtain ⟨hR4, -, hN, -⟩ := R_facts n
  have hab : Fintype.card (RBuyer n) + Fintype.card (RGood n) + 3 ≤ (4 ^ (n + 1)) ^ 2 := by
    rw [Emb.card_RBuyer, Emb.card_RGood]; nlinarith
  obtain ⟨p1, p2, p3, p4⟩ := poly (4 ^ (n + 1)) _ _ hR4 hab
  have cardT : Fintype.card (MType (RBuyer n) (RGood n)) =
      Fintype.card (RBuyer n) + (Fintype.card (RGood n) + 1) := by
    simp [Fintype.card_sum]
  refine ⟨rfl, ?_, ?_, ?_⟩
  · intro θ
    have h := (prior_small I.preprocess.redMarket _ hm hc θ).bits
    have s1 := size_le_R n 4 _ p1
    have p2' : Fintype.card (MType (RBuyer n) (RGood n)) *
        (1 + Fintype.card (RBuyer n) * (4 ^ (n + 1)) ^ 2 + (4 ^ (n + 1)) ^ 2 + (4 ^ (n + 1)) ^ 2)
        ≤ (4 ^ (n + 1)) ^ 6 := by rw [cardT]; exact p2
    have s2 := size_le_R n 6 _ p2'
    change ratBits (I.preprocess.redMarket.toGame.prior θ) ≤ _
    omega
  · intro θ t
    obtain ⟨q0, q1⟩ := pay_small I.preprocess.redMarket _ ha hb θ t
    have s1 := size_le_R n 8 _ p4
    have s2 := size_le_R n 5 _ p3
    have b0 := q0.bits
    have b1 := q1.bits
    exact ⟨by change ratBits (I.preprocess.redMarket.gPay θ t).1 ≤ _; omega,
      by
        change ratBits ((I.preprocess.redMarket.gPay θ t).1 -
          (I.preprocess.redMarket.gPay θ t).2) ≤ _
        omega⟩
  · intro t
    refine ⟨?_, ?_⟩ <;> simp [Red, Market.toGame, ratBits]

open Size in
/-- **Total description size, product form.** Charging every entry its maximal bound:
`descBits (Red I) ≤ #types·#targets·(2·28(n+1)) + #types·28(n+1) + #targets·(2+2) + 1`. -/
theorem red_descBits_le_product {n : ℕ} (I : ArrivalInstance n) :
    (Red I).descBits ≤
      Fintype.card (RType n) * Fintype.card (RTarget n) * (2 * (28 * (n + 1))) +
        Fintype.card (RType n) * (28 * (n + 1)) + Fintype.card (RTarget n) * 4 + 1 := by
  obtain ⟨hr, hp, hu, hd⟩ := red_bits I
  unfold BSSG.descBits
  rw [hr, Nat.size_one]
  have e1 : ∑ θ, ratBits ((Red I).prior θ) ≤ Fintype.card (RType n) * (28 * (n + 1)) := by
    simpa [card_univ] using sum_le_card_nsmul univ _ _ fun θ _ => hp θ
  have e2 : ∑ t, (ratBits ((Red I).ud0 t) + ratBits ((Red I).ud1 t)) ≤
      Fintype.card (RTarget n) * 4 := by
    simpa [card_univ] using sum_le_card_nsmul univ _ 4 fun t _ =>
      (add_le_add (hd t).1 (hd t).2 : _ ≤ 2 + 2)
  have e3 : ∑ θ, ∑ t, (ratBits ((Red I).ua0 θ t) + ratBits ((Red I).ua1 θ t)) ≤
      Fintype.card (RType n) * (Fintype.card (RTarget n) * (2 * (28 * (n + 1)))) := by
    have := sum_le_card_nsmul univ (fun θ => ∑ t, (ratBits ((Red I).ua0 θ t) +
        ratBits ((Red I).ua1 θ t))) (Fintype.card (RTarget n) * (2 * (28 * (n + 1))))
      fun θ _ => by
        simpa [card_univ] using sum_le_card_nsmul univ _ _ fun t _ =>
          (add_le_add (hu θ t).1 (hu θ t).2).trans (by omega)
    simpa [card_univ] using this
  rw [mul_assoc (Fintype.card (RType n))]
  omega

open Size in
/-- **Total description size is polynomial.** For every ARRIVAL instance with `n` switches, the
explicit game `Red I` (all `12n²+6n+2` priors, all `2(12n²+6n+2)(12n²+6n+3)` attacker payoffs, all
defender payoffs and `r`) has total binary length `descBits (Red I) ≤ 8500 (n+1)⁵`. -/
theorem red_descBits {n : ℕ} (I : ArrivalInstance n) :
    (Red I).descBits ≤ 8500 * (n + 1) ^ 5 := by
  refine (red_descBits_le_product I).trans ?_
  obtain ⟨hT, hΘ⟩ := red_sizes_proof n
  rw [hT, hΘ]
  have hN : 1 ≤ n + 1 := Nat.le_add_left 1 n
  have a1 : 12 * n ^ 2 + 6 * n + 3 ≤ 12 * (n + 1) ^ 2 := by nlinarith
  have a2 : 12 * n ^ 2 + 6 * n + 2 ≤ 12 * (n + 1) ^ 2 := by omega
  generalize 12 * n ^ 2 + 6 * n + 3 = cT at a1 ⊢
  generalize 12 * n ^ 2 + 6 * n + 2 = cΘ at a2 ⊢
  generalize n + 1 = N at hN a1 a2 ⊢
  have b1 : cΘ * cT * (2 * (28 * N)) ≤ 12 * N ^ 2 * (12 * N ^ 2) * (2 * (28 * N)) :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul a2 a1)
  have b2 : cΘ * (28 * N) ≤ 12 * N ^ 2 * (28 * N) := Nat.mul_le_mul_right _ a2
  have c2 : N ^ 2 ≤ N ^ 5 := Nat.pow_le_pow_right hN (by norm_num)
  have c3 : N ^ 3 ≤ N ^ 5 := Nat.pow_le_pow_right hN (by norm_num)
  have c0 : 1 ≤ N ^ 5 := Nat.one_le_pow _ _ hN
  have d1 : 12 * N ^ 2 * (12 * N ^ 2) * (2 * (28 * N)) = 8064 * N ^ 5 := by ring
  have d2 : 12 * N ^ 2 * (28 * N) = 336 * N ^ 3 := by ring
  omega

end Bssg

#print axioms Bssg.redMarket_bits
#print axioms Bssg.red_bits
#print axioms Bssg.red_descBits_le_product
#print axioms Bssg.red_descBits
