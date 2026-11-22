import BssgProofs.Definitions
import Mathlib.Data.Nat.Size

/-!
# Market → game (book Chapter 3, "Market to game"): definitions and statements

Book: `book/readable/chapters/ch3-market.tex`, Section `sec:mk-m2g`:
* Lemma `lem:mk-rescale` (row rescaling by powers of two, slopes `≥ 1`);
* Theorem `thm:mk-embed` (one-resource embedding `Γ_ω`), decoding direction;
* Theorem `thm:mk-main` (a): one BNE-oracle call decodes to an equilibrium of the ORIGINAL market.

Every statement is a `Prop`-valued definition (no `sorry` here); `Proofs.lean` proves each as
`<name>_proof`.  The map to the book is in `DEFINITIONS-marketgame.md`.

Two games appear:
* `Market.toGame` (frozen, `Definitions.lean`): Appendix C / simple-proof §6 constants,
  `W = 1 + Σμ + max(0, max c)`;
* `toGameW Mk W` (here): the same table of types/targets/payoffs with an arbitrary base weight `W`;
  `gameOmega Mk ω = toGameW Mk ((2 + 2/ω) D̂)` is Chapter 3's `Γ_ω` (eq. `eq:mk-consts`), and
  `toGameW Mk Mk.gW = Mk.toGame` (`ToGameW_gW`).
-/

namespace Bssg
namespace MarketGame

open Finset

/-! ## 1. Row rescaling (Lemma `lem:mk-rescale`) -/

section Rescale

variable {I J : Type*} [DecidableEq I] [DecidableEq J]

/-- Multiply all intercepts and slopes of buyer `i` by `ν_i` (masses, capacities, options kept). -/
def rescale (Mk : Market I J) (ν : I → ℚ) : Market I J where
  mass := Mk.mass
  cap := Mk.cap
  E := Mk.E
  a := fun e => ν e.1 * Mk.a e
  b := fun e => ν e.1 * Mk.b e

/-- Utilities original → rescaled: `v_i ↦ ν_i v_i`. -/
def upV (ν v : I → ℚ) : I → ℚ := fun i => ν i * v i

/-- Utilities rescaled → original: `v'_i ↦ v'_i / ν_i`. -/
def downV (ν v' : I → ℚ) : I → ℚ := fun i => v' i / ν i

/-- Exponent of `ν_i`: `k_i = max_{j ∈ E_i} size(den b_ij)` (`0` if `E_i = ∅`), where
`size d` is the binary length of `d`.  Then `2^{k_i} > den b_ij`, so `2^{k_i} b_ij ≥ 1`. -/
def nuExp (Mk : Market I J) (i : I) : ℕ :=
  (Mk.E.filter (fun e => e.1 = i)).sup (fun e => Nat.size (Mk.b e).den)

/-- The book's scale factor `ν_i = 2^{k_i}`. -/
def nu (Mk : Market I J) (i : I) : ℚ := 2 ^ nuExp Mk i

/-- The rescaled market of Lemma `lem:mk-rescale` with the explicit choice `ν = nu Mk`. -/
def rescaled (Mk : Market I J) : Market I J := rescale Mk (nu Mk)

/-- Lemma `lem:mk-rescale`, forward map: for ANY positive row factors `ν`,
`(P, v, f)` is an equilibrium iff `(P, ν v, f)` is an equilibrium of the rescaled market.
No assumption on `E_i` (buyers with `E_i = ∅` are allowed, not deleted). -/
def RescaleEquiv (I J : Type*) [DecidableEq I] [DecidableEq J] : Prop :=
  ∀ (Mk : Market I J) (ν : I → ℚ), (∀ i, 0 < ν i) → ∀ (P : J → ℚ) (v : I → ℚ) (f : I × J → ℚ),
    Mk.IsEquilibrium P v f ↔ (rescale Mk ν).IsEquilibrium P (upV ν v) f

/-- Lemma `lem:mk-rescale`, backward map: `(P, v', f)` is an equilibrium of the rescaled market iff
`(P, v'/ν, f)` is one of the original; the two utility maps are mutually inverse. -/
def RescaleEquivBack (I J : Type*) [DecidableEq I] [DecidableEq J] : Prop :=
  ∀ (Mk : Market I J) (ν : I → ℚ), (∀ i, 0 < ν i) →
    (∀ v, downV ν (upV ν v) = v) ∧ (∀ v', upV ν (downV ν v') = v') ∧
    ∀ (P : J → ℚ) (v' : I → ℚ) (f : I × J → ℚ),
      (rescale Mk ν).IsEquilibrium P v' f ↔ Mk.IsEquilibrium P (downV ν v') f

/-- The explicit `ν = nu Mk`: each `ν_i` is a power of two `2^{k_i}`, `ν_i b_ij ≥ 1` on options
(vacuous if `E_i = ∅`), and `k_i` is `0` or the binary length of the denominator of some slope
`b_ij`, `j ∈ E_i` (so `ν_i` has polynomial binary length `k_i + 1`). -/
def NuSpec (I J : Type*) [DecidableEq I] [DecidableEq J] : Prop :=
  ∀ Mk : Market I J, Mk.WellFormed →
    (∀ i, nu Mk i = 2 ^ nuExp Mk i ∧ 0 < nu Mk i) ∧
    (∀ e ∈ Mk.E, 1 ≤ nu Mk e.1 * Mk.b e) ∧
    (∀ i, nuExp Mk i = 0 ∨ ∃ e ∈ Mk.E, e.1 = i ∧ nuExp Mk i = Nat.size (Mk.b e).den)

/-- The rescaled market is well formed and has all slopes `≥ 1`. -/
def RescaledWF (I J : Type*) [DecidableEq I] [DecidableEq J] : Prop :=
  ∀ Mk : Market I J, Mk.WellFormed →
    (rescaled Mk).WellFormed ∧ ∀ e ∈ (rescaled Mk).E, 1 ≤ (rescaled Mk).b e

end Rescale

/-! ## 2. The one-call reduction market → game (Theorem `thm:mk-main` (a)), with `toGame` -/

section Reduce

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

/-- The game handed to the BNE oracle: `toGame` (Appendix C constants) of the rescaled market. -/
def reduce (Mk : Market I J) : BSSG (MTarget I J) (MType I J) := (rescaled Mk).toGame

/-- Decoding a (general mixed) BNE `(δ, σ)` of `reduce Mk` to a candidate equilibrium of `Mk`:
coverage `ξ = coverage δ`; `P = Sξ_j`, `v_i = S u_i / ν_i`, `f_ij = (W + μ_i) σ_i(j)`, all constants
`S, W` those of the rescaled market. -/
def decode (Mk : Market I J) (δ : Finset (MTarget I J) → ℚ) (σ : MType I J → MTarget I J → ℚ) :
    (J → ℚ) × (I → ℚ) × (I × J → ℚ) :=
  ((rescaled Mk).decP (BSSG.coverage δ),
    downV (nu Mk) ((rescaled Mk).decV (BSSG.coverage δ)),
    (rescaled Mk).decF σ)

/-- Coverage-form composition: every coverage-form BNE of `reduce Mk` decodes (lemma 8 then the
rescaling map back) to an equilibrium of the ORIGINAL market. -/
def ComposeCoverage (I J : Type*) [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] :
    Prop :=
  ∀ Mk : Market I J, Mk.WellFormed → ∀ ξ σ, (reduce Mk).IsCoverageBNE ξ σ →
    Mk.IsEquilibrium ((rescaled Mk).decP ξ) (downV (nu Mk) ((rescaled Mk).decV ξ))
      ((rescaled Mk).decF σ)

/-- **Theorem `thm:mk-main` (a), correctness.** For every well-formed market (positive slopes,
masses, capacities), every general mixed BNE of the one game `reduce Mk` decodes to an
equilibrium of `Mk`. -/
def ComposeBNE (I J : Type*) [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] : Prop :=
  ∀ Mk : Market I J, Mk.WellFormed → ∀ δ σ, (reduce Mk).IsBNE δ σ →
    Mk.IsEquilibrium (decode Mk δ σ).1 (decode Mk δ σ).2.1 (decode Mk δ σ).2.2

/-- Converse (lift; not needed for the reduction): every equilibrium of `Mk` gives a BNE of
`reduce Mk` whose decoding returns the same prices `P` (only the prices are stated). -/
def ComposeLift (I J : Type*) [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] : Prop :=
  ∀ Mk : Market I J, Mk.WellFormed → ∀ P v f, Mk.IsEquilibrium P v f →
    ∃ δ σ, (reduce Mk).IsBNE δ σ ∧ (decode Mk δ σ).1 = P

end Reduce

/-! ## 3. Chapter 3's game `Γ_ω` (arbitrary base weight `W`) -/

section Omega

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

/-- Type weights with base weight `W`: `W + μ_i`, `W − c_j`, `W` (Table `tab:mk-types`). -/
def gWeightW (Mk : Market I J) (W : ℚ) : MType I J → ℚ
  | .inl i => W + Mk.mass i
  | .inr (.inl j) => W - Mk.cap j
  | .inr (.inr ()) => W

/-- The game of Table `tab:mk-types` with base weight `W` (payoffs `Market.gPay`, which use
`A`, `S` of eq. `eq:mk-consts`; `A`, `S` are the same in Chapter 3 and Appendix C). -/
def toGameW (Mk : Market I J) (W : ℚ) : BSSG (MTarget I J) (MType I J) where
  r := 1
  prior := fun θ => gWeightW Mk W θ / ∑ θ', gWeightW Mk W θ'
  ud0 := fun _ => 0
  ud1 := fun _ => 1
  ua0 := fun θ k => (Mk.gPay θ k).1
  ua1 := fun θ k => (Mk.gPay θ k).1 - (Mk.gPay θ k).2

/-- Decoded utilities in `toGameW`: `v_i = S u_i`. -/
def decVW (Mk : Market I J) (W : ℚ) (ξ : MTarget I J → ℚ) (i : I) : ℚ :=
  Mk.gS * (toGameW Mk W).typeValue (.inl i) ξ

/-- Decoded purchases in `toGameW`: `f_ij = (W + μ_i) σ_i(j)`. -/
def decFW (Mk : Market I J) (W : ℚ) (σ : MType I J → MTarget I J → ℚ) (e : I × J) : ℚ :=
  (W + Mk.mass e.1) * σ (.inl e.1) (.inl e.2)

/-- `D̂ = 1 + max(Σμ, max_j c_j)` (eq. `eq:mk-consts`; `max_j c_j` as `fold max 0`, equal for
`c > 0` and nonempty `J`). -/
def hatD (Mk : Market I J) : ℚ := 1 + max (∑ i, Mk.mass i) (univ.fold max 0 Mk.cap)

/-- Chapter 3's base weight `W = (2 + 2/ω) D̂`. -/
def wOmega (Mk : Market I J) (ω : ℚ) : ℚ := (2 + 2 / ω) * hatD Mk

/-- Chapter 3's game `Γ_ω` (Theorem `thm:mk-embed`). -/
def gameOmega (Mk : Market I J) (ω : ℚ) : BSSG (MTarget I J) (MType I J) :=
  toGameW Mk (wOmega Mk ω)

/-- `toGame` is the instance `W = 1 + Σμ + max c` of `toGameW`. -/
def ToGameW_gW (I J : Type*) [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] : Prop :=
  ∀ Mk : Market I J, toGameW Mk Mk.gW = Mk.toGame

/-- Decoding for any base weight `W > Σμ`, `W > c_j` ("The proof uses `W` only through ..."). -/
def DecodeW (I J : Type*) [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] : Prop :=
  ∀ (Mk : Market I J) (W : ℚ), Mk.WellFormed → (∀ e ∈ Mk.E, 1 ≤ Mk.b e) →
    (∑ i, Mk.mass i) < W → (∀ j, Mk.cap j < W) →
    ∀ ξ σ, (toGameW Mk W).IsCoverageBNE ξ σ →
      Mk.IsEquilibrium (Mk.decP ξ) (decVW Mk W ξ) (decFW Mk W σ)

/-- **Theorem `thm:mk-embed`, decoding** (Chapter 3's `Γ_ω`, any rational `ω > 0`, in particular
`0 < ω ≤ 1`): every general mixed BNE of `Γ_ω` decodes to an equilibrium. -/
def OmegaDecode (I J : Type*) [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] : Prop :=
  ∀ (Mk : Market I J) (ω : ℚ), 0 < ω → Mk.WellFormed → (∀ e ∈ Mk.E, 1 ≤ Mk.b e) →
    ∀ δ σ, (gameOmega Mk ω).IsBNE δ σ →
      Mk.IsEquilibrium (Mk.decP (BSSG.coverage δ)) (decVW Mk (wOmega Mk ω) (BSSG.coverage δ))
        (decFW Mk (wOmega Mk ω) σ)

/-- **Theorem `thm:mk-main` (a) with Chapter 3's `Γ_ω`:** rescale, build `Γ_ω`, one BNE, decode,
undo the rescaling of utilities; the result is an equilibrium of the ORIGINAL market. -/
def OmegaCompose (I J : Type*) [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] : Prop :=
  ∀ (Mk : Market I J) (ω : ℚ), 0 < ω → Mk.WellFormed →
    ∀ δ σ, (gameOmega (rescaled Mk) ω).IsBNE δ σ →
      Mk.IsEquilibrium ((rescaled Mk).decP (BSSG.coverage δ))
        (downV (nu Mk) (decVW (rescaled Mk) (wOmega (rescaled Mk) ω) (BSSG.coverage δ)))
        (decFW (rescaled Mk) (wOmega (rescaled Mk) ω) σ)

end Omega

end MarketGame
end Bssg
