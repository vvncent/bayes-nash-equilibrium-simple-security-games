import BssgProofs.MarketLCP.Defs

/-!
# The market (M1) reduces to one P-matrix LCP: statements

Every result of [PL] (`ch5-upper.tex`, Section `sec:plcp`) that is formalized here is stated as a
`Prop`-valued definition (so this file contains no `sorry`).  `Proofs.lean` proves each one as
`<name>_proof`.  The map to the book is in `DEFINITIONS-marketlcp.md`.
-/

namespace Bssg
namespace MarketLCP

open Finset Matrix DirectLCP

section

variable (I J : Type*) [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

/-- [PL, display defining `w`]: `q + M z` is the slack table. -/
def SlackTable : Prop :=
  ∀ (Mk : Market I J) (z : Idx Mk → ℚ), slack (lcpq Mk) (lcpM Mk) z = slackTable Mk z

/-- [PL Lemma plcp:lem:formulation], direction SOL ⇒ equilibrium: every solution `z = (f, u, P)`
of `LCP(q, M)` gives the (M1) equilibrium `(P, u, f)`.  No hypothesis on the market. -/
def FormulationSolEq : Prop :=
  ∀ (Mk : Market I J) (z : Idx Mk → ℚ), IsLCPSol (lcpq Mk) (lcpM Mk) z →
    Mk.IsEquilibrium (zP Mk z) (zu Mk z) (zf Mk z)

/-- [PL Lemma plcp:lem:formulation], direction equilibrium ⇒ SOL: every (M1) equilibrium
`(P, v, f)` gives the solution `z = (f, v, P)`, and decoding it returns `P`, `v`, and `f` on `E`. -/
def FormulationEqSol : Prop :=
  ∀ (Mk : Market I J) (P : J → ℚ) (v : I → ℚ) (f : I × J → ℚ), Mk.IsEquilibrium P v f →
    IsLCPSol (lcpq Mk) (lcpM Mk) (encode Mk P v f) ∧ zP Mk (encode Mk P v f) = P ∧
      zu Mk (encode Mk P v f) = v ∧ ∀ e ∈ Mk.E, zf Mk (encode Mk P v f) e = f e

/-- [PL Lemma plcp:lem:formulation] as an equivalence: `z ∈ SOL(q, M)` iff its decoding is an
equilibrium, and decoding is injective (`encode ∘ decode = id`). -/
def Formulation : Prop :=
  ∀ (Mk : Market I J) (z : Idx Mk → ℚ),
    (IsLCPSol (lcpq Mk) (lcpM Mk) z ↔ Mk.IsEquilibrium (zP Mk z) (zu Mk z) (zf Mk z)) ∧
      encode Mk (zP Mk z) (zu Mk z) (zf Mk z) = z

/-- [PL Lemma plcp:lem:p0]: for every market (any edge set) with slopes `b ≥ 0` on `E` (the book
assumes `b > 0`), every principal minor of `M` is nonnegative. -/
def P0 : Prop :=
  ∀ Mk : Market I J, (∀ e ∈ Mk.E, 0 ≤ Mk.b e) → IsP0Matrix (lcpM Mk)

/-- [PL Lemma plcp:lem:pmatrix] for the market matrix, with the proof's bound
`det (M + εI)_{SS} ≥ ε^{|S|}`, and uniqueness of the solution of `LCP(q', M + εI)` for every `q'`. -/
def PMatrix : Prop :=
  ∀ Mk : Market I J, (∀ e ∈ Mk.E, 0 ≤ Mk.b e) → ∀ ε : ℚ, 0 < ε →
    IsPMatrix (lcpMeps Mk ε) ∧ (∀ S, ε ^ S.card ≤ (principal (lcpMeps Mk ε) S).det) ∧
    ∀ q' z z', IsLCPSol q' (lcpMeps Mk ε) z → IsLCPSol q' (lcpMeps Mk ε) z' → z = z'

/-- [PL Lemma plcp:lem:bound]: for `0 < ε ≤ 1`, every solution of `LCP(q, M + εI)` lies in
`[0, Z̄ − 1]^N`. -/
def UniformBound : Prop :=
  ∀ Mk : Market I J, Mk.WellFormed → ∀ ε : ℚ, 0 < ε → ε ≤ 1 →
    ∀ z : Idx Mk → ℚ, IsLCPSol (lcpq Mk) (lcpMeps Mk ε) z → ∀ k, 0 ≤ z k ∧ z k ≤ Zbar Mk - 1

/-- [PL Thm. plcp:thm:main] (mathematical content; polynomial time and bit sizes are not
formalized): with `ε = 1/(2⌈Z̄⌉(dC)^d)`, `M + εI` is a P-matrix, `0 < ε ≤ 1`, `LCP(q, M + εI)` has at
most one solution, and for any solution `z^ε`, with `A = {k : z^ε_k > 0}`, the system `(∗)` is
feasible and every feasible point `z = (f, u, P)` of `(∗)` solves `LCP(q, M)` and gives the (M1)
equilibrium `(P, u, f)`. -/
def MainTheorem : Prop :=
  ∀ Mk : Market I J, Mk.WellFormed →
    IsPMatrix (lcpMeps Mk (eps Mk)) ∧ 0 < eps Mk ∧ eps Mk ≤ 1 ∧
    (∀ z z', IsLCPSol (lcpq Mk) (lcpMeps Mk (eps Mk)) z →
      IsLCPSol (lcpq Mk) (lcpMeps Mk (eps Mk)) z' → z = z') ∧
    ∀ zε : Idx Mk → ℚ, IsLCPSol (lcpq Mk) (lcpMeps Mk (eps Mk)) zε →
      (∃ z, IsStarFeasible (lcpq Mk) (lcpM Mk) (support zε) z) ∧
      ∀ z, IsStarFeasible (lcpq Mk) (lcpM Mk) (support zε) z →
        IsLCPSol (lcpq Mk) (lcpM Mk) z ∧ Mk.IsEquilibrium (zP Mk z) (zu Mk z) (zf Mk z)

end

section

variable (ι : Type*) [Fintype ι] [DecidableEq ι]

/-- [PL Lemma plcp:lem:gap], for any `LCP(q, M)` over `ℚ`: for every `A`, `LP(A)` has an optimum
`ρ*_A` (attained), and either `ρ*_A = 0` or `ρ*_A ≥ (dC)^{−d}`. -/
def Gap : Prop :=
  ∀ (q : ι → ℚ) (M : Matrix ι ι ℚ) (A : Finset ι),
    ∃ z₀ ρ₀, IsLPFeasible q M A z₀ ρ₀ ∧ (∀ z ρ, IsLPFeasible q M A z ρ → ρ₀ ≤ ρ) ∧
      (ρ₀ = 0 ∨ 1 / ((dimd ι * cC q M : ℕ) : ℚ) ^ dimd ι ≤ ρ₀)

/-- [PL Thm. plcp:thm:main, "Soundness"], generic: every feasible point of `(∗)` solves `LCP(q, M)`. -/
def StarSol : Prop :=
  ∀ (q : ι → ℚ) (M : Matrix ι ι ℚ) (A : Finset ι) (z : ι → ℚ),
    IsStarFeasible q M A z → IsLCPSol q M z

end

/-- [PL Example plcp:ex:negative]: for `μ = 1`, `c = 2`, `a = b = 1` (one buyer, one good):
`(P, v, f) = (0, 1, 1)` is the unique equilibrium; at `ε = 1` the unique solution of
`LCP(q, M + I)` is `(f, u, P) = (1, 0, 0)`, its support is `{f}`, and `(∗)` is infeasible; for every
`0 < ε < 1` the solution of `LCP(q, M + εI)` is `u = (1−ε)/(1+ε²)`, `f = 1 + εu`, `P = 0`, with
support `{f, u}`, for which `(∗)` has exactly one feasible point, `(1, 1, 0)`; the book's `ε` lies in
`(0, 1)`. -/
def NegativeExample : Prop :=
  exMarket.IsEquilibrium (fun _ => 0) (fun _ => 1) (fun _ => 1) ∧
  (∀ P v f, exMarket.IsEquilibrium P v f → P () = 0 ∧ v () = 1 ∧ f ((), ()) = 1) ∧
  IsLCPSol (lcpq exMarket) (lcpMeps exMarket 1) (exZ 1 0 0) ∧
  (∀ z, IsLCPSol (lcpq exMarket) (lcpMeps exMarket 1) z → z = exZ 1 0 0) ∧
  support (exZ 1 0 0) = {.inl exEdge} ∧
  (¬ ∃ z, IsStarFeasible (lcpq exMarket) (lcpM exMarket) (support (exZ 1 0 0)) z) ∧
  (∀ ε : ℚ, 0 < ε → ε < 1 →
    IsLCPSol (lcpq exMarket) (lcpMeps exMarket ε)
        (exZ (1 + ε * ((1 - ε) / (1 + ε ^ 2))) ((1 - ε) / (1 + ε ^ 2)) 0) ∧
      support (exZ (1 + ε * ((1 - ε) / (1 + ε ^ 2))) ((1 - ε) / (1 + ε ^ 2)) 0) =
        {.inl exEdge, Idx.u ()} ∧
      IsStarFeasible (lcpq exMarket) (lcpM exMarket) {.inl exEdge, Idx.u ()} (exZ 1 1 0) ∧
      ∀ z, IsStarFeasible (lcpq exMarket) (lcpM exMarket) {.inl exEdge, Idx.u ()} z →
        z = exZ 1 1 0) ∧
  0 < eps exMarket ∧ eps exMarket < 1

end MarketLCP
end Bssg
