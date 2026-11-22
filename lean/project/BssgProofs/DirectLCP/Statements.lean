import BssgProofs.DirectLCP.Defs

/-!
# Exact BNE reduces to one P-matrix LCP: statements

Every lemma of `book/articles/07-direct-lcp.tex` ([DL]) that is formalized here is stated as a
`Prop`-valued definition (so this file contains no `sorry`).  `Proofs.lean` proves each one as
`<name>_proof : <Name> T Θ` (or with an explicit extra hypothesis, see `main_proof_of_gap`).
The map to the article is in `DEFINITIONS-directlcp.md`.
-/

namespace Bssg
namespace DirectLCP

open Finset Matrix

section

variable (T Θ : Type*) [Fintype T] [DecidableEq T] [Fintype Θ] [DecidableEq Θ]

/-- [DL Lemma dl:lem:cutoff] cutoff form of the defender's best response (any scores `π`). -/
def CutoffForm : Prop :=
  ∀ (G : BSSG T Θ) (π x : T → ℚ), IsFeasibleCov G x →
    ((∀ x', IsFeasibleCov G x' → ∑ j, π j * x' j ≤ ∑ j, π j * x j) ↔
      ∃ l0 : ℚ, ∀ j, (0 < x j → l0 ≤ π j) ∧ (x j < 1 → π j ≤ l0))

/-- [DL §3, "Variables and pairs"] `q + M z` is the slack table (dl:eq:lcp), and
`M = (0 Bᵀ; −D 0)` holds by definition (`lcpM`). -/
def SlackTable [Nonempty T] : Prop :=
  ∀ (G : BSSG T Θ) (z : Idx Θ T → ℚ), slack (lcpq G) (lcpM G) z = slackTable G z

/-- [DL Lemma dl:lem:formulation (a)]: every solution of `LCP(q, M)` has `λ > 0`, `Σ x = r`, and
`(x, f)` is a BNE in marginal coordinates. -/
def FormulationA [Nonempty T] : Prop :=
  ∀ G : BSSG T Θ, G.WellFormed → 0 < G.r → G.r < Fintype.card T →
    ∀ z : Idx Θ T → ℚ, IsLCPSol (lcpq G) (lcpM G) z →
      0 < z Idx.lam ∧ ∑ j, zx z j = G.r ∧ IsMarginalBNE G (zx z) (zf z)

/-- [DL Lemma dl:lem:formulation (b)]: every BNE in marginal coordinates extends to a solution. -/
def FormulationB [Nonempty T] : Prop :=
  ∀ G : BSSG T Θ, G.WellFormed → 0 < G.r → G.r < Fintype.card T →
    ∀ (x : T → ℚ) (f : Θ → T → ℚ), IsMarginalBNE G x f →
      ∃ z : Idx Θ T → ℚ, IsLCPSol (lcpq G) (lcpM G) z ∧ zx z = x ∧ zf z = f

/-- [DL Lemma dl:lem:p0, Steps 0–4]: `det B_{R,F} · det D_{R,F} ≥ 0` for every selection of
`k` rows `ρ` and `k` columns `φ` of the incidence matrices, for all `b ≥ 0`, `d ≥ 0`. -/
def P0Core : Prop :=
  ∀ (β : Θ → T → ℚ), (∀ i j, 0 ≤ β i j) → ∀ (d : T → ℚ), (∀ j, 0 ≤ d j) →
    ∀ (k : ℕ) (ρ : Fin k → RIdx Θ T) (φ : Fin k → FIdx Θ T),
      0 ≤ ((incMat β).submatrix ρ φ).det * ((incMat (fun _ j => d j)).submatrix ρ φ).det

/-- [DL Lemma dl:lem:p0]: for all data with `b_ij ≥ 0`, `d_j ≥ 0`, `M` is a P₀-matrix. -/
def P0 : Prop :=
  ∀ G : BSSG T Θ, (∀ i j, 0 ≤ bb G i j) → (∀ j, 0 ≤ dd G j) → IsP0Matrix (lcpM G)

/-- [DL Lemma dl:lem:pmatrix]: for `δ > 0`, `M + δ I` is a P-matrix (with the proof's bound
`det (M+δI)_{SS} ≥ δ^{|S|}`), has no sign-reversing vector, and its LCP has at most one solution
for every `q`. -/
def DiagPerturbation : Prop :=
  ∀ G : BSSG T Θ, G.WellFormed → ∀ δ : ℚ, 0 < δ →
    IsPMatrix (lcpM G + δ • (1 : Matrix (Idx Θ T) (Idx Θ T) ℚ)) ∧
    (∀ S : Finset (Idx Θ T),
      δ ^ S.card ≤ (principal (lcpM G + δ • (1 : Matrix (Idx Θ T) (Idx Θ T) ℚ)) S).det) ∧
    (∀ y, ¬ IsSignReversing (lcpM G + δ • (1 : Matrix (Idx Θ T) (Idx Θ T) ℚ)) y) ∧
    ∀ q z z', IsLCPSol q (lcpM G + δ • (1 : Matrix (Idx Θ T) (Idx Θ T) ℚ)) z →
      IsLCPSol q (lcpM G + δ • (1 : Matrix (Idx Θ T) (Idx Θ T) ℚ)) z' → z = z'

/-- [DL Lemma dl:lem:bound]: for `0 < δ ≤ 1` every solution of `LCP(q, M + δI)` lies in `[0,K]^N`. -/
def UniformBound [Nonempty T] : Prop :=
  ∀ G : BSSG T Θ, G.WellFormed → ∀ δ : ℚ, 0 < δ → δ ≤ 1 →
    ∀ z : Idx Θ T → ℚ, IsLCPSol (lcpq G) (lcpMδ G δ) z → ∀ k, 0 ≤ z k ∧ z k ≤ cK G

/-- [DL §4 "The pattern LP"]: every feasible point of a pattern LP solves `LCP(q, M)`. -/
def PatternSol [Nonempty T] : Prop :=
  ∀ (G : BSSG T Θ) (P : Finset (Idx Θ T)) (z : Idx Θ T → ℚ),
    IsPatternFeasible G P z → IsLCPSol (lcpq G) (lcpM G) z

/-- [DL Lemma dl:lem:gap] for one game: for every pattern whose relaxed LP is feasible, the
optimum is attained and is either `0` or at least `1/Q`. -/
def GapLemma [Nonempty T] (G : BSSG T Θ) : Prop :=
  ∀ P : Finset (Idx Θ T), (∃ z τ, IsRelaxedFeasible G P z τ) →
    ∃ z₀ τ₀, IsRelaxedFeasible G P z₀ τ₀ ∧ (∀ z τ, IsRelaxedFeasible G P z τ → τ₀ ≤ τ) ∧
      (τ₀ = 0 ∨ 1 / (cQ G : ℚ) ≤ τ₀)

/-- [DL Lemma dl:lem:gap] for all games. -/
def Gap [Nonempty T] : Prop := ∀ G : BSSG T Θ, GapLemma T Θ G

/-- [DL Thm. dl:thm:main], `0 < r < n` (the mathematical content; polynomial time is not
formalized): with `δ = 1/(2KQ)`, `M + δI` is a P-matrix, `0 < δ ≤ 1`, and for any solution `z*` of
`LCP(q, M + δI)` the pattern LP of `P = {k : z*_k > 0}` is feasible, and each of its solutions solves
`LCP(q, M)` and gives a BNE in marginal coordinates. -/
def MainTheorem [Nonempty T] : Prop :=
  ∀ G : BSSG T Θ, G.WellFormed → 0 < G.r → G.r < Fintype.card T →
    IsPMatrix (lcpMδ G (cδ G)) ∧ 0 < cδ G ∧ cδ G ≤ 1 ∧
    ∀ z : Idx Θ T → ℚ, IsLCPSol (lcpq G) (lcpMδ G (cδ G)) z →
      (∃ z', IsPatternFeasible G (support z) z') ∧
      ∀ z', IsPatternFeasible G (support z) z' →
        IsLCPSol (lcpq G) (lcpM G) z' ∧ IsMarginalBNE G (zx z') (zf z')

/-- Bridge to the frozen definitions (one resource, defender payoffs 0/1, positive priors): the BNE in
marginal coordinates with `f_ij = p_i σ_i(j)` is exactly the frozen `BSSG.IsCoverageBNE` (Fact 0
form). -/
def MarginalIffCoverage : Prop :=
  ∀ G : BSSG T Θ, G.r = 1 → (∀ t, G.ud0 t = 0) → (∀ t, G.ud1 t = 1) → (∀ θ, 0 < G.prior θ) →
    ∀ (ξ : T → ℚ) (σ : Θ → T → ℚ), (∀ θ, BSSG.IsDist (σ θ)) →
      (IsMarginalBNE G ξ (fun i j => G.prior i * σ i j) ↔ G.IsCoverageBNE ξ σ)

/-- Bridge to the frozen general mixed-strategy BNE `BSSG.IsBNE` (same hypotheses, via Fact 0 of
`Proofs/Embedding.lean`): `(δ, σ)` is a BNE iff `δ` is a defender mixed strategy, every `σ_θ` is a
distribution, and `(coverage δ, p σ)` is a BNE in marginal coordinates. -/
def BNEIffMarginal : Prop :=
  ∀ G : BSSG T Θ, G.r = 1 → (∀ t, G.ud0 t = 0) → (∀ t, G.ud1 t = 1) → (∀ θ, 0 < G.prior θ) →
    ∀ (δ : Finset T → ℚ) (σ : Θ → T → ℚ),
      (G.IsBNE δ σ ↔ G.IsDefMixed δ ∧ (∀ θ, BSSG.IsDist (σ θ)) ∧
        IsMarginalBNE G (BSSG.coverage δ) (fun i j => G.prior i * σ i j))

end

section

variable (F R : Type*) [Fintype F] [Fintype R] [DecidableEq F] [DecidableEq R]

/-- [DL eq. (dl:eq:blockdet)]: a principal minor of `(0 Bᵀ; −D 0)` on `S = F' ∪ R'` is `0` if
`|F'| ≠ |R'|`, and equals `det B_{R',F'} · det D_{R',F'}` if `|F'| = |R'| = k` (rows and columns
listed through any bijections `Fin k ≃ R'`, `Fin k ≃ F'`). -/
def BlockDet : Prop :=
  ∀ (B D : Matrix R F ℚ) (S : Finset (F ⊕ R)),
    (Fintype.card {a // Sum.inl a ∈ S} ≠ Fintype.card {b // Sum.inr b ∈ S} →
      (principal (fromBlocks 0 Bᵀ (-D) 0) S).det = 0) ∧
    ∀ (k : ℕ) (e1 : Fin k ≃ {a // Sum.inl a ∈ S}) (e2 : Fin k ≃ {b // Sum.inr b ∈ S}),
      (principal (fromBlocks 0 Bᵀ (-D) 0) S).det =
        (B.submatrix (fun p => (e2 p).1) (fun p => (e1 p).1)).det *
          (D.submatrix (fun p => (e2 p).1) (fun p => (e1 p).1)).det

end

section

variable (ι : Type*) [Fintype ι] [DecidableEq ι]

/-- [DL Lemma dl:lem:pmatrix], generic form: `M` P₀ and `δ > 0` ⇒ `M + δ I` is a P-matrix. -/
def P0AddSmulIsP : Prop :=
  ∀ M : Matrix ι ι ℚ, IsP0Matrix M → ∀ δ : ℚ, 0 < δ → IsPMatrix (M + δ • (1 : Matrix ι ι ℚ))

end

end DirectLCP
end Bssg
