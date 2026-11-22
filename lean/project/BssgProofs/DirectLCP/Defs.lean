import Mathlib
import BssgProofs.Definitions

/-!
# Exact BNE reduces to one P-matrix LCP: definitions

Formalization of `book/articles/07-direct-lcp.tex` ("Exact Bayes–Nash equilibrium reduces to one
P-matrix LCP"), cited below as **[DL]**.  Every definition is cross-referenced in
`DEFINITIONS-directlcp.md`.  All numbers are exact rationals `ℚ`.

The game is the frozen `Bssg.BSSG T Θ` of `BssgProofs/Definitions.lean` (`T` targets, `Θ` types),
and the attacker payoff at coverage `x` is the frozen `BSSG.U θ k x = u₂⁰ − (u₂⁰ − u₂¹) x_k`.

Sections
1. Matrix classes (P, P₀) via principal minors, LCP solutions, sign-reversing vectors.
2. Game data `a, b, d`, scores, BNE in marginal coordinates.
3. The LCP `(q, M)`: index type, the incidence matrices `B, D`, `M = (0 Bᵀ; −D 0)`, `q`,
   and the slack table (dl:eq:lcp) written out row by row.
4. Constants `U, W, D_*, S, K`, the pattern LP and the relaxed pattern LP, `C`, `Q`, `δ`.
-/

namespace Bssg
namespace DirectLCP

open Finset Matrix

/-! ## 1. Matrix classes and the LCP -/

section MatrixClasses

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The principal submatrix `M_{SS}` (rows and columns `S`) [DL §1 "Linear complementarity"]. -/
def principal (M : Matrix ι ι ℚ) (S : Finset ι) : Matrix S S ℚ :=
  M.submatrix (fun k : S => (k : ι)) (fun k : S => (k : ι))

/-- `M` is a **P-matrix**: every principal minor is positive (`det M_{∅∅} = 1` is included). -/
def IsPMatrix (M : Matrix ι ι ℚ) : Prop :=
  ∀ S : Finset ι, 0 < (principal M S).det

/-- `M` is a **P₀-matrix**: every principal minor is nonnegative. -/
def IsP0Matrix (M : Matrix ι ι ℚ) : Prop :=
  ∀ S : Finset ι, 0 ≤ (principal M S).det

/-- The slack vector `w = q + M z` paired with `z`. -/
def slack (q : ι → ℚ) (M : Matrix ι ι ℚ) (z : ι → ℚ) : ι → ℚ := q + M *ᵥ z

/-- `z` solves `LCP(q, M)`: `z ≥ 0`, `w := q + M z ≥ 0`, `z_k w_k = 0` for every `k`. -/
def IsLCPSol (q : ι → ℚ) (M : Matrix ι ι ℚ) (z : ι → ℚ) : Prop :=
  (∀ k, 0 ≤ z k) ∧ (∀ k, 0 ≤ slack q M z k) ∧ ∀ k, z k * slack q M z k = 0

/-- A sign-reversing vector (violation PV2): `y ≠ 0` and `y_k (M y)_k ≤ 0` for all `k`. -/
def IsSignReversing (M : Matrix ι ι ℚ) (y : ι → ℚ) : Prop :=
  y ≠ 0 ∧ ∀ k, y k * (M *ᵥ y) k ≤ 0

end MatrixClasses

/-! ## 2. Game data and BNE in marginal coordinates -/

section Game

variable {T Θ : Type*} [Fintype T] [DecidableEq T] [Fintype Θ] [DecidableEq Θ]
variable (G : BSSG T Θ)

/-- `a_ij = u₂⁰(θ_i, j)`. -/
def aa (i : Θ) (j : T) : ℚ := G.ua0 i j

/-- `b_ij = u₂⁰(θ_i, j) − u₂¹(θ_i, j)` (attacker loss from coverage). -/
def bb (i : Θ) (j : T) : ℚ := G.ua0 i j - G.ua1 i j

/-- `d_j = u₁¹(j) − u₁⁰(j)` (defender gain from coverage). -/
def dd (j : T) : ℚ := G.ud1 j - G.ud0 j

/-- Load `w_j = Σ_i f_ij`. -/
def wload (f : Θ → T → ℚ) (j : T) : ℚ := ∑ i, f i j

/-- Score `π_j = d_j w_j`. -/
def score (f : Θ → T → ℚ) (j : T) : ℚ := dd G j * wload f j

/-- Feasible coverage: `x ∈ [0,1]^n`, `Σ_j x_j = r`. -/
def IsFeasibleCov (x : T → ℚ) : Prop := (∀ j, 0 ≤ x j ∧ x j ≤ 1) ∧ ∑ j, x j = G.r

/-- **BNE in marginal coordinates** [DL Def. dl:def:bne]: `x` feasible, `f ≥ 0`, `Σ_j f_ij = p_i`,
(a) `f_ij > 0 ⇒ a_ij − b_ij x_j = max_k (a_ik − b_ik x_k)` (stated with the frozen `BSSG.U`), and
(b) `x` maximizes `Σ_j π_j x'_j` over feasible `x'`.
All types of `Θ` are kept; a zero-prior type is forced to `f_i = 0` and (a) is vacuous for it. -/
def IsMarginalBNE (x : T → ℚ) (f : Θ → T → ℚ) : Prop :=
  IsFeasibleCov G x ∧ (∀ i j, 0 ≤ f i j) ∧ (∀ i, ∑ j, f i j = G.prior i) ∧
    (∀ i j, 0 < f i j → ∀ k, G.U i k x ≤ G.U i j x) ∧
    ∀ x', IsFeasibleCov G x' → ∑ j, score G f j * x' j ≤ ∑ j, score G f j * x j

end Game

/-! ## 3. The LCP `(q, M)` -/

/-- First-block indices `(f, t, λ)`: `inl (i, j)` attack column `f_ij`, `inr (inl j)` cap `t_j`,
`inr (inr ())` budget `λ`. -/
abbrev FIdx (Θ T : Type*) := (Θ × T) ⊕ (T ⊕ Unit)

/-- Second-block indices `(u, x)`: `inl i` type row `u_i`, `inr j` target row `x_j`. -/
abbrev RIdx (Θ T : Type*) := Θ ⊕ T

/-- LCP variables in the order `z = (f, t, λ, u, x)`; `N = mn + n + 1 + m + n`. -/
abbrev Idx (Θ T : Type*) := FIdx Θ T ⊕ RIdx Θ T

namespace Idx

variable {Θ T : Type*}

/-- `f_ij`. -/
abbrev f (i : Θ) (j : T) : Idx Θ T := .inl (.inl (i, j))
/-- `t_j`. -/
abbrev t (j : T) : Idx Θ T := .inl (.inr (.inl j))
/-- `λ`. -/
abbrev lam : Idx Θ T := .inl (.inr (.inr ()))
/-- `u_i`. -/
abbrev u (i : Θ) : Idx Θ T := .inr (.inl i)
/-- `x_j`. -/
abbrev x (j : T) : Idx Θ T := .inr (.inr j)

end Idx

section LCP

variable {T Θ : Type*} [Fintype T] [DecidableEq T] [Fintype Θ] [DecidableEq Θ]

/-- The incidence matrix with weights `β` [DL §3]: rows `RIdx` (type rows `i`, target rows `j`),
columns `FIdx`.  Attack column `ij`: `1` in type row `i`, `β_ij` in target row `j`.  Cap column
`t_j`: `−1` in target row `j`.  Budget column `λ`: `−1` in every target row.  Else `0`. -/
def incMat (β : Θ → T → ℚ) : Matrix (RIdx Θ T) (FIdx Θ T) ℚ :=
  Matrix.of fun r c =>
    match r, c with
    | .inl i, .inl (i', _) => if i = i' then 1 else 0
    | .inr j, .inl (i', j') => if j = j' then β i' j' else 0
    | .inl _, .inr _ => 0
    | .inr j, .inr (.inl j') => if j = j' then -1 else 0
    | .inr _, .inr (.inr _) => -1

variable (G : BSSG T Θ)

/-- `B`: the incidence matrix carrying the attacker losses `b_ij`. -/
def lcpB : Matrix (RIdx Θ T) (FIdx Θ T) ℚ := incMat (bb G)

/-- `D`: the incidence matrix carrying the defender gains `d_j`. -/
def lcpD : Matrix (RIdx Θ T) (FIdx Θ T) ℚ := incMat (fun _ j => dd G j)

/-- `M = (0 Bᵀ; −D 0)` [DL §3, display before "The block determinant"]. -/
def lcpM : Matrix (Idx Θ T) (Idx Θ T) ℚ := Matrix.fromBlocks 0 (lcpB G)ᵀ (-lcpD G) 0

variable [Nonempty T]

/-- Shifted intercept `A_ij = a_ij + 1 + max_k (b_ik − a_ik)` [DL §2 "Shifting the attacker payoffs"]. -/
def shiftA (i : Θ) (j : T) : ℚ :=
  aa G i j + 1 + univ.sup' univ_nonempty (fun k => bb G i k - aa G i k)

/-- The constant `q`, read off the table (dl:eq:lcp): `−A_ij`, `1`, `r`, `p_i`, `−1`. -/
def lcpq : Idx Θ T → ℚ :=
  Sum.elim (Sum.elim (fun p => -shiftA G p.1 p.2) (Sum.elim (fun _ => 1) (fun _ => (G.r : ℚ))))
    (Sum.elim G.prior (fun _ => -1))

/-- The slack table (dl:eq:lcp), row by row, with `w_j = Σ_i f_ij` and defender scores shifted by `1`. -/
def slackTable (z : Idx Θ T → ℚ) : Idx Θ T → ℚ
  | .inl (.inl (i, j)) => z (Idx.u i) + bb G i j * z (Idx.x j) - shiftA G i j
  | .inl (.inr (.inl j)) => 1 - z (Idx.x j)
  | .inl (.inr (.inr _)) => (G.r : ℚ) - ∑ j, z (Idx.x j)
  | .inr (.inl i) => G.prior i - ∑ j, z (Idx.f i j)
  | .inr (.inr j) => z Idx.lam - 1 + z (Idx.t j) - dd G j * ∑ i, z (Idx.f i j)

/-- Coverage part `x` of an LCP vector. -/
def zx (z : Idx Θ T → ℚ) (j : T) : ℚ := z (Idx.x j)

/-- Flow part `f` of an LCP vector. -/
def zf (z : Idx Θ T → ℚ) (i : Θ) (j : T) : ℚ := z (Idx.f i j)

/-! ## 4. Constants, pattern LPs, `δ` -/

/-- `U = max_{ij} A_ij` (as `fold max 1`, equal to the max when `Θ` is nonempty, since `A_ij ≥ 1`). -/
def cU : ℚ := univ.fold max 1 (fun p : Θ × T => shiftA G p.1 p.2)

/-- `W = 1 + m U`. -/
def cW : ℚ := 1 + (Fintype.card Θ : ℚ) * cU G

/-- `D_* = max_j d_j` (as `fold max 0`; equal to the max as `d ≥ 0` and `T` is nonempty). -/
def cDstar : ℚ := univ.fold max 0 (dd G)

/-- `S = 1 + D_* W`. -/
def cS : ℚ := 1 + cDstar G * cW G

/-- `K = ⌈max(1, U, W, 1 + S)⌉`, as a rational. -/
def cK : ℚ := (⌈max (max 1 (cU G)) (max (cW G) (1 + cS G))⌉ : ℤ)

/-- The perturbed matrix `M + δ I`. -/
def lcpMδ (δ : ℚ) : Matrix (Idx Θ T) (Idx Θ T) ℚ := lcpM G + δ • (1 : Matrix (Idx Θ T) (Idx Θ T) ℚ)

/-- The **pattern LP** of `P` [DL §4]: `0 ≤ z ≤ K`, `z_k = 0` off `P`, `(q+Mz)_k ≥ 0` for all `k`,
`(q+Mz)_k = 0` on `P`. -/
def IsPatternFeasible (P : Finset (Idx Θ T)) (z : Idx Θ T → ℚ) : Prop :=
  (∀ k, 0 ≤ z k ∧ z k ≤ cK G) ∧ (∀ k, k ∉ P → z k = 0) ∧
    (∀ k, 0 ≤ slack (lcpq G) (lcpM G) z k) ∧ ∀ k, k ∈ P → slack (lcpq G) (lcpM G) z k = 0

/-- The **relaxed pattern LP** feasibility (R1)–(R5) for `(z, τ)`. -/
def IsRelaxedFeasible (P : Finset (Idx Θ T)) (z : Idx Θ T → ℚ) (τ : ℚ) : Prop :=
  (∀ k, 0 ≤ slack (lcpq G) (lcpM G) z k + τ) ∧
    (∀ k, k ∈ P → 0 ≤ -slack (lcpq G) (lcpM G) z k + τ) ∧
    (∀ k, 0 ≤ z k ∧ z k ≤ cK G) ∧ (∀ k, k ∉ P → z k ≤ 0) ∧ 0 ≤ τ ∧ τ ≤ 1

/-- Indices of the fixed list of `5N + 2` rows: `±(q+Mz)_k + τ ≥ 0`, `z_k ≥ 0`, `z_k ≤ K`, `z_k ≤ 0`,
`τ ≥ 0`, `τ ≤ 1`. -/
abbrev RowIdx (Θ T : Type*) :=
  Idx Θ T ⊕ Idx Θ T ⊕ Idx Θ T ⊕ Idx Θ T ⊕ Idx Θ T ⊕ Bool

/-- Coefficients of a row `coef ⬝ (z, τ) ≥ rhs`, over the variables `Idx ⊕ Unit` (`inr ()` is `τ`),
with the coefficient of `τ` inserted. -/
def rowCoef : RowIdx Θ T → (Idx Θ T ⊕ Unit) → ℚ
  | .inl k => Sum.elim (fun c => lcpM G k c) (fun _ => 1)
  | .inr (.inl k) => Sum.elim (fun c => -lcpM G k c) (fun _ => 1)
  | .inr (.inr (.inl k)) => Sum.elim (fun c => if c = k then 1 else 0) (fun _ => 0)
  | .inr (.inr (.inr (.inl k))) => Sum.elim (fun c => if c = k then -1 else 0) (fun _ => 0)
  | .inr (.inr (.inr (.inr (.inl k)))) => Sum.elim (fun c => if c = k then -1 else 0) (fun _ => 0)
  | .inr (.inr (.inr (.inr (.inr b)))) => Sum.elim (fun _ => 0) (fun _ => if b then -1 else 1)

/-- Right sides of the rows (same order as `rowCoef`). -/
def rowRhs : RowIdx Θ T → ℚ
  | .inl k => -lcpq G k
  | .inr (.inl k) => lcpq G k
  | .inr (.inr (.inl _)) => 0
  | .inr (.inr (.inr (.inl _))) => -cK G
  | .inr (.inr (.inr (.inr (.inl _)))) => 0
  | .inr (.inr (.inr (.inr (.inr b)))) => if b then -1 else 0

/-- The lcm of the denominators of a row's coefficients and right side. -/
def rowDen (ρ : RowIdx Θ T) : ℕ :=
  (univ.lcm fun c => (rowCoef G ρ c).den).lcm (rowRhs G ρ).den

/-- `C ≥ 1` bounds the absolute values of all cleared (integer) coefficients and right sides. -/
def cC : ℕ :=
  max 1 (univ.sup fun ρ : RowIdx Θ T =>
    (univ.sup fun c => ((rowDen G ρ : ℚ) * rowCoef G ρ c).num.natAbs) ⊔
      ((rowDen G ρ : ℚ) * rowRhs G ρ).num.natAbs)

/-- `Q = ((N+1) C)^(N+1)`. -/
def cQ : ℕ := ((Fintype.card (Idx Θ T) + 1) * cC G) ^ (Fintype.card (Idx Θ T) + 1)

/-- `δ = 1 / (2 K Q)`. -/
def cδ : ℚ := 1 / (2 * cK G * cQ G)

/-- The support pattern `P = {k : z_k > 0}`. -/
def support (z : Idx Θ T → ℚ) : Finset (Idx Θ T) := univ.filter fun k => 0 < z k

end LCP

end DirectLCP
end Bssg
