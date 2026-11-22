import Mathlib
import BssgProofs.DirectLCP.Defs

/-!
# One `ℓ₁` contraction for the game: definitions

Formalization of `book/readable/chapters/ch5-upper.tex`, Section "One ℓ1 contraction for the game"
(`sec:contraction`), cited below as **[C]**, with its subsections *Pattern LPs and the repair
threshold*, *Constants*, *The map*.  Every definition is cross-referenced in
`DEFINITIONS-contraction.md`.  Everything is over `ℚ`.

The game is the frozen `Bssg.BSSG T Θ` (targets `T`, types `Θ`) with the data
`a_ij = aa G i j`, `b_ij = bb G i j`, `d_j = dd G j` and the load / score `wload`, `score` of
`DirectLCP/Defs.lean`; the attacker payoff is the frozen `BSSG.U i j x = a_ij − b_ij x_j`.

`F` is represented as a function on rational vectors `T ⊕ Unit → ℚ` (`inl j` is `x_j`, `inr ()` is
the extra coordinate `q`).  It is built only from `max`, `min`, `+`, `−`, multiplication by rational
constants and division by rational constants (a LinearFIXP-style piecewise-affine map); no circuit
datatype is formalized.  The simplex projection's threshold `θ` is written as a maximum over all
nonempty subsets instead of over sorted prefixes; the two maxima are equal (a `k`-subset sum is at
most the top-`k` prefix sum, and prefixes are subsets).

Sections
1. Clipping and the simplex projection.
2. Pattern LPs: patterns, the relaxed pattern LP (human-readable form), its fixed list of rows,
   clearing denominators, `H`, `N`, `Q`, the repair threshold `g`.
3. Constants `b_max, d'_j, d̄, σ, κ, η, δ, a⁰`.
4. The map: `y_i(x)`, `f_ij(x)`, `w_j(x)`, `λ(s)`, `T_j(x,s)`, `R(x,s)`, `F(x,q)`.
5. Decoding data: the pattern recorded at a point, `v_i = max_j U_ij(z)`.
-/

namespace Bssg
namespace Contraction

open Finset
open DirectLCP (aa bb dd wload score IsFeasibleCov IsMarginalBNE)

/-! ## 1. Clipping and the simplex projection -/

/-- `C_{l,h}(u) = min(h, max(l, u))` [C, *Constants*, last sentence]. -/
def clip (l h u : ℚ) : ℚ := min h (max l u)

section Proj

variable {T : Type*} [Fintype T] [DecidableEq T] [Nonempty T]

/-- The nonempty subsets of `T`. -/
def nonemptySubsets (T : Type*) [Fintype T] [DecidableEq T] : Finset (Finset T) :=
  univ.filter fun S => S.Nonempty

theorem nonemptySubsets_nonempty : (nonemptySubsets T).Nonempty :=
  ⟨univ, mem_filter.mpr ⟨mem_univ _, univ_nonempty⟩⟩

/-- The simplex-projection threshold `θ(u) = max_{∅ ≠ S ⊆ T} (Σ_{h∈S} u_h − 1)/|S|`
[C, Lemma ueopl-proj]; equal to the book's `max_k (Σ_{h ≤ k} u_(h) − 1)/k` over sorted prefixes. -/
def projTheta (u : T → ℚ) : ℚ :=
  (nonemptySubsets T).sup' nonemptySubsets_nonempty fun S => (∑ h ∈ S, u h - 1) / S.card

/-- The projection of `u` onto the probability simplex: `y_j = max(0, u_j − θ)`
[C, Lemma ueopl-proj]. (`Proofs.lean` proves it is the Euclidean projection.) -/
def proj (u : T → ℚ) (j : T) : ℚ := max 0 (u j - projTheta u)

end Proj

/-! ## 2. Pattern LPs and the repair threshold -/

/-- Target labels of a pattern [C, *Pattern LPs*]. -/
inductive Label
  | zero
  | one
  | free
  deriving DecidableEq

/-- A pattern: a set of allowed type–target edges and a label for every target. -/
structure Pattern (Θ T : Type*) where
  allowed : Θ → T → Bool
  label : T → Label

section PatternLP

variable {T Θ : Type*} [Fintype T] [DecidableEq T] [Fintype Θ] [DecidableEq Θ]
variable (G : BSSG T Θ)

/-- `max_j d_j` (as `fold max 0`; equal to the maximum when `T ≠ ∅` and `d ≥ 0`). -/
def dMax : ℚ := univ.fold max 0 (dd G)

/-- `max_{i,j} (|a_ij| + b_ij)` (as `fold max 0`). -/
def abMax : ℚ := (univ : Finset (Θ × T)).fold max 0 fun p => |aa G p.1 p.2| + bb G p.1 p.2

/-- Outer box for `λ`: `0 ≤ λ ≤ 1 + max_j d_j`. -/
def lamBox : ℚ := 1 + dMax G

/-- Outer box for `v`: `|v_i| ≤ 2 + max_{i,j}(|a_ij| + b_ij)`. -/
def vBox : ℚ := 2 + abMax G

/-- **The relaxed pattern LP** at slack `t` [C, Lemma ueopl-pattern (b)]: every pattern constraint
(each equality as two inequalities) holds up to the additive slack `t`, the outer boxes hold
exactly, and `0 ≤ t ≤ 1` (the `t ≤ 1` form of the remark after the lemma).  The (unrelaxed)
pattern LP is the case `t = 0` (`IsPatternPoint`).  Variables `x, f, v, λ`; `w_j = Σ_i f_ij`,
`d_j w_j = score G f j`. -/
structure IsRelaxedPattern (P : Pattern Θ T) (t : ℚ) (x : T → ℚ) (f : Θ → T → ℚ) (v : Θ → ℚ)
    (l : ℚ) : Prop where
  t_nonneg : 0 ≤ t
  t_le_one : t ≤ 1
  x_box : ∀ j, 0 ≤ x j ∧ x j ≤ 1
  f_box : ∀ i j, 0 ≤ f i j ∧ f i j ≤ 1
  l_box : 0 ≤ l ∧ l ≤ lamBox G
  v_box : ∀ i, -vBox G ≤ v i ∧ v i ≤ vBox G
  budget_le : ∑ j, x j ≤ (G.r : ℚ) + t
  budget_ge : (G.r : ℚ) ≤ ∑ j, x j + t
  rowsum_le : ∀ i, ∑ j, f i j ≤ G.prior i + t
  rowsum_ge : ∀ i, G.prior i ≤ ∑ j, f i j + t
  off : ∀ i j, P.allowed i j = false → f i j ≤ t
  br : ∀ i j, G.U i j x ≤ v i + t
  br_eq : ∀ i j, P.allowed i j = true → v i ≤ G.U i j x + t
  zero_x : ∀ j, P.label j = .zero → x j ≤ t
  one_x : ∀ j, P.label j = .one → 1 ≤ x j + t
  cut_le : ∀ j, P.label j ≠ .one → score G f j ≤ l + t
  cut_ge : ∀ j, P.label j ≠ .zero → l ≤ score G f j + t

/-- A feasible point of the (unrelaxed) **pattern LP** [C, *Pattern LPs*]. -/
def IsPatternPoint (P : Pattern Θ T) (x : T → ℚ) (f : Θ → T → ℚ) (v : Θ → ℚ) (l : ℚ) : Prop :=
  IsRelaxedPattern G P 0 x f v l

/-- The pattern LP of `P` is feasible. -/
def PatternFeasible (P : Pattern Θ T) : Prop :=
  ∃ x f v l, IsPatternPoint G P x f v l

/-! ### The fixed list of rows -/

/-- LP variables `(x, f, v, λ, t)`: `inl j` = `x_j`, `inr (inl (i,j))` = `f_ij`,
`inr (inr (inl i))` = `v_i`, `inr (inr (inr (inl ())))` = `λ`, `inr (inr (inr (inr ())))` = `t`.
`N = |Var| = n + mn + m + 2`. -/
abbrev Var (Θ T : Type*) := T ⊕ (Θ × T) ⊕ Θ ⊕ Unit ⊕ Unit

/-- A vector on `Var` from its blocks `(x, f, v, λ, t)`. -/
def vec (cx : T → ℚ) (cf : Θ → T → ℚ) (cv : Θ → ℚ) (cl ct : ℚ) : Var Θ T → ℚ :=
  Sum.elim cx (Sum.elim (fun p => cf p.1 p.2) (Sum.elim cv (Sum.elim (fun _ => cl) (fun _ => ct))))

/-- Every row that can occur in any pattern LP, written `rhs ≤ coef ⬝ (x,f,v,λ,t)` with the
coefficient of `t` inserted (`0` for the outer boxes).  Pattern rows: `budLe/budGe` (budget),
`sumLe/sumGe` (row sums), `off` (`f_ij ≤ t` off allowed edges), `br` (`U_ij(x) ≤ v_i + t`),
`brEq` (`v_i ≤ U_ij(x) + t` on allowed edges), `zeroX` (`x_j ≤ t`), `oneX` (`1 ≤ x_j + t`),
`cutLe` (`d_j w_j ≤ λ + t`), `cutGe` (`λ ≤ d_j w_j + t`).  Outer boxes and `0 ≤ t ≤ 1`:
`xLo … tHi`. -/
inductive Row (Θ T : Type*)
  | budLe | budGe
  | sumLe (i : Θ) | sumGe (i : Θ)
  | off (i : Θ) (j : T) | br (i : Θ) (j : T) | brEq (i : Θ) (j : T)
  | zeroX (j : T) | oneX (j : T) | cutLe (j : T) | cutGe (j : T)
  | xLo (j : T) | xHi (j : T) | fLo (i : Θ) (j : T) | fHi (i : Θ) (j : T)
  | lLo | lHi | vLo (i : Θ) | vHi (i : Θ) | tLo | tHi
  deriving DecidableEq, Fintype

/-- Indicator vectors. -/
def ind {α : Type*} [DecidableEq α] (a : α) (c : ℚ) : α → ℚ := fun a' => if a' = a then c else 0

/-- Coefficients of the rows (the coefficient of `t` included). -/
def coef : Row Θ T → Var Θ T → ℚ
  | .budLe => vec (fun _ => -1) 0 0 0 1
  | .budGe => vec (fun _ => 1) 0 0 0 1
  | .sumLe i => vec 0 (fun i' _ => if i' = i then -1 else 0) 0 0 1
  | .sumGe i => vec 0 (fun i' _ => if i' = i then 1 else 0) 0 0 1
  | .off i j => vec 0 (fun i' j' => if i' = i ∧ j' = j then -1 else 0) 0 0 1
  | .br i j => vec (ind j (bb G i j)) 0 (ind i 1) 0 1
  | .brEq i j => vec (ind j (-bb G i j)) 0 (ind i (-1)) 0 1
  | .zeroX j => vec (ind j (-1)) 0 0 0 1
  | .oneX j => vec (ind j 1) 0 0 0 1
  | .cutLe j => vec 0 (fun _ j' => if j' = j then -dd G j else 0) 0 1 1
  | .cutGe j => vec 0 (fun _ j' => if j' = j then dd G j else 0) 0 (-1) 1
  | .xLo j => vec (ind j 1) 0 0 0 0
  | .xHi j => vec (ind j (-1)) 0 0 0 0
  | .fLo i j => vec 0 (fun i' j' => if i' = i ∧ j' = j then 1 else 0) 0 0 0
  | .fHi i j => vec 0 (fun i' j' => if i' = i ∧ j' = j then -1 else 0) 0 0 0
  | .lLo => vec 0 0 0 1 0
  | .lHi => vec 0 0 0 (-1) 0
  | .vLo i => vec 0 0 (ind i 1) 0 0
  | .vHi i => vec 0 0 (ind i (-1)) 0 0
  | .tLo => vec 0 0 0 0 1
  | .tHi => vec 0 0 0 0 (-1)

/-- Right sides of the rows (same order as `coef`). -/
def rhs : Row Θ T → ℚ
  | .budLe => -(G.r : ℚ)
  | .budGe => (G.r : ℚ)
  | .sumLe i => -G.prior i
  | .sumGe i => G.prior i
  | .off _ _ => 0
  | .br i j => aa G i j
  | .brEq i j => -aa G i j
  | .zeroX _ => 0
  | .oneX _ => 1
  | .cutLe _ => 0
  | .cutGe _ => 0
  | .xLo _ => 0
  | .xHi _ => -1
  | .fLo _ _ => 0
  | .fHi _ _ => -1
  | .lLo => 0
  | .lHi => -lamBox G
  | .vLo _ => -vBox G
  | .vHi _ => -vBox G
  | .tLo => 0
  | .tHi => -1

/-- The rows belonging to the relaxed LP of pattern `P`. -/
def isActive (P : Pattern Θ T) : Row Θ T → Bool
  | .off i j => !P.allowed i j
  | .brEq i j => P.allowed i j
  | .zeroX j => decide (P.label j = .zero)
  | .oneX j => decide (P.label j = .one)
  | .cutLe j => decide (P.label j ≠ .one)
  | .cutGe j => decide (P.label j ≠ .zero)
  | _ => true

/-- Clearing denominators of row `ρ`: the lcm of the denominators of its coefficients and its
right side ("clear denominators row by row"). -/
def rowDen (ρ : Row Θ T) : ℕ :=
  (univ.lcm fun c => (coef G ρ c).den).lcm (rhs G ρ).den

/-- `H ≥ 1` bounds all resulting integer entries and right-hand sides. -/
def cH : ℕ :=
  max 1 (univ.sup fun ρ : Row Θ T =>
    (univ.sup fun c => ((rowDen G ρ : ℚ) * coef G ρ c).num.natAbs) ⊔
      ((rowDen G ρ : ℚ) * rhs G ρ).num.natAbs)

/-- `N = n + mn + m + 2`, the number of variables including `t`. -/
def cN : ℕ := Fintype.card (Var Θ T)

/-- `Q = (N H)^N`. -/
def cQ : ℕ := (cN (Θ := Θ) (T := T) * cH G) ^ cN (Θ := Θ) (T := T)

/-- **The repair threshold** `g = 1/(4Q)` [C, Lemma ueopl-pattern (c)]. -/
def gThr : ℚ := 1 / (4 * cQ G)

end PatternLP

/-! ## 3. Constants -/

section Constants

variable {T Θ : Type*} [Fintype T] [DecidableEq T] [Fintype Θ] [DecidableEq Θ] [Nonempty T]
variable (G : BSSG T Θ)

/-- `b_max = max_{i,j} b_ij` (as `fold max 0`). -/
def bMax : ℚ := (univ : Finset (Θ × T)).fold max 0 fun p => bb G p.1 p.2

/-- `d'_j = d_j + g/16`. -/
def dP (j : T) : ℚ := dd G j + gThr G / 16

/-- `d̄ = max_j d'_j`. -/
def dBar : ℚ := univ.sup' univ_nonempty (dP G)

/-- `σ = g/8`. -/
def cσ : ℚ := gThr G / 8

/-- `κ = g/8`. -/
def cκ : ℚ := gThr G / 8

/-- `Σ_j 1/d'_j`. -/
def invSum : ℚ := ∑ j, 1 / dP G j

/-- `η = min(1, σ/(1+b_max), κ/(4(1+d̄)(1+Σ_j 1/d'_j)))`. -/
def cη : ℚ :=
  min 1 (min (cσ G / (1 + bMax G)) (cκ G / (4 * (1 + dBar G) * (1 + invSum G))))

/-- `δ = min(1/8, η g/(8(1+d̄)), g/(8(1+b_max)))`. -/
def cδ : ℚ :=
  min (1 / 8) (min (cη G * gThr G / (8 * (1 + dBar G))) (gThr G / (8 * (1 + bMax G))))

/-- `a⁰ = (r/n) 𝟏`. -/
def a0 : ℚ := (G.r : ℚ) / Fintype.card T

end Constants

/-! ## 4. The map -/

section Map

variable {T Θ : Type*} [Fintype T] [DecidableEq T] [Fintype Θ] [DecidableEq Θ] [Nonempty T]
variable (G : BSSG T Θ)

/-- `y_i(x)`: the projection of `U_i(x)/σ` onto the simplex on the targets. -/
def yA (x : T → ℚ) (i : Θ) : T → ℚ := proj fun j => G.U i j x / cσ G

/-- `f_ij(x) = p_i y_ij(x)`. -/
def fA (x : T → ℚ) (i : Θ) (j : T) : ℚ := G.prior i * yA G x i j

/-- `w_j(x) = Σ_i p_i y_ij(x)`. -/
def wA (x : T → ℚ) (j : T) : ℚ := ∑ i, G.prior i * yA G x i j

/-- `λ(s) = C_{0,d̄}(d̄ ((1−δ)κ − s)/((1−2δ)κ))`. -/
def lam (s : ℚ) : ℚ :=
  clip 0 (dBar G) (dBar G * ((1 - cδ G) * cκ G - s) / ((1 - 2 * cδ G) * cκ G))

/-- The unclipped defender update `x_j + η (w_j(x) − λ(s)/d'_j)`. -/
def preT (x : T → ℚ) (s : ℚ) (j : T) : ℚ := x j + cη G * (wA G x j - lam G s / dP G j)

/-- `T_j(x,s) = C_{0,1}(x_j + η (w_j(x) − λ(s)/d'_j))`. -/
def Tm (x : T → ℚ) (s : ℚ) (j : T) : ℚ := clip 0 1 (preT G x s j)

/-- The unclipped budget update `s + Σ_j x_j − Σ_j T_j(x,s)`. -/
def preR (x : T → ℚ) (s : ℚ) : ℚ := s + ∑ j, x j - ∑ j, Tm G x s j

/-- `R(x,s) = C_{0,κ}(s + Σ_j x_j − Σ_j T_j(x,s))`. -/
def Rm (x : T → ℚ) (s : ℚ) : ℚ := clip 0 (cκ G) (preR G x s)

/-- The coverage part `x` of `u ∈ ℚ^{n+1}`. -/
def xPart (u : T ⊕ Unit → ℚ) : T → ℚ := fun j => u (.inl j)

/-- The extra coordinate `q` of `u ∈ ℚ^{n+1}`. -/
def qPart (u : T ⊕ Unit → ℚ) : ℚ := u (.inr ())

/-- `s = C_{0,κ}(q)`. -/
def sOf (u : T ⊕ Unit → ℚ) : ℚ := clip 0 (cκ G) (qPart u)

/-- **The map** `F(x,q) = (1−δ)(T(x,s), R(x,s)) + δ (a⁰, κ/2)` [C, *The map*]. -/
def F (u : T ⊕ Unit → ℚ) : T ⊕ Unit → ℚ :=
  Sum.elim (fun j => (1 - cδ G) * Tm G (xPart u) (sOf G u) j + cδ G * a0 G)
    (fun _ => (1 - cδ G) * Rm G (xPart u) (sOf G u) + cδ G * (cκ G / 2))

/-- The `ℓ₁` norm on `ℚ^{n+1}`. -/
def l1 {ι : Type*} [Fintype ι] (u : ι → ℚ) : ℚ := ∑ k, |u k|

/-- The unit cube `[0,1]^{n+1}`. -/
def InCube {ι : Type*} (u : ι → ℚ) : Prop := ∀ k, 0 ≤ u k ∧ u k ≤ 1

end Map

/-! ## 5. Decoding data -/

section Decode

variable {T Θ : Type*} [Fintype T] [DecidableEq T] [Fintype Θ] [DecidableEq Θ] [Nonempty T]
variable (G : BSSG T Θ)

/-- `z = T(x, s)` at a point `u = (x, q)`. -/
def zOf (u : T ⊕ Unit → ℚ) : T → ℚ := Tm G (xPart u) (sOf G u)

/-- The label of a target from `z_j`: zero if `z_j = 0`, one if `z_j = 1`, free otherwise. -/
def labelOf (z : ℚ) : Label := if z = 0 then .zero else if z = 1 then .one else .free

/-- **The pattern recorded at `u`** [C, Lemma ueopl-decoding]: allowed edges are the pairs with
`f_ij(x) > 0`; labels from `z = T(x,q)`. -/
def patternOf (u : T ⊕ Unit → ℚ) : Pattern Θ T where
  allowed i j := decide (0 < fA G (xPart u) i j)
  label j := labelOf (zOf G u j)

/-- `v_i = max_j U_ij(z)`. -/
def vOf (z : T → ℚ) (i : Θ) : ℚ := univ.sup' univ_nonempty fun j => G.U i j z

end Decode

end Contraction
end Bssg
