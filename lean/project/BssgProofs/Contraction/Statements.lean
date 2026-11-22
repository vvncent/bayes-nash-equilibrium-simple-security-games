import BssgProofs.Contraction.Defs

/-!
# One `ℓ₁` contraction for the game: statements

Every result of [C] (`book/readable/chapters/ch5-upper.tex`, sections `sec:contraction` and
`sec:ueopl`) that is formalized here is stated as a `Prop`-valued definition (no `sorry` in this
file).  `Proofs.lean` proves each as `<name>_proof`.  The map to the book is in
`DEFINITIONS-contraction.md`.

Hypotheses: only `G.WellFormed` (priors `p_i ≥ 0` summing to `1`, `b_ij ≥ 0`, `d_j ≥ 0`, `r ≤ n`)
and `Nonempty T`.  Zero slopes `b_ij = 0`, zero gains `d_j = 0` and zero priors are all allowed;
the book's standing assumptions `p_i > 0` and `0 < r < n` are not needed.
-/

namespace Bssg
namespace Contraction

open Finset
open DirectLCP (IsMarginalBNE)

section

variable (T Θ : Type*) [Fintype T] [DecidableEq T] [Fintype Θ] [DecidableEq Θ] [Nonempty T]

/-- [C, Lemma ueopl-proj]: `y = proj u` lies in the simplex, is the Euclidean projection of `u`
onto it, and (a) a positive coordinate is within `1` of the maximum (in payoff units: within `σ`
of the row maximum). -/
def ProjectionLemma : Prop :=
  ∀ u : T → ℚ, BSSG.IsDist (proj u) ∧
    (∀ z : T → ℚ, BSSG.IsDist z → ∑ j, (u j - proj u j) ^ 2 ≤ ∑ j, (u j - z j) ^ 2) ∧
    ∀ j, 0 < proj u j → ∀ k, u k < u j + 1

/-- [C, *Constants*]: positivity and (eq:ueopl-const) `η d̄ Σ_j 1/d'_j ≤ κ/4 ≤ κ(1−2δ)`. -/
def ConstantsLemma : Prop :=
  ∀ G : BSSG T Θ, G.WellFormed →
    0 < gThr G ∧ (∀ j, 0 < dP G j) ∧ 0 < cη G ∧ 0 < cδ G ∧ cδ G ≤ 1 / 8 ∧
    cη G * dBar G * invSum G ≤ cκ G / 4 ∧ cκ G / 4 ≤ cκ G * (1 - 2 * cδ G)

/-- [C, *The map*]: `F` maps `[0,1]^{n+1}` into itself. -/
def MapsCube : Prop :=
  ∀ G : BSSG T Θ, G.WellFormed → ∀ u : T ⊕ Unit → ℚ, InCube u → InCube (F G u)

/-- [C, Lemma ueopl-contraction]: `‖F u − F u'‖₁ ≤ (1−δ)‖u − u'‖₁` on `[0,1]^{n+1}`, with `δ > 0`. -/
def L1Contraction : Prop :=
  ∀ G : BSSG T Θ, G.WellFormed → 0 < cδ G ∧
    ∀ u u' : T ⊕ Unit → ℚ, InCube u → InCube u' →
      l1 (F G u - F G u') ≤ (1 - cδ G) * l1 (u - u')

/-- [C, Lemma ueopl-contraction], "in particular": `F` has at most one fixed point.
(Existence over `ℚ` is not stated; see `DEFINITIONS-contraction.md`.) -/
def FixedPointUnique : Prop :=
  ∀ G : BSSG T Θ, G.WellFormed → ∀ u u' : T ⊕ Unit → ℚ,
    F G u = u → F G u' = u' → u = u'

/-- [C, Lemma ueopl-budget] and the sharper bound after it. -/
def BudgetAtFixedPoint : Prop :=
  ∀ G : BSSG T Θ, G.WellFormed → ∀ u : T ⊕ Unit → ℚ, F G u = u →
    (cδ G * cκ G / 2 ≤ qPart u ∧ qPart u ≤ (1 - cδ G / 2) * cκ G) ∧ sOf G u = qPart u ∧
    Rm G (xPart u) (sOf G u) = preR G (xPart u) (sOf G u) ∧
    ∑ j, xPart u j + qPart u = G.r + cκ G / 2 ∧
    |∑ j, zOf G u j - G.r| ≤ cκ G / (2 * (1 - cδ G)) ∧
    |∑ j, zOf G u j - G.r| ≤ cκ G / 2

end

section

variable (T Θ : Type*) [Fintype T] [DecidableEq T] [Fintype Θ] [DecidableEq Θ]

/-- [C, Lemma ueopl-pattern (a)]: every feasible point of a pattern LP is an exact BNE (in marginal
coordinates), even if some allowed flows vanish. -/
def PatternSoundness : Prop :=
  ∀ (G : BSSG T Θ) (P : Pattern Θ T) (x : T → ℚ) (f : Θ → T → ℚ) (v : Θ → ℚ) (l : ℚ),
    IsPatternPoint G P x f v l → IsMarginalBNE G x f

/-- [C, Lemma ueopl-pattern (c); part (b) is not stated separately]: with `g = 1/(4Q)`, `Q = (NH)^N`, a point satisfying every
constraint of a pattern to accuracy `t₀ < g` and the outer boxes exactly makes the unrelaxed pattern
LP feasible. -/
def RepairThreshold : Prop :=
  ∀ (G : BSSG T Θ) (P : Pattern Θ T) (t0 : ℚ) (x : T → ℚ) (f : Θ → T → ℚ) (v : Θ → ℚ) (l : ℚ),
    t0 < gThr G → IsRelaxedPattern G P t0 x f v l → PatternFeasible G P

end

section

variable (T Θ : Type*) [Fintype T] [DecidableEq T] [Fintype Θ] [DecidableEq Θ] [Nonempty T]

/-- [C, Lemma ueopl-decoding], residual part: at the fixed point, `(z, f(x), v, λ(q))` with
`z = T(x,q)` and `v_i = max_j U_ij(z)` satisfies the outer boxes exactly and all constraints of the
recorded pattern with residual at most `3g/8` (strictly below `g`). -/
def DecodingResiduals : Prop :=
  ∀ G : BSSG T Θ, G.WellFormed → ∀ u : T ⊕ Unit → ℚ, F G u = u →
    IsRelaxedPattern G (patternOf G u) (3 * gThr G / 8) (zOf G u) (fA G (xPart u))
      (vOf G (zOf G u)) (lam G (sOf G u))

/-- [C, Lemma ueopl-decoding], conclusion: the pattern LP recorded at the fixed point is feasible,
and every solution of it is an exact BNE in marginal coordinates. -/
def Decoding : Prop :=
  ∀ G : BSSG T Θ, G.WellFormed → ∀ u : T ⊕ Unit → ℚ, F G u = u →
    PatternFeasible G (patternOf G u) ∧
      ∀ x f v l, IsPatternPoint G (patternOf G u) x f v l → IsMarginalBNE G x f

/-- [C, Thm. sx-game and Thm. ueopl-main], correctness of the reduction (not its running time):
for every well-formed game, `F` maps the cube into itself, is a `(1−δ)`-contraction in `ℓ₁` with
`δ > 0` (so the PL-Contraction instance `(F, 1−δ, 1)` has no violations of type CMV1/CMV2), has at
most one fixed point, and from any fixed point the recorded pattern LP is feasible and each of its
solutions is an exact BNE; in particular an exact BNE exists as soon as a fixed point does. -/
def Reduction : Prop :=
  ∀ G : BSSG T Θ, G.WellFormed →
    0 < cδ G ∧ (∀ u, InCube u → InCube (F G u)) ∧
    (∀ u u', InCube u → InCube u' → l1 (F G u - F G u') ≤ (1 - cδ G) * l1 (u - u')) ∧
    (∀ u u', F G u = u → F G u' = u' → u = u') ∧
    ∀ u, F G u = u → InCube u ∧ PatternFeasible G (patternOf G u) ∧
      (∀ x f v l, IsPatternPoint G (patternOf G u) x f v l → IsMarginalBNE G x f) ∧
      ∃ x f, IsMarginalBNE G x f

end

end Contraction
end Bssg
