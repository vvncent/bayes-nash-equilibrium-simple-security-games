# DEFINITIONS-directlcp.md: audit map for `BssgProofs/DirectLCP/`

Source: **[DL]** `book/articles/07-direct-lcp.tex` ("Exact Bayes–Nash equilibrium reduces to one
P-matrix LCP"); primary source `agent-runs/night-20261122T0016Z/remote_complexity/direct-game.md`.
Files: `Defs.lean` (definitions), `Statements.lean` (each lemma as a `Prop`, no `sorry`),
`Proofs.lean` (proofs, no `sorry`/`admit`/`axiom`). Everything is over `ℚ`, in namespace
`Bssg.DirectLCP`. Frozen definitions reused from `Definitions.lean`: `BSSG`, `BSSG.WellFormed`,
`BSSG.U`, `BSSG.IsDist`, `BSSG.IsDefMixed`, `BSSG.IsBNE`, `BSSG.coverage`, `BSSG.load`,
`BSSG.IsCoverageBNE`. Reused from `Proofs/Embedding.lean`: `Emb.simplex_br`, `Emb.fact0_main`.

## 1. Definitions (`Defs.lean`)

| Lean | Formalizes | [DL] sentence |
|---|---|---|
| `principal M S` | `M_{SS}` | §1 "For S ⊆ [N], M_SS is the principal submatrix on rows and columns S, and det M_∅∅ = 1" (`Matrix.submatrix` on the subtype `↥S`; `det` of the empty matrix is 1 in Mathlib) |
| `IsPMatrix`, `IsP0Matrix` | P- / P₀-matrix | §1 "M is a P-matrix if every principal minor is positive, and a P₀-matrix if every principal minor is nonnegative" (quantified over all `S : Finset ι`, incl. `∅`) |
| `slack q M z`, `IsLCPSol q M z` | `w = q + Mz`; LCP(q,M) | §1 "LCP(q,M) asks for z with z ≥ 0, w := q+Mz ≥ 0, z_k w_k = 0" |
| `IsSignReversing M y` | PV2 violation | Prop. classical (ii) "a nonzero vector y with y_k(My)_k ≤ 0 for all k" |
| `aa`, `bb`, `dd` | `a_ij`, `b_ij`, `d_j` | §1 Notation "a_ij = u₂⁰(θ_i,j), b_ij = u₂⁰ − u₂¹ ≥ 0, d_j = u₁¹(j) − u₁⁰(j) ≥ 0" |
| `wload f j`, `score G f j` | `w_j`, `π_j` | "w_j = Σ_i f_ij (load), π_j = d_j w_j (score)" |
| `IsFeasibleCov G x` | feasible coverage | "x ∈ [0,1]^n with Σ_j x_j = r" |
| `IsMarginalBNE G x f` | BNE in marginal coordinates | Def. dl:def:bne: feasible x, f ≥ 0, Σ_j f_ij = p_i, (a) f_ij > 0 ⇒ a_ij − b_ij x_j = max_k(...) (via frozen `BSSG.U`), (b) x maximizes Σ_j π_j x'_j over feasible x' |
| `FIdx`, `RIdx`, `Idx`, `Idx.f/t/lam/u/x` | variables `z = (f,t,λ,u,x)` | §2 "The variable order is z = (f,t,λ,u,x)"; first block `(f,t,λ)`, second block `(u,x)` (§3) |
| `incMat β` | the incidence matrices | §3 bullet list: attack column ij: 1 in type row i, β_ij in target row j; cap t_j: −1 in target row j; budget λ: −1 in every target row, 0 in type rows; all else 0 |
| `lcpB G = incMat b`, `lcpD G = incMat d` | `B`, `D` | §3 "B carries the attacker losses b_ij and D the defender gains d_j" |
| `lcpM G = fromBlocks 0 Bᵀ (−D) 0` | `M` | §3 display "M = (0 Bᵀ; −D 0)" |
| `shiftA G i j` | `A_ij` | §2 "A_ij = a_ij + 1 + max_k (b_ik − a_ik)" (`Finset.sup'`, needs `Nonempty T`) |
| `lcpq G` | `q` | read off table (dl:eq:lcp): `−A_ij`, `1`, `r`, `p_i`, `−1` |
| `slackTable G z` | the five slacks | table (dl:eq:lcp): `u_i + b_ij x_j − A_ij`, `1 − x_j`, `r − Σx`, `p_i − Σ_j f_ij`, `λ − 1 + t_j − d_j w_j`. `slackTable_proof` shows `q + Mz = slackTable` |
| `zx z`, `zf z` | the `x`, `f` parts of `z` | |
| `cU`, `cW`, `cDstar`, `cS`, `cK` | `U, W, D_*, S, K` | §4 "Constants" (see C4 below for `fold max`) |
| `lcpMδ G δ` | `M + δI` | Lemma dl:lem:pmatrix |
| `IsPatternFeasible G P z` | pattern LP | §4 "0 ≤ z ≤ K, z_k = 0 (k ∉ P), (q+Mz)_k ≥ 0 (all k), (q+Mz)_k = 0 (k ∈ P)" |
| `IsRelaxedFeasible G P z τ` | relaxed pattern LP (R1)–(R5) | §4 list (R1)–(R5) |
| `RowIdx`, `rowCoef`, `rowRhs` | the fixed list of `5N+2` rows | "the 2N rows ±(q+Mz)_k + τ ≥ 0, the 3N rows z_k ≥ 0, z_k ≤ K, z_k ≤ 0, and the two rows of (R5)", each written `coef ⬝ (z,τ) ≥ rhs` with the τ-coefficient inserted |
| `rowDen`, `cC` | clearing denominators, `C` | "Clear the denominators of each of these 5N+2 rows separately (lcm ...). Let C ≥ 1 be an integer bounding the absolute values of all resulting integer coefficients and right sides" (`C = max 1 (max over rows and entries of |cleared|)`) |
| `cQ` | `Q = ((N+1)C)^{N+1}` | display after (R5) |
| `cδ` | `δ = 1/(2KQ)` | Thm. dl:thm:main |
| `support z` | `P = {k : z*_k > 0}` | Thm. dl:thm:main |

## 2. Statements (`Statements.lean`) and status

| Lean `Prop` | [DL] | Proof | Status |
|---|---|---|---|
| `CutoffForm` | Lemma dl:lem:cutoff (any scores π) | `cutoffForm_proof` | proved |
| `SlackTable` | table (dl:eq:lcp) = `q + Mz` with `M = (0 Bᵀ; −D 0)` | `slackTable_proof` | proved |
| `FormulationA` | Lemma dl:lem:formulation (a), incl. `λ > 0`, `Σx = r` | `formulationA_proof` | proved |
| `FormulationB` | Lemma dl:lem:formulation (b) | `formulationB_proof` | proved |
| `BlockDet` | eq. (dl:eq:blockdet) and "if |F| ≠ |R| the minor is 0" | `blockDet_proof` | proved |
| `P0Core` | Lemma dl:lem:p0, Steps 0–4: `det B_{R,F} det D_{R,F} ≥ 0` | `p0Core_proof` | proved (different route, see §3) |
| `P0` | Lemma dl:lem:p0 | `p0_proof` | proved |
| `DiagPerturbation` | Lemma dl:lem:pmatrix: P-matrix, `det(M+δI)_SS ≥ δ^{|S|}`, no sign-reversing vector, ≤ 1 LCP solution | `diagPerturbation_proof` | proved |
| `P0AddSmulIsP` | generic P₀ + δI ⇒ P | `p0AddSmulIsP_proof` | proved |
| `UniformBound` | Lemma dl:lem:bound | `uniformBound_proof` | proved |
| `PatternSol` | "Every feasible point solves LCP(q,M)" | `patternSol_proof` | proved |
| `GapLemma`, `Gap` | Lemma dl:lem:gap | `gap_proof` (Gap.lean) | proved |
| `MainTheorem` | Thm. dl:thm:main (mathematical content) | `main_proof` (Gap.lean) | proved |
| `MarginalIffCoverage` | bridge: r = 1, payoffs 0/1, positive priors: marginal BNE ⇔ frozen `IsCoverageBNE` | `marginalIffCoverage_proof` | proved |
| `BNEIffMarginal` | bridge to frozen `IsBNE` (same hypotheses, via Fact 0) | `bneIffMarginal_proof` | proved |

## 3. Modelling choices an auditor should check

1. **D1. Rationals only.** All data, LCP vectors and BNEs are in `ℚ`.
2. **D2. Zero-prior types are kept**, not dropped. `IsMarginalBNE` forces `f_i = 0` for them and
   (a) is vacuous; `FormulationA/B` hold with `p_i ≥ 0` (the article assumes `p_i > 0`). Restoring
   zero-prior types by a best response (decoder (b)) is not formalized.
3. **D3. BNE notion.** `IsMarginalBNE` is new: the frozen `IsCoverageBNE` is the `r = 1`, 0/1-payoff
   Fact 0 form and does not express general `r` and `d`. The link to the frozen general `IsBNE` is
   proved only for `r = 1`, `u₁⁰ ≡ 0`, `u₁¹ ≡ 1`, positive priors (`BNEIffMarginal`). For general
   `r` the link needs the decoder Lemma dl:lem:decode (every feasible `x` is the coverage of a mixed
   strategy on ≤ n pure strategies), which is not formalized.
4. **D4. Constants.** `U = fold max 1 A` and `D_* = fold max 0 d`. These equal `max A` and `max d`
   when `Θ` is nonempty (since `A_ij ≥ 1`) and since `d ≥ 0`, `T ≠ ∅`. If `Θ = ∅`, `U = 1`.
   `K` is the integer ceiling, cast to `ℚ`.
5. **D5. `C`** is `max 1` of the sup over all `5N+2` rows of `|lcm(dens) · entry|` (computed as
   `num.natAbs` of the cleared, integral value); the article's "C ≥ 1 bounding ..." is any such
   bound, we fix the least one (≥ 1).
6. **D6. Main theorem.** `MainTheorem` quantifies over every solution `z*` of `LCP(q, M+δI)`;
   existence of a solution for a P-matrix (cited Prop. classical (i)) is not formalized, uniqueness
   is (`DiagPerturbation`). Edge cases `r = 0`, `r = n` (fixed instance `[1],[0]`), polynomial
   running time, bit lengths and the decoder are not formalized. `Nonempty T` is assumed where
   `A_ij` (a max over targets) is used.
7. **D7. P₀ proof route differs from [DL].** Instead of forests, anchored trees and cofactor-sign
   comparisons, `p0core_pos` (for `d > 0`, `b ≥ 0`) inducts on the size of the selection: expand
   along a column of `D` with ≤ 1 nonzero entry; otherwise every column of `D` is a full attack
   column or the budget column, `y = (1 on type rows, −1/d_j on target rows)` annihilates the attack
   columns of `D`, giving `det D = 0` without budget column and `det D · y = κ · adj(D)_{λ,·}`
   (`κ > 0`) with it; then the Laplace expansion of `det B` along the budget column has terms of one
   sign by the induction hypothesis on the cofactors. Zero `d_j` follow by continuity in `d`
   (Step 4); zero `b_ij` need no continuity. Statement-level content is the same.
8. **D8. Article inaccuracy (minor, harmless).** [DL] Step 0 says that after dividing target rows
   of `D` by `d_j`, "a cap column has the single entry −1 in both" and the budget column has "−1
   at every selected target row ... in both". In `D'` these entries are `−1/d_j`, not `−1`. Only
   signs and zero patterns are used afterwards, so the argument is unaffected.
