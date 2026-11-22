# DEFINITIONS-contraction.md: audit map for `BssgProofs/Contraction/`

Source: **[C]** `book/readable/chapters/ch5-upper.tex`, Section "One ℓ1 contraction for the game"
(`sec:contraction`: *Pattern LPs and the repair threshold*, *Constants*, *The map*, *Contraction*,
*Decoding the fixed point*) and Section `sec:ueopl`. Secondary: `book/articles/04-ueopl.tex`,
`book/articles/05-subexp.tex`; referee reports `review2/ueopl.md`, `review2/subexp.md`.

Files: `Defs.lean` (definitions), `Statements.lean` (each result as a `Prop`, no `sorry`),
`Proofs.lean` (proofs; no `sorry`/`admit`/`axiom`). Namespace `Bssg.Contraction`, everything over `ℚ`.
Reused, not edited: `BSSG`, `BSSG.WellFormed`, `BSSG.U`, `BSSG.IsDist` (`Definitions.lean`);
`aa`, `bb`, `dd`, `wload`, `score`, `IsFeasibleCov`, `IsMarginalBNE` (`DirectLCP/Defs.lean`);
`cutoff_form`, `bb_nonneg`, `dd_nonneg`, `int_of_den_dvd` (`DirectLCP/Proofs.lean`);
the generic LP lemmas `exists_vertex`, `vertex_value` (vertex walk, Cramer, `|det| ≤ N! H^N`) from
`DirectLCP/Gap.lean`.

## 1. Definitions (`Defs.lean`)

| Lean | [C] sentence |
|---|---|
| `clip l h u = min h (max l u)` | *Constants*: "write `C_{l,h}(u)=min(h,max(l,u))` for clipping" |
| `projTheta u`, `proj u j` | Lemma ueopl-proj: "`y_j=max(0,u_j−θ)`, `θ=max_k (Σ_{h≤k}u_(h)−1)/k`". **Choice:** `θ` is the max over *all nonempty subsets* `S` of `(Σ_S u−1)/|S|`; equal in value (a `k`-subset sum ≤ top-`k` prefix sum; prefixes are subsets). Not the sorting-network circuit. `proj_euclidean` proves it is the Euclidean projection ("let `y_i(x)` be the Euclidean projection ... onto the probability simplex") |
| `Label` (`zero/one/free`), `Pattern` (`allowed : Θ → T → Bool`, `label`) | *Pattern LPs*: "A pattern specifies a set of allowed type–target edges and, for every target, a label in {zero, one, free}" |
| `dMax`, `abMax`, `lamBox = 1+max d`, `vBox = 2+max(|a|+b)` | "outer boxes `x,f∈[0,1]`, `0≤λ≤1+max_j d_j`, `|v_i|≤2+max_{i,j}(|a_ij|+b_ij)`" (`fold max 0`; equals the max as `d,b ≥ 0`) |
| `IsRelaxedPattern G P t x f v l` | Lemma ueopl-pattern (b): every pattern constraint relaxed by the common slack `t` (each equality as two inequalities): budget, row sums, `f_ij ≤ t` off allowed edges, `U_ij(x) ≤ v_i+t` all pairs, `v_i ≤ U_ij(x)+t` on allowed edges, `x_j ≤ t` & `d_jw_j ≤ λ+t` (zero), `x_j ≥ 1−t` & `d_jw_j ≥ λ−t` (one), both cutoff rows (free); outer boxes exact; **`0 ≤ t ≤ 1`** (the "`t` restricted to `[0,1]`" form of the remark after the lemma). `0 ≤ x ≤ 1` is kept as an exact box (it is both a pattern bound and an outer box) |
| `IsPatternPoint G P … = IsRelaxedPattern G P 0 …`, `PatternFeasible` | the pattern LP itself |
| `Var Θ T = T ⊕ (Θ×T) ⊕ Θ ⊕ Unit ⊕ Unit`, `vec` | variables `x, f, v, λ, t`; `N = |Var| = n+mn+m+2` |
| `Row`, `coef`, `rhs`, `isActive` | "Write every row that can occur in any pattern LP with the coefficient of `t` inserted before clearing denominators": a fixed list of 21 row families `rhs ≤ coef·(x,f,v,λ,t)`; a pattern selects its active rows. `relaxed_iff` proves the row list is exactly `IsRelaxedPattern` |
| `rowDen`, `cH` | "clear denominators row by row, let `H ≥ 1` bound all resulting integer entries and right-hand sides" (`H = max 1 (max over all rows/entries)`) |
| `cN`, `cQ = (N H)^N`, `gThr = 1/(4Q)` | "`N=n+mn+m+2` ... `Q=(NH)^N`", Lemma (c) "put `g=1/(4Q)`" |
| `bMax`, `dP j = d_j+g/16`, `dBar = max_j d'_j`, `cσ = cκ = g/8`, `invSum = Σ 1/d'_j`, `cη`, `cδ`, `a0 = r/n` | *Constants*, verbatim formulas for `σ, κ, η, δ`, `a⁰=(r/n)𝟏` |
| `yA`, `fA`, `wA` | *The map*: "`y_i(x)` projection of `U_i(x)/σ`; `f_ij=p_iy_ij`, `w_j=Σ_ip_iy_ij`" |
| `lam s` | "`λ(s)=C_{0,d̄}(d̄((1−δ)κ−s)/((1−2δ)κ))`" |
| `preT`, `Tm` | "`T_j(x,s)=C_{0,1}(x_j+η(w_j(x)−λ(s)/d'_j))`" (`preT` = before the clip) |
| `preR`, `Rm` | "`R(x,s)=C_{0,κ}(s+Σx_j−ΣT_j)`" (`preR` = before the clip) |
| `xPart`, `qPart`, `sOf = C_{0,κ}(q)` | "Add one coordinate `q∈[0,1]` and put `s=C_{0,κ}(q)`" |
| `F G : (T ⊕ Unit → ℚ) → (T ⊕ Unit → ℚ)` | "`F(x,q)=(1−δ)(T(x,s),R(x,s))+δ(a⁰,κ/2)`"; `inl j` = `x_j`, `inr ()` = `q` |
| `l1`, `InCube` | `‖·‖₁` and `[0,1]^{n+1}` |
| `zOf u = T(x,s)`, `labelOf`, `patternOf`, `vOf` | Lemma ueopl-decoding: "`z=T(x,q)`; allowed edges `f_ij(x)>0`; label zero/one/free according to `z_j=0`, `z_j=1`, `0<z_j<1`; `v_i=max_jU_ij(z)`" |

## 2. Statements (`Statements.lean`) and proofs (`Proofs.lean`)

| Prop | [C] | proof |
|---|---|---|
| `ProjectionLemma` | Lemma ueopl-proj: simplex, Euclidean, (a) | `projectionLemma_proof` |
| `ConstantsLemma` | *Constants*, (eq:ueopl-const) | `constantsLemma_proof` |
| `MapsCube` | *The map*: "F maps `[0,1]^{n+1}` into itself" | `mapsCube_proof` (`F_mem_cube`: all of `ℚ^{n+1}`) |
| `L1Contraction` | Lemma ueopl-contraction | `l1Contraction_proof` (`F_contraction`: all of `ℚ^{n+1}`) |
| `FixedPointUnique` | "In particular F has a unique fixed point" (uniqueness part) | `fixedPointUnique_proof` |
| `BudgetAtFixedPoint` | Lemma ueopl-budget + sharper bound | `budgetAtFixedPoint_proof` |
| `PatternSoundness` | Lemma ueopl-pattern (a) | `patternSoundness_proof` |
| `RepairThreshold` | Lemma ueopl-pattern (b)+(c) | `repairThreshold_proof` |
| `DecodingResiduals` | Lemma ueopl-decoding (residual bounds, `≤ 3g/8`) | `decodingResiduals_proof` |
| `Decoding` | Lemma ueopl-decoding (conclusion) | `decoding_proof` |
| `Reduction` | Thm. sx-game / Thm. ueopl-main (correctness only) | `reduction_proof` |

## 3. Modelling choices an auditor should check

1. **Contraction proof route.** Not per affine piece. `(T, R̃)` with `R̃ = s+Σx−ΣT` is shown
   *monotone* in `(x,s)` (projection: `θ` monotone, so lowering `u_h` by `τ` lowers `y_h` by ≤ `τ`
   and raises the others; `η ≤ σ/(1+b_max)`; `λ` antitone) and *mass-preserving*
   (`ΣT+R̃ = s+Σx`, from `Σ_j w_j = Σ_i p_i = 1`), with `ΣT` rising by at most the input rise
   (`λ` Lipschitz `d̄/((1−2δ)κ)` and (eq:ueopl-const)). Crandall–Tartar
   (`Σ|Gu−Gu'| ≤ Σ(2G(u⊔u')−Gu−Gu') = Σ|u−u'|`) gives nonexpansiveness; clipping `R` and `q` is
   1-Lipschitz. This is the order-theoretic content of "nonnegative Jacobian, column sums one".
2. **Existence of a fixed point over `ℚ` is not proved** (only uniqueness). Over `ℚ` Banach does not
   apply; existence needs rationality of the real fixed point (piecewise-affine with rational data),
   which is what FGMS/LinearFIXP supplies. `Reduction` is therefore the correctness of the
   reduction: *every* fixed point decodes to an exact BNE.
3. **`t ≤ 1` in the relaxed LP** (the book's remark form); needed for a bounded polytope so that the
   vertex walk of `DirectLCP.exists_vertex` applies. `H` includes the outer-box rows and `t` rows.
4. **No minimisation of `t`:** Lemma (c) is proved directly: from the witness, walk to a vertex
   with no larger `t`; at a vertex `t = p/q`, `|q| ≤ N!H^N ≤ Q`, so `t > 0` would give `t ≥ 1/Q > g`.
5. **`λ` argument.** The decoded `λ` is `λ(s)` with `s = C_{0,κ}(q)`; `fix_s` proves `s = q`.
6. **Hypotheses weaker than the book:** only `WellFormed` (`p ≥ 0`, `Σp = 1`, `b,d ≥ 0`, `r ≤ n`) and
   `T ≠ ∅`. Zero priors, zero slopes, zero gains, `r = 0` and `r = n` are all covered; the book's
   `p_i > 0` and `0 < r < n` are not used. Zero gains enter only through `d'_j = d_j+g/16 > 0`.
7. **BNE notion.** The output is `DirectLCP.IsMarginalBNE` (marginal coordinates). For `r = 1` and
   0/1 defender payoffs, `DirectLCP.bneIffMarginal_proof` links it to the frozen `BSSG.IsBNE`; the
   general-`r` realization (Lemma realize) is not formalized here.
8. **Not formalized:** the LinearFIXP circuit and its gate count, polynomial bit lengths and running
   times, FGMS Thm. 34 (PL-Contraction ∈ UEOPL) and the CMV3 exclusion, the sorted-prefix form of `θ`.
