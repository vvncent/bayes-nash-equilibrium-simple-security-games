# DEFINITIONS-marketlcp.md: audit map for `BssgProofs/MarketLCP/`

Source: **[PL]** `book/readable/chapters/ch5-upper.tex`, Section "The market reduces to P-matrix LCP"
(`sec:plcp`); article version `book/articles/03-plcp.tex`; referee report `review2/plcp.md`.
Files: `Defs.lean` (definitions), `Statements.lean` (each result as a `Prop`, no `sorry`),
`Proofs.lean` (proofs, no `sorry`/`admit`/`axiom`). Everything is over `ℚ`, namespace
`Bssg.MarketLCP`.

Frozen definitions reused from `Definitions.lean`: `Market` (`mass` = μ, `cap` = c, `E`, `a`, `b`),
`Market.WellFormed` (μ > 0, c > 0, b > 0 on E), `Market.rowSum`, `Market.colSum`,
`Market.IsEquilibrium` (conditions (a)-(d)). Reused from `DirectLCP/Defs.lean`: `principal`,
`IsPMatrix`, `IsP0Matrix`, `slack q M z = q + Mz`, `IsLCPSol` (z ≥ 0, w ≥ 0, z_k w_k = 0), `incMat`,
`FIdx`, `RIdx`. Reused proofs: `DirectLCP.blockdet`, `blockdet_card_ne`, `p0core`, `isP_add_smul`,
`det_principal_add_smul_ge`, `lcp_unique_add_smul`, `slack_add_smul` (Proofs.lean) and
`abs_det_le`, `tightSpan`, `exists_perp`, `vertex_value`, `int_of_den_dvd` (Gap.lean).

## 1. Definitions (`Defs.lean`)

| Lean | Formalizes | [PL] sentence |
|---|---|---|
| `Edge Mk` = `{e // e ∈ Mk.E}` | the edge index set | "Index coordinates by edges, buyers and goods" |
| `Idx Mk` = `Edge Mk ⊕ (I ⊕ J)`; `Idx.f e`, `Idx.u i`, `Idx.P j` | `z = (f, u, P) ∈ ℝ^E × ℝ^I × ℝ^J`, `N = |E|+|I|+|J|` | "N=|E|+|I|+|J|, and z=(f,u,P)" |
| `matB Mk : Matrix (I ⊕ J) (Edge Mk) ℚ` | `Bᵀ` | "the row of edge (i,j) has entries 1 (column i) and b_ij (column j) in B" (transposed: vertex rows, edge columns) |
| `matK Mk` | `Kᵀ` | "entries 1 in both columns i and j in K, and zeros elsewhere" (transposed) |
| `lcpM Mk = fromBlocks 0 (matB)ᵀ (−matK) 0` | `M = (0 B; −Kᵀ 0)` | display "M = (0 B; −K^T 0)" (rows/cols ordered edges, then vertices `V = I ∪ J`) |
| `lcpq Mk = (−a, μ, c)` | `q` | "So q=(−a,μ,c)" |
| `slackTable Mk z` | `w = q + Mz` | display "w_ij=u_i+b_ij P_j−a_ij, w_i=μ_i−Σ_j f_ij, w_j=c_j−Σ_i f_ij" (sums over options, i.e. frozen `rowSum`/`colSum`); `slackTable_proof` shows `slack (lcpq) (lcpM) z = slackTable z` |
| `zf`, `zu`, `zP` | decoding `z ↦ (P, v, f)` with `v = u` | Lemma plcp:lem:formulation "(f,u,P) ∈ SOL(q,M) iff (P,v,f) with v=u is an equilibrium"; `zf` extends f by 0 off E |
| `encode Mk P v f` | `(P, v, f) ↦ z = (f, v, P)` | same lemma, converse direction |
| `support z` | `A = {k : z^ε_k > 0}` | Thm. plcp:thm:main |
| `IsLPFeasible q M A z ρ` | feasible set of `LP(A)` | display "LP(A): min ρ s.t. z ≥ 0, ρ ≥ 0, z_Ā = 0, q+Mz ≥ −ρ1, (q+Mz)_A ≤ ρ1" (generic in `q, M`) |
| `IsStarFeasible q M A z` | the system `(∗)` | display "z ≥ 0, z_Ā = 0, q+Mz ≥ 0, (q+Mz)_A = 0" |
| `lcmDen q M` | `D` | "D the least common multiple of all denominators of entries of M and q" |
| `cC q M : ℕ` | `C` | "C = D·max(1, max_{k,l}|M_kl|, max_k|q_k|), an integer". Lean form `max(D, max |D M_kl|, max |D q_k|)` via numerators; `cC_eq` proves it equals `D * max 1 (max (fold max 0 |M|) (fold max 0 |q|))` |
| `dimd ι = card ι + 1` | `d = N + 1` | "d = N+1" |
| `cH Mk = E.fold max 0 a` | `H = max(0, max_E a_ij)` | §"The reduction" first display |
| `bmin Mk` | `b_min = min_E b_ij` | same display; `1` when `E = ∅` (then `H = 0`, value unused) |
| `muMax Mk = univ.fold max 0 μ` | `max_i μ_i` | same display (equal to the max for `I ≠ ∅` as μ > 0; `0` if `I = ∅`) |
| `Zbar Mk = 1 + max(muMax + H, H / bmin)` | `Z̄` | "Z̄ = 1 + max{max_i μ_i + H, H/b_min}" |
| `mD`, `mC`, `md` | `D, C, d` of the market LCP | |
| `eps Mk = 1/(2⌈Z̄⌉(dC)^d)` | `ε` | Thm. plcp:thm:main display |
| `lcpMeps Mk ε = M + ε•1` | `M + εI` | |
| `exMarket`, `exEdge`, `exZ f u P` | Example plcp:ex:negative market and its LCP vectors | "one buyer and one good with μ=1, c=2, a=b=1" |

## 2. Statements (`Statements.lean`) and proofs (`Proofs.lean`)

| Prop | [PL] | Proof | Status |
|---|---|---|---|
| `SlackTable` | display defining `w` | `slackTable_proof` | proved |
| `FormulationSolEq` | Lemma plcp:lem:formulation, SOL ⇒ equilibrium (no hypotheses on the market) | `formulationSolEq_proof` | proved |
| `FormulationEqSol` | same, equilibrium ⇒ SOL (and decoding the encoding returns P, v, f on E) | `formulationEqSol_proof` | proved |
| `Formulation` | same, as an iff plus `encode ∘ decode = id` | `formulation_proof` | proved |
| `P0` | Lemma plcp:lem:p0 (any E, slopes `b ≥ 0` on E; book: `b > 0`) | `p0_proof` | proved |
| `PMatrix` | Lemma plcp:lem:pmatrix for the market matrix, `det(M+εI)_SS ≥ ε^|S|`, uniqueness | `pMatrix_proof` | proved |
| `UniformBound` | Lemma plcp:lem:bound (WellFormed, 0 < ε ≤ 1) | `uniformBound_proof` | proved |
| `Gap ι` | Lemma plcp:lem:gap, for any `q, M` over `ℚ`: optimum attained, `ρ* = 0 ∨ ρ* ≥ (dC)^{−d}` | `gap_proof` | proved |
| `StarSol ι` | Thm. plcp:thm:main "Soundness": feasible `(∗)` ⇒ SOL(q,M) | `starSol_proof` | proved |
| `MainTheorem` | Thm. plcp:thm:main (mathematical content) | `main_proof` | proved |
| `NegativeExample` | Example plcp:ex:negative (all claims, for every `0 < ε < 1`) | `negativeExample_proof` | proved |

## 3. Modelling choices an auditor should check

1. **M1. Edge-indexed coordinates.** Flow coordinates exist only for `e ∈ E` (subtype). The frozen
   market's `f : I × J → ℚ` is total; `zf` extends by `0`, and `FormulationEqSol` only recovers `f` on
   `E` (values off `E` never enter `IsEquilibrium`).
2. **M2. Transposes.** `matB`, `matK` are `Bᵀ`, `Kᵀ` (vertex × edge) so that `M` has DirectLCP's shape
   `fromBlocks 0 Bᵀ (−D) 0`; then `matB`/`matK` are literally the edge columns of DirectLCP's
   `incMat β` / `incMat 1` (`matB_eq`, `matK_eq`) with `β = b` on `E`, `0` off `E`, and P₀ is
   DirectLCP's `p0core` + `blockdet`. The book's forest/cycle/matching argument is therefore not
   re-done; DirectLCP's (different, Laplace + continuity) proof of the incidence-matrix core is used.
3. **M3. P₀ hypothesis** is `b ≥ 0` on `E` (weaker than the book's `b > 0`); everything else assumes
   the frozen `WellFormed` (μ > 0, c > 0, b > 0). The bound and main theorem use μ ≥ 0, c > 0 only
   through `WellFormed`.
4. **M4. LP(A) without a box.** The gap lemma is proved for the book's LP (no upper bound on `z`), via
   a variant `exists_vertex_pointed` of DirectLCP's vertex walk that needs only a pointed polyhedron
   (rows `z ≥ 0`, `ρ ≥ 0`) and an objective bounded below on recession directions. `z_Ā = 0` is
   encoded as the rows `z_k ≥ 0` and `−z_k ≥ 0`. Rows `±(q+Mz)` and `ρ` are scaled by `D`; the simple
   rows by `1`. Vertex denominators satisfy `|Δ| ≤ d! C^d ≤ (dC)^d`.
5. **M5. `C`** is defined as a natural number through numerators of `D·x`; `cC_eq` proves equality
   with the book's `D·max(1, max|M|, max|q|)` (maxima as `fold max 0`, harmless because of the
   outer `max 1`).
6. **M6. Existence of `z^ε` is not formalized.** The book's "Let z^ε be the unique solution"
   uses Prop. classical (i) (every P-matrix LCP has a solution). `MainTheorem` proves uniqueness and
   quantifies over all solutions `zε`, so it is vacuous if none existed. Consequently the remark
   "every (M1) market has an equilibrium" is not formalized either.
7. **M7. Complexity not formalized.** "log₂(1/ε) = O(L²)", "O(L³) bits", polynomial time and the
   ellipsoid solution of `(∗)` are not stated; only the exact value of `ε` is.
8. **M8. `muMax`, `cH`** use `fold max 0`; `bmin` is `1` for `E = ∅`. With `I = ∅` the book's
   `max_i μ_i` is undefined and Lean uses `0`.
