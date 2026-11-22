# Adversarial faithfulness audit: MarketLCP, MarketGame, Contraction

Date: 2026-11-22. Read-only audit (no project file edited except this report).
Book: `book/readable/chapters/ch5-upper.tex` (sec:plcp, sec:contraction, sec:ueopl),
`ch3-market.tex` (sec:mk-m2g), `ch2-prelim.tex` (def:m1). Every line of each `Defs.lean`,
`Statements.lean`, and `DEFINITIONS-*.md` was read. Proof files were only checked for axioms.

Axioms: `#print axioms` on `MarketLCP.{main,gap,negativeExample,formulation}_proof`,
`MarketGame.{omegaCompose,composeBNE,composeLift,nuSpec}_proof`, and
`Contraction.{reduction,budgetAtFixedPoint,projectionLemma}_proof` shows only
`propext, Classical.choice, Quot.sound`. No `sorry`, `admit`, `axiom` or `native_decide` appears in the three directories.

Scratch tests are in `/tmp/auditns/` (`mlcp.lean`, `con.lean`, `con2.lean`, `mg.lean`, `ref.py`, `ref2.py`).

---

## 1. MarketLCP (sec:plcp). Verdict: faithful

Checked against the book:
- `lcpM = fromBlocks 0 (matB)ᵀ (−matK) 0`. `matB` and `matK` are Bᵀ and Kᵀ (V×E), so the edge rows are
  `B` and the vertex rows are `−Kᵀ`, which matches `M = (0 B; −Kᵀ 0)`. `q = (−a, μ, c)` matches. Flow coordinates exist only
  on E (subtype). `zf` extends f by 0 off E, and `IsEquilibrium` reads f only on E, so the
  statement `IsLCPSol ↔ IsEquilibrium` is exactly the book's lemma, with `encode ∘ decode = id`.
- C = `max(D, max|D·M|, max|D·q|)` = D·max(1, max|M|, max|q|). Hand check below. d = |E|+|I|+|J|+1.
  H = fold max 0 a = max(0, max_E a). b_min = inf' over E, and 1 if E = ∅ (then H = 0, so Z̄ does not use it).
  muMax = fold max 0 μ, which equals max μ for I ≠ ∅. Z̄ and ε = 1/(2⌈Z̄⌉(dC)^d) are verbatim.
- LP(A), (∗), Gap (generic q, M; optimum attained; ρ* = 0 or ρ* ≥ (dC)^{−d}), StarSol, and UniformBound
  (WellFormed, 0 < ε ≤ 1) all match the book.
- NegativeExample covers every claim of the book's example and adds uniqueness claims.
- **Existence (honest).** `MainTheorem` quantifies over all solutions `zε` of LCP(q, M+εI), so
  its last conjunct is vacuous if no solution exists. Existence of a solution (Prop. classical (i)) is not proved, and neither is the
  remark "every (M1) market has an equilibrium". The docstring says "for any solution" and
  DEFINITIONS M6 states this explicitly. The other conjuncts (P-matrix, 0 < ε ≤ 1, uniqueness) are not vacuous.
- P0 assumes b ≥ 0 on E, which is weaker than the book's b > 0, so the Lean statement is more general (fine).

Mismatches: none of substance.

Test (2×2 market, E = {(0,0),(0,1),(1,1)}, b = (2, 1/4, 3), a = (5, −1/2, 7/3), μ = (1, 3/2), c = (2, 1/3)):
- `lcpM` matches the hand-built book matrix entry by entry.
- q = (−5, 1/2, −7/3, 1, 3/2, 2, 1/3).
- D = 12, C = 60, d = 8, H = 5, b_min = 1/4, max μ = 3/2, Z̄ = 21, and ε = 1/(42·480⁸). All agree with hand computation.
- `slack q M z` equals `slackTable z` at a random z.

## 2. MarketGame (Ch. 3 market to game). Verdict: faithful

- `toGameW Mk W` is exactly Table tab:mk-types.
  - Payoffs: source i gets a_ij/S − b_ij ξ_j at listed j, (−2,1) at unlisted j, A/S − ξ at its own g_i, (−2,1) at other g_i', and −ξ_o at o. Dedicated j gets 2 − ξ_j at its own j. Control gets 2 − ξ_h at h. Every other pair, including source at h, pays (−2,1).
  - Weights are W+μ_i, W−c_j, W. The prior is weight/total, there is one resource, and defender payoffs are 0/1.
  - A and S are the book's (max over listed pairs). D̂ and W = (2+2/ω)D̂ are verbatim (`max c` written as fold max 0).
  - Decoding is P = Sξ, v = S·u_i with u_i = typeValue (equal to the BNE payoff), and f = (W+μ_i)σ_i(j).
- `RescaleEquiv` / `RescaleEquivBack` hold for any ν > 0, which is stronger than Lemma lem:mk-rescale needs.
  The explicit ν_i = 2^{k_i} with k_i = max_{E_i} size(den b_ij) gives ν_i b_ij ≥ 1 and polynomial length.
  This is a valid choice: k_i ≥ 1 when E_i ≠ ∅, so ν_i is a positive power of two, as the book's text in ch3 says.
- Empty E_i is kept with ν = 1. This is consistent: def:m1 only deletes such buyers "without changing the equilibria", and all Lean statements hold for arbitrary E.
- `OmegaCompose` (rescale, build Γ_ω, take any general mixed BNE, decode, undo the rescaling) is Thm. mk-main (a). `OmegaDecode` and `DecodeW` (W > Σμ, W > c_j, b ≥ 1) match the book.

Mismatches:
- **M-G1, `ComposeLift` docstring overclaims (cosmetic / weaker than its docstring).** The docstring says decoding returns "the same prices P and utilities v". The statement has only `(decode Mk δ σ).1 = P`.
  Fix: add `∧ (decode Mk δ σ).2.1 = v`, or change the docstring.
- Not formalized, and disclosed in DEFINITIONS-marketgame.md:
  - legality of Γ_ω and the prior bounds 1−ω ≤ |Θ|Pr ≤ 1+ω;
  - the lift and the inverse maps for Γ_ω (the lift is proved for `toGame` only);
  - Prop. mk-below-one.
  No BNE existence is proved for Γ_ω, so the `OmegaDecode` and `OmegaCompose` statements hold vacuously for any game that has no BNE. The book gets existence from Nash's theorem.
- `NuSpec` bounds k_i by the largest slope-denominator length instead of the book's "bit length of min b" (cosmetic; still polynomial).

Test: the book's Prop. mk-below-one market (μ = 2, c = 1, a = 1, b = 1/100, ω = 1).
- Lean gives D̂ = 3, W = 12, A = 2, S = 5, weights (14, 11, 12), and priors (14/37, 11/37, 12/37).
- The payoff table matches the book. At ξ = (80/101, 21/101, 0, 0) the source type is tied at 97/505.
- Loads ×37 = (25/2, 25/2, 0, 12), and decP = 400/101, all as in the book.
- The rescaling gives ν = 2⁷ = 128 and b' = 32/25 ≥ 1.

## 3. Contraction (sec:contraction, sec:ueopl). Verdict: faithful

- **F matches the book term by term:**
  - clipping C_{l,h};
  - y_i = proj(U_i(x)/σ), f = p·y, w = Σ p·y;
  - λ(s) = C_{0,d̄}(d̄((1−δ)κ−s)/((1−2δ)κ));
  - T_j = C_{0,1}(x_j + η(w_j − λ/d'_j));
  - R = C_{0,κ}(s + Σx − ΣT);
  - s = C_{0,κ}(q);
  - F = (1−δ)(T, R) + δ(a⁰, κ/2), with a⁰ = r/n.
- **Constants** g = 1/(4Q), Q = (NH)^N, N = n+mn+m+2, d' = d + g/16, d̄, σ = κ = g/8, η, δ, b_max (fold max 0, with b ≥ 0) are all verbatim.
- **θ.** The max over nonempty subsets of (Σ_S u − 1)/|S| equals the sorted-prefix maximum: for each k the best k-subset is the top-k prefix. It was also confirmed numerically against a Python sorted-prefix implementation.
- **H.** H is the tightest bound ≥ 1 over all row families, including the outer boxes and the rows 0 ≤ t ≤ 1, after clearing denominators row by row. The book only asks for some bound H ≥ 1 on these rows, so this choice is legitimate. Rows the book also relaxes but Lean omits as redundant (x ≥ −t, f ≥ −t) have entries ±1 and rhs 0, so H is unchanged.
- **Relaxed LP with t ≤ 1.** This is the form of the book's remark. It is harmless for (c), because any witness with t₀ < g ≤ 1 already satisfies it.
- **Pattern rows.** All rows match the book's pattern LP: budget, row sums, f ≤ t off allowed edges, U ≤ v+t, v ≤ U+t on allowed edges, the zero/one/free x and cutoff rows, and exact boxes x, f ∈ [0,1], λ ≤ 1+max d, |v| ≤ 2+max(|a|+b).
- **Statements.** MapsCube, L1Contraction, FixedPointUnique, BudgetAtFixedPoint (including the sharper κ/2 bound), DecodingResiduals (≤ 3g/8 < g), and Decoding all match the book. Lean's ProjectionLemma (a) is strict, which is stronger than the book.
- **Existence (honest).** `Reduction` states correctness only: every fixed point decodes to an LP-feasible pattern, and hence to a marginal BNE. Existence of a rational fixed point is not proved, so the decoding conjuncts are vacuous if none exists. This is stated in the docstring ("as soon as a fixed point does") and in DEFINITIONS §3.2.

Mismatches:
- **C1, `RepairThreshold` (weaker than its name / cosmetic).** The docstring says Lemma (b)+(c), but only (c) is stated. The dichotomy "optimal t is 0 or ≥ 1/Q" is not a standalone Prop.
  Fix: rename it or reword the docstring as "(c)", or add the (b) statement.
- **C2, BNE notion (weaker than its name for r > 1; disclosed).** The output is `IsMarginalBNE`. It is bridged to `BSSG.IsBNE` only for r = 1 with 0/1 payoffs; Lemma realize is not formalized. Zero-prior types get no best-response check under `IsMarginalBNE`, while the book gives them one explicitly. This is trivial to add.

Tests:
1. One type, two targets (a = (1, 1/2), b = 1, d = 1, r = 1):
   - H = 4 by hand, matching Lean, so Q = 28⁷ and g = 1/53971714048.
   - η and δ agree with Python exactly.
   - F(1/2, 1/2; 0) agrees with the hand formula (1/2, (1−δ)(1/2−η)+δ/2, (1−δ)η+δκ/2) exactly.
2. Two types, three targets, mixed priors, b = 0 present, d = 0 present:
   - H = 10, computed independently in Python from the row families, matches Lean.
   - Lean's F at an interior point equals the Python reference (sorted-prefix θ) on all 4 coordinates.
3. `proj` of (0.3, 0.1, 0.25) is (5/12, 13/60, 11/30), and proj of (3, 1, 2) is (1, 0, 0). Both are correct.
