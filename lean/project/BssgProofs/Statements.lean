import BssgProofs.Definitions

/-!
# Target statements (proofs to be supplied; `sorry` allowed only in this file)

Numbering follows `simplify/simple/simple-proof.md`.  Every statement uses only the frozen
definitions of `BssgProofs.Definitions`.  Later agents should prove these in place (or in new
files that import `Definitions` and restate them verbatim) without changing the statements.

Dependency sketch:
* `dohrau_lemma1`, `toSwitchGraph_terminates_iff`  →  `lemma1`
* `lemma2_*`  →  `lemma3`  →  `lemma6` (with `lemma5`)
* `lemma4`, `lemma6`, `lemma1`  →  `theorem7`
* `lemma8`, `theorem7`, `preprocess_*`, `fact0`  →  `main`
-/

namespace Bssg

open Finset

/-! ## ARRIVAL, Dohrau et al. -/

/-- Dohrau et al., Lemma 1: if a switching flow exists, `Run(G, o, d)` terminates, and the run
profile is bounded componentwise by the switching flow (at every time `k`). -/
theorem dohrau_lemma1 {V : Type*} [Fintype V] [DecidableEq V] (G : SwitchGraph V) (o d : V)
    (hod : o ≠ d) (x : V × V → ℕ) (hx : G.IsSwitchingFlow o d x) :
    G.RunTerminates o d ∧ ∀ k, ∀ e ∈ G.E, G.runProfile o d k e ≤ x e := by
  sorry

/-- Bridge: the instance's run reaches `t` iff `Run(G′, o, t)` terminates, where `G′` makes both
terminals self-loops (simple-proof Lemma 1 (iii), last sentence). -/
theorem toSwitchGraph_terminates_iff {n : ℕ} (I : ArrivalInstance n) (t : Terminal) :
    I.Reaches t ↔ I.toSwitchGraph.RunTerminates (.inl I.origin) (.inr t) := by
  sorry

/-- The run reaches at most one terminal. -/
theorem reaches_unique {n : ℕ} (I : ArrivalInstance n) {t t' : Terminal}
    (ht : I.Reaches t) (ht' : I.Reaches t') : t = t' := by
  sorry

/-- Fuel bound (Dohrau Thm 1): a terminal, if reached, is reached within `n · 2^n` steps. -/
theorem reaches_iff_outcomeWithin {n : ℕ} (I : ArrivalInstance n) (t : Terminal) :
    I.Reaches t ↔ I.outcomeWithin (n * 2 ^ n) = some t := by
  sorry

/-- Preprocessing preserves the answer (and, more precisely, which terminal is reached first is
unchanged when the original run reaches one). -/
theorem preprocess_reaches_yes {n : ℕ} (I : ArrivalInstance n) :
    I.preprocess.Reaches .yes ↔ I.Reaches .yes := by
  sorry

/-- After preprocessing every switch has a path of length `≤ n` to a terminal. -/
theorem preprocess_preprocessed {n : ℕ} (I : ArrivalInstance n) :
    I.preprocess.Preprocessed := by
  sorry

/-! ## The switch map (helper facts of §1.3 and Lemma 1 (i)) -/

theorem h0_add_h1 (x : ℚ) : h0 x + h1 x = x := by
  unfold h0 h1
  rcases le_total (x - 2 * ((⌊x / 2⌋ : ℤ) : ℚ)) 1 with h | h
  · rw [min_eq_left h, max_eq_right (by linarith)]; ring
  · rw [min_eq_right h, max_eq_left (by linarith)]; ring

/-- Lemma 1 (i): floors commute with the switch map. -/
theorem h_floor (i : Bool) (x : ℚ) (hx : 0 ≤ x) :
    h i ((⌊x⌋ : ℤ) : ℚ) = ((⌊h i x⌋ : ℤ) : ℚ) := by
  sorry

/-- Summing (FP): `y_yes + y_no = 1`. -/
theorem fixedPoint_termInflow_sum {n : ℕ} (I : ArrivalInstance n) (x : Fin n → ℚ)
    (hx : I.IsFixedPoint x) : I.termInflow x .yes + I.termInflow x .no = 1 := by
  sorry

/-! ## Lemma 1 (decoder) -/

/-- **Lemma 1.** Every fixed point loads the terminal the run reaches: the run reaches some
terminal `t*`, `y_{t*} = 1`, and the other terminal has inflow `0`. -/
theorem lemma1 {n : ℕ} (I : ArrivalInstance n) (x : Fin n → ℚ) (hx : I.IsFixedPoint x) :
    ∃ t, I.Reaches t ∧ I.termInflow x t = 1 ∧ I.termInflow x t.other = 0 := by
  sorry

/-! ## Lemma 2 (Disser–Skutella counting network) -/

theorem lemma2_length (k : ℕ) : (countD k).length = 2 ^ k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [countD, ih, pow_succ, mul_two]

theorem lemma2_first (k : ℕ) : (countD k).getD 0 0 = 0 := by
  sorry

theorem lemma2_last (k : ℕ) (hk : 1 ≤ k) : (countD k).getLast? = some (2 * 3 ^ k) := by
  sorry

/-- For `k ≥ 1`, `D_k` increases strictly with all gaps `≥ 6`. -/
theorem lemma2_gaps (k : ℕ) (hk : 1 ≤ k) (i : ℕ) (hi : i + 1 < (countD k).length) :
    (countD k).getD i 0 + 6 ≤ (countD k).getD (i + 1) 0 := by
  sorry

/-- `F_k` is the piecewise-linear function with increments `D_k`: min-cost flows of every value
`y ∈ [0, 2^k]` exist and all have cost `pwl (countD k) y`. -/
theorem lemma2_minCost (k : ℕ) (y : ℚ) (hy0 : 0 ≤ y) (hy : y ≤ 2 ^ k) :
    (∃ φ, (countingNetwork k).IsMinCostFlow (gSource k) (gSink k) y φ) ∧
    ∀ φ, (countingNetwork k).IsMinCostFlow (gSource k) (gSink k) y φ →
      (countingNetwork k).totalCost φ = pwl (countD k) y := by
  sorry

/-- The maximum flow of `G_k` is `2^k`. -/
theorem lemma2_maxFlow (k : ℕ) (y : ℚ) (hy : 2 ^ k < y) :
    ¬ ∃ φ, (countingNetwork k).IsFlow (gSource k) (gSink k) y φ := by
  sorry

/-! ## Lemma 3 (alternation) -/

/-- **Lemma 3.** For `0 < θ < 6` and `x ∈ [0, K]`, every `s → {a,b}` flow of value `x` in `N_m`
minimising `Σ κ_e φ_e + θ · inflow(b)` has `inflow(a) = h₀(x)` and `inflow(b) = h₁(x)`. -/
theorem lemma3 (m : ℕ) (hm : 1 ≤ m) (θ : ℚ) (hθ0 : 0 < θ) (hθ6 : θ < 6) (x : ℚ) (hx0 : 0 ≤ x)
    (hxK : x ≤ bigK m) (φ : SArc m → ℚ) (hφ : IsSplitFlow m x φ)
    (hmin : ∀ ψ, IsSplitFlow m x ψ → splitObjective m θ φ ≤ splitObjective m θ ψ) :
    (splitter m).inflow φ (sinkA m) = h0 x ∧ (splitter m).inflow φ (sinkB m) = h1 x := by
  sorry

/-! ## Lemmas 4, 5 (LP facts) -/

/-- **Lemma 4 (complementary slackness).** -/
theorem lemma4 {I J : Type*} [DecidableEq I] [DecidableEq J]
    (L : AllocLP I J) (f : I × J → ℚ) (hf : L.Feasible f) (v : I → ℚ) (π : J → ℚ)
    (hv : ∀ i, 0 ≤ v i) (hπ : ∀ j, 0 ≤ π j) (hπinf : ∀ j, L.cap j = none → π j = 0)
    (hdual : ∀ e ∈ L.E, L.coef e ≤ v e.1 + π e.2)
    (htight : ∀ e ∈ L.E, 0 < f e → L.coef e = v e.1 + π e.2)
    (hrow : ∀ i, 0 < v i → L.rowSum f i = L.mass i)
    (hcol : ∀ j c, L.cap j = some c → 0 < π j → L.colSum f j = c) :
    L.IsOptimal f := by
  sorry

/-- **Lemma 5 (big M).** If `a_ij = M(1 + [j finite]) − κ_ij` with `κ ≥ 0` and `M > Σ_E κ`, every
optimum maximises the trade `T`. -/
theorem lemma5 {I J : Type*} [DecidableEq I] [DecidableEq J]
    (L : AllocLP I J) (M : ℚ) (κ : I × J → ℚ) (hκ0 : ∀ e ∈ L.E, 0 ≤ κ e)
    (hcoef : ∀ e ∈ L.E, L.coef e = M * (1 + if (L.cap e.2).isSome then 1 else 0) - κ e)
    (hM : (∑ e ∈ L.E, κ e) < M) (f : I × J → ℚ) (hf : L.IsOptimal f) :
    ∀ g, L.Feasible g → L.trade g ≤ L.trade f := by
  sorry

/-! ## Lemma 6 (one gadget) -/

/-- **Lemma 6.** If `α_a = M − P′`, `α_b = M − ε − P″` with `P′, P″ ∈ [0,1]`, every optimal
solution of `G(c, x, α_a, α_b)` has port purchases `(h₀(min(x,K)), h₁(min(x,K)))`. -/
theorem lemma6 (m : ℕ) (hm : 1 ≤ m) (c x P' P'' : ℚ) (hc : 0 < c) (hx0 : 0 ≤ x) (hxc : x < c)
    (hP'0 : 0 ≤ P') (hP'1 : P' ≤ 1) (hP''0 : 0 ≤ P'') (hP''1 : P'' ≤ 1) (f : _ → ℚ)
    (hf : (gadgetLP m c x (bigM m - P') (bigM m - epsC - P'')).IsOptimal f) :
    f (sinkA m, .inr .πa) = h0 (min x (bigK m)) ∧ f (sinkB m, .inr .πb) = h1 (min x (bigK m)) := by
  sorry

/-! ## Theorem 7 (composition) -/

/-- **Theorem 7.** For a preprocessed instance, in every equilibrium of the §5 market, `x` is a
fixed point, the exit loads are the terminal inflows, and they are `1` at the terminal the run
reaches and `0` otherwise. -/
theorem theorem7 {n : ℕ} (I : ArrivalInstance n) (hI : I.Preprocessed) (P : RGood n → ℚ)
    (v : RBuyer n → ℚ) (f : RBuyer n × RGood n → ℚ) (heq : I.redMarket.IsEquilibrium P v f) :
    I.IsFixedPoint (I.redX f) ∧
    ∀ t, I.exitLoad f t = I.termInflow (I.redX f) t ∧
      (I.Reaches t → I.exitLoad f t = 1) ∧ (¬ I.Reaches t → I.exitLoad f t = 0) := by
  sorry

/-! ## Fact 0 (BNE ⇔ coverage form for one resource, defender payoffs 0/1) -/

/-- **Fact 0.** For `r = 1`, `u₁⁰ ≡ 0`, `u₁¹ ≡ 1`, a mixed profile is a BNE iff its coverage
vector satisfies the coverage-form conditions. -/
theorem fact0 {T Θ : Type*} [Fintype T] [DecidableEq T] [Fintype Θ] (G : BSSG T Θ)
    (hr : G.r = 1) (hd0 : ∀ t, G.ud0 t = 0) (hd1 : ∀ t, G.ud1 t = 1)
    (δ : Finset T → ℚ) (σ : Θ → T → ℚ) :
    G.IsBNE δ σ ↔ G.IsDefMixed δ ∧ G.IsCoverageBNE (BSSG.coverage δ) σ := by
  sorry

/-- Converse realisation: a coverage-form BNE is realised by singleton defenses. -/
theorem fact0_realize {T Θ : Type*} [Fintype T] [DecidableEq T] [Fintype Θ] (G : BSSG T Θ)
    (hr : G.r = 1) (hd0 : ∀ t, G.ud0 t = 0) (hd1 : ∀ t, G.ud1 t = 1)
    (ξ : T → ℚ) (σ : Θ → T → ℚ) (h : G.IsCoverageBNE ξ σ) :
    G.IsBNE (BSSG.singletonDefense ξ) σ ∧ BSSG.coverage (BSSG.singletonDefense ξ) = ξ := by
  sorry

/-! ## Lemma 8 (market → game) -/

/-- **Lemma 8.** For a well-formed market with all slopes `≥ 1`, every coverage-form BNE of Γ
decodes (`P = Sξ`, `v = S·value`, `f = (W + μ)σ`) to a market equilibrium. -/
theorem lemma8 {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (Mk : Market I J) (hwf : Mk.WellFormed) (hb : ∀ e ∈ Mk.E, 1 ≤ Mk.b e)
    (ξ : MTarget I J → ℚ) (σ : MType I J → MTarget I J → ℚ)
    (h : Mk.toGame.IsCoverageBNE ξ σ) :
    Mk.IsEquilibrium (Mk.decP ξ) (Mk.decV ξ) (Mk.decF σ) := by
  sorry

/-! ## The theorem -/

/-- `Red I` is a legal Bayesian simple security game with one resource, defender payoffs 0/1 and
positive priors. -/
theorem red_wellFormed {n : ℕ} (I : ArrivalInstance n) :
    (Red I).WellFormed ∧ (Red I).r = 1 ∧ (∀ t, (Red I).ud0 t = 0 ∧ (Red I).ud1 t = 1) ∧
      ∀ θ, 0 < (Red I).prior θ := by
  sorry

/-- The §5 market of a (preprocessed) instance is well formed with slopes `≥ 1`. -/
theorem redMarket_wellFormed {n : ℕ} (I : ArrivalInstance n) :
    I.redMarket.WellFormed ∧ ∀ e ∈ I.redMarket.E, 1 ≤ I.redMarket.b e := by
  sorry

/-- Sizes: `12n² + 6n + 3` targets and `12n² + 6n + 2` attacker types. -/
theorem red_sizes (n : ℕ) :
    Fintype.card (RTarget n) = 12 * n ^ 2 + 6 * n + 3 ∧
      Fintype.card (RType n) = 12 * n ^ 2 + 6 * n + 2 := by
  sorry

/-- Non-vacuity: `Red I` has a (rational) BNE.  Not part of simple-proof (it follows from
Nash's theorem / rationality of 2-player equilibria); stated so the main theorem is not vacuous. -/
theorem red_bne_exists {n : ℕ} (I : ArrivalInstance n) :
    ∃ δ σ, (Red I).IsBNE δ σ := by
  sorry

/-- **Main theorem, coverage form.** -/
theorem main_coverage {n : ℕ} (I : ArrivalInstance n) (ξ : RTarget n → ℚ)
    (σ : RType n → RTarget n → ℚ) (h : (Red I).IsCoverageBNE ξ σ) :
    Dec I σ = true ↔ I.Reaches .yes := by
  sorry

/-- **Main theorem.** For every ARRIVAL instance and every Bayes–Nash equilibrium `(δ, σ)` of
`Red I` (general mixed strategies), `Dec I σ` is the answer of the instance. -/
theorem main {n : ℕ} (I : ArrivalInstance n) (δ : Finset (RTarget n) → ℚ)
    (σ : RType n → RTarget n → ℚ) (h : (Red I).IsBNE δ σ) :
    Dec I σ = true ↔ I.Reaches .yes := by
  sorry

end Bssg
