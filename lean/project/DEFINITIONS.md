# DEFINITIONS.md: audit map for `BssgProofs/Definitions.lean` and `BssgProofs/Statements.lean`

Sources:
- **SP**: `simplify/simple/simple-proof.md`
- **Ch2**: `book/readable/chapters/ch2-prelim.tex`
- **DGKMW**: Dohrau, Gärtner, Kohler, Matoušek, Welzl, arXiv:1605.03546v4 (§1, Def. 1, Def. 2, Lemma 1)
- **Con**: Conitzer, *Open problem: Computing Bayes-Nash equilibrium in simple security games*

`Definitions.lean` must stay sorry-free and frozen. Sorries are allowed only in `Statements.lean`.
All numbers are in `ℚ`.

## 1. Definitions

| Lean (namespace `Bssg`) | Formalizes | Source sentence |
|---|---|---|
| `SwitchGraph V` (`s0 s1 : V → V`) | switch graph `G=(V,E,s0,s1)` | DGKMW §1: "a switch graph is a 4-tuple G = (V,E,s0,s1), where s0,s1 : V → V, E = {(v,s0(v))} ∪ {(v,s1(v))}, with loops allowed" |
| `SwitchGraph.E` | `E` as a **set** (`Finset (V×V)`, a union of images) | same; "We may have s0(v)=s1(v) in which case v has just one outgoing edge" |
| `outE`, `inE` | `E⁺(v)`, `E⁻(v)` | DGKMW §1 |
| `IsSwitchingFlow G o d x` | Def. 2: (1) out − in = [v=o] − [v=d]; (2) `x(v,s1 v) ≤ x(v,s0 v) ≤ x(v,s1 v)+1` | DGKMW Def. 2 |
| `runStep`, `runState`, `RunTerminates` | `procedure Run(G,o,d)` and "Run terminates" | DGKMW §1 pseudocode, Def. 1 |
| `traversed`, `runProfile o d k e` | run profile (traversals of `e` in the first `k` iterations) | DGKMW Obs. 1 |
| `Terminal` (`yes`,`no`), `Node n = Fin n ⊕ Terminal` | terminals; `V ∪ {yes,no}` | SP §1.3; Ch2 Def. ARRIVAL |
| `ArrivalInstance n` (`s0 s1 : Fin n → Node n`, `origin`) | ARRIVAL instance | SP §1.3: "Switch vertices V (|V| = n), terminals yes, no, an origin o ∈ V, and successors s₀(v), s₁(v) ∈ V ∪ {yes, no}" |
| `succ v i` (`false`=label 0, `true`=label 1) | labelled edge `(v,i)` from `v` to `s_i(v)` | SP §1.3 "A labelled edge is a pair (u,i)" |
| `step`, `state k`, `Reaches t`, `Answer` | the token run, its outcome | SP §1.3 "A token starts at o, every switch points to s₀; the token at v moves to the current successor of v and v's switch toggles. Answer: yes iff the token reaches yes." |
| `outcomeWithin fuel` | fuel-bounded, computable version of the outcome | DGKMW Thm 1 (≤ n·2ⁿ states) |
| `toSwitchGraph` | `G′` on `V ∪ {t*,t′}` with self-loops at both terminals | SP Lemma 1 (iii) |
| `liveWithin k v`, `Preprocessed`, `redirect`, `preprocess` | preprocessing | SP §1.3 *Preprocessing* (see choice C3) |
| `indeg w` | number of labelled edges into `w` | SP §5 "indeg(w)" |
| `h0`, `h1`, `h` | `h₀(x)=z+min(ρ,1)`, `h₁(x)=z+max(ρ−1,0)`, `x=2z+ρ`, `z=⌊x/2⌋` | SP §1.3 *Switch map* |
| `inflow x w`, `IsFixedPoint`, `termInflow` | (FP) and terminal inflows `y_t` | SP §1.3 (FP) |
| `Network N A`, `outflow`, `inflow`, `netOut`, `Feasible`, `totalCost`, `IsFlow`, `IsMinCostFlow` | flows, s→t flow of value y, min-cost flow; `F_k(y)` is the cost of an `IsMinCostFlow` | SP §3 |
| `GNode k`, `GArc k`, `gTail`, `gHead`, `gCap`, `gCost`, `countingNetwork k`, `gSource`, `gSink` | `G_k`: arc s₀→t₀ (cap 1, cost 0); level ℓ: s_ℓ→s_{ℓ−1}, t_{ℓ−1}→t_ℓ (cost 0), s_ℓ→t_{ℓ−1}, s_{ℓ−1}→t_ℓ (cost 3^ℓ), all of capacity 2^{ℓ−1} | SP §3 first paragraph (Disser–Skutella §3.1) |
| `countD k` | `D₀=(0)`, `D_k=(D_{k−1}, 2·3^k − reverse D_{k−1})` | SP Lemma 2 |
| `pwl D y` | piecewise-linear `F` with `F(0)=0` and unit increments `D` | SP Lemma 2 |
| `SNode m`, `SArc m`, `embed`, `splitter m`, `sSource`, `sinkA`, `sinkB`, `sinkOf` | splitter `N_m`: two copies of `G_m` sharing `s=s_m`, sinks `a` (copy A = `false`), `b` (copy B = `true`); `4m+3` nodes, `8m+2` arcs exactly | SP §3 *The splitter* |
| `bigK m = 2^{m+1}`, `inCap` | `K`, in-capacity | SP §3 |
| `IsSplitFlow m x φ`, `splitObjective` | s→{a,b} flow of value x; `Σκφ + θ·inflow(b)` | SP §3 before Lemma 3 |
| `bigM m = 2·3^{m+1}`, `epsC = 3`, `lam m = 2M` | constants | SP §5 *Construction* |
| `AllocLP`, `rowSum`, `colSum`, `Feasible`, `objective`, `IsOptimal`, `trade` | allocation LP; `cap = none` encodes the unbounded goods `J_∞`; `T(f)` | SP §4 |
| `GadgetPort`, `gadgetE`, `gadgetCoef`, `gadgetLP m c x αa αb` | `G(c,x,α_a,α_b)` | SP §5 *The gadget LP* |
| `Market`, `WellFormed`, `rowSum`, `colSum`, `IsEquilibrium` (`cond_a` … `cond_d_eq`) | (M1) market and equilibrium (a)–(d) | SP §1.2; Ch2 Def. (M1) |
| `RBuyer n`, `RGood n`, `portGood`, `redIsOption`, `redA`, `redB`, `capV`, `redMarket` | the market of §5 with `m = n`: goods `p_v` (cap `1+2^m·indeg v`), `g_{v,e}` (cap `c_e`), exit `E` (cap `1+2^m(indeg yes+indeg no)`); buyers `(v,u)` with the listed options, intercepts and slopes | SP §5 *Construction* |
| `portPurchase`, `redX`, `exitLoad` | `A_v`, `B_v`, `x_v`, `ℓ_t` | SP §5 after Construction, Thm 7 Step 3 |
| `BSSG T Θ` (`r`, `prior`, `ud0`, `ud1`, `ua0`, `ua1`), `WellFormed` | Bayesian simple security game | Con §1; Ch2 Def. 2.1 |
| `IsDist`, `IsDefMixed`, `attEU`, `defEU`, `IsBNE` | general mixed-strategy BNE (defender: distribution on r-subsets) | Ch2 "A BNE is a mixed strategy of the defender and a mixed strategy for every type that are mutual best responses in expectation" |
| `coverage`, `singletonDefense`, `U`, `load`, `IsCoverageBNE`, `typeValue` | coverage vector; `U_θk(ξ)`; load; Fact 0 conditions (i), (ii); value `u_i` | SP §1.1 Fact 0; Ch2 *One resource* |
| `MTarget`, `MType`, `gW`, `gA`, `gS`, `gWeight`, `gPay`, `toGame` | Γ of §6: real, private, outside, control targets; source, dedicated, control types; `W`, `A`, `S`, weights, payoff table, "−2 − ξ_k elsewhere" | SP §6 table |
| `decP`, `decV`, `decF` | `P_j=Sξ_j`, `v_i=S u_i`, `f_ij=(W+μ_i)σ_i(j)` | SP Lemma 8 |
| `Red I`, `Dec I σ` | Red = preprocess, then §5 market, then Γ; Dec = "yes iff Σ (W+μ_i)σ_i(E) = 1 over sink types (u,a) with s₀(u)=yes and (u,b) with s₁(u)=yes" | SP *Proof of the Theorem* |

## 2. Statements (`Statements.lean`)

| Lean | SP / source | Status |
|---|---|---|
| `dohrau_lemma1` | DGKMW Lemma 1 (termination and run profile ≤ x) | sorry |
| `toSwitchGraph_terminates_iff`, `reaches_unique`, `reaches_iff_outcomeWithin` | bridges between the run of the instance and `Run(G′,o,t)`; fuel bound | sorry |
| `preprocess_reaches_yes`, `preprocess_preprocessed` | SP §1.3 Preprocessing | sorry |
| `h0_add_h1` | SP §1.3 `h₀+h₁=x` | **proved** |
| `h_floor`, `fixedPoint_termInflow_sum` | SP Lemma 1 (i); `y_yes+y_no=1` | sorry |
| `lemma1` | SP Lemma 1 | sorry |
| `lemma2_length` | `|D_k| = 2^k` | **proved** |
| `lemma2_first`, `lemma2_last`, `lemma2_gaps`, `lemma2_minCost`, `lemma2_maxFlow` | SP Lemma 2 | sorry |
| `lemma3` | SP Lemma 3 | sorry |
| `lemma4`, `lemma5` | SP Lemmas 4, 5 | sorry |
| `lemma6` | SP Lemma 6 | sorry |
| `theorem7` | SP Theorem 7 | sorry |
| `fact0`, `fact0_realize` | SP Fact 0, both directions | sorry |
| `lemma8` | SP Lemma 8 | sorry |
| `red_wellFormed`, `redMarket_wellFormed`, `red_sizes` | SP proof of the Theorem: legality, slopes ≥ 1, sizes | sorry |
| `red_bne_exists` | non-vacuity (not in SP) | sorry |
| `main_coverage`, `main` | SP Theorem (end to end, coverage form and general BNE) | sorry |

## 3. Modelling choices an auditor should check

1. **C1. Exact rationals.** Everything is over `ℚ`. In particular `main` quantifies over *rational*
   BNEs, and `lemma1` over rational fixed points. SP works over ℝ. The rational statement is what
   exact BNE search needs (an oracle returns rationals), but it is formally weaker than "every real
   BNE". Generalising to a `LinearOrderedField` with `FloorRing` would remove this gap.
2. **C2. Run encoding.** The run is relational: `Reaches t := ∃ k, (state k).1 = inr t`. Terminals are
   absorbing in `step`. A switch state `false` means "points to s₀", and every switch starts at `false`.
   `outcomeWithin` is a computable fuel version, linked to `Reaches` by `reaches_iff_outcomeWithin`.
   For Dohrau's `Run`, termination at `d` is modelled as a fixed point of `runStep`.
3. **C3. Preprocessing redirects and does not delete.** Dead switches (no path of ≤ n edges to a
   terminal) are kept, and every edge into them is redirected to `no`. Dead switches therefore point
   to `no` themselves, the instance keeps `n` switches, and "origin deleted, output a fixed
   no-instance" needs no special case (o's edges go to `no`). As a result `Red` always uses `m = n`
   and the sizes are exactly `12n²+6n+3` / `12n²+6n+2`, where SP has `≤` because `n′ ≤ n`.
   "Cannot reach a terminal" is encoded as `liveWithin n v = false`, i.e. no path with ≤ n edges.
   This is equivalent because a shortest path is simple.
4. **C4. Switching flows** are `V × V → ℕ`. Only values on `G.E` matter, and conservation sums run
   over the edge *set*, so a double edge `s₀ v = s₁ v` is one edge and (2) compares it with itself
   (SP Lemma 1 (iii)). `o ≠ d` is a hypothesis of `dohrau_lemma1`, as in DGKMW.
5. **C5. (FP) uses labelled edges.** `inflow` sums over pairs `(u, i)`, so a double edge contributes
   `h₀+h₁`. `IsFixedPoint` includes `x ≥ 0`. `h0`, `h1` are defined on all of ℚ through `⌊x/2⌋`, and
   the definition from the paper applies only for `x ≥ 0`.
6. **C6. Flows.** `IsFlow s t y` requires capacity feasibility, net outflow `y` at `s` and
   conservation at every node other than `s, t`. Net outflow `−y` at `t` is implied, not assumed.
   `F_k` is never defined as a function. Lemma 2 states existence of min-cost flows and that their
   cost equals `pwl (countD k) y`, which together with `lemma2_gaps` gives convexity.
7. **C7. Splitter indexing** is exact (`4m+3` nodes, `8m+2` arcs, no isolated or junk nodes):
   `embed` identifies `s_m` of both copies with `sSource`. Copy A is `false`, ending in `sinkA`.
   Copy B is `true`, ending in `sinkB`.
8. **C8. Options as a `Finset` of pairs** (markets, LPs). This automatically gives "at most one
   option per good". The functions `a`, `b`, `coef`, `f` are total on `I × J`, and only their values
   on `E` enter any definition. `f ≥ 0` is required only on `E`. `AllocLP.cap = none` encodes `J_∞`.
9. **C9. `redA`/`redB` on non-option pairs** return junk values that are never used. For option pairs:
   arc goods get `2M − κ_e` (tail) or `2M` (head) with slope 1. `p_v` for `(v,s)` gets `2M` with slope
   `λ`. Ports get `M` (sink a) or `M − ε` (sink b) with slope 1. Check `redIsOption` against the
   bullet list in SP §5.
10. **C10. Game payoffs** use `(intercept, slope)`: `u₂⁰ = intercept`, `u₂¹ = intercept − slope`.
    The prior is `weight / Σ weight`, and the defender gets 0 uncovered, 1 covered, with `r = 1`.
    `gW = 1 + Σμ + fold max 0 c`, which equals SP's `1 + Σμ + max_j c_j` because `c > 0`.
    `gA = 1 + max(0, max_E a)`, `gS = 1 + (|I|+|J|)·A`. Overlapping `match` arms in `gPay` are
    resolved first-match, and the final arm is the "−2 − ξ elsewhere" default.
11. **C11. BNE.** `IsBNE`: the defender mixes over subsets of size **exactly** `r` (Ch2. Con says "a
    subset of r targets"). Types best-respond *interim* (every type, whatever its prior), and the
    defender best-responds *ex ante*. Best responses are checked against all mixed deviations.
    `IsCoverageBNE` is the Fact 0 form and is meaningful only for `r = 1`, defender payoffs 0/1;
    `fact0` proves the equivalence under exactly these hypotheses. Loads in `IsCoverageBNE` use
    normalized priors, while `decF` and `Dec` use weights `W + μ_i`; SP notes these are equivalent
    (positive scaling).
12. **C12. `Dec`** reads only the type strategies `σ`, together with `W` and the sink masses of the
    preprocessed instance's market. It compares the weighted sum to `1` exactly (`decide` on `ℚ`).
13. **C13. Non-vacuity.** `main` says nothing if `Red I` has no BNE. `red_bne_exists` is stated
    separately; it is not part of SP.
14. **C14. Polynomial time / bit sizes** are not formalized. Only exact cardinalities (`red_sizes`)
    are stated.
15. **C15. Theorem 7** is stated for any instance satisfying `Preprocessed`. `main` composes it with
    `preprocess_preprocessed` and `preprocess_reaches_yes`.
