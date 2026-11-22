# Market -> game (book Chapter 3, Section "Market to game"): Lean map

Files: `BssgProofs/MarketGame/Statements.lean` (definitions + `Prop` specs, no `sorry`),
`BssgProofs/MarketGame/Proofs.lean` (proofs `<name>_proof`). Reuses, unedited:
`Definitions.lean` (`Market`, `IsEquilibrium`, `WellFormed`, `BSSG`, `IsBNE`, `IsCoverageBNE`,
`toGame`, `decP`, `decV`, `decF`, `gPay`, `gA`, `gS`, `gW`), `lemma8_proof`, `fact0_proof`,
`fact0_realize_proof` (Proofs/Embedding.lean), `Exist.lift_bne`, `Exist.liftξ` (Proofs/Existence.lean).

## Book -> Lean

| Book (ch3-market.tex) | Lean |
|---|---|
| (M1) market, equilibrium (a)-(d), positive data | `Market`, `Market.IsEquilibrium`, `Market.WellFormed` (mu>0, c>0, b>0 on E) |
| row rescaling by nu_i (Lemma lem:mk-rescale) | `rescale Mk ν`: `a' = ν_i a`, `b' = ν_i b`; mu, c, E unchanged |
| `(P,v,f) <-> (P, nu v, f)` | `upV ν v = ν·v`, `downV ν v' = v'/ν`; `RescaleEquiv` (any ν>0), `RescaleEquivBack` (inverse maps) |
| nu_i a power of two, nu_i min_{E_i} b >= 1, polynomial length | `nu Mk i = 2^(nuExp Mk i)`, `nuExp Mk i = max_{j in E_i} Nat.size (den b_ij)`; `NuSpec` |
| rescaled market has slopes >= 1 | `rescaled Mk = rescale Mk (nu Mk)`; `RescaledWF` |
| Thm thm:mk-main (a), correctness: rescale, build game, one BNE call, decode, undo rescaling | `reduce Mk = (rescaled Mk).toGame`, `decode Mk δ σ`; `ComposeBNE` (general mixed BNE), `ComposeCoverage` (coverage form) |
| lift (converse, Thm thm:mk-embed "Conversely") | `ComposeLift` (for `reduce`, i.e. Appendix C constants only) |
| table tab:mk-types with base weight W | `gWeightW Mk W`, `toGameW Mk W`, `decVW`, `decFW` |
| `D̂ = 1 + max(Σμ, max_j c_j)`, `W = (2+2/ω) D̂` (eq. eq:mk-consts) | `hatD Mk` (`max_j c_j` written `univ.fold max 0 cap`), `wOmega Mk ω` |
| Γ_ω | `gameOmega Mk ω = toGameW Mk (wOmega Mk ω)` |
| "The proof uses W only through W > Σμ and W > max c" | `DecodeW` |
| Thm thm:mk-embed, decoding of every BNE of Γ_ω | `OmegaDecode` (any rational ω > 0) |
| Thm thm:mk-main (a) with Γ_ω | `OmegaCompose` |

## How `toGame` relates to Chapter 3's Γ_ω

* Same targets (real j, private g_i, outside o, control h), same types, same attacker payoffs
  (`Market.gPay`), same A = 1 + max(0, max_{E} a), same S = 1 + (|I|+|J|)A, one resource,
  defender payoffs 0/1, prior = weight / total weight.
* DIFFERENT base weight: `toGame` uses `W = 1 + Σμ + max(0, max_j c_j)` (Appendix C / simple-proof §6);
  Γ_ω uses `W = (2 + 2/ω) D̂`. Since `1 + Σμ + max c ≤ 2D̂ - 1 < 2D̂ < (2+2/ω)D̂`, the base weights
  never coincide, so `toGame` is never Γ_ω (e.g. Σμ = 2, c = 1: `toGame` has W = 4, Γ_1 has W = 12).
* Both are instances of `toGameW`: `toGameW Mk Mk.gW = Mk.toGame` (`ToGameW_gW`, by `rfl`) and
  `gameOmega Mk ω = toGameW Mk (wOmega Mk ω)` (definition). `DecodeW` (proof of lemma 8 copied
  with `Mk.gW` replaced by a variable W) covers both, so Chapter 3's exact Γ_ω decoding IS
  formalized (`OmegaDecode`, `OmegaCompose`), in addition to the `toGame` route (`ComposeBNE`).

## Conventions and scope

* Empty option lists: NOT deleted and NOT assumed nonempty. The book (ch2-prelim, Def. of (M1)) deletes
  buyers with E_i = ∅; here they are kept: the condition `ν_i b_ij ≥ 1` is vacuous, `nuExp = 0`,
  `ν_i = 1`, and all statements hold for arbitrary E (including E = ∅).
* ν_i = 2^{k_i} with k_i ≥ 0 ("positive power of two" read as 2^k, k ∈ ℕ); k_i ≥ 1 whenever E_i ≠ ∅.
  The book chooses any such ν_i; Lean fixes the explicit choice above. `RescaleEquiv(Back)` hold for
  every positive ν.
* ω: the book has 0 < ω ≤ 1; Lean needs only ω > 0.

## Not formalized (from Thm thm:mk-embed / thm:mk-main (a))

* Legality of Γ_ω as a `BSSG.WellFormed` game and the prior bounds `1-ω ≤ |Θ|Pr(θ) ≤ 1+ω`, ratio ≤ 1+ω.
* Lift and mutual-inverse maps for Γ_ω (the lift is proved only for `toGame`, via `Exist.lift_bne`,
  and only the price component of decode∘lift = id is stated).
* Running time / bit lengths of the game (only the bound on ν_i's exponent, `NuSpec`).
* Proposition prop:mk-below-one (counterexample for slope < 1).
