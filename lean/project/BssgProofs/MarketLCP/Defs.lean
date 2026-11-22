import BssgProofs.DirectLCP.Defs

/-!
# The affine matching market (M1) reduces to one P-matrix LCP: definitions

Formalization of `book/readable/chapters/ch5-upper.tex`, Section "The market reduces to P-matrix
LCP" (`sec:plcp`), cited below as **[PL]**.  Every definition is cross-referenced in
`DEFINITIONS-marketlcp.md`.  All numbers are exact rationals `ℚ`.

The market is the frozen `Bssg.Market I J` of `BssgProofs/Definitions.lean` and its equilibrium
is the frozen `Market.IsEquilibrium` (conditions (a)–(d)).  The matrix classes (`IsPMatrix`,
`IsP0Matrix`), `principal`, `slack` and `IsLCPSol` are reused from `BssgProofs/DirectLCP/Defs.lean`.

Sections
1. The LCP `(q, M)` of a market: coordinates `z = (f, u, P)`, the matrices `B`, `K`, `M`, `q`,
   the slack table, decoding and encoding.
2. Generic LP data for any `LCP(q, M)`: `LP(A)`, the system `(∗)`, support, `D`, `C`, `d`.
3. The market constants `H`, `b_min`, `Z̄` and the explicit `ε`.
-/

namespace Bssg
namespace MarketLCP

open Finset Matrix DirectLCP

/-! ## 1. The LCP of an (M1) market -/

section MarketLCPData

variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
variable (Mk : Market I J)

/-- Edge coordinates: the options `(i, j) ∈ E` as a type. -/
abbrev Edge := {e : I × J // e ∈ Mk.E}

/-- LCP coordinates `z = (f, u, P)` [PL §"The LCP formulation"]: `inl e` is `f_e` (`e ∈ E`),
`inr (inl i)` is `u_i`, `inr (inr j)` is `P_j`.  `N = |E| + |I| + |J|`. -/
abbrev Idx := Edge Mk ⊕ (I ⊕ J)

namespace Idx
variable {Mk}
/-- `f_e`. -/
abbrev f (e : Edge Mk) : Idx Mk := .inl e
/-- `u_i`. -/
abbrev u (i : I) : Idx Mk := .inr (.inl i)
/-- `P_j`. -/
abbrev P (j : J) : Idx Mk := .inr (.inr j)
end Idx

/-- `Bᵀ ∈ ℚ^{V × E}` (vertex rows `V = I ⊕ J`, edge columns): the column of edge `(i, j)` has
`1` in row `i` and `b_ij` in row `j`, zeros elsewhere.  [PL] writes `B ∈ ℚ^{E×V}`; this is its
transpose. -/
def matB : Matrix (I ⊕ J) (Edge Mk) ℚ :=
  Matrix.of fun v e =>
    match v with
    | .inl i => if e.1.1 = i then 1 else 0
    | .inr j => if e.1.2 = j then Mk.b e.1 else 0

/-- `Kᵀ ∈ ℚ^{V × E}`: the column of edge `(i, j)` has `1` in rows `i` and `j`, zeros elsewhere. -/
def matK : Matrix (I ⊕ J) (Edge Mk) ℚ :=
  Matrix.of fun v e =>
    match v with
    | .inl i => if e.1.1 = i then 1 else 0
    | .inr j => if e.1.2 = j then 1 else 0

/-- `M = (0 B; −Kᵀ 0)` [PL display], in the order `(edges, vertices)`. -/
def lcpM : Matrix (Idx Mk) (Idx Mk) ℚ := Matrix.fromBlocks 0 (matB Mk)ᵀ (-matK Mk) 0

/-- `q = (−a, μ, c)` [PL]. -/
def lcpq : Idx Mk → ℚ := Sum.elim (fun e => -Mk.a e.1) (Sum.elim Mk.mass Mk.cap)

/-- The flow part `f` of `z`, extended by `0` off `E` (a total function on `I × J`, as in the
frozen `Market`). -/
def zf (z : Idx Mk → ℚ) : I × J → ℚ := fun e => if h : e ∈ Mk.E then z (.inl ⟨e, h⟩) else 0

/-- The utility part `u` of `z`. -/
def zu (z : Idx Mk → ℚ) : I → ℚ := fun i => z (Idx.u i)

/-- The price part `P` of `z`. -/
def zP (z : Idx Mk → ℚ) : J → ℚ := fun j => z (Idx.P j)

/-- The vector `z = (f, v, P)` of a candidate equilibrium `(P, v, f)` (only `f` on `E` is used). -/
def encode (P : J → ℚ) (v : I → ℚ) (f : I × J → ℚ) : Idx Mk → ℚ :=
  Sum.elim (fun e => f e.1) (Sum.elim v P)

/-- The slack table [PL display defining `w = q + Mz`]:
`w_ij = u_i + b_ij P_j − a_ij`, `w_i = μ_i − Σ_j f_ij`, `w_j = c_j − Σ_i f_ij`, with the sums over
options (the frozen `Market.rowSum`, `Market.colSum`). -/
def slackTable (z : Idx Mk → ℚ) : Idx Mk → ℚ
  | .inl e => z (Idx.u e.1.1) + Mk.b e.1 * z (Idx.P e.1.2) - Mk.a e.1
  | .inr (.inl i) => Mk.mass i - Mk.rowSum (zf Mk z) i
  | .inr (.inr j) => Mk.cap j - Mk.colSum (zf Mk z) j

/-! ## 4. Example plcp:ex:negative -/

section Example

/-- [PL Example plcp:ex:negative]: one buyer, one good, `μ = 1`, `c = 2`, `a = b = 1`. -/
def exMarket : Market Unit Unit where
  mass := fun _ => 1
  cap := fun _ => 2
  E := {((), ())}
  a := fun _ => 1
  b := fun _ => 1

/-- The single edge of `exMarket`. -/
def exEdge : Edge exMarket := ⟨((), ()), Finset.mem_singleton_self _⟩

/-- The LCP vector `(f, u, P)` of the example. -/
def exZ (f u P : ℚ) : Idx exMarket → ℚ := Sum.elim (fun _ => f) (Sum.elim (fun _ => u) (fun _ => P))

end Example

end MarketLCPData

/-! ## 2. Generic LP data for `LCP(q, M)` -/

section Generic

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The support `A = {k : z_k > 0}`. -/
def support (z : ι → ℚ) : Finset ι := univ.filter fun k => 0 < z k

/-- Feasible points `(z, ρ)` of `LP(A)` [PL, display before Lemma plcp:lem:gap]:
`z ≥ 0`, `ρ ≥ 0`, `z_{Ā} = 0`, `q + Mz ≥ −ρ𝟏`, `(q + Mz)_A ≤ ρ𝟏`.  (The objective is `min ρ`.) -/
def IsLPFeasible (q : ι → ℚ) (M : Matrix ι ι ℚ) (A : Finset ι) (z : ι → ℚ) (ρ : ℚ) : Prop :=
  (∀ k, 0 ≤ z k) ∧ 0 ≤ ρ ∧ (∀ k, k ∉ A → z k = 0) ∧ (∀ k, -ρ ≤ slack q M z k) ∧
    ∀ k, k ∈ A → slack q M z k ≤ ρ

/-- Feasible points of the system `(∗)` of Thm. plcp:thm:main:
`z ≥ 0`, `z_{Ā} = 0`, `q + Mz ≥ 0`, `(q + Mz)_A = 0`. -/
def IsStarFeasible (q : ι → ℚ) (M : Matrix ι ι ℚ) (A : Finset ι) (z : ι → ℚ) : Prop :=
  (∀ k, 0 ≤ z k) ∧ (∀ k, k ∉ A → z k = 0) ∧ (∀ k, 0 ≤ slack q M z k) ∧
    ∀ k, k ∈ A → slack q M z k = 0

/-- `D`: the least common multiple of all denominators of entries of `M` and `q`. -/
def lcmDen (q : ι → ℚ) (M : Matrix ι ι ℚ) : ℕ :=
  (univ.lcm fun p : ι × ι => (M p.1 p.2).den).lcm (univ.lcm fun k => (q k).den)

/-- `C = D · max(1, max_{kl} |M_kl|, max_k |q_k|)`, written as a natural number:
`max(D, max_{kl} |D M_kl|, max_k |D q_k|)` (each `D x` is an integer; `cC_eq` in `Proofs.lean`
shows the two forms agree). -/
def cC (q : ι → ℚ) (M : Matrix ι ι ℚ) : ℕ :=
  max (lcmDen q M)
    ((univ.sup fun p : ι × ι => ((lcmDen q M : ℚ) * M p.1 p.2).num.natAbs) ⊔
      (univ.sup fun k => ((lcmDen q M : ℚ) * q k).num.natAbs))

/-- `d = N + 1`, the number of variables `(z, ρ)` of `LP(A)`. -/
def dimd (ι : Type*) [Fintype ι] : ℕ := Fintype.card ι + 1

end Generic

/-! ## 3. Market constants and `ε` -/

section Constants

variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
variable (Mk : Market I J)

/-- `H = max(0, max_{(i,j) ∈ E} a_ij)`. -/
def cH : ℚ := Mk.E.fold max 0 Mk.a

/-- `b_min = min_{(i,j) ∈ E} b_ij` (`1` if `E = ∅`, a value that is then never used since `H = 0`). -/
def bmin : ℚ := if h : Mk.E.Nonempty then Mk.E.inf' h Mk.b else 1

/-- `max_i μ_i` (as `fold max 0`; equal to the maximum when `I ≠ ∅`, since `μ > 0`). -/
def muMax : ℚ := univ.fold max 0 Mk.mass

/-- `Z̄ = 1 + max(max_i μ_i + H, H / b_min)`. -/
def Zbar : ℚ := 1 + max (muMax Mk + cH Mk) (cH Mk / bmin Mk)

/-- `D` for the market LCP. -/
def mD : ℕ := lcmDen (lcpq Mk) (lcpM Mk)

/-- `C` for the market LCP. -/
def mC : ℕ := cC (lcpq Mk) (lcpM Mk)

/-- `d = N + 1 = |E| + |I| + |J| + 1`. -/
def md : ℕ := dimd (Idx Mk)

/-- `ε = 1 / (2 ⌈Z̄⌉ (dC)^d)` [PL Thm. plcp:thm:main]. -/
def eps : ℚ := 1 / (2 * (⌈Zbar Mk⌉ : ℚ) * ((md Mk * mC Mk : ℕ) : ℚ) ^ md Mk)

/-- `M + ε I`. -/
def lcpMeps (ε : ℚ) : Matrix (Idx Mk) (Idx Mk) ℚ := lcpM Mk + ε • (1 : Matrix (Idx Mk) (Idx Mk) ℚ)

end Constants

end MarketLCP
end Bssg
