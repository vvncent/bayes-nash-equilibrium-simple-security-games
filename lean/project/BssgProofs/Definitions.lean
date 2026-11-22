import Mathlib.Data.Rat.Floor
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Fin

/-!
# Shared definitions (FROZEN interface)

Formalization of `simplify/simple/simple-proof.md` ("Exact Bayes–Nash equilibria of Bayesian simple
security games are ARRIVAL-hard — a simplified proof").

All numbers are exact rationals `ℚ`; all index types are finite with decidable equality.
This file must stay `sorry`-free.  Every definition is cross-referenced in `DEFINITIONS.md`.

Sections
1. Dohrau et al. switch graphs, `Run`, switching flows (arXiv:1605.03546v4, Def. 1, Def. 2).
2. ARRIVAL instances as in simple-proof §1.3 (`Fin n` switches + two terminals), run, preprocessing.
3. The continuous switch map `h₀, h₁` and fixed points (FP).
4. Flow networks; the Disser–Skutella counting network `G_k`; the splitter `N_m`.
5. Allocation LPs (§4) and the gadget LP `G(c, x, α_a, α_b)` (§5).
6. Affine matching market (M1) and its equilibrium, conditions (a)–(d).
7. The market of §5 built from an ARRIVAL instance.
8. Bayesian simple security games: general mixed-strategy BNE and the one-resource coverage form.
9. The game Γ of §6 built from a market; the decoding of Lemma 8; `Red` and `Dec`.
-/

namespace Bssg

open Finset

/-! ## 1. Dohrau et al.: switch graphs, `Run`, switching flows -/

/-- A switch graph `G = (V, E, s₀, s₁)` [Dohrau et al., §1]: `s₀ s₁ : V → V`.
The edge set `E` is derived (`SwitchGraph.E`) and is a *set* (so `s₀ v = s₁ v` gives one edge). -/
structure SwitchGraph (V : Type*) where
  s0 : V → V
  s1 : V → V

namespace SwitchGraph

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SwitchGraph V)

/-- `E = {(v, s₀ v) : v ∈ V} ∪ {(v, s₁ v) : v ∈ V}` as a `Finset` (a set, not a multiset). -/
def E : Finset (V × V) :=
  (univ.image fun v => (v, G.s0 v)) ∪ (univ.image fun v => (v, G.s1 v))

/-- `E⁺(v)`: outgoing edges at `v`. -/
def outE (v : V) : Finset (V × V) := G.E.filter fun e => e.1 = v

/-- `E⁻(v)`: incoming edges at `v`. -/
def inE (v : V) : Finset (V × V) := G.E.filter fun e => e.2 = v

/-- Dohrau et al., Definition 2.  A switching flow for origin `o` and destination `d` is
`x : E → ℕ₀`; we encode it as `x : V × V → ℕ` of which only the values on `G.E` matter.
(1) flow conservation, stated in `ℤ`; (2) `0 ≤ x(v,s₁ v) ≤ x(v,s₀ v) ≤ x(v,s₁ v) + 1`
(the `0 ≤` part is automatic in `ℕ`).  The side condition `o ≠ d` is a hypothesis of the
lemmas that use this notion, as in the paper. -/
structure IsSwitchingFlow (o d : V) (x : V × V → ℕ) : Prop where
  conservation : ∀ v : V,
    (∑ e ∈ G.outE v, (x e : ℤ)) - (∑ e ∈ G.inE v, (x e : ℤ)) =
      (if v = o then 1 else 0) - (if v = d then 1 else 0)
  switching : ∀ v : V, x (v, G.s1 v) ≤ x (v, G.s0 v) ∧ x (v, G.s0 v) ≤ x (v, G.s1 v) + 1

/-- One iteration of `procedure Run(G, o, d)`.  State = (current vertex `v`, switch array),
where `sw v = false` means `s_curr[v] = s₀ v` and `sw v = true` means `s_curr[v] = s₁ v`.
At `v = d` the loop has exited, which we model as a fixed state. -/
def runStep (d : V) (st : V × (V → Bool)) : V × (V → Bool) :=
  if st.1 = d then st
  else (if st.2 st.1 then G.s1 st.1 else G.s0 st.1, Function.update st.2 st.1 (!st.2 st.1))

/-- State of `Run(G, o, d)` after `k` iterations (initially `s_curr = s₀` everywhere). -/
def runState (o d : V) (k : ℕ) : V × (V → Bool) :=
  (G.runStep d)^[k] (o, fun _ => false)

/-- The edge traversed by the iteration that starts in state `st`. -/
def traversed (st : V × (V → Bool)) : V × V :=
  (st.1, if st.2 st.1 then G.s1 st.1 else G.s0 st.1)

/-- `Run(G, o, d)` terminates. -/
def RunTerminates (o d : V) : Prop := ∃ k, (G.runState o d k).1 = d

/-- Run profile restricted to the first `k` iterations: how often edge `e` was traversed. -/
def runProfile (o d : V) (k : ℕ) (e : V × V) : ℕ :=
  ((range k).filter fun j => (G.runState o d j).1 ≠ d ∧ G.traversed (G.runState o d j) = e).card

end SwitchGraph

/-! ## 2. ARRIVAL instances (simple-proof §1.3) -/

/-- The two terminals. -/
inductive Terminal
  | yes
  | no
  deriving DecidableEq, Repr

instance : Fintype Terminal :=
  ⟨{.yes, .no}, by intro t; cases t <;> simp⟩

/-- The other terminal. -/
def Terminal.other : Terminal → Terminal
  | .yes => .no
  | .no => .yes

/-- Nodes of an instance with `n` switches: a switch `Sum.inl v` or a terminal `Sum.inr t`. -/
abbrev Node (n : ℕ) := Fin n ⊕ Terminal

/-- An ARRIVAL instance: switches `Fin n`, terminals yes/no, successors `s₀, s₁`, origin `o`.
(`n ≥ 1` is forced by `origin : Fin n`.) -/
structure ArrivalInstance (n : ℕ) where
  s0 : Fin n → Node n
  s1 : Fin n → Node n
  origin : Fin n

namespace ArrivalInstance

variable {n : ℕ} (I : ArrivalInstance n)

/-- Labelled successor: `succ v false = s₀ v` (label 0), `succ v true = s₁ v` (label 1). -/
def succ (v : Fin n) (i : Bool) : Node n := if i then I.s1 v else I.s0 v

/-- One step of the token: at a switch `v` move to its current successor and toggle `v`;
a terminal is absorbing.  `sw v = false` means `v` currently points to `s₀ v`. -/
def step (st : Node n × (Fin n → Bool)) : Node n × (Fin n → Bool) :=
  match st.1 with
  | .inl v => (I.succ v (st.2 v), Function.update st.2 v (!st.2 v))
  | .inr _ => st

/-- State after `k` steps, starting at the origin with every switch at `s₀`. -/
def state (k : ℕ) : Node n × (Fin n → Bool) :=
  I.step^[k] (.inl I.origin, fun _ => false)

/-- RELATIONAL run outcome: the token reaches terminal `t` (after finitely many steps). -/
def Reaches (t : Terminal) : Prop := ∃ k, (I.state k).1 = .inr t

/-- The answer of the instance: yes iff the token reaches `yes`
(if it never reaches a terminal the answer is no). -/
def Answer : Prop := I.Reaches .yes

/-- FUEL-BOUNDED computable outcome (for testing / `#eval`): the terminal occupied after
`fuel` steps, if any.  Bridge to `Reaches`: see `Statements.reaches_iff_outcomeWithin`. -/
def outcomeWithin (fuel : ℕ) : Option Terminal :=
  match (I.state fuel).1 with
  | .inl _ => none
  | .inr t => some t

/-- The Dohrau switch graph `G′` on `V ∪ {yes, no}` in which both terminals are self-loops. -/
def toSwitchGraph : SwitchGraph (Node n) where
  s0 := fun w => match w with
    | .inl v => I.s0 v
    | .inr t => .inr t
  s1 := fun w => match w with
    | .inl v => I.s1 v
    | .inr t => .inr t

/-- `liveWithin k v`: some path of at most `k` labelled edges leads from `v` to a terminal. -/
def liveWithin : ℕ → Fin n → Bool
  | 0, _ => false
  | k + 1, v => [false, true].any fun i =>
      match I.succ v i with
      | .inr _ => true
      | .inl w => liveWithin k w

/-- Preprocessed: every switch has a path of length `≤ n` to a terminal. -/
def Preprocessed : Prop := ∀ v, I.liveWithin n v = true

/-- Redirect edges into vertices that cannot reach a terminal to `no`. -/
def redirect (w : Node n) : Node n :=
  match w with
  | .inl u => if I.liveWithin n u then .inl u else .inr .no
  | .inr t => .inr t

/-- Preprocessing (MODELLING CHOICE: dead switches are kept, not deleted; all edges into them are
redirected to `no`.  Dead switches then point to `no` directly, so the result is `Preprocessed`;
the case "origin deleted" needs no special treatment). -/
def preprocess : ArrivalInstance n where
  s0 := fun v => I.redirect (I.s0 v)
  s1 := fun v => I.redirect (I.s1 v)
  origin := I.origin

/-- Number of labelled edges `(u, i)` with `s_i(u) = w`. -/
def indeg (w : Node n) : ℕ :=
  (univ.filter fun p : Fin n × Bool => I.succ p.1 p.2 = w).card

end ArrivalInstance

/-! ## 3. The continuous switch map and fixed points -/

/-- `h₀(x) = z + min(ρ, 1)` where `x = 2z + ρ`, `z = ⌊x/2⌋`, `ρ ∈ [0,2)`. -/
def h0 (x : ℚ) : ℚ :=
  ((⌊x / 2⌋ : ℤ) : ℚ) + min (x - 2 * ((⌊x / 2⌋ : ℤ) : ℚ)) 1

/-- `h₁(x) = z + max(ρ − 1, 0)` where `x = 2z + ρ`. -/
def h1 (x : ℚ) : ℚ :=
  ((⌊x / 2⌋ : ℤ) : ℚ) + max (x - 2 * ((⌊x / 2⌋ : ℤ) : ℚ) - 1) 0

/-- `h false = h₀`, `h true = h₁`. -/
def h (i : Bool) (x : ℚ) : ℚ := if i then h1 x else h0 x

namespace ArrivalInstance

variable {n : ℕ} (I : ArrivalInstance n)

/-- Inflow into node `w` under `x`: `Σ_{(u,i) : s_i(u) = w} h_i(x_u)` (labelled edges, so a
double edge `s₀ u = s₁ u = w` contributes `h₀ + h₁`). -/
def inflow (x : Fin n → ℚ) (w : Node n) : ℚ :=
  ∑ u : Fin n, ∑ i : Bool, if I.succ u i = w then h i (x u) else 0

/-- (FP): `x ≥ 0` and `x_v = [v = o] + Σ_{(u,i): s_i(u)=v} h_i(x_u)` for every switch `v`. -/
def IsFixedPoint (x : Fin n → ℚ) : Prop :=
  (∀ v, 0 ≤ x v) ∧ ∀ v, x v = (if v = I.origin then 1 else 0) + I.inflow x (.inl v)

/-- Terminal inflow `y_t`. -/
def termInflow (x : Fin n → ℚ) (t : Terminal) : ℚ := I.inflow x (.inr t)

end ArrivalInstance

/-! ## 4. Flow networks, counting network `G_k`, splitter `N_m` -/

/-- A network with nodes `N`, arcs `A`, arc endpoints, capacities and costs. -/
structure Network (N A : Type*) where
  tail : A → N
  head : A → N
  cap : A → ℚ
  cost : A → ℚ

namespace Network

variable {N A : Type*} [Fintype A] [DecidableEq N] (G : Network N A)

/-- Flow on arcs leaving `u`. -/
def outflow (φ : A → ℚ) (u : N) : ℚ := ∑ a ∈ univ.filter (fun a => G.tail a = u), φ a

/-- Flow on arcs entering `u`. -/
def inflow (φ : A → ℚ) (u : N) : ℚ := ∑ a ∈ univ.filter (fun a => G.head a = u), φ a

/-- Net outflow. -/
def netOut (φ : A → ℚ) (u : N) : ℚ := G.outflow φ u - G.inflow φ u

/-- Capacity feasibility `0 ≤ φ ≤ cap`. -/
def Feasible (φ : A → ℚ) : Prop := ∀ a, 0 ≤ φ a ∧ φ a ≤ G.cap a

/-- Linear cost `Σ_a cost_a φ_a`. -/
def totalCost (φ : A → ℚ) : ℚ := ∑ a, G.cost a * φ a

/-- An `s → t` flow of value `y`: feasible, net outflow `y` at `s`, conserved at every node other
than `s, t` (net outflow `-y` at `t` then follows). -/
def IsFlow (s t : N) (y : ℚ) (φ : A → ℚ) : Prop :=
  G.Feasible φ ∧ G.netOut φ s = y ∧ ∀ u, u ≠ s → u ≠ t → G.netOut φ u = 0

/-- A minimum-cost `s → t` flow of value `y`.  `F_k(y)` of the paper is its cost. -/
def IsMinCostFlow (s t : N) (y : ℚ) (φ : A → ℚ) : Prop :=
  G.IsFlow s t y φ ∧ ∀ ψ, G.IsFlow s t y ψ → G.totalCost φ ≤ G.totalCost ψ

end Network

/-- Nodes of `G_k`: `Sum.inl i = s_i`, `Sum.inr i = t_i` for `i = 0..k`. -/
abbrev GNode (k : ℕ) := Fin (k + 1) ⊕ Fin (k + 1)

/-- Arcs of `G_k`: `none` = the arc `s₀ → t₀`; `some (j, r)` = arc number `r` of level `ℓ = j+1`:
`r = 0 : s_ℓ → s_{ℓ-1}`, `r = 1 : t_{ℓ-1} → t_ℓ`,
`r = 2 : s_ℓ → t_{ℓ-1}`, `r = 3 : s_{ℓ-1} → t_ℓ`. -/
abbrev GArc (k : ℕ) := Option (Fin k × Fin 4)

/-- Tail of an arc of `G_k`. -/
def gTail {k : ℕ} : GArc k → GNode k
  | none => .inl 0
  | some (j, r) =>
    if r.val = 0 then .inl j.succ
    else if r.val = 1 then .inr j.castSucc
    else if r.val = 2 then .inl j.succ
    else .inl j.castSucc

/-- Head of an arc of `G_k`. -/
def gHead {k : ℕ} : GArc k → GNode k
  | none => .inr 0
  | some (j, r) =>
    if r.val = 0 then .inl j.castSucc
    else if r.val = 1 then .inr j.succ
    else if r.val = 2 then .inr j.castSucc
    else .inr j.succ

/-- Capacity: `1` for `s₀ → t₀`, `2^{ℓ-1} = 2^j` at level `ℓ = j+1`. -/
def gCap {k : ℕ} : GArc k → ℚ
  | none => 1
  | some (j, _) => 2 ^ (j : ℕ)

/-- Cost `κ`: `0` for `s₀ → t₀` and the arcs `r = 0, 1`; `3^ℓ = 3^{j+1}` for `r = 2, 3`. -/
def gCost {k : ℕ} : GArc k → ℚ
  | none => 0
  | some (j, r) => if r.val ≤ 1 then 0 else 3 ^ ((j : ℕ) + 1)

/-- The counting network `G_k` [Disser–Skutella §3.1, costs `3^k`]. -/
def countingNetwork (k : ℕ) : Network (GNode k) (GArc k) where
  tail := gTail
  head := gHead
  cap := gCap
  cost := gCost

/-- Source `s_k` of `G_k`. -/
def gSource (k : ℕ) : GNode k := .inl (Fin.last k)

/-- Sink `t_k` of `G_k`. -/
def gSink (k : ℕ) : GNode k := .inr (Fin.last k)

/-- Increment lists: `D₀ = (0)`, `D_{k+1} = (D_k, 2·3^{k+1} − reverse(D_k))`. -/
def countD : ℕ → List ℚ
  | 0 => [0]
  | k + 1 => countD k ++ (countD k).reverse.map fun d => 2 * 3 ^ (k + 1) - d

/-- The piecewise-linear function with `F(0) = 0` and unit increments `D`:
`F(y) = Σ_{i < ⌊y⌋} D_i + (y − ⌊y⌋) D_{⌊y⌋}` (for `0 ≤ y ≤ length D`). -/
def pwl (D : List ℚ) (y : ℚ) : ℚ :=
  (D.take ⌊y⌋₊).sum + (y - (⌊y⌋₊ : ℚ)) * D.getD ⌊y⌋₊ 0

/-- Nodes of the splitter `N_m`: `Sum.inl () = s` (shared source `s_m`); for copy `c`
(`false = A`, `true = B`): `Sum.inr (c, Sum.inl i) = s_i` (`i < m`), `Sum.inr (c, Sum.inr i) = t_i`
(`i ≤ m`).  Exactly `4m + 3` nodes. -/
abbrev SNode (m : ℕ) := Unit ⊕ (Bool × (Fin m ⊕ Fin (m + 1)))

/-- Arcs of `N_m`: an arc of `G_m` in copy `c`.  Exactly `2(4m+1) = 8m+2` arcs. -/
abbrev SArc (m : ℕ) := Bool × GArc m

instance (k : ℕ) : DecidableEq (GArc k) := inferInstance
instance (m : ℕ) : DecidableEq (SNode m) := inferInstance
instance (m : ℕ) : DecidableEq (SArc m) := inferInstance
instance (m : ℕ) : Fintype (SNode m) := inferInstance
instance (m : ℕ) : Fintype (SArc m) := inferInstance

/-- Embedding of the nodes of copy `c` of `G_m` into `N_m` (identifying both `s_m` with `s`). -/
def embed {m : ℕ} (c : Bool) : GNode m → SNode m
  | .inl i => if h : (i : ℕ) < m then .inr (c, .inl ⟨i, h⟩) else .inl ()
  | .inr i => .inr (c, .inr i)

/-- The splitter `N_m`: two copies of `G_m` sharing their source. -/
def splitter (m : ℕ) : Network (SNode m) (SArc m) where
  tail := fun e => embed e.1 (gTail e.2)
  head := fun e => embed e.1 (gHead e.2)
  cap := fun e => gCap e.2
  cost := fun e => gCost e.2

/-- The shared source `s`. -/
def sSource (m : ℕ) : SNode m := .inl ()

/-- Sink `a` (= `t_m` of copy A). -/
def sinkA (m : ℕ) : SNode m := .inr (false, .inr (Fin.last m))

/-- Sink `b` (= `t_m` of copy B). -/
def sinkB (m : ℕ) : SNode m := .inr (true, .inr (Fin.last m))

/-- `sinkOf false = a`, `sinkOf true = b`. -/
def sinkOf (m : ℕ) : Bool → SNode m
  | false => sinkA m
  | true => sinkB m

/-- `K = 2^{m+1}`. -/
def bigK (m : ℕ) : ℚ := 2 ^ (m + 1)

/-- In-capacity of a node of `N_m`. -/
def inCap (m : ℕ) (u : SNode m) : ℚ := (splitter m).inflow (splitter m).cap u

/-- An `s → {a, b}` flow of value `x` in `N_m`. -/
def IsSplitFlow (m : ℕ) (x : ℚ) (φ : SArc m → ℚ) : Prop :=
  (splitter m).Feasible φ ∧ (splitter m).netOut φ (sSource m) = x ∧
    ∀ u, u ≠ sSource m → u ≠ sinkA m → u ≠ sinkB m → (splitter m).netOut φ u = 0

/-- `Σ_e κ_e φ_e + θ · inflow_φ(b)` (Lemma 3). -/
def splitObjective (m : ℕ) (θ : ℚ) (φ : SArc m → ℚ) : ℚ :=
  (splitter m).totalCost φ + θ * (splitter m).inflow φ (sinkB m)

/-! ## 5. Allocation LPs and the gadget LP -/

/-- Constants of §5: `M = 2·3^{m+1}`, `ε = 3`, `λ = 2M`. -/
def bigM (m : ℕ) : ℚ := 2 * 3 ^ (m + 1)

/-- `ε = 3`. -/
def epsC : ℚ := 3

/-- `λ = 2M`. -/
def lam (m : ℕ) : ℚ := 2 * bigM m

/-- An allocation LP (§4): buyers `I` with masses, goods `J` with capacity `some c` (finite good)
or `none` (unbounded good, `J_∞`), options `E ⊆ I × J`, objective coefficients on options. -/
structure AllocLP (I J : Type*) where
  mass : I → ℚ
  cap : J → Option ℚ
  E : Finset (I × J)
  coef : I × J → ℚ

namespace AllocLP

variable {I J : Type*} [DecidableEq I] [DecidableEq J] (L : AllocLP I J)

/-- Row sum `Σ_j f_ij` over options of `i`. -/
def rowSum (f : I × J → ℚ) (i : I) : ℚ := ∑ e ∈ L.E.filter (fun e => e.1 = i), f e

/-- Column sum `Σ_i f_ij` over options on `j`. -/
def colSum (f : I × J → ℚ) (j : J) : ℚ := ∑ e ∈ L.E.filter (fun e => e.2 = j), f e

/-- Feasible: `f ≥ 0` on `E`, rows `≤ μ_i`, finite columns `≤ c_j` (values off `E` ignored). -/
def Feasible (f : I × J → ℚ) : Prop :=
  (∀ e ∈ L.E, 0 ≤ f e) ∧ (∀ i, L.rowSum f i ≤ L.mass i) ∧
    ∀ j c, L.cap j = some c → L.colSum f j ≤ c

/-- Objective `Σ_E a_ij f_ij`. -/
def objective (f : I × J → ℚ) : ℚ := ∑ e ∈ L.E, L.coef e * f e

/-- Optimal = feasible and maximal objective among feasible points. -/
def IsOptimal (f : I × J → ℚ) : Prop :=
  L.Feasible f ∧ ∀ g, L.Feasible g → L.objective g ≤ L.objective f

/-- `T(f)` of Lemma 5: row trade plus finite-column trade. -/
def trade (f : I × J → ℚ) : ℚ :=
  (∑ e ∈ L.E, f e) + ∑ e ∈ L.E.filter (fun e => (L.cap e.2).isSome), f e

end AllocLP

/-- Goods of the gadget LP other than arcs: input good `p`, ports `π_a`, `π_b`. -/
inductive GadgetPort
  | p
  | πa
  | πb
  deriving DecidableEq, Repr

/-- Options of the gadget LP: `tail(e)` and `head(e)` on arc `e`; `s` on `p`; `a` on `π_a`;
`b` on `π_b`. -/
def gadgetE (m : ℕ) : Finset (SNode m × (SArc m ⊕ GadgetPort)) :=
  (univ.image fun e : SArc m => ((splitter m).tail e, (Sum.inl e : SArc m ⊕ GadgetPort))) ∪
  (univ.image fun e : SArc m => ((splitter m).head e, (Sum.inl e : SArc m ⊕ GadgetPort))) ∪
  {(sSource m, .inr .p), (sinkA m, .inr .πa), (sinkB m, .inr .πb)}

/-- Coefficients: `2M − κ_e` (tail of `e`), `2M` (head of `e`), `2M` (`s` on `p`), `α_a`, `α_b`. -/
def gadgetCoef (m : ℕ) (αa αb : ℚ) : SNode m × (SArc m ⊕ GadgetPort) → ℚ
  | (u, .inl e) => if (splitter m).tail e = u then 2 * bigM m - gCost e.2 else 2 * bigM m
  | (_, .inr .p) => 2 * bigM m
  | (_, .inr .πa) => αa
  | (_, .inr .πb) => αb

/-- The gadget LP `G(c, x, α_a, α_b)` of §5: buyers = nodes of `N_m` (mass `c` for `s`,
in-capacity otherwise), finite goods = arcs (capacity `c_e`) and `p` (capacity `c − x`),
unbounded goods `π_a`, `π_b`. -/
def gadgetLP (m : ℕ) (c x αa αb : ℚ) : AllocLP (SNode m) (SArc m ⊕ GadgetPort) where
  mass := fun u => if u = sSource m then c else inCap m u
  cap := fun j => match j with
    | .inl e => some (gCap e.2)
    | .inr .p => some (c - x)
    | .inr .πa => none
    | .inr .πb => none
  E := gadgetE m
  coef := gadgetCoef m αa αb

/-! ## 6. The affine matching market (M1) -/

/-- An (M1) market: masses `μ_i`, capacities `c_j`, options `E ⊆ I × J` (a set, hence at most one
option per (buyer, good)), intercepts `a_ij`, slopes `b_ij` (only values on `E` matter). -/
structure Market (I J : Type*) where
  mass : I → ℚ
  cap : J → ℚ
  E : Finset (I × J)
  a : I × J → ℚ
  b : I × J → ℚ

namespace Market

variable {I J : Type*} [DecidableEq I] [DecidableEq J] (Mk : Market I J)

/-- `μ > 0`, `c > 0`, `b > 0` on options. -/
def WellFormed : Prop :=
  (∀ i, 0 < Mk.mass i) ∧ (∀ j, 0 < Mk.cap j) ∧ ∀ e ∈ Mk.E, 0 < Mk.b e

/-- `Σ_j f_ij` over options of buyer `i`. -/
def rowSum (f : I × J → ℚ) (i : I) : ℚ := ∑ e ∈ Mk.E.filter (fun e => e.1 = i), f e

/-- `Σ_i f_ij` over options on good `j`. -/
def colSum (f : I × J → ℚ) (j : J) : ℚ := ∑ e ∈ Mk.E.filter (fun e => e.2 = j), f e

/-- Equilibrium `(P, v, f)` of (M1), conditions (a)–(d) (Chapter 2, Def. 2.3; simple-proof §1.2). -/
structure IsEquilibrium (P : J → ℚ) (v : I → ℚ) (f : I × J → ℚ) : Prop where
  P_nonneg : ∀ j, 0 ≤ P j
  v_nonneg : ∀ i, 0 ≤ v i
  f_nonneg : ∀ e ∈ Mk.E, 0 ≤ f e
  cond_a : ∀ e ∈ Mk.E, Mk.a e - Mk.b e * P e.2 ≤ v e.1
  cond_b : ∀ e ∈ Mk.E, 0 < f e → v e.1 = Mk.a e - Mk.b e * P e.2
  cond_c_le : ∀ i, Mk.rowSum f i ≤ Mk.mass i
  cond_c_eq : ∀ i, 0 < v i → Mk.rowSum f i = Mk.mass i
  cond_d_le : ∀ j, Mk.colSum f j ≤ Mk.cap j
  cond_d_eq : ∀ j, 0 < P j → Mk.colSum f j = Mk.cap j

end Market

/-! ## 7. The market of §5 built from an ARRIVAL instance (`m = n`) -/

/-- Buyers `(v, u)`: switch `v`, node `u` of `N_n`.  `n(4n+3)` buyers. -/
abbrev RBuyer (n : ℕ) := Fin n × SNode n

/-- Goods: `Sum.inl v = p_v`; `Sum.inr (Sum.inl (v, e)) = g_{v,e}`; `Sum.inr (Sum.inr ()) = E`
(exit good).  `n(8n+3)+1` goods. -/
abbrev RGood (n : ℕ) := Fin n ⊕ ((Fin n × SArc n) ⊕ Unit)

instance (n : ℕ) : DecidableEq (RBuyer n) := inferInstance
instance (n : ℕ) : DecidableEq (RGood n) := inferInstance
instance (n : ℕ) : Fintype (RBuyer n) := inferInstance
instance (n : ℕ) : Fintype (RGood n) := inferInstance
instance : Fintype GadgetPort := ⟨{.p, .πa, .πb}, by intro t; cases t <;> simp⟩

namespace ArrivalInstance

variable {n : ℕ} (I : ArrivalInstance n)

/-- Port of labelled edge `(v, i)`: `p_{s_i(v)}` if `s_i(v)` is a switch, the exit good
otherwise. -/
def portGood (v : Fin n) (i : Bool) : RGood n :=
  match I.succ v i with
  | .inl w => .inl w
  | .inr _ => .inr (.inr ())

/-- Option predicate of the §5 market. -/
def redIsOption (e : RBuyer n × RGood n) : Prop :=
  (e.1.2 = sSource n ∧ e.2 = .inl e.1.1) ∨
  (e.1.2 = sinkA n ∧ e.2 = I.portGood e.1.1 false) ∨
  (e.1.2 = sinkB n ∧ e.2 = I.portGood e.1.1 true) ∨
  ∃ a : SArc n, e.2 = .inr (.inl (e.1.1, a)) ∧
    ((splitter n).tail a = e.1.2 ∨ (splitter n).head a = e.1.2)

instance : DecidablePred I.redIsOption := by
  intro e; unfold redIsOption; infer_instance

/-- Intercepts: arc goods `2M − κ_e` (tail) / `2M` (head); `p_v` for `s`: `2M`;
port of `(v,0)` for `a`: `M`; port of `(v,1)` for `b`: `M − ε`. -/
def redA (e : RBuyer n × RGood n) : ℚ :=
  match e.2 with
  | .inr (.inl (_, a)) => if (splitter n).tail a = e.1.2 then 2 * bigM n - gCost a.2 else 2 * bigM n
  | _ => if e.1.2 = sSource n then 2 * bigM n
         else if e.1.2 = sinkA n then bigM n else bigM n - epsC

/-- Slopes: `λ` for `s` on `p_v`, `1` otherwise. -/
def redB (e : RBuyer n × RGood n) : ℚ :=
  match e.2 with
  | .inr (.inl _) => 1
  | _ => if e.1.2 = sSource n then lam n else 1

/-- `c_v = 1 + 2^m · indeg(v)`. -/
def capV (v : Fin n) : ℚ := 1 + 2 ^ n * (I.indeg (.inl v) : ℚ)

/-- The market of §5 (without preprocessing; `Red` applies it to `I.preprocess`). -/
def redMarket : Market (RBuyer n) (RGood n) where
  mass := fun b => if b.2 = sSource n then I.capV b.1 + (if b.1 = I.origin then 1 else 0)
                   else inCap n b.2
  cap := fun g => match g with
    | .inl v => I.capV v
    | .inr (.inl (_, a)) => gCap a.2
    | .inr (.inr ()) => 1 + 2 ^ n * ((I.indeg (.inr .yes) : ℚ) + (I.indeg (.inr .no) : ℚ))
  E := univ.filter I.redIsOption
  a := redA
  b := redB

/-- Port purchase of the sink of gadget `v` for label `i` (`A_v` for `i = false`, `B_v` for
`i = true`). -/
def portPurchase (f : RBuyer n × RGood n → ℚ) (v : Fin n) (i : Bool) : ℚ :=
  f ((v, sinkOf n i), I.portGood v i)

/-- `x_v = [v = o] + Σ_{(u,i): s_i(u) = v} (port purchase of (u,i))`. -/
def redX (f : RBuyer n × RGood n → ℚ) (v : Fin n) : ℚ :=
  (if v = I.origin then 1 else 0) +
    ∑ u : Fin n, ∑ i : Bool, if I.succ u i = .inl v then I.portPurchase f u i else 0

/-- Load `ℓ_t` that the sinks whose port edge leads to terminal `t` put on the exit good. -/
def exitLoad (f : RBuyer n × RGood n → ℚ) (t : Terminal) : ℚ :=
  ∑ u : Fin n, ∑ i : Bool, if I.succ u i = .inr t then I.portPurchase f u i else 0

end ArrivalInstance

/-! ## 8. Bayesian simple security games -/

/-- A Bayesian simple security game [Conitzer; Ch. 2 Def. 2.1]: `r` resources, prior on types,
defender payoffs `u₁⁰ ≤ u₁¹` (uncovered/covered), attacker payoffs `u₂⁰ ≥ u₂¹`. -/
structure BSSG (T Θ : Type*) where
  r : ℕ
  prior : Θ → ℚ
  ud0 : T → ℚ
  ud1 : T → ℚ
  ua0 : Θ → T → ℚ
  ua1 : Θ → T → ℚ

namespace BSSG

variable {T Θ : Type*} [Fintype T] [DecidableEq T] [Fintype Θ] (G : BSSG T Θ)

/-- Well-formedness of an instance (Ch. 2, Def. 2.1). -/
def WellFormed : Prop :=
  G.r ≤ Fintype.card T ∧ (∀ θ, 0 ≤ G.prior θ) ∧ (∑ θ, G.prior θ) = 1 ∧
    (∀ t, G.ud0 t ≤ G.ud1 t) ∧ ∀ θ t, G.ua1 θ t ≤ G.ua0 θ t

/-- A probability vector on a finite type. -/
def IsDist {X : Type*} [Fintype X] (τ : X → ℚ) : Prop := (∀ x, 0 ≤ τ x) ∧ (∑ x, τ x) = 1

/-- Defender mixed strategy: a probability distribution on `r`-subsets of targets. -/
def IsDefMixed (δ : Finset T → ℚ) : Prop := IsDist δ ∧ ∀ S, δ S ≠ 0 → S.card = G.r

/-- Expected attacker payoff of type `θ` playing mixed `τ` against defender mixed `δ`. -/
def attEU (θ : Θ) (δ : Finset T → ℚ) (τ : T → ℚ) : ℚ :=
  ∑ S, δ S * ∑ t, τ t * (if t ∈ S then G.ua1 θ t else G.ua0 θ t)

/-- Expected defender payoff (ex ante over types). -/
def defEU (δ : Finset T → ℚ) (σ : Θ → T → ℚ) : ℚ :=
  ∑ θ, G.prior θ * ∑ t, σ θ t * ∑ S, δ S * (if t ∈ S then G.ud1 t else G.ud0 t)

/-- GENERAL Bayes–Nash equilibrium in mixed strategies: the defender's mixed strategy and every
type's mixed strategy are best responses in expectation (types interim, defender ex ante). -/
def IsBNE (δ : Finset T → ℚ) (σ : Θ → T → ℚ) : Prop :=
  G.IsDefMixed δ ∧ (∀ θ, IsDist (σ θ)) ∧
    (∀ θ τ, IsDist τ → G.attEU θ δ τ ≤ G.attEU θ δ (σ θ)) ∧
    ∀ δ', G.IsDefMixed δ' → G.defEU δ' σ ≤ G.defEU δ σ

/-- Coverage vector of a defender mixed strategy. -/
def coverage (δ : Finset T → ℚ) (t : T) : ℚ := ∑ S, δ S * (if t ∈ S then 1 else 0)

/-- The defender mixed strategy covering singleton `{t}` with probability `ξ_t`. -/
def singletonDefense (ξ : T → ℚ) (S : Finset T) : ℚ := ∑ t, if S = {t} then ξ t else 0

/-- `U_θk(ξ) = u₂⁰(θ,k) − (u₂⁰ − u₂¹)(θ,k) ξ_k`. -/
def U (θ : Θ) (k : T) (ξ : T → ℚ) : ℚ := G.ua0 θ k - (G.ua0 θ k - G.ua1 θ k) * ξ k

/-- Load `ℓ_k = Σ_θ p_θ σ_θ(k)`. -/
def load (σ : Θ → T → ℚ) (k : T) : ℚ := ∑ θ, G.prior θ * σ θ k

/-- COVERAGE-FORM BNE for one resource and defender payoffs 0/1 (Fact 0): `ξ` in the simplex,
each type mixes over its best targets, coverage only on max-load targets.  Only meaningful when
`r = 1`, `u₁⁰ ≡ 0`, `u₁¹ ≡ 1` (the equivalence with `IsBNE` is `Statements.fact0`). -/
def IsCoverageBNE (ξ : T → ℚ) (σ : Θ → T → ℚ) : Prop :=
  IsDist ξ ∧ (∀ θ, IsDist (σ θ)) ∧
    (∀ θ k, 0 < σ θ k → ∀ j, G.U θ j ξ ≤ G.U θ k ξ) ∧
    ∀ k, 0 < ξ k → ∀ j, G.load σ j ≤ G.load σ k

/-- Value of type `θ`: `max_k U_θk(ξ)`. -/
def typeValue [Nonempty T] (θ : Θ) (ξ : T → ℚ) : ℚ :=
  univ.sup' univ_nonempty fun k => G.U θ k ξ

end BSSG

/-! ## 9. The game Γ of §6, Lemma 8 decoding, `Red` and `Dec` -/

/-- Targets of Γ: `inl j` real target of good `j`; `inr (inl i)` private target `g_i`;
`inr (inr (inl ()))` outside target `o`; `inr (inr (inr ()))` control target `h`. -/
abbrev MTarget (I J : Type*) := J ⊕ (I ⊕ (Unit ⊕ Unit))

/-- Types of Γ: `inl i` source type of buyer `i`; `inr (inl j)` dedicated type of good `j`;
`inr (inr ())` control type. -/
abbrev MType (I J : Type*) := I ⊕ (J ⊕ Unit)

namespace Market

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
  (Mk : Market I J)

/-- `W = 1 + Σ_i μ_i + max(0, max_j c_j)` (`= 1 + Σμ + max_j c_j` as `c > 0`). -/
def gW : ℚ := 1 + (∑ i, Mk.mass i) + univ.fold max 0 Mk.cap

/-- `A = 1 + max(0, max_{(i,j) ∈ E} a_ij)`. -/
def gA : ℚ := 1 + Mk.E.fold max 0 Mk.a

/-- `S = 1 + (|I| + |J|) A`. -/
def gS : ℚ := 1 + ((Fintype.card I : ℚ) + (Fintype.card J : ℚ)) * Mk.gA

/-- Type weights: `W + μ_i` (source), `W − c_j` (dedicated), `W` (control). -/
def gWeight : MType I J → ℚ
  | .inl i => Mk.gW + Mk.mass i
  | .inr (.inl j) => Mk.gW - Mk.cap j
  | .inr (.inr ()) => Mk.gW

/-- Attacker payoff at coverage `ξ_k` is `intercept − slope · ξ_k`; this is `(intercept, slope)`. -/
def gPay : MType I J → MTarget I J → ℚ × ℚ
  | .inl i, .inl j => if (i, j) ∈ Mk.E then (Mk.a (i, j) / Mk.gS, Mk.b (i, j)) else (-2, 1)
  | .inl i, .inr (.inl i') => if i' = i then (Mk.gA / Mk.gS, 1) else (-2, 1)
  | .inl _, .inr (.inr (.inl ())) => (0, 1)
  | .inr (.inl j), .inl j' => if j' = j then (2, 1) else (-2, 1)
  | .inr (.inr ()), .inr (.inr (.inr ())) => (2, 1)
  | _, _ => (-2, 1)

/-- The game Γ of §6: one resource, defender payoffs 0/1, prior = weight / total weight,
`u₂⁰ = intercept`, `u₂¹ = intercept − slope`. -/
def toGame : BSSG (MTarget I J) (MType I J) where
  r := 1
  prior := fun θ => Mk.gWeight θ / ∑ θ', Mk.gWeight θ'
  ud0 := fun _ => 0
  ud1 := fun _ => 1
  ua0 := fun θ k => (Mk.gPay θ k).1
  ua1 := fun θ k => (Mk.gPay θ k).1 - (Mk.gPay θ k).2

instance : Nonempty (MTarget I J) := ⟨.inr (.inr (.inl ()))⟩

/-- Lemma 8 decoding, prices: `P_j = S ξ_j`. -/
def decP (ξ : MTarget I J → ℚ) (j : J) : ℚ := Mk.gS * ξ (.inl j)

/-- Lemma 8 decoding, utilities: `v_i = S u_i`, `u_i` the value of source type `i`. -/
def decV (ξ : MTarget I J → ℚ) (i : I) : ℚ := Mk.gS * Mk.toGame.typeValue (.inl i) ξ

/-- Lemma 8 decoding, purchases: `f_ij = (W + μ_i) σ_i(j)`. -/
def decF (σ : MType I J → MTarget I J → ℚ) (e : I × J) : ℚ :=
  (Mk.gW + Mk.mass e.1) * σ (.inl e.1) (.inl e.2)

end Market

/-- Target type of `Red I`. -/
abbrev RTarget (n : ℕ) := MTarget (RBuyer n) (RGood n)

/-- Type (attacker type) type of `Red I`. -/
abbrev RType (n : ℕ) := MType (RBuyer n) (RGood n)

/-- `Red`: preprocess, build the §5 market, build the §6 game. -/
def Red {n : ℕ} (I : ArrivalInstance n) : BSSG (RTarget n) (RType n) :=
  I.preprocess.redMarket.toGame

/-- `Dec`: given the type strategies `σ` of a BNE of `Red I`, answer yes iff
`Σ (W + μ_i) σ_i(E) = 1`, the sum over the sink types `i = (u, a)` with `s₀(u) = yes` and
`i = (u, b)` with `s₁(u) = yes` (successors of the preprocessed instance). -/
def Dec {n : ℕ} (I : ArrivalInstance n) (σ : RType n → RTarget n → ℚ) : Bool :=
  let J := I.preprocess
  decide ((∑ u : Fin n, ∑ i : Bool,
    if J.succ u i = .inr .yes then
      (J.redMarket.gW + J.redMarket.mass (u, sinkOf n i)) *
        σ (.inl (u, sinkOf n i)) (.inl (.inr (.inr ())))
    else 0) = 1)

end Bssg
