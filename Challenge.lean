/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Paths
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-!
# Gallai's conjecture with two exceptional even vertices

The induced even-degree graph has at most two vertices of degree greater
than three. The selected claims give the ceiling path budget, one prescribed
endpoint reserve, and simultaneous reserves within floor plus one. At odd
order the simultaneous budget equals the ceiling. All paths are simple and
nonempty, and every graph edge occurs exactly once.

The theorem bodies below are deliberate statement holes. Their matching
Solution declarations supply the proofs. No unrestricted Gallai theorem or
simultaneous even-order ceiling exposure is asserted.
-/

@[expose] public section

namespace Gallai
universe u
variable {V : Type u} (G : SimpleGraph V)

/-- A simple oriented graph path containing at least one edge. -/
structure NonemptyPath where
  start : V
  finish : V
  walk : G.Walk start finish
  isPath : walk.IsPath
  nonempty : ¬ walk.Nil

/-- An indexed partition of the graph's edges into nonempty simple paths.
Isolated vertices contribute no path. -/
structure Decomposition where
  size : ℕ
  path : Fin size → NonemptyPath G
  covers : ∀ e ∈ G.edgeSet, ∃! i, e ∈ (path i).walk.edges

/-- Existence of an edge partition using at most the given number of paths. -/
def HasPathBudget (k : ℕ) : Prop := ∃ D : Decomposition G, D.size ≤ k

variable {G} [Fintype V] [DecidableEq V]

/-- Number of endpoint occurrences at the vertex in this path partition. -/
def Decomposition.endpointCount (D : Decomposition G) (v : V) : ℕ :=
  ∑ i : Fin D.size,
    ((if (D.path i).start = v then 1 else 0) +
     (if (D.path i).finish = v then 1 else 0))

/-- Neighbours whose degrees in the original graph are even. -/
def evenNeighbors (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) : Finset V :=
  (G.neighborFinset v).filter fun w => Even (G.degree w)

/-- Number of even neighbours; at an even vertex this is its induced E-degree. -/
def eDegree (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) : ℕ :=
  (evenNeighbors G v).card

namespace Submission

/-- A prescribed positive even vertex is an endpoint of at least two paths
within the ceiling budget when all E-degree exceptions lie in its designated
pair. Neither exceptional degree is bounded. -/
theorem prescribed_endpoint (G : SimpleGraph V) [DecidableRel G.Adj] (h x : V)
    (hconn : G.Connected) (hhne : h ≠ x) (hhpos : 0 < G.degree h)
    (hhEven : Even (G.degree h)) (hxEven : Even (G.degree x))
    (hcap : ∀ a, Even (G.degree a) → a ≠ h → a ≠ x → eDegree G a ≤ 3) :
    ∃ D : Decomposition G, D.size ≤ (Fintype.card V + 1) / 2 ∧
      2 ≤ D.endpointCount h := by sorry

/-- Every connected finite simple graph with at most two even vertices
having more than three even neighbours meets Gallai's ceiling path budget. -/
theorem ceiling_bound (G : SimpleGraph V) [DecidableRel G.Adj]
    (hconn : G.Connected)
    (hcount : (Finset.univ.filter
      (fun v : V => Even (G.degree v) ∧ 3 < eDegree G v)).card ≤ 2) :
    HasPathBudget G ((Fintype.card V + 1) / 2) := by sorry

variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Two distinct designated even vertices are simultaneously exposed at least
twice within floor(|V|/2)+1 paths. Adjacency is unrestricted; connectedness
and distinctness ensure both vertices have positive degree. -/
theorem simultaneous_floor_add_one
    (hconn : G.Connected) (h x : V) (hne : h ≠ x)
    (hh : Even (G.degree h)) (hx : Even (G.degree x))
    (hcap : ∀ v, Even (G.degree v) → v ≠ h → v ≠ x → eDegree G v ≤ 3) :
    ∃ D : Decomposition G, D.size ≤ Fintype.card V / 2 + 1 ∧
      2 ≤ D.endpointCount h ∧ 2 ≤ D.endpointCount x := by sorry

/-- At odd order, both designated even vertices are exposed at least twice
in one decomposition meeting the ceiling budget. -/
theorem odd_order_simultaneous (m : ℕ) (horder : Fintype.card V = 2 * m + 1)
    (hconn : G.Connected) (h x : V) (hne : h ≠ x)
    (hh : Even (G.degree h)) (hx : Even (G.degree x))
    (hcap : ∀ v, Even (G.degree v) → v ≠ h → v ≠ x → eDegree G v ≤ 3) :
    ∃ D : Decomposition G, D.size ≤ m + 1 ∧
      2 ≤ D.endpointCount h ∧ 2 ≤ D.endpointCount x := by sorry

end Submission
end Gallai
