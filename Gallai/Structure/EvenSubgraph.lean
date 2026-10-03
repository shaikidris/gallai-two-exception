/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Algebra.Ring.Parity

@[expose] public section

/-!
# The induced even-vertex graph and its external boundary

Evenness always refers to degree in the original graph. The induced graph
uses the subtype of all even vertices, including isolates. Its components
cannot have even external neighbours in the original graph. This supplies
the odd-anchor condition for whole-bowtie removal, without a degree cap.
-/

namespace Gallai

open scoped Finset

universe u

variable {V : Type u} [Fintype V]

/-- Vertices having even degree in the original graph, including isolated vertices. -/
abbrev evenVertices (G : SimpleGraph V) [DecidableRel G.Adj] : Set V :=
  {v | Even (G.degree v)}

/-- The actual induced graph on the subtype of even-degree vertices. -/
abbrev evenSubgraph (G : SimpleGraph V) [DecidableRel G.Adj] :
    SimpleGraph (evenVertices G) :=
  G.induce (evenVertices G)

/-- The canonical inclusion of the induced even-vertex graph into the
ambient graph.  It lets shortest even-subgraph walks be used as ordinary
walks without changing their vertices or length. -/
def evenSubgraphInclusion (G : SimpleGraph V) [DecidableRel G.Adj] :
    evenSubgraph G →g G where
  toFun := Subtype.val
  map_rel' := by
    intro u v huv
    exact huv

@[simp] theorem evenSubgraphInclusion_apply {G : SimpleGraph V} [DecidableRel G.Adj]
    (v : evenVertices G) :
    evenSubgraphInclusion G v = (v : V) := rfl

/-- Original neighbours whose original degree is even. -/
def evenNeighbors (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) : Finset V :=
  (G.neighborFinset v).filter fun w => Even (G.degree w)

/-- Number of even neighbours; at even vertices this is the induced even-graph degree. -/
def eDegree (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) : ℕ :=
  #(evenNeighbors G v)

variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Membership retains both the original adjacency and the neighbour's original parity. -/
@[simp] theorem mem_evenNeighbors (v w : V) :
    w ∈ evenNeighbors G v ↔ G.Adj v w ∧ Even (G.degree w) := by
  simp [evenNeighbors]

/-- The neighbour-count definition is exactly the degree in the induced even graph. -/
theorem eDegree_eq_induced_degree [DecidableEq V] (v : evenVertices G) :
    eDegree G v = (evenSubgraph G).degree v := by
  have h := congrArg Finset.card (G.map_neighborFinset_induce (s := evenVertices G) v)
  have hset : G.neighborFinset v ∩ (evenVertices G).toFinset = evenNeighbors G v := by
    ext w
    simp [evenNeighbors]
  rw [hset] at h
  simpa [eDegree] using h.symm

/-- The even-neighbour count cannot exceed the ordinary degree. -/
theorem eDegree_le_degree (v : V) : eDegree G v ≤ G.degree v := by
  exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq
    (G.card_neighborFinset_eq_degree v)

/-- Passing to a subgraph cannot increase the even-neighbour count provided
every vertex that remains even was already even in the ambient graph.  The
parity hypothesis is deliberately pointwise: puncture consumers establish it
only for their literal surviving-even profile. -/
theorem eDegree_le_of_subgraph_of_even_preservation
    {J : SimpleGraph V} [DecidableRel J.Adj] (hsub : J ≤ G)
    (hEven : ∀ w : V, Even (J.degree w) → Even (G.degree w)) (v : V) :
    eDegree J v ≤ eDegree G v := by
  apply Finset.card_le_card
  intro w hw
  obtain ⟨hvw, hwEven⟩ := (mem_evenNeighbors (G := J) v w).mp hw
  exact (mem_evenNeighbors (G := G) v w).mpr ⟨hsub hvw, hEven w hwEven⟩

/-- A vertex with two retained even neighbours and two distinct additional
ambient even neighbours has ambient E-degree at least four.  This is the
cardinality transfer used when a SET triangle in an auxiliary graph is viewed
inside the original graph: its two internal even neighbours are disjoint from
two affected vertices that were originally even but became odd. -/
theorem eDegree_ge_four_of_two_extra_evenNeighbors [DecidableEq V]
    {J : SimpleGraph V} [DecidableRel J.Adj] (v x y : V)
    (hsub : evenNeighbors J v ⊆ evenNeighbors G v)
    (hJ : (evenNeighbors J v).card = 2)
    (hx : x ∈ evenNeighbors G v) (hy : y ∈ evenNeighbors G v)
    (hxJ : x ∉ evenNeighbors J v) (hyJ : y ∉ evenNeighbors J v)
    (hxy : x ≠ y) :
    4 ≤ eDegree G v := by
  let S := evenNeighbors J v
  let T := evenNeighbors G v
  have hpair : ({x, y} : Finset V) ⊆ T := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with hzx | hzy
    · subst z
      exact hx
    · subst z
      exact hy
  have hdisjoint : Disjoint S ({x, y} : Finset V) := by
    rw [Finset.disjoint_left]
    intro z hzS hzpair
    simp only [Finset.mem_insert, Finset.mem_singleton] at hzpair
    rcases hzpair with hzx | hzy
    · exact hxJ (hzx ▸ hzS)
    · exact hyJ (hzy ▸ hzS)
  have hunion : S ∪ ({x, y} : Finset V) ⊆ T :=
    Finset.union_subset hsub hpair
  have hcard : 4 ≤ T.card := by
    have hle := Finset.card_le_card hunion
    rw [Finset.card_union_of_disjoint hdisjoint, hJ] at hle
    have hp : ({x, y} : Finset V).card = 2 := by simp [hxy]
    omega
  exact hcard

/-- Four pairwise distinct even-neighbour witnesses force E-degree at least
four.  This direct witness form is convenient when the first two neighbours
come from an induced SET component and the latter two are affected vertices
of the original graph. -/
theorem eDegree_ge_four_of_four_distinct_evenNeighbors [DecidableEq V]
    (v w₁ w₂ x y : V)
    (hw₁ : w₁ ∈ evenNeighbors G v) (hw₂ : w₂ ∈ evenNeighbors G v)
    (hx : x ∈ evenNeighbors G v) (hy : y ∈ evenNeighbors G v)
    (hw₁w₂ : w₁ ≠ w₂) (hw₁x : w₁ ≠ x) (hw₁y : w₁ ≠ y)
    (hw₂x : w₂ ≠ x) (hw₂y : w₂ ≠ y) (hxy : x ≠ y) :
    4 ≤ eDegree G v := by
  let S : Finset V := insert w₁ (insert w₂ (insert x {y}))
  have hS : S ⊆ evenNeighbors G v := by
    intro z hz
    simp only [S, Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with hzw₁ | hzw₂ | hzx | hzy
    · simpa [hzw₁] using hw₁
    · simpa [hzw₂] using hw₂
    · simpa [hzx] using hx
    · simpa [hzy] using hy
  have hcardS : S.card = 4 := by
    simp only [S, Finset.card_insert_of_notMem]
    simp [hw₁w₂, hw₁x, hw₁y, hw₂x, hw₂y, hxy]
  change 4 ≤ (evenNeighbors G v).card
  rw [← hcardS]
  exact Finset.card_le_card hS

/-- Vertices of an even-graph component, regarded in the original vertex type. -/
def evenComponentVertices (K : (evenSubgraph G).ConnectedComponent) : Set V :=
  Subtype.val '' K.supp

/-- Every vertex of an even component has even degree in the original graph. -/
theorem even_of_mem_evenComponent (K : (evenSubgraph G).ConnectedComponent)
    {v : V} (hv : v ∈ evenComponentVertices K) : Even (G.degree v) := by
  obtain ⟨w, _, rfl⟩ := hv
  exact w.property

/-- A whole even component absorbs every even original neighbour of its vertices. -/
theorem mem_evenComponent_of_adj (K : (evenSubgraph G).ConnectedComponent)
    {v w : V} (hv : v ∈ evenComponentVertices K) (hvw : G.Adj v w)
    (hw : Even (G.degree w)) : w ∈ evenComponentVertices K := by
  obtain ⟨v, hv, rfl⟩ := hv
  exact ⟨⟨w, hw⟩, (K.mem_supp_congr_adj (show (evenSubgraph G).Adj v ⟨w, hw⟩
    from hvw)).mp hv, rfl⟩

/-- External anchors of a whole even component are odd in the original graph. -/
theorem odd_of_adj_evenComponent (K : (evenSubgraph G).ConnectedComponent)
    {v w : V} (hv : v ∈ evenComponentVertices K) (hvw : G.Adj v w)
    (hw : w ∉ evenComponentVertices K) : Odd (G.degree w) := by
  apply Nat.not_even_iff_odd.mp
  intro he
  exact hw (mem_evenComponent_of_adj K hv hvw he)

end Gallai
