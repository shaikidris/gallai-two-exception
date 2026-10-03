/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.Inputs.UniqueEvenNeighbor
public import Gallai.Structure.EvenSubgraphInduce

@[expose] public section

/-! # Recipient component of a unique-even-neighbour puncture

The component has its own vertex type, so outside vertices are not counted
as even isolates. The smaller-graph hypothesis remains explicitly guarded.
-/

namespace Gallai

universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Every induced part of a genuine edge puncture has strictly fewer edges. -/
theorem induced_puncture_edge_count_lt (x y : V) (hxy : G.Adj x y)
    (S : Set V) [DecidablePred (· ∈ S)] :
    ((G.deleteEdges {s(x, y)}).induce S).edgeFinset.card < G.edgeFinset.card := by
  classical
  have hle : ((G.deleteEdges {s(x, y)}).induce S).edgeFinset.card ≤
      (G.deleteEdges {s(x, y)}).edgeFinset.card := by
    have hm := congrArg Finset.card
      (SimpleGraph.map_edgeFinset_induce (G := G.deleteEdges {s(x, y)}) (s := S))
    rw [Finset.card_map] at hm
    rw [hm]
    exact Finset.card_le_card Finset.inter_subset_left
  apply hle.trans_lt
  apply Finset.card_lt_card
  apply SimpleGraph.edgeFinset_strict_mono
  refine lt_of_le_not_ge (G.deleteEdges_le _) ?_
  intro hg
  exact (SimpleGraph.deleteEdges_adj.mp (hg hxy)).2 rfl

/-- A neighbour-closed puncture part containing the recipient cannot be SET. -/
theorem unique_even_neighbor_closed_not_set (x y : V) (hxy : G.Adj x y)
    (hy : Even (G.degree y))
    (hu : ∀ v, G.Adj x v → Even (G.degree v) → v = y)
    (S : Set V) [DecidablePred (· ∈ S)] (hx : x ∈ S)
    (hs : ∀ v ∈ S, (G.deleteEdges {s(x, y)}).neighborSet v ⊆ S) :
    ¬ IsSET ((G.deleteEdges {s(x, y)}).induce S) := by
  intro h
  have hd := eDegree_induce_of_closed (G.deleteEdges {s(x, y)}) S hs ⟨x, hx⟩
  have hz := unique_even_neighbor_puncture_eDegree x y hxy hy hu
  have hzero : eDegree ((G.deleteEdges {s(x, y)}).induce S) ⟨x, hx⟩ = 0 := hd.trans hz
  have hbound := h.eDegree_two_or_three ⟨x, hx⟩
  rw [hzero] at hbound
  omega

/-- The actual puncture component containing x is excluded from SET. -/
theorem unique_even_neighbor_component_not_set (x y : V) (hxy : G.Adj x y)
    (hy : Even (G.degree y))
    (hu : ∀ v, G.Adj x v → Even (G.degree v) → v = y)
    (C : (G.deleteEdges {s(x, y)}).ConnectedComponent)
    [DecidablePred (· ∈ C.supp)] (hx : x ∈ C.supp) :
    ¬ IsSET ((G.deleteEdges {s(x, y)}).induce C.supp) := by
  apply unique_even_neighbor_closed_not_set x y hxy hy hu C.supp hx
  intro v hv w hw
  exact C.mem_supp_of_adj_mem_supp hv hw

/-- Bounded induction supplies an actual floor decomposition of the recipient
component; connectivity, cap and edge decrease are all derived here. -/
theorem unique_even_neighbor_component_floor (x y : V) (hxy : G.Adj x y)
    (hy : Even (G.degree y))
    (hu : ∀ v, G.Adj x v → Even (G.degree v) → v = y)
    (hcap : ∀ v, Even (G.degree v) → eDegree G v ≤ 3)
    (C : (G.deleteEdges {s(x, y)}).ConnectedComponent)
    [DecidablePred (· ∈ C.supp)] (hx : x ∈ C.supp)
    (hmin : ∀ (U : Set V) [DecidablePred (· ∈ U)]
      (J : SimpleGraph U) [DecidableRel J.Adj],
      J.edgeFinset.card < G.edgeFinset.card → J.Connected →
      (∀ v, Even (J.degree v) → eDegree J v ≤ 3) →
      HasPathBudget J (Fintype.card U / 2) ∨ IsSET J) :
    HasPathBudget ((G.deleteEdges {s(x, y)}).induce C.supp) (Fintype.card C.supp / 2) := by
  have hc := even_degree_cap_induce_of_closed (G.deleteEdges {s(x, y)}) C.supp
    (fun _ hv _ hw => C.mem_supp_of_adj_mem_supp hv hw) 3
    (unique_even_neighbor_puncture_cap x y hxy hy hu 3 hcap)
  rcases hmin C.supp ((G.deleteEdges {s(x, y)}).induce C.supp)
      (induced_puncture_edge_count_lt x y hxy C.supp) C.connected_toSimpleGraph hc with h | h
  · exact h
  · exact (unique_even_neighbor_component_not_set x y hxy hy hu C hx h).elim

end Gallai
