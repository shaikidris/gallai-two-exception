/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.Inputs.UniqueEvenComponent
public import Gallai.Operations.ComponentAssembly

@[expose] public section

/-! # Floor budgets for components of a proper puncture

The punctured graph's even-degree cap is an explicit source hypothesis.
SET exclusion and strict smaller-edge induction produce an actual witness.
-/

namespace Gallai

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G H : SimpleGraph V} [DecidableRel G.Adj] [DecidableRel H.Adj]

/-- Inducing any vertex part of a proper subgraph strictly decreases edge count. -/
theorem induced_proper_subgraph_edge_count_lt (hlt : H < G)
    (S : Set V) [DecidablePred (· ∈ S)] :
    (H.induce S).edgeFinset.card < G.edgeFinset.card := by
  classical
  have hle : (H.induce S).edgeFinset.card ≤ H.edgeFinset.card := by
    have hm := congrArg Finset.card
      (SimpleGraph.map_edgeFinset_induce (G := H) (s := S))
    rw [Finset.card_map] at hm
    rw [hm]
    exact Finset.card_le_card Finset.inter_subset_left
  exact hle.trans_lt (Finset.card_lt_card (SimpleGraph.edgeFinset_strict_mono hlt))

/-- Guarded minimality gives a floor decomposition of each non-SET component
of a proper puncture. The cap is required on the puncture, not just on G. -/
theorem proper_puncture_component_floor (hlt : H < G)
    (hcap : ∀ v, Even (H.degree v) → eDegree H v ≤ 3)
    (hmin : ∀ (U : Set V) [DecidablePred (· ∈ U)]
      (J : SimpleGraph U) [DecidableRel J.Adj],
      J.edgeFinset.card < G.edgeFinset.card → J.Connected →
      (∀ v, Even (J.degree v) → eDegree J v ≤ 3) →
      HasPathBudget J (Fintype.card U / 2) ∨ IsSET J)
    (C : H.ConnectedComponent) [DecidablePred (· ∈ C.supp)]
    (hnot : ¬ IsSET (H.induce C.supp)) :
    HasPathBudget (H.induce C.supp) (Fintype.card C.supp / 2) := by
  have hc := even_degree_cap_induce_of_closed H C.supp
    (fun _ hv _ hw => C.mem_supp_of_adj_mem_supp hv hw) 3 hcap
  rcases hmin C.supp (H.induce C.supp)
      (induced_proper_subgraph_edge_count_lt hlt C.supp)
      C.connected_toSimpleGraph hc with h | h
  · exact h
  · exact (hnot h).elim

/-- All non-SET components of a proper capped puncture assemble to a floor
decomposition. No connectedness of the puncture is assumed. -/
theorem proper_puncture_floor (hlt : H < G)
    (hcap : ∀ v, Even (H.degree v) → eDegree H v ≤ 3)
    (hmin : ∀ (U : Set V) [DecidablePred (· ∈ U)]
      (J : SimpleGraph U) [DecidableRel J.Adj],
      J.edgeFinset.card < G.edgeFinset.card → J.Connected →
      (∀ v, Even (J.degree v) → eDegree J v ≤ 3) →
      HasPathBudget J (Fintype.card U / 2) ∨ IsSET J)
    (hnot : ∀ C : H.ConnectedComponent, ¬ IsSET (H.induce C.supp)) :
    HasPathBudget H (Fintype.card V / 2) := by
  exact floor_of_components H fun C => proper_puncture_component_floor hlt hcap hmin C (hnot C)

end Gallai
