/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.Inputs.ComponentSecondCase

@[expose] public section

/-! # The modified selected star and opposite matching

The witnessed opposite pair is retained in G rather than deleted; its recipient
spoke is deleted instead. Other component choices remain unchanged.
-/

namespace Gallai

open scoped Finset

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {u : V}

/-- Replace one opposite-edge deletion by deletion of its recipient spoke. -/
noncomputable def componentModifiedDeletion
    (d : ∀ C : (evenSubgraph G).ConnectedComponent, ComponentDeletionChoice G u C)
    (e : V × V) : SimpleGraph V := by
  classical
  exact (insert e.1 (componentDeletionLeaves d)).sup (SimpleGraph.edge u) ⊔
    ((componentDeletionPairs d).erase e).sup (fun f => SimpleGraph.edge f.1 f.2)

/-- The modified graph contains only edges of G when the witnessed spoke exists. -/
theorem componentModifiedDeletion_le
    (d : ∀ C : (evenSubgraph G).ConnectedComponent, ComponentDeletionChoice G u C)
    (e : V × V) (ha : G.Adj u e.1) : componentModifiedDeletion d e ≤ G := by
  classical
  apply sup_le
  · apply Finset.sup_le
    intro v hv
    apply (SimpleGraph.edge_le_iff G).mpr
    right
    rcases Finset.mem_insert.mp hv with hv | hv
    · exact hv ▸ ha
    · exact componentDeletionLeaves_adj d v hv
  · apply Finset.sup_le
    intro f hf
    exact (SimpleGraph.edge_le_iff G).mpr (Or.inr
      ((componentDeletionUnion_le d) (componentDeletionPairs_edge_data d f
        (Finset.mem_erase.mp hf).2).2.1))

/-- Decision instance for the modified graph's degree statements. -/
noncomputable local instance modifiedDeletionAdj
    (d : ∀ C : (evenSubgraph G).ConnectedComponent, ComponentDeletionChoice G u C)
    (e : V × V) : DecidableRel (componentModifiedDeletion d e).Adj :=
  fun _ _ => Classical.propDecidable _

/-- The modified hub loses precisely the enlarged selected-star size. -/
theorem componentModifiedDeletion_degree_hub
    (d : ∀ C : (evenSubgraph G).ConnectedComponent, ComponentDeletionChoice G u C)
    (hu : Odd (G.degree u)) (e : V × V) (he : e ∈ componentDeletionPairs d) :
    (componentModifiedDeletion d e).degree u = #(insert e.1 (componentDeletionLeaves d)) := by
  classical
  have hne : u ≠ e.1 := fun h => Nat.not_even_iff_odd.mpr hu
    (h.symm ▸ (componentDeletionPairs_edge_data d e he).2.2.1)
  have huS : u ∉ insert e.1 (componentDeletionLeaves d) := by
    simp [hne, componentDeletionLeaves_not_hub d]
  have hM : ((componentDeletionPairs d).erase e).sup (fun f => SimpleGraph.edge f.1 f.2) ≤
      (componentDeletionPairs d).sup (fun f => SimpleGraph.edge f.1 f.2) := by
    apply Finset.sup_le
    intro f hf
    exact Finset.le_sup (f := fun f : V × V => SimpleGraph.edge f.1 f.2)
      (Finset.mem_erase.mp hf).2
  have hn : (componentModifiedDeletion d e).neighborFinset u =
      insert e.1 (componentDeletionLeaves d) := by
    ext v
    rw [SimpleGraph.mem_neighborFinset]
    change ((insert e.1 (componentDeletionLeaves d)).sup (SimpleGraph.edge u)).Adj u v ∨
      (((componentDeletionPairs d).erase e).sup (fun f => SimpleGraph.edge f.1 f.2)).Adj u v ↔ _
    rw [star_sup_adj_center u _ huS]
    exact or_iff_left (fun ha => componentDeletionPairs_not_adj_hub d hu v (hM ha))
  rw [← SimpleGraph.card_neighborFinset_eq_degree, hn]

/-- The witnessed complementary branch gives an even removed hub degree at least four. -/
theorem componentModifiedDeletion_hub_reserve
    (d : ∀ C : (evenSubgraph G).ConnectedComponent, ComponentDeletionChoice G u C)
    (hu : Odd (G.degree u)) (e : V × V) (he : e ∈ componentDeletionPairs d)
    (ho : Odd #(componentDeletionLeaves d)) (hsize : 2 ≤ #(componentDeletionLeaves d)) :
    Even ((componentModifiedDeletion d e).degree u) ∧
      4 ≤ (componentModifiedDeletion d e).degree u := by
  rw [componentModifiedDeletion_degree_hub d hu e he]
  exact componentDeletionPairs_insert_reserve d e he ho hsize

end Gallai
