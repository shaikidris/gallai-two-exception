/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.Inputs.ComponentMatchingRestore
public import Gallai.Structure.StarPuncture

@[expose] public section

/-! # Identifying the restored graph and the source cardinality case

After the opposite matching is restored, precisely the selected hub star
remains deleted. Even star size makes the originally odd hub remain odd.
-/

namespace Gallai

open scoped Finset

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {u : V}

/-- Degree decision for the actual component union. -/
noncomputable local instance componentMatchingGraphAdj
    (d : ∀ C : (evenSubgraph G).ConnectedComponent, ComponentDeletionChoice G u C) :
    DecidableRel (componentDeletionUnion d).Adj := fun _ _ => Classical.propDecidable _

/-- Every selected edge is an original edge. -/
theorem componentDeletionUnion_le
    (d : ∀ C : (evenSubgraph G).ConnectedComponent, ComponentDeletionChoice G u C) :
    componentDeletionUnion d ≤ G := by
  classical
  exact Finset.sup_le (fun C _ => (d C).graph_le)

/-- The selected star never has the hub as a leaf. -/
theorem componentDeletionLeaves_not_hub
    (d : ∀ C : (evenSubgraph G).ConnectedComponent, ComponentDeletionChoice G u C) :
    u ∉ componentDeletionLeaves d := by
  classical
  intro h
  obtain ⟨C, _, h⟩ := Finset.mem_biUnion.mp h
  exact ((d C).leaf_data u h).1.ne rfl

/-- The opposite matching has no edge incident with the originally odd hub. -/
theorem componentDeletionPairs_not_adj_hub
    (d : ∀ C : (evenSubgraph G).ConnectedComponent, ComponentDeletionChoice G u C)
    (hu : Odd (G.degree u)) (v : V) :
    ¬ ((componentDeletionPairs d).sup (fun e => SimpleGraph.edge e.1 e.2)).Adj u v := by
  classical
  intro h
  rw [Finset.sup_eq_iSup] at h
  simp only [SimpleGraph.iSup_adj] at h
  obtain ⟨e, he, ha⟩ := h
  have hd := componentDeletionPairs_edge_data d e he
  rcases (SimpleGraph.edge_adj ..).mp ha with ⟨⟨h, _⟩ | ⟨h, _⟩, _⟩
  · exact Nat.not_even_iff_odd.mpr hu (h.symm ▸ hd.2.2.1)
  · exact Nat.not_even_iff_odd.mpr hu (h.symm ▸ hd.2.2.2.1)

/-- The removed degree at the hub is exactly the number of selected spokes. -/
theorem componentDeletionUnion_degree_hub
    (d : ∀ C : (evenSubgraph G).ConnectedComponent, ComponentDeletionChoice G u C)
    (hu : Odd (G.degree u)) :
    (componentDeletionUnion d).degree u = #(componentDeletionLeaves d) := by
  classical
  have hn : (componentDeletionUnion d).neighborFinset u = componentDeletionLeaves d := by
    ext v
    rw [SimpleGraph.mem_neighborFinset, componentDeletionUnion_eq_split,
      SimpleGraph.sup_adj, star_sup_adj_center u _ (componentDeletionLeaves_not_hub d)]
    simp [componentDeletionPairs_not_adj_hub d hu v]
  rw [← SimpleGraph.card_neighborFinset_eq_degree, hn]

/-- Even selected-star size retains odd parity at the hub of the puncture. -/
theorem componentDeletionUnion_odd_hub_of_even_leaves
    (d : ∀ C : (evenSubgraph G).ConnectedComponent, ComponentDeletionChoice G u C)
    (hu : Odd (G.degree u)) (hs : Even #(componentDeletionLeaves d)) :
    Odd ((G \ componentDeletionUnion d).degree u) := by
  have hd := degree_sdiff_add_of_le (componentDeletionUnion_le d) u
  rw [componentDeletionUnion_degree_hub d hu] at hd
  rw [Nat.odd_iff] at hu ⊢
  rw [Nat.even_iff] at hs
  omega

/-- Restoring the opposite matching leaves exactly the selected star deleted. -/
theorem componentDeletionUnion_restore_pairs
    (d : ∀ C : (evenSubgraph G).ConnectedComponent, ComponentDeletionChoice G u C)
    (hu : Odd (G.degree u)) :
    (G \ componentDeletionUnion d) ⊔
        (componentDeletionPairs d).sup (fun e => SimpleGraph.edge e.1 e.2) =
      starPuncture G u (componentDeletionLeaves d) := by
  classical
  let S := (componentDeletionLeaves d).sup (SimpleGraph.edge u)
  let M := (componentDeletionPairs d).sup (fun e => SimpleGraph.edge e.1 e.2)
  have hM : M ≤ G := by
    apply le_trans (show M ≤ componentDeletionUnion d from ?_) (componentDeletionUnion_le d)
    rw [componentDeletionUnion_eq_split]
    exact le_sup_right
  have hdis : ∀ v w, S.Adj v w → ¬ M.Adj v w := by
    intro v w hS hM'
    by_cases hv : v = u
    · subst v
      exact componentDeletionPairs_not_adj_hub d hu w hM'
    · have hw : w = u := ((star_sup_adj_off_center u _ v w hv).mp hS).2
      subst w
      exact componentDeletionPairs_not_adj_hub d hu v hM'.symm
  rw [componentDeletionUnion_eq_split]
  ext v w
  change ((G.Adj v w ∧ ¬ (S.Adj v w ∨ M.Adj v w)) ∨ M.Adj v w) ↔
    G.Adj v w ∧ ¬ S.Adj v w
  constructor
  · rintro (⟨hG, hn⟩ | hm)
    · exact ⟨hG, fun hs => hn (Or.inl hs)⟩
    · exact ⟨hM hm, fun hs => hdis v w hs hm⟩
  · rintro ⟨hG, hn⟩
    by_cases hm : M.Adj v w
    · exact Or.inr hm
    · exact Or.inl ⟨hG, fun h => h.elim hn hm⟩

/-- Source Subclaim 5.1's matching stage, with the original star-cardinality
alternative and the exact remaining graph and endpoint vector. -/
theorem Decomposition.restore_component_pairs_to_star
    (d : ∀ C : (evenSubgraph G).ConnectedComponent, ComponentDeletionChoice G u C)
    (hu : Odd (G.degree u)) (D : Decomposition (G \ componentDeletionUnion d))
    (hcase : (∀ e ∈ componentDeletionPairs d, ¬ G.Adj u e.1) ∨
      Even #(componentDeletionLeaves d)) :
    ∃ E : Decomposition (starPuncture G u (componentDeletionLeaves d)),
      E.size = D.size ∧ ∀ v,
        E.endpointCount v + (∑ e ∈ componentDeletionPairs d, if e.2 = v then 1 else 0) =
          D.endpointCount v + ∑ e ∈ componentDeletionPairs d, if e.1 = v then 1 else 0 := by
  have h := D.restore_component_pairs d hu
    (hcase.imp id (componentDeletionUnion_odd_hub_of_even_leaves d hu))
  rwa [componentDeletionUnion_restore_pairs d hu] at h

end Gallai
