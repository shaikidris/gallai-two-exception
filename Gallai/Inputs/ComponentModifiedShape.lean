/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.Inputs.ComponentModifiedDeletion

@[expose] public section

/-! # Matching shape and active parity of the modified component deletion -/

namespace Gallai

open scoped Finset

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {u : V}

/-- The old and modified deletions differ by exactly the witnessed opposite
edge and its recipient spoke, expressed without cancelling overlapping sets. -/
theorem componentModifiedDeletion_exchange
    (d : ∀ C : (evenSubgraph G).ConnectedComponent, ComponentDeletionChoice G u C)
    (e : V × V) (he : e ∈ componentDeletionPairs d) :
    componentModifiedDeletion d e ⊔ SimpleGraph.edge e.1 e.2 =
      componentDeletionUnion d ⊔ SimpleGraph.edge u e.1 := by
  classical
  have hm : SimpleGraph.edge e.1 e.2 ⊔
      ((componentDeletionPairs d).erase e).sup (fun f => SimpleGraph.edge f.1 f.2) =
      (componentDeletionPairs d).sup (fun f => SimpleGraph.edge f.1 f.2) := by
    rw [← Finset.sup_insert (f := fun f : V × V => SimpleGraph.edge f.1 f.2),
      Finset.insert_erase he]
  rw [componentModifiedDeletion, Finset.sup_insert, componentDeletionUnion_eq_split]
  calc
    _ = ((componentDeletionLeaves d).sup (SimpleGraph.edge u) ⊔
        (SimpleGraph.edge e.1 e.2 ⊔ ((componentDeletionPairs d).erase e).sup
          (fun f => SimpleGraph.edge f.1 f.2))) ⊔ SimpleGraph.edge u e.1 := by ac_rfl
    _ = _ := by rw [hm]

/-- Erasing the witnessed pair removes every matching incidence at its recipient. -/
theorem componentDeletionPairs_erase_not_adj_fst
    (d : ∀ C : (evenSubgraph G).ConnectedComponent, ComponentDeletionChoice G u C)
    (e : V × V) (he : e ∈ componentDeletionPairs d) (v : V) :
    ¬ (((componentDeletionPairs d).erase e).sup
      (fun f => SimpleGraph.edge f.1 f.2)).Adj e.1 v := by
  classical
  intro h
  rw [Finset.sup_eq_iSup] at h
  simp only [SimpleGraph.iSup_adj] at h
  obtain ⟨f, hf, ha⟩ := h
  obtain ⟨hne, hf⟩ := Finset.mem_erase.mp hf
  have hs := componentDeletionPairs_separated d e he f hf hne.symm
  rcases (SimpleGraph.edge_adj ..).mp ha with ⟨⟨h, _⟩ | ⟨h, _⟩, _⟩
  · exact hs.1 h
  · exact hs.2.1 h

/-- Decision instances for removed-degree comparisons. -/
noncomputable local instance modifiedShapeAdj
    (d : ∀ C : (evenSubgraph G).ConnectedComponent, ComponentDeletionChoice G u C)
    (e : V × V) : DecidableRel (componentModifiedDeletion d e).Adj :=
  fun _ _ => Classical.propDecidable _

/-- Decision instance for the unmodified selected graph. -/
noncomputable local instance originalShapeAdj
    (d : ∀ C : (evenSubgraph G).ConnectedComponent, ComponentDeletionChoice G u C) :
    DecidableRel (componentDeletionUnion d).Adj := fun _ _ => Classical.propDecidable _

/-- The modified deletion still has degree at most one away from the hub. -/
theorem componentModifiedDeletion_degree_le_one
    (d : ∀ C : (evenSubgraph G).ConnectedComponent, ComponentDeletionChoice G u C)
    (hu : Odd (G.degree u)) (e : V × V) (he : e ∈ componentDeletionPairs d)
    (v : V) (hvu : v ≠ u) : (componentModifiedDeletion d e).degree v ≤ 1 := by
  classical
  by_cases hve : v = e.1
  · subst v
    rw [← SimpleGraph.card_neighborFinset_eq_degree]
    apply Finset.card_le_one.mpr
    intro p hp q hq
    have only : ∀ w, (componentModifiedDeletion d e).Adj e.1 w → w = u := by
      intro w hw
      rcases hw with hs | hm
      · exact ((star_sup_adj_off_center u _ e.1 w hvu).mp hs).2
      · exact (componentDeletionPairs_erase_not_adj_fst d e he w hm).elim
    exact (only p ((SimpleGraph.mem_neighborFinset ..).mp hp)).trans
      (only q ((SimpleGraph.mem_neighborFinset ..).mp hq)).symm
  · have hle : componentModifiedDeletion d e ≤
        componentDeletionUnion d ⊔ SimpleGraph.edge u e.1 := by
      rw [← componentModifiedDeletion_exchange d e he]
      exact le_sup_left
    have hs : (componentModifiedDeletion d e).neighborFinset v ⊆
        (componentDeletionUnion d).neighborFinset v := by
      intro w hw
      have ha := hle ((SimpleGraph.mem_neighborFinset ..).mp hw)
      apply (SimpleGraph.mem_neighborFinset ..).mpr
      rcases ha with h | h
      · exact h
      · rcases (SimpleGraph.edge_adj ..).mp h with ⟨⟨h, _⟩ | ⟨h, _⟩, _⟩
        · exact (hvu h).elim
        · exact (hve h).elim
    have hc := Finset.card_le_card hs
    have ho := even_component_piece_union_degree_le_one Finset.univ
      (fun C => (d C).graph) u (fun C _ => (d C).supported hu)
      (fun C _ => (d C).degree_le_one hu) v hvu
    have hd : (componentModifiedDeletion d e).degree v ≤ (componentDeletionUnion d).degree v := by
      simpa only [SimpleGraph.card_neighborFinset_eq_degree] using hc
    exact hd.trans ho

/-- Every active off-hub endpoint of the modified deletion was originally even. -/
theorem componentModifiedDeletion_active_even
    (d : ∀ C : (evenSubgraph G).ConnectedComponent, ComponentDeletionChoice G u C)
    (hu : Odd (G.degree u)) (e : V × V) (he : e ∈ componentDeletionPairs d)
    (v : V) (hvu : v ≠ u) (hp : 0 < (componentModifiedDeletion d e).degree v) :
    Even (G.degree v) := by
  classical
  obtain ⟨w, hw⟩ := ((componentModifiedDeletion d e).degree_pos_iff_exists_adj v).mp hp
  have hle : componentModifiedDeletion d e ≤
      componentDeletionUnion d ⊔ SimpleGraph.edge u e.1 := by
    rw [← componentModifiedDeletion_exchange d e he]
    exact le_sup_left
  rcases hle hw with h | h
  · exact even_component_piece_union_active_even Finset.univ (fun C => (d C).graph) u
      (fun C _ => (d C).supported hu) v hvu h.degree_pos_left
  · rcases (SimpleGraph.edge_adj ..).mp h with ⟨⟨h, _⟩ | ⟨h, _⟩, _⟩
    · exact (hvu h).elim
    · exact h.symm ▸ (componentDeletionPairs_edge_data d e he).2.2.1

/-- Erasing the pair also removes every matching incidence at its donor. -/
theorem componentDeletionPairs_erase_not_adj_snd
    (d : ∀ C : (evenSubgraph G).ConnectedComponent, ComponentDeletionChoice G u C)
    (e : V × V) (he : e ∈ componentDeletionPairs d) (v : V) :
    ¬ (((componentDeletionPairs d).erase e).sup
      (fun f => SimpleGraph.edge f.1 f.2)).Adj e.2 v := by
  classical
  intro h
  rw [Finset.sup_eq_iSup] at h
  simp only [SimpleGraph.iSup_adj] at h
  obtain ⟨f, hf, ha⟩ := h
  obtain ⟨hne, hf⟩ := Finset.mem_erase.mp hf
  have hs := componentDeletionPairs_separated d e he f hf hne.symm
  rcases (SimpleGraph.edge_adj ..).mp ha with ⟨⟨h, _⟩ | ⟨h, _⟩, _⟩
  · exact hs.2.2.1 h
  · exact hs.2.2.2 h

/-- The exceptional donor is untouched by the modified deletion. -/
theorem componentModifiedDeletion_donor_degree_zero
    (d : ∀ C : (evenSubgraph G).ConnectedComponent, ComponentDeletionChoice G u C)
    (hu : Odd (G.degree u)) (e : V × V) (he : e ∈ componentDeletionPairs d) :
    (componentModifiedDeletion d e).degree e.2 = 0 := by
  classical
  have hd := componentDeletionPairs_edge_data d e he
  have hnu : e.2 ≠ u := fun h => Nat.not_even_iff_odd.mpr hu (h ▸ hd.2.2.2.1)
  have hnS : e.2 ∉ insert e.1 (componentDeletionLeaves d) := by
    intro h
    rcases Finset.mem_insert.mp h with h | h
    · exact hd.1 h.symm
    · exact hd.2.2.2.2 (componentDeletionLeaves_adj d e.2 h)
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro w hw
  have ha := (SimpleGraph.mem_neighborFinset ..).mp hw
  rcases ha with h | h
  · exact hnS ((star_sup_adj_off_center u _ e.2 w hnu).mp h).1
  · exact componentDeletionPairs_erase_not_adj_snd d e he w h

end Gallai
