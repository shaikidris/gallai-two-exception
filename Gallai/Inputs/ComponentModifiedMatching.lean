/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.Inputs.ComponentModifiedFloor

@[expose] public section

/-! # Restoring the opposite matching after the exceptional exchange

The untouched donor can pass, but no remaining recipient is adjacent to it.
This permits the same exact matching restoration on the erased pair set.
-/

namespace Gallai

open scoped Finset

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {u : V}

/-- Decision instance for the modified deletion. -/
noncomputable local instance modifiedMatchingAdj
    (d : ∀ C : (evenSubgraph G).ConnectedComponent, ComponentDeletionChoice G u C)
    (e : V × V) : DecidableRel (componentModifiedDeletion d e).Adj :=
  fun _ _ => Classical.propDecidable _

/-- Decision instance for the original deletion. -/
noncomputable local instance originalMatchingAdj
    (d : ∀ C : (evenSubgraph G).ConnectedComponent, ComponentDeletionChoice G u C) :
    DecidableRel (componentDeletionUnion d).Adj := fun _ _ => Classical.propDecidable _

/-- Original activity survives away from the erased donor. -/
theorem componentModifiedDeletion_active_of_old
    (d : ∀ C : (evenSubgraph G).ConnectedComponent, ComponentDeletionChoice G u C)
    (e : V × V) (he : e ∈ componentDeletionPairs d) (ha : G.Adj u e.1)
    (v : V) (hv : v ≠ e.2) (hp : 0 < (componentDeletionUnion d).degree v) :
    0 < (componentModifiedDeletion d e).degree v := by
  classical
  obtain ⟨w, hw⟩ := ((componentDeletionUnion d).degree_pos_iff_exists_adj v).mp hp
  have hle : componentDeletionUnion d ≤
      componentModifiedDeletion d e ⊔ SimpleGraph.edge e.1 e.2 := by
    rw [componentModifiedDeletion_exchange d e he]
    exact le_sup_left
  rcases hle hw with h | h
  · exact h.degree_pos_left
  · rcases (SimpleGraph.edge_adj ..).mp h with ⟨⟨h, _⟩ | ⟨h, _⟩, _⟩
    · subst v
      have hnew : (componentModifiedDeletion d e).Adj e.1 u := by
        apply Or.inl
        exact (Finset.le_sup (f := SimpleGraph.edge u) (Finset.mem_insert_self _ _))
          ((SimpleGraph.edge_adj ..).mpr ⟨Or.inr ⟨rfl, rfl⟩, ha.ne.symm⟩)
      exact hnew.degree_pos_left
    · exact (hv h).elim

/-- An odd original selected star becomes an even removed star, so the
originally odd hub stays odd in the modified puncture. -/
theorem componentModifiedDeletion_odd_hub
    (d : ∀ C : (evenSubgraph G).ConnectedComponent, ComponentDeletionChoice G u C)
    (hu : Odd (G.degree u)) (e : V × V) (he : e ∈ componentDeletionPairs d)
    (ha : G.Adj u e.1) (hs : Odd #(componentDeletionLeaves d)) :
    Odd ((G \ componentModifiedDeletion d e).degree u) := by
  classical
  have hd := degree_sdiff_add_of_le (componentModifiedDeletion_le d e ha) u
  rw [componentModifiedDeletion_degree_hub d hu e he,
    Finset.card_insert_of_notMem (componentDeletionPairs_fst_not_leaf d e he)] at hd
  rw [Nat.odd_iff] at hu hs ⊢
  omega

/-- Every remaining opposite recipient has no passing neighbours in any
decomposition of the modified puncture. -/
theorem Decomposition.no_passing_modified_pair
    (d : ∀ C : (evenSubgraph G).ConnectedComponent, ComponentDeletionChoice G u C)
    (hu : Odd (G.degree u)) (e : V × V) (he : e ∈ componentDeletionPairs d)
    (ha : G.Adj u e.1) (hs : Odd #(componentDeletionLeaves d))
    (D : Decomposition (G \ componentModifiedDeletion d e))
    (f : V × V) (hf : f ∈ (componentDeletionPairs d).erase e) :
    #{v ∈ (G \ componentModifiedDeletion d e).neighborFinset f.1 |
      D.endpointCount v = 0} = 0 := by
  classical
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro v hv
  obtain ⟨hvn, hz⟩ := Finset.mem_filter.mp hv
  have hvn := ((G \ componentModifiedDeletion d e).mem_neighborFinset f.1 v).mp hvn
  have hp := D.endpointCount_mod_two v
  have hev : Even ((G \ componentModifiedDeletion d e).degree v) := by
    rw [Nat.even_iff]
    omega
  by_cases hvu : v = u
  · subst v
    exact Nat.not_even_iff_odd.mpr
      (componentModifiedDeletion_odd_hub d hu e he ha hs) hev
  · obtain ⟨ho, hk⟩ := componentModifiedDeletion_parity d hu e he ha
    have hg := hk v hvu hev
    have hve : v ≠ e.2 := fun h =>
      componentDeletionPairs_cross_not_adj d f (Finset.mem_erase.mp hf).2 e he
        (Finset.mem_erase.mp hf).1 (h ▸ hvn.1)
    exact Nat.not_even_iff_odd.mpr (ho v hvu
      (componentModifiedDeletion_active_of_old d e he ha v hve
        (componentDeletionPairs_neighbor_active d f (Finset.mem_erase.mp hf).2 v hvn.1 hg))) hev

/-- Restore precisely the nonexceptional opposite pairs, preserving path
count and recording every endpoint transfer. -/
theorem Decomposition.restore_modified_pairs
    (d : ∀ C : (evenSubgraph G).ConnectedComponent, ComponentDeletionChoice G u C)
    (hu : Odd (G.degree u)) (e : V × V) (he : e ∈ componentDeletionPairs d)
    (ha : G.Adj u e.1) (hs : Odd #(componentDeletionLeaves d))
    (D : Decomposition (G \ componentModifiedDeletion d e)) :
    ∃ E : Decomposition ((G \ componentModifiedDeletion d e) ⊔
        ((componentDeletionPairs d).erase e).sup (fun f => SimpleGraph.edge f.1 f.2)),
      E.size = D.size ∧ ∀ v,
        E.endpointCount v + (∑ f ∈ (componentDeletionPairs d).erase e,
          if f.2 = v then 1 else 0) =
        D.endpointCount v + ∑ f ∈ (componentDeletionPairs d).erase e,
          if f.1 = v then 1 else 0 := by
  classical
  have hd := componentDeletionPairs_edge_data d
  apply D.matching_addibility ((componentDeletionPairs d).erase e)
    (fun f hf => (hd f (Finset.mem_erase.mp hf).2).1)
    (fun f hf g hg hfg => componentDeletionPairs_separated d f
      (Finset.mem_erase.mp hf).2 g (Finset.mem_erase.mp hg).2 hfg)
  · intro f hf hmissing
    apply hmissing.2
    apply Or.inr
    exact (Finset.le_sup (f := fun f : V × V => SimpleGraph.edge f.1 f.2) hf)
      ((SimpleGraph.edge_adj ..).mpr
        ⟨Or.inl ⟨rfl, rfl⟩, (hd f (Finset.mem_erase.mp hf).2).1⟩)
  · intro f hf g hg hfg hcross
    exact componentDeletionPairs_cross_not_adj d f (Finset.mem_erase.mp hf).2
      g (Finset.mem_erase.mp hg).2 hfg hcross.1
  · exact fun f hf => D.no_passing_modified_pair d hu e he ha hs f hf
  · intro f hf
    have hdata := hd f (Finset.mem_erase.mp hf).2
    apply D.endpointCount_pos_of_odd_degree
    apply (componentModifiedDeletion_parity d hu e he ha).1 f.2
    · intro h
      exact Nat.not_even_iff_odd.mpr hu (h ▸ hdata.2.2.2.1)
    · apply componentModifiedDeletion_active_of_old d e he ha f.2
      · exact (componentDeletionPairs_separated d f (Finset.mem_erase.mp hf).2
          e he (Finset.mem_erase.mp hf).1).2.2.2
      · exact hdata.2.1.degree_pos_right

end Gallai
