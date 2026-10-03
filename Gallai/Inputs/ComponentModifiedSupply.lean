/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.Inputs.ComponentModifiedMatching

@[expose] public section

/-! # The enlarged-star interface after modified matching restoration -/

namespace Gallai

open scoped Finset

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {u : V}

/-- Decision instance for the modified removed graph. -/
noncomputable local instance modifiedSupplyAdj
    (d : ∀ C : (evenSubgraph G).ConnectedComponent, ComponentDeletionChoice G u C)
    (e : V × V) : DecidableRel (componentModifiedDeletion d e).Adj :=
  fun _ _ => Classical.propDecidable _

/-- Restoring the erased opposite matching leaves exactly the enlarged star. -/
theorem componentModifiedDeletion_restore_pairs
    (d : ∀ C : (evenSubgraph G).ConnectedComponent, ComponentDeletionChoice G u C)
    (hu : Odd (G.degree u)) (e : V × V) (ha : G.Adj u e.1) :
    (G \ componentModifiedDeletion d e) ⊔
        ((componentDeletionPairs d).erase e).sup (fun f => SimpleGraph.edge f.1 f.2) =
      starPuncture G u (insert e.1 (componentDeletionLeaves d)) := by
  classical
  let S := (insert e.1 (componentDeletionLeaves d)).sup (SimpleGraph.edge u)
  let M := ((componentDeletionPairs d).erase e).sup (fun f => SimpleGraph.edge f.1 f.2)
  have hM : M ≤ G := le_trans le_sup_right (componentModifiedDeletion_le d e ha)
  have hsub : M ≤ (componentDeletionPairs d).sup (fun f => SimpleGraph.edge f.1 f.2) := by
    apply Finset.sup_le
    intro f hf
    exact Finset.le_sup (f := fun f : V × V => SimpleGraph.edge f.1 f.2)
      (Finset.mem_erase.mp hf).2
  have hdis : ∀ v w, S.Adj v w → ¬ M.Adj v w := by
    intro v w hS hM'
    by_cases hv : v = u
    · subst v
      exact componentDeletionPairs_not_adj_hub d hu w (hsub hM')
    · have hw : w = u := ((star_sup_adj_off_center u _ v w hv).mp hS).2
      subst w
      exact componentDeletionPairs_not_adj_hub d hu v (hsub hM'.symm)
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

/-- The modified matching stage on its exact output graph and endpoint vector. -/
theorem Decomposition.restore_modified_pairs_to_star
    (d : ∀ C : (evenSubgraph G).ConnectedComponent, ComponentDeletionChoice G u C)
    (hu : Odd (G.degree u)) (e : V × V) (he : e ∈ componentDeletionPairs d)
    (ha : G.Adj u e.1) (hs : Odd #(componentDeletionLeaves d))
    (D : Decomposition (G \ componentModifiedDeletion d e)) :
    ∃ E : Decomposition (starPuncture G u (insert e.1 (componentDeletionLeaves d))),
      E.size = D.size ∧ ∀ v,
        E.endpointCount v + (∑ f ∈ (componentDeletionPairs d).erase e,
          if f.2 = v then 1 else 0) =
        D.endpointCount v + ∑ f ∈ (componentDeletionPairs d).erase e,
          if f.1 = v then 1 else 0 := by
  have h := D.restore_modified_pairs d hu e he ha hs
  rwa [componentModifiedDeletion_restore_pairs d hu e ha] at h

/-- Every original hub neighbour is odd in the modified puncture, including
those whose spokes have been deleted. The exceptional donor is not one. -/
theorem componentModifiedDeletion_odd_neighbor
    (d : ∀ C : (evenSubgraph G).ConnectedComponent, ComponentDeletionChoice G u C)
    (hu : Odd (G.degree u)) (e : V × V) (he : e ∈ componentDeletionPairs d)
    (ha : G.Adj u e.1) (v : V) (hv : G.Adj u v) :
    Odd ((G \ componentModifiedDeletion d e).degree v) := by
  obtain ⟨ho, hk⟩ := componentModifiedDeletion_parity d hu e he ha
  by_cases hEven : Even (G.degree v)
  · exact ho v hv.ne.symm (componentModifiedDeletion_covers d hu e he ha v hEven hv)
  · exact Nat.not_even_iff_odd.mp (fun h => hEven (hk v hv.ne.symm h))

/-- The same matching witness preserves the hub count and supplies all
original hub neighbours for inward restoration of the enlarged star. -/
theorem Decomposition.modified_matching_supply
    (d : ∀ C : (evenSubgraph G).ConnectedComponent, ComponentDeletionChoice G u C)
    (hu : Odd (G.degree u)) (e : V × V) (he : e ∈ componentDeletionPairs d)
    (ha : G.Adj u e.1) (D : Decomposition (G \ componentModifiedDeletion d e))
    (E : Decomposition (starPuncture G u (insert e.1 (componentDeletionLeaves d))))
    (hb : ∀ v,
      E.endpointCount v + (∑ f ∈ (componentDeletionPairs d).erase e,
        if f.2 = v then 1 else 0) =
      D.endpointCount v + ∑ f ∈ (componentDeletionPairs d).erase e,
        if f.1 = v then 1 else 0) :
    E.endpointCount u = D.endpointCount u ∧
      ∀ v, G.Adj u v → 0 < E.endpointCount v := by
  classical
  have hz₁ : (∑ f ∈ (componentDeletionPairs d).erase e,
      if f.1 = u then 1 else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro f hf
    have hd := componentDeletionPairs_edge_data d f (Finset.mem_erase.mp hf).2
    have hn : f.1 ≠ u := fun h => Nat.not_even_iff_odd.mpr hu (h ▸ hd.2.2.1)
    simp [hn]
  have hz₂ : (∑ f ∈ (componentDeletionPairs d).erase e,
      if f.2 = u then 1 else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro f hf
    have hd := componentDeletionPairs_edge_data d f (Finset.mem_erase.mp hf).2
    have hn : f.2 ≠ u := fun h => Nat.not_even_iff_odd.mpr hu (h ▸ hd.2.2.2.1)
    simp [hn]
  constructor
  · simpa [hz₁, hz₂] using hb u
  · intro v huv
    have hz : (∑ f ∈ (componentDeletionPairs d).erase e,
        if f.2 = v then 1 else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro f hf
      have hd := componentDeletionPairs_edge_data d f (Finset.mem_erase.mp hf).2
      have hn : f.2 ≠ v := fun h => hd.2.2.2.2 (h.symm ▸ huv)
      simp [hn]
    have hp := D.endpointCount_pos_of_odd_degree v
      (componentModifiedDeletion_odd_neighbor d hu e he ha v huv)
    have h := hb v
    rw [hz] at h
    omega

end Gallai
