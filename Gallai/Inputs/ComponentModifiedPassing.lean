/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.Inputs.ComponentModifiedLocal

@[expose] public section

/-! # Localizing actual passing neighbours after modified inward restoration -/

namespace Gallai

open scoped Finset

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {u : V}

/-- The full endpoint vector confines passing neighbours to selected local
leaves and original local donors, including the retained exceptional donor. -/
theorem Decomposition.modified_passing_subset
    (d : ∀ C : (evenSubgraph G).ConnectedComponent, ComponentDeletionChoice G u C)
    (hu : Odd (G.degree u)) (C₀ : (evenSubgraph G).ConnectedComponent)
    (e : V × V) (he : e ∈ (d C₀).pairs) (ha : G.Adj u e.1)
    (D : Decomposition (G \ componentModifiedDeletion d e))
    {K : SimpleGraph V} [DecidableRel K.Adj] (hKG : K ≤ G) (Q : Decomposition K)
    (B : Finset V) (hB : B ⊆ insert e.1 (componentDeletionLeaves d))
    (hqu : 0 < Q.endpointCount u)
    (hbal : ∀ w, Q.endpointCount w + (if w ∈ B then 1 else 0) +
        (∑ f ∈ (componentDeletionPairs d).erase e, if f.2 = w then 1 else 0) =
      D.endpointCount w +
        (∑ f ∈ (componentDeletionPairs d).erase e, if f.1 = w then 1 else 0) +
        if u = w then #B else 0)
    (C : (evenSubgraph G).ConnectedComponent) (v : V)
    (hv : v ∈ componentModifiedLocalLeaves d C₀ e C) :
    {w ∈ K.neighborFinset v | Q.endpointCount w = 0} ⊆
      (((componentModifiedLocalLeaves d C₀ e C ∩ B) ∪
        (d C).pairs.image Prod.snd).erase v) := by
  classical
  have heg := componentDeletionPairs_mem_of_local d C₀ e he
  intro w hw
  obtain ⟨hvw, hz⟩ := Finset.mem_filter.mp hw
  have hvw := (K.mem_neighborFinset v w).mp hvw
  have hwu : w ≠ u := fun h => by subst w; omega
  have hloss : w ∈ B ∨ ∃ f ∈ componentDeletionPairs d, f.2 = w := by
    by_cases hwe : w = e.2
    · exact Or.inr ⟨e, heg, hwe.symm⟩
    have hp := D.endpointCount_pos_of_odd_degree w
      (componentModifiedLocalLeaves_neighbor_odd d hu C₀ e he ha C v hv
        w (hKG hvw) hwu hwe)
    by_cases hwB : w ∈ B
    · exact Or.inl hwB
    right
    by_contra hn
    have hsum : (∑ f ∈ (componentDeletionPairs d).erase e,
        if f.2 = w then 1 else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro f hf
      have hfw : f.2 ≠ w := fun h => hn ⟨f, (Finset.mem_erase.mp hf).2, h⟩
      simp [hfw]
    have h := hbal w
    simp only [hz, hwB, if_false, hsum] at h
    omega
  have hwEven : Even (G.degree w) := by
    rcases hloss with h | ⟨f, hf, hfw⟩
    · exact componentModifiedLeaves_even d e heg w (hB h)
    · exact hfw ▸ (componentDeletionPairs_edge_data d f hf).2.2.2.1
  have hwC := mem_evenComponent_of_adj C
    (componentModifiedLocalLeaves_supported d C₀ e he C v hv) (hKG hvw) hwEven
  apply Finset.mem_erase.mpr
  refine ⟨hvw.ne.symm, ?_⟩
  rcases hloss with h | ⟨f, hf, hfw⟩
  · exact Finset.mem_union_left _ (Finset.mem_inter.mpr
      ⟨componentModifiedLocalLeaves_of_global d C₀ e he C w hwC (hB h), h⟩)
  · exact Finset.mem_union_right _ (Finset.mem_image.mpr
      ⟨f, componentDeletionPairs_local_of_snd d C f hf (hfw.symm ▸ hwC), hfw⟩)

end Gallai
