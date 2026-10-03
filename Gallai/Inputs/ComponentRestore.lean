/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.Inputs.ComponentPassingBounds
public import Gallai.Inputs.TwoTierStar

@[expose] public section

/-! # Restoring the first actual component puncture without a path-count loss -/

namespace Gallai

open scoped Finset

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {u : V}

/-- Decision instance for the initial puncture. -/
noncomputable local instance componentRestoreUnionAdj
    (d : ∀ C : (evenSubgraph G).ConnectedComponent, ComponentDeletionChoice G u C) :
    DecidableRel (componentDeletionUnion d).Adj := fun _ _ => Classical.propDecidable _

/-- Restore every selected component edge under the first source-case
condition, using actual matching, half-star, passing and reserve proofs.
The result is a decomposition of the original graph, not an auxiliary. -/
theorem Decomposition.restore_component_puncture
    (d : ∀ C : (evenSubgraph G).ConnectedComponent, ComponentDeletionChoice G u C)
    (hu : Odd (G.degree u)) (D : Decomposition (G \ componentDeletionUnion d))
    (hcase : (∀ e ∈ componentDeletionPairs d, ¬ G.Adj u e.1) ∨
      Even #(componentDeletionLeaves d))
    (htwo : ∃ C E : (evenSubgraph G).ConnectedComponent, C ≠ E ∧
      (∃ v : evenVertices G, v ∈ C.supp ∧ G.Adj u v) ∧
      (∃ v : evenVertices G, v ∈ E.supp ∧ G.Adj u v)) :
    ∃ E : Decomposition G, E.size = D.size := by
  classical
  have ht := componentDeletionLeaves_two_touched d htwo
  obtain ⟨C, _, _, ⟨b, hb⟩, _⟩ := ht
  have hbS : b ∈ componentDeletionLeaves d :=
    Finset.mem_biUnion.mpr ⟨C, Finset.mem_univ C, hb⟩
  obtain ⟨B, hB, _, _, Q, hQ, hbal, hqu, hreserve⟩ :=
    D.restore_component_half_star d hu hcase b hbS
  let S := componentDeletionLeaves d
  let T := componentDifficultLeaves d B
  let R := (S \ B) \ T
  let K := starPuncture G u S ⊔ B.sup (SimpleGraph.edge u)
  have hKG : K ≤ G := by
    apply sup_le
    · exact fun _ _ h => h.1
    · apply Finset.sup_le
      intro v hv
      exact (SimpleGraph.edge_le_iff G).mpr
        (Or.inr (componentDeletionLeaves_adj d v (hB hv)))
  have hpos : 0 < Q.endpointCount u := by omega
  have hselected : #B ≤ Q.endpointCount u := by omega
  have hc := componentDifficultLeaves_reserve d B (Q.endpointCount u)
    hB hselected hreserve (componentDeletionLeaves_two_touched d htwo)
  have hsub : T ⊆ S \ B := componentDifficultLeaves_subset d B
  have hunion : T ∪ R = S \ B := Finset.union_sdiff_of_subset hsub
  have huS : u ∉ S := componentDeletionLeaves_not_hub d
  have huTR : u ∉ T ∪ R := by
    rw [hunion]
    exact fun h => huS (Finset.mem_sdiff.mp h).1
  have hmissing : ∀ v ∈ T ∪ R, ¬ K.Adj u v := by
    intro v hv ha
    rw [hunion] at hv
    obtain ⟨hvS, hvB⟩ := Finset.mem_sdiff.mp hv
    rcases ha with ha | ha
    · exact starPuncture_missing G u S huS v hvS ha
    · exact hvB ((star_sup_adj_center u B (fun h => huS (hB h)) v).mp ha)
  have hp := D.component_passing_bounds d hu hKG Q B hB hpos hbal
  obtain ⟨E, hE, _⟩ := Q.two_tier_outward_star u T R huTR
    (Finset.disjoint_left.mpr (fun _ hv hw => (Finset.mem_sdiff.mp hw).2 hv)) hmissing
    (fun v hv => (hp v (hsub hv)).1)
    (fun v hv => (hp v (Finset.mem_sdiff.mp hv).1).2 (Finset.mem_sdiff.mp hv).2)
    hc.2.1 hc.1 hc.2.2
  have hg : K ⊔ (T ∪ R).sup (SimpleGraph.edge u) = G := by
    rw [hunion]
    change (starPuncture G u S ⊔ B.sup (SimpleGraph.edge u)) ⊔
      (S \ B).sup (SimpleGraph.edge u) = G
    rw [sup_assoc, ← Finset.sup_union, Finset.union_sdiff_of_subset hB]
    exact starPuncture_restore G u S (componentDeletionLeaves_adj d)
  have hout : ∃ E : Decomposition (K ⊔ (T ∪ R).sup (SimpleGraph.edge u)),
      E.size = D.size := ⟨E, hE.trans hQ⟩
  rwa [hg] at hout

end Gallai
