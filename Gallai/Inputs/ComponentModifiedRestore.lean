/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.Inputs.ComponentModifiedPassingBounds

@[expose] public section

/-! # Restoring the modified puncture and excluding two touched components -/

namespace Gallai

open scoped Finset

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {u : V}

/-- Restore the modified puncture without a path-count loss, using the
actual matching, inward, passing and counting witnesses. -/
theorem Decomposition.restore_modified_puncture
    (d : ∀ C : (evenSubgraph G).ConnectedComponent, ComponentDeletionChoice G u C)
    (hu : Odd (G.degree u)) (e : V × V) (he : e ∈ componentDeletionPairs d)
    (ha : G.Adj u e.1) (hs : Odd #(componentDeletionLeaves d))
    (hsize : 4 ≤ #(insert e.1 (componentDeletionLeaves d)))
    (D : Decomposition (G \ componentModifiedDeletion d e)) :
    ∃ E : Decomposition G, E.size = D.size := by
  classical
  obtain ⟨C₀, _, heC⟩ := Finset.mem_biUnion.mp he
  obtain ⟨B, hB, _, hhalf, Q, hQ, hbal, _, hbudget, _, _⟩ :=
    D.restore_modified_half_star d hu e he ha hs e.1 (Finset.mem_insert_self _ _)
  let S := insert e.1 (componentDeletionLeaves d)
  let T := componentModifiedDifficultLeaves d C₀ e B
  let R := (S \ B) \ T
  let K := starPuncture G u S ⊔ B.sup (SimpleGraph.edge u)
  have hKG : K ≤ G := by
    apply sup_le
    · exact fun _ _ h => h.1
    · apply Finset.sup_le
      intro v hv
      exact (SimpleGraph.edge_le_iff G).mpr
        (Or.inr (componentModifiedLeaves_adj d e ha v (hB hv)))
  have hpos : 0 < Q.endpointCount u := by omega
  have hc := componentModifiedDifficultLeaves_reserve d C₀ e heC B
    (Q.endpointCount u) hB hhalf hsize hbudget
  have hsub : T ⊆ S \ B := componentModifiedDifficultLeaves_subset d C₀ e B
  have hunion : T ∪ R = S \ B := Finset.union_sdiff_of_subset hsub
  have huS : u ∉ S := componentModifiedLeaves_not_hub d e ha
  have huTR : u ∉ T ∪ R := by
    rw [hunion]
    exact fun h => huS (Finset.mem_sdiff.mp h).1
  have hmissing : ∀ v ∈ T ∪ R, ¬ K.Adj u v := by
    intro v hv hadj
    rw [hunion] at hv
    obtain ⟨hvS, hvB⟩ := Finset.mem_sdiff.mp hv
    rcases hadj with hadj | hadj
    · exact starPuncture_missing G u S huS v hvS hadj
    · exact hvB ((star_sup_adj_center u B (fun h => huS (hB h)) v).mp hadj)
  have hp := D.modified_passing_bounds d hu C₀ e heC ha hKG Q B hB hpos hbal
  obtain ⟨E, hE, _⟩ := Q.two_tier_outward_star u T R huTR
    (Finset.disjoint_left.mpr (fun _ hv hw => (Finset.mem_sdiff.mp hw).2 hv)) hmissing
    (fun v hv => (hp v (hsub hv)).1)
    (fun v hv => (hp v (Finset.mem_sdiff.mp hv).1).2 (Finset.mem_sdiff.mp hv).2)
    (fun _ => hc.2.1) hc.1 hc.2.2
  have hg : K ⊔ (T ∪ R).sup (SimpleGraph.edge u) = G := by
    rw [hunion]
    change (starPuncture G u S ⊔ B.sup (SimpleGraph.edge u)) ⊔
      (S \ B).sup (SimpleGraph.edge u) = G
    rw [sup_assoc, ← Finset.sup_union, Finset.union_sdiff_of_subset hB]
    exact starPuncture_restore G u S (componentModifiedLeaves_adj d e ha)
  have hout : ∃ E : Decomposition (K ⊔ (T ∪ R).sup (SimpleGraph.edge u)),
      E.size = D.size := ⟨E, hE.trans hQ⟩
  rwa [hg] at hout

/-- In a strict minimal counterexample, all even neighbours of any odd vertex
lie in one even component. Both source restoration cases are discharged. -/
theorem minimal_counterexample_odd_neighbors_one_component
    (u : V) (hu : Odd (G.degree u))
    (hconn : G.Connected) (hcap : ∀ v, Even (G.degree v) → eDegree G v ≤ 3)
    (hnot : ¬ HasPathBudget G (Fintype.card V / 2)) (hset : ¬ IsSET G)
    (hmin : ∀ (U : Set V) [DecidablePred (· ∈ U)]
      (J : SimpleGraph U) [DecidableRel J.Adj],
      J.edgeFinset.card < G.edgeFinset.card → J.Connected →
      (∀ v, Even (J.degree v) → eDegree J v ≤ 3) →
      HasPathBudget J (Fintype.card U / 2) ∨ IsSET J)
    (C E : (evenSubgraph G).ConnectedComponent)
    (hC : ∃ v : evenVertices G, v ∈ C.supp ∧ G.Adj u v)
    (hE : ∃ v : evenVertices G, v ∈ E.supp ∧ G.Adj u v) : C = E := by
  classical
  by_contra hCE
  let d := fun F => Classical.choice (componentDeletionChoice_nonempty u F
    (minimal_counterexample_even_components hconn hcap hnot hset hmin F))
  obtain ⟨e, he, ha, _, hs, _, hsize⟩ := minimal_counterexample_component_second_case
    d hu ⟨C, E, hCE, hC, hE⟩ hconn hcap hnot hset hmin
  obtain ⟨D, hD⟩ := componentModifiedDeletion_floor d hu e he ha
    hconn hcap hnot hset hmin
  obtain ⟨Q, hQ⟩ := D.restore_modified_puncture d hu e he ha hs hsize
  exact hnot ⟨Q, hQ ▸ hD⟩

end Gallai
