/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.Inputs.ComponentMatchingGraph

@[expose] public section

/-! # Endpoint supply and inward restoration of the actual component star

The matching and inward stages are composed on actual decompositions. Their
balanced endpoint vectors retain donor losses for the outward consumer.
-/

namespace Gallai

open scoped Finset

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {u : V}

/-- Decision instance for the initial component puncture. -/
noncomputable local instance componentHalfUnionAdj
    (d : ∀ C : (evenSubgraph G).ConnectedComponent, ComponentDeletionChoice G u C) :
    DecidableRel (componentDeletionUnion d).Adj := fun _ _ => Classical.propDecidable _

/-- Every original hub neighbour is odd in the initial puncture, whether
its hub spoke was deleted or retained. -/
theorem componentDeletionUnion_odd_neighbor
    (d : ∀ C : (evenSubgraph G).ConnectedComponent, ComponentDeletionChoice G u C)
    (hu : Odd (G.degree u)) (v : V) (ha : G.Adj u v) :
    Odd ((G \ componentDeletionUnion d).degree v) := by
  obtain ⟨ho, hk⟩ := componentDeletionUnion_parity d hu
  by_cases hv : Even (G.degree v)
  · exact ho v ha.ne.symm (componentDeletionUnion_covers d hu v hv ha)
  · exact Nat.not_even_iff_odd.mp (fun he => hv (hk v ha.ne.symm he))

/-- Every selected leaf is an original neighbour of the hub. -/
theorem componentDeletionLeaves_adj
    (d : ∀ C : (evenSubgraph G).ConnectedComponent, ComponentDeletionChoice G u C)
    (v : V) (hv : v ∈ componentDeletionLeaves d) : G.Adj u v := by
  classical
  obtain ⟨C, _, hv⟩ := Finset.mem_biUnion.mp hv
  exact ((d C).leaf_data v hv).1

/-- The matching vector preserves the hub count and supplies every original
hub neighbour, including the missing-spoke leaves. -/
theorem Decomposition.component_matching_supply
    (d : ∀ C : (evenSubgraph G).ConnectedComponent, ComponentDeletionChoice G u C)
    (hu : Odd (G.degree u)) (D : Decomposition (G \ componentDeletionUnion d))
    (E : Decomposition (starPuncture G u (componentDeletionLeaves d)))
    (hb : ∀ v,
      E.endpointCount v + (∑ e ∈ componentDeletionPairs d, if e.2 = v then 1 else 0) =
        D.endpointCount v + ∑ e ∈ componentDeletionPairs d, if e.1 = v then 1 else 0) :
    E.endpointCount u = D.endpointCount u ∧
      ∀ v, G.Adj u v → 0 < E.endpointCount v := by
  classical
  have hz₁ : (∑ e ∈ componentDeletionPairs d, if e.1 = u then 1 else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro e he
    have hd := componentDeletionPairs_edge_data d e he
    have hn : e.1 ≠ u := fun h => Nat.not_even_iff_odd.mpr hu (h ▸ hd.2.2.1)
    simp [hn]
  have hz₂ : (∑ e ∈ componentDeletionPairs d, if e.2 = u then 1 else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro e he
    have hd := componentDeletionPairs_edge_data d e he
    have hn : e.2 ≠ u := fun h => Nat.not_even_iff_odd.mpr hu (h ▸ hd.2.2.2.1)
    simp [hn]
  constructor
  · simpa [hz₁, hz₂] using hb u
  · intro v ha
    have hz : (∑ e ∈ componentDeletionPairs d, if e.2 = v then 1 else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro e he
      have hd := componentDeletionPairs_edge_data d e he
      have hn : e.2 ≠ v := fun h => hd.2.2.2.2 (h.symm ▸ ha)
      simp [hn]
    have hp := D.endpointCount_pos_of_odd_degree v
      (componentDeletionUnion_odd_neighbor d hu v ha)
    have h := hb v
    rw [hz] at h
    omega

/-- Restore a prescribed half of the selected star after the opposite matching.
The combined vector and strict reserve refer to the same final decomposition. -/
theorem Decomposition.restore_component_half_star
    (d : ∀ C : (evenSubgraph G).ConnectedComponent, ComponentDeletionChoice G u C)
    (hu : Odd (G.degree u)) (D : Decomposition (G \ componentDeletionUnion d))
    (hcase : (∀ e ∈ componentDeletionPairs d, ¬ G.Adj u e.1) ∨
      Even #(componentDeletionLeaves d))
    (b : V) (hb : b ∈ componentDeletionLeaves d) :
    ∃ B : Finset V, B ⊆ componentDeletionLeaves d ∧ b ∈ B ∧
      #(componentDeletionLeaves d) ≤ 2 * #B ∧
      ∃ Q : Decomposition (starPuncture G u (componentDeletionLeaves d) ⊔
          B.sup (SimpleGraph.edge u)),
        Q.size = D.size ∧
        (∀ v, Q.endpointCount v + (if v ∈ B then 1 else 0) +
            (∑ e ∈ componentDeletionPairs d, if e.2 = v then 1 else 0) =
          D.endpointCount v + (∑ e ∈ componentDeletionPairs d, if e.1 = v then 1 else 0) +
            if u = v then #B else 0) ∧
        Q.endpointCount u = D.endpointCount u + #B ∧
        #(componentDeletionLeaves d \ B) < Q.endpointCount u := by
  classical
  obtain ⟨E, hE, he⟩ := D.restore_component_pairs_to_star d hu hcase
  obtain ⟨heu, hpos⟩ := D.component_matching_supply d hu E he
  have huS := componentDeletionLeaves_not_hub d
  have hmissing := starPuncture_missing G u (componentDeletionLeaves d) huS
  obtain ⟨B, hB, hbB, hhalf, Q, hQ, hq⟩ := E.prescribed_half_star_addibility u
    (componentDeletionLeaves d) huS hmissing
    (fun v hv => hpos v (hv.elim (fun h => h.1) (componentDeletionLeaves_adj d v))) b hb
  have huB : u ∉ B := fun h => huS (hB h)
  have hqu : Q.endpointCount u = E.endpointCount u + #B := by
    simpa [huB] using hq u
  refine ⟨B, hB, hbB, hhalf, Q, hQ.trans hE, ?_, hqu.trans (by rw [heu]), ?_⟩
  · intro v
    have h₁ := he v
    have h₂ := hq v
    omega
  · have hd := starPuncture_degree_center G u (componentDeletionLeaves d) huS
      (fun v hv => (G.mem_neighborFinset u v).mpr (componentDeletionLeaves_adj d v hv))
    have hp := E.endpointCount_mod_two u
    have hc := Finset.card_sdiff_add_card_eq_card hB
    rw [Nat.odd_iff] at hu
    simp only [SimpleGraph.degree, SimpleGraph.neighborFinset,
      ← Set.ncard_eq_toFinset_card'] at hp hd hu
    omega

end Gallai
