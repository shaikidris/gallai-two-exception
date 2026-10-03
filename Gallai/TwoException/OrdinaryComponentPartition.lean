/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.OrdinaryContributionSum

@[expose] public section

/-! # Contact packets indexed by actual original even components -/
namespace Gallai.TwoException
open scoped BigOperators Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
noncomputable local instance componentPartitionEq :
    DecidableEq (evenSubgraph G).ConnectedComponent := Classical.decEq _

/-- Restrict an even contact set to a single original even component. -/
noncomputable def ordinaryComponentPacket (S : Finset (evenVertices G))
    (C : (evenSubgraph G).ConnectedComponent) : Finset (evenVertices G) := by
  classical
  exact S.filter (fun t => t ∈ C.supp)

/-- Every contact belongs to exactly one of the touched even components. -/
theorem ordinary_component_packet_partition (S : Finset (evenVertices G)) :
    (S.image (evenSubgraph G).connectedComponentMk).biUnion
      (ordinaryComponentPacket G S) = S := by
  classical
  ext t
  constructor
  · intro ht
    obtain ⟨C, _, htC⟩ := Finset.mem_biUnion.mp ht
    exact (Finset.mem_filter.mp htC).1
  · intro ht
    apply Finset.mem_biUnion.mpr
    refine ⟨(evenSubgraph G).connectedComponentMk t, Finset.mem_image.mpr ⟨t, ht, rfl⟩, ?_⟩
    exact Finset.mem_filter.mpr ⟨ht,
      (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).mpr rfl⟩

/-- Original component packets are pairwise disjoint without a separate
carrier or incidence selection assumption. -/
theorem ordinary_component_packets_disjoint (S : Finset (evenVertices G)) :
    ((S.image (evenSubgraph G).connectedComponentMk :
      Finset (evenSubgraph G).ConnectedComponent) : Set _).PairwiseDisjoint
      (ordinaryComponentPacket G S) := by
  classical
  intro C _ D _ hCD
  apply Finset.disjoint_left.mpr
  intro t htC htD
  exact hCD (SimpleGraph.ConnectedComponent.eq_of_common_vertex
    (Finset.mem_filter.mp htC).2 (Finset.mem_filter.mp htD).2)

/-- Local gains summed over the graph's actual touched components give
the literal global ordinary-contact bound. -/
theorem ordinary_component_contact_gain
    (S A : Finset (evenVertices G))
    (special : Finset (evenSubgraph G).ConnectedComponent)
    (hregular : ∀ C ∈ S.image (evenSubgraph G).connectedComponentMk, C ∉ special →
      #(ordinaryComponentPacket G S C \ A) + 1 ≤ #(ordinaryComponentPacket G S C ∩ A))
    (hspecial : ∀ C ∈ S.image (evenSubgraph G).connectedComponentMk, C ∈ special →
      #(ordinaryComponentPacket G S C \ A) ≤ #(ordinaryComponentPacket G S C ∩ A)) :
    #(S \ A) + #(S.image (evenSubgraph G).connectedComponentMk) ≤ #(S ∩ A) + #special := by
  classical
  obtain ⟨hselected, hpending⟩ := ordinary_disjoint_packet_counts
    (S.image (evenSubgraph G).connectedComponentMk) (ordinaryComponentPacket G S) A
    (ordinary_component_packets_disjoint G S)
  rw [ordinary_component_packet_partition G S] at hselected hpending
  exact ordinary_contact_gain_of_packet_counts _ special S A
    (ordinaryComponentPacket G S) hselected hpending hregular hspecial

end Gallai.TwoException
