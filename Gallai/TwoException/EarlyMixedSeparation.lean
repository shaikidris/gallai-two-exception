/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.EarlyOrientedMixedFamily

@[expose] public section

/-! # Original component separation in the mixed early auxiliary -/
namespace Gallai.TwoException
open scoped Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
noncomputable local instance separationComponents :
    DecidableEq (evenSubgraph G).ConnectedComponent := Classical.decEq _

/-- A component outside the hub contains neither the hub nor any even
private neighbour. This derives the spoke-separation guard for every
ordinary packet vertex, including its retained third vertex. -/
theorem early_ordinary_component_spoke_separation
    (x q : evenVertices G) (hxq : G.Adj x q)
    (C : (evenSubgraph G).ConnectedComponent) (hxC : x ∉ C.supp) :
    ∀ t : evenVertices G, t ∈ C.supp → (t : V) ≠ x ∧ (t : V) ≠ q := by
  intro t ht
  constructor
  · intro he
    exact hxC (Subtype.val_injective he ▸ ht)
  · intro he
    have hqC : q ∈ C.supp := Subtype.val_injective he ▸ ht
    exact hxC (C.mem_supp_of_adj_mem_supp hqC hxq.symm)

/-- A retained vertex in a special component is absent from all regular
mate edges, independently of the orientation chosen inside each packet. -/
theorem early_special_vertex_avoids_regular_mates
    (F special : Finset (evenSubgraph G).ConnectedComponent)
    (mates : (evenSubgraph G).ConnectedComponent → List (evenVertices G × evenVertices G))
    (hsupp : ∀ D ∈ F, D ∉ special → ∀ e ∈ mates D,
      e.1 ∈ D.supp ∧ e.2 ∈ D.supp)
    (C : (evenSubgraph G).ConnectedComponent) (hC : C ∈ special)
    (c : evenVertices G) (hc : c ∈ C.supp) :
    ∀ e ∈ ((F \ special).toList.flatMap mates).map
      (fun e => ((e.1 : V),(e.2 : V))), (c : V) ≠ e.1 ∧ (c : V) ≠ e.2 := by
  intro e he
  obtain ⟨f,hf,rfl⟩ := List.mem_map.mp he
  obtain ⟨D,hD,hfD⟩ := List.mem_flatMap.mp hf
  obtain ⟨hDF,hDS⟩ := Finset.mem_sdiff.mp (Finset.mem_toList.mp hD)
  obtain ⟨hl,hr⟩ := hsupp D hDF hDS f hfD
  constructor
  · intro heq
    have hcD : c ∈ D.supp := (Subtype.val_injective heq).symm ▸ hl
    exact hDS ((SimpleGraph.ConnectedComponent.eq_of_common_vertex hc hcD) ▸ hC)
  · intro heq
    have hcD : c ∈ D.supp := (Subtype.val_injective heq).symm ▸ hr
    exact hDS ((SimpleGraph.ConnectedComponent.eq_of_common_vertex hc hcD) ▸ hC)

/-- The special third vertex also avoids the entire merged spoke union,
not just the two contacts selected inside its own triangle. -/
theorem early_special_vertex_avoids_ordinary_spokes
    (S : Finset (evenVertices G)) (F : Finset (evenSubgraph G).ConnectedComponent)
    (Q : (evenSubgraph G).ConnectedComponent → Finset (evenVertices G))
    (hsupp : ∀ D ∈ F, ∀ t ∈ Q D, t ∈ D.supp)
    (C : (evenSubgraph G).ConnectedComponent) (c : evenVertices G)
    (hc : c ∈ C.supp) (hcS : c ∉ S)
    (hQ : Q C = ordinaryComponentPacket G S C) :
    (c : V) ∉ (F.biUnion Q).image Subtype.val := by
  apply ordinary_component_vertex_avoids_spoke_union G F Q hsupp C c hc
  intro ht
  rw [hQ] at ht
  exact hcS (Finset.mem_filter.mp ht).1

end Gallai.TwoException
