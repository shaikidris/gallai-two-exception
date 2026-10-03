/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.OrdinaryComponentPartition
public import Gallai.TwoException.OrdinaryNativeTriangleGain

@[expose] public section

/-! # Ambient-vertex summation of native component gains -/
namespace Gallai.TwoException
open scoped Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
noncomputable local instance ambientGainComponentEq :
    DecidableEq (evenSubgraph G).ConnectedComponent := Classical.decEq _

/-- Component gains stated on ambient vertices sum to the literal contact
bound. The selected set may also contain hub contacts outside these packets. -/
theorem ordinary_ambient_component_gain
    (S : Finset (evenVertices G)) (A : Finset V)
    (special : Finset (evenSubgraph G).ConnectedComponent)
    (hregular : ∀ C ∈ S.image (evenSubgraph G).connectedComponentMk, C ∉ special →
      #((ordinaryComponentPacket G S C).image Subtype.val \ A) + 1 ≤
        #((ordinaryComponentPacket G S C).image Subtype.val ∩ A))
    (hspecial : ∀ C ∈ S.image (evenSubgraph G).connectedComponentMk, C ∈ special →
      #((ordinaryComponentPacket G S C).image Subtype.val \ A) ≤
        #((ordinaryComponentPacket G S C).image Subtype.val ∩ A)) :
    #(S.image Subtype.val \ A) + #(S.image (evenSubgraph G).connectedComponentMk) ≤
      #(S.image Subtype.val ∩ A) + #special := by
  classical
  let F := S.image (evenSubgraph G).connectedComponentMk
  let packet := fun C => (ordinaryComponentPacket G S C).image Subtype.val
  have hdis : (F : Set _).PairwiseDisjoint packet := by
    intro C hC D hD hCD
    apply Finset.disjoint_left.mpr
    intro t htC htD
    obtain ⟨c, hc, hct⟩ := Finset.mem_image.mp htC
    obtain ⟨d, hd, hdt⟩ := Finset.mem_image.mp htD
    have hcd : c = d := Subtype.val_injective (hct.trans hdt.symm)
    subst d
    exact Finset.disjoint_left.mp
      (ordinary_component_packets_disjoint G S hC hD hCD) hc hd
  have hunion : F.biUnion packet = S.image Subtype.val := by
    have hp := ordinary_component_packet_partition G S
    ext t
    simp only [packet, F, Finset.mem_biUnion, Finset.mem_image]
    constructor
    · rintro ⟨C, hC, c, hc, rfl⟩
      exact ⟨c, hp ▸ Finset.mem_biUnion.mpr ⟨C, Finset.mem_image.mpr hC, hc⟩, rfl⟩
    · rintro ⟨c, hc, rfl⟩
      obtain ⟨C, hC, hcC⟩ := Finset.mem_biUnion.mp (hp.symm ▸ hc)
      exact ⟨C, Finset.mem_image.mp hC, c, hcC, rfl⟩
  obtain ⟨hs, hp⟩ := ordinary_disjoint_packet_counts F packet A hdis
  rw [hunion] at hs hp
  exact ordinary_contact_gain_of_packet_counts F special (S.image Subtype.val) A
    packet hs hp hregular hspecial

end Gallai.TwoException
