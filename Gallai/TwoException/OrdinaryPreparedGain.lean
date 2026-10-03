/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.OrdinaryAmbientGain

@[expose] public section

/-! # Summation over the actual deleted ordinary spoke packets -/
namespace Gallai.TwoException
open scoped Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
noncomputable local instance preparedGainEq :
    DecidableEq (evenSubgraph G).ConnectedComponent := Classical.decEq _

/-- Gains of prepared deletions sum over exactly the deleted spokes.
Undeleted contacts do not enter the pending-star count. -/
theorem ordinary_prepared_component_gain
    (F special : Finset (evenSubgraph G).ConnectedComponent)
    (P : (evenSubgraph G).ConnectedComponent → Finset (evenVertices G))
    (A : Finset V)
    (hsupp : ∀ C ∈ F, ∀ t ∈ P C, t ∈ C.supp)
    (hregular : ∀ C ∈ F, C ∉ special →
      #((P C).image Subtype.val \ A) + 1 ≤ #((P C).image Subtype.val ∩ A))
    (hspecial : ∀ C ∈ F, C ∈ special →
      #((P C).image Subtype.val \ A) ≤ #((P C).image Subtype.val ∩ A)) :
    #((F.biUnion P).image Subtype.val \ A) + #F ≤
      #((F.biUnion P).image Subtype.val ∩ A) + #special := by
  classical
  let packet := fun C => (P C).image Subtype.val
  have hdis : (F : Set _).PairwiseDisjoint packet := by
    intro C hC D hD hCD
    apply Finset.disjoint_left.mpr
    intro t htC htD
    obtain ⟨c,hc,hct⟩ := Finset.mem_image.mp htC
    obtain ⟨d,hd,hdt⟩ := Finset.mem_image.mp htD
    have hcd : c = d := Subtype.val_injective (hct.trans hdt.symm)
    subst d
    exact hCD (SimpleGraph.ConnectedComponent.eq_of_common_vertex
      (hsupp C hC c hc) (hsupp D hD c hd))
  have hunion : F.biUnion packet = (F.biUnion P).image Subtype.val := by
    ext t
    simp only [packet,Finset.mem_biUnion,Finset.mem_image]
    constructor
    · rintro ⟨C,hC,c,hc,rfl⟩
      exact ⟨c,⟨C,hC,hc⟩,rfl⟩
    · rintro ⟨c,⟨C,hC,hc⟩,rfl⟩
      exact ⟨C,hC,c,hc,rfl⟩
  obtain ⟨hs,hp⟩ := ordinary_disjoint_packet_counts F packet A hdis
  rw [hunion] at hs hp
  exact ordinary_contact_gain_of_packet_counts F special _ A packet
    hs hp hregular hspecial

end Gallai.TwoException
