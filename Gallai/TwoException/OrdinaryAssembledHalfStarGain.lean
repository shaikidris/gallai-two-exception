/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.OrdinaryRestoredPacketShape
public import Gallai.TwoException.OrdinarySpecialExistence

@[expose] public section

/-! # Global half-star gain from actual ordinary preparation data -/
namespace Gallai.TwoException
open scoped Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
noncomputable local instance assembledGainEq :
    DecidableEq (evenSubgraph G).ConnectedComponent := Classical.decEq _
noncomputable local instance assembledGainStarAdj (u : V) (B : Finset V) :
    DecidableRel (starPuncture G u B).Adj := fun _ _ => Classical.propDecidable _
noncomputable local instance assembledGainHalfAdj (u : V) (B A : Finset V) :
    DecidableRel ((starPuncture G u B) ⊔ A.sup (SimpleGraph.edge u)).Adj :=
  fun _ _ => Classical.propDecidable _

/-- Actual preparation metadata and restored recipients imply the global
gain in a tight half-star failure; packet shapes and gains are derived. -/
theorem bare_ordinary_assembled_half_star_gain
    (h : V) (x : evenVertices G) (H : BareMinimalCounterexample G h (x : V))
    (u : V) (B A : Finset V) (hAB : A ⊆ B)
    (hadj : ∀ t ∈ B, G.Adj u t) (hleaves : ∀ t ∈ B, Even (G.degree t))
    (S : Finset (evenVertices G)) (F special : Finset (evenSubgraph G).ConnectedComponent)
    (P : (evenSubgraph G).ConnectedComponent → Finset (evenVertices G))
    (mates : (evenSubgraph G).ConnectedComponent → List (evenVertices G × evenVertices G))
    (hF : F ⊆ S.image (evenSubgraph G).connectedComponentMk)
    (hx : ∀ C ∈ F, x ∉ C.supp)
    (hP : ∀ C ∈ F, P C ⊆ ordinaryComponentPacket G S C)
    (hPB : ∀ C ∈ F, (P C).image Subtype.val ⊆ B)
    (hcover : ∀ C ∈ F, C ∉ special → ∀ t ∈ C.supp,
      t ∈ P C ∨ ∃ e ∈ mates C, t = e.1 ∨ t = e.2)
    (havoid : ∀ C ∈ F, ∀ e ∈ mates C, e.1 ∉ P C ∧ e.2 ∉ P C)
    (hlabels : ∀ C ∈ F, ∀ e ∈ mates C, ∃ a : evenVertices G,
      C.supp = {a,e.1,e.2} ∧ a ∈ P C)
    (hspecial : ∀ C ∈ F, C ∈ special →
      (ordinaryComponentPacket G S C).card = 2 ∧ P C = ordinaryComponentPacket G S C)
    (D : Decomposition (starPuncture G u B))
    (hrec : ∀ e ∈ (F.toList.flatMap mates).map (fun e => ((e.1 : V),(e.2 : V))),
      2 ≤ D.endpointCount e.1)
    (E : Decomposition ((starPuncture G u B) ⊔ A.sup (SimpleGraph.edge u)))
    (hvec : ∀ t, E.endpointCount t + (if t ∈ A then 1 else 0) =
      D.endpointCount t + if u = t then #A else 0)
    (htight : ∀ w ∈ B \ A, passingNeighborCount E w = 2) :
    #((F.biUnion P).image Subtype.val \ A) + #F ≤
      #((F.biUnion P).image Subtype.val ∩ A) + #special := by
  classical
  have hsupp : ∀ C ∈ F, ∀ t ∈ P C, t ∈ C.supp :=
    fun C hC t ht => (Finset.mem_filter.mp (hP C hC ht)).2
  apply ordinary_prepared_half_star_gain u B A hAB hadj hleaves F special P
    hsupp hPB D E hvec htight
  · intro C hC hCs
    obtain ⟨w,hw,he⟩ := Finset.mem_image.mp (hF hC)
    have hwC : w ∈ C.supp :=
      (SimpleGraph.ConnectedComponent.mem_supp_iff C w).mpr he
    apply bare_ordinary_restored_regular_shape h x w H S C (hx C hC) hwC hw
      (P C) (mates C) (hsupp C hC) (hcover C hC hCs) (havoid C hC)
      (hlabels C hC) (starPuncture G u B) D
    intro e he
    apply hrec ((e.1 : V),(e.2 : V))
    exact List.mem_map.mpr ⟨e,List.mem_flatMap.mpr
      ⟨C,Finset.mem_toList.mpr hC,he⟩,rfl⟩
  · intro C hC hCs
    obtain ⟨w,hw,he⟩ := Finset.mem_image.mp (hF hC)
    have hwC : w ∈ C.supp :=
      (SimpleGraph.ConnectedComponent.mem_supp_iff C w).mpr he
    obtain ⟨htwo,hPC⟩ := hspecial C hC hCs
    obtain ⟨b,c,hs,hwb,hbc,hcw,hpacket⟩ :=
      bare_ordinary_two_contact_labels h x w H S C (hx C hC) hwC hw htwo
    refine ⟨w,b,c,hs,hwb,?_⟩
    simp [hPC,hpacket]

end Gallai.TwoException
