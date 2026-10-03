/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.EarlyOrdinaryFamily
public import Gallai.TwoException.OrdinaryMateOrientation

@[expose] public section

/-! # Oriented regular packets for actual early contact coverage -/
namespace Gallai.TwoException
open scoped Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
noncomputable local instance orientedEarlyComponents :
    DecidableEq (evenSubgraph G).ConnectedComponent := Classical.decEq _

/-- Choose native regular packets with every donor outside the original
contact set. Orientation changes neither packet cardinality nor coverage,
and preserves the triangle labels required by mate restoration. -/
theorem bare_early_oriented_regular_family
    (h : V) (x : evenVertices G) (H : BareMinimalCounterexample G h (x : V))
    (S : Finset (evenVertices G)) (F : Finset (evenSubgraph G).ConnectedComponent)
    (hF : F ⊆ S.image (evenSubgraph G).connectedComponentMk)
    (hx : ∀ C ∈ F, x ∉ C.supp) :
    ∃ P : (evenSubgraph G).ConnectedComponent → Finset (evenVertices G),
    ∃ mates : (evenSubgraph G).ConnectedComponent → List (evenVertices G × evenVertices G),
      ∀ C ∈ F, (P C).Nonempty ∧ P C ⊆ ordinaryComponentPacket G S C ∧
        (∀ t ∈ P C, t ∈ C.supp) ∧
        (∀ t, t ∈ C.supp → t ∈ P C ∨ ∃ e ∈ mates C, t = e.1 ∨ t = e.2) ∧
        (mates C).length ≤ 1 ∧
        #(P C) = 1 + 2 * (if #(ordinaryComponentPacket G S C) = 3 then 1 else 0) ∧
        (∀ e ∈ mates C, G.Adj e.1 e.2 ∧ e.1 ∈ C.supp ∧ e.2 ∈ C.supp ∧
          e.1 ∉ P C ∧ e.2 ∉ P C ∧ e.2 ∉ S ∧
          ∃ a : evenVertices G, C.supp = {a,e.1,e.2} ∧ a ∈ P C ∧
            G.Adj a e.1 ∧ G.Adj e.2 a) := by
  classical
  obtain ⟨P,M,hdata⟩ := bare_ordinary_regular_preparation_family h x H S F hF hx
  let mates := fun C => (M C).map (orientOrdinaryMate S)
  refine ⟨P,mates,?_⟩
  intro C hC
  obtain ⟨hnon,hsub,hcover,hmates,hlen,_,hcount,hlabels⟩ := hdata C hC
  have ho := ordinary_regular_preparation_oriented S (P C) C (M C)
    hsub hcount hcover hmates hlabels
  refine ⟨hnon,hsub,?_,ho.2.1,?_,hcount,ho.2.2⟩
  · intro t ht
    exact (Finset.mem_filter.mp (hsub ht)).2
  · change ((M C).map (orientOrdinaryMate S)).length ≤ 1
    simpa only [List.length_map] using hlen

/-- Oriented component mates give the full recipient-only coverage of
the original ordinary contacts in the flattened ambient list. -/
theorem early_oriented_ordinary_contact_coverage
    (S : Finset (evenVertices G)) (F : Finset (evenSubgraph G).ConnectedComponent)
    (P : (evenSubgraph G).ConnectedComponent → Finset (evenVertices G))
    (mates : (evenSubgraph G).ConnectedComponent → List (evenVertices G × evenVertices G))
    (htouched : ∀ t ∈ S, (evenSubgraph G).connectedComponentMk t ∈ F)
    (hcover : ∀ C ∈ F, ∀ t ∈ C.supp,
      t ∈ P C ∨ ∃ e ∈ mates C, t = e.1 ∨ t = e.2)
    (hdonor : ∀ C ∈ F, ∀ e ∈ mates C, e.2 ∉ S) :
    ∀ t ∈ S, (t : V) ∈ (F.biUnion P).image Subtype.val ∨
      ∃ e ∈ (F.toList.flatMap mates).map (fun e => ((e.1 : V),(e.2 : V))),
        (t : V) = e.1 := by
  classical
  intro t ht
  let C := (evenSubgraph G).connectedComponentMk t
  have hC : C ∈ F := htouched t ht
  have htC : t ∈ C.supp :=
    (SimpleGraph.ConnectedComponent.mem_supp_iff C t).mpr rfl
  rcases hcover C hC t htC with hp | ⟨e,he,heq⟩
  · exact Or.inl (Finset.mem_image.mpr
      ⟨t,Finset.mem_biUnion.mpr ⟨C,hC,hp⟩,rfl⟩)
  · rcases heq with heq | heq
    · exact Or.inr ⟨((e.1 : V),(e.2 : V)),List.mem_map.mpr
        ⟨e,List.mem_flatMap.mpr ⟨C,Finset.mem_toList.mpr hC,he⟩,rfl⟩,
        congrArg Subtype.val heq⟩
    · exact False.elim (hdonor C hC e he (heq ▸ ht))

end Gallai.TwoException
