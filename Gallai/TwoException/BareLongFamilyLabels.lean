/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.BareLongPreparation

@[expose] public section

/-! # Coherent ambient boundary labels for one native preparation family -/
namespace Gallai.TwoException
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Flattening preserves whole-component coverage without inserting a
fictitious hub leaf, and labels each actual boundary vertex by a touched
component in the same family. -/
theorem long_ordinary_family_boundary_labels
    (F : Finset (evenSubgraph G).ConnectedComponent)
    (P : (evenSubgraph G).ConnectedComponent → Finset (evenVertices G))
    (mates : (evenSubgraph G).ConnectedComponent → List (evenVertices G × evenVertices G))
    (hsupp : ∀ C ∈ F, ∀ t ∈ P C, t ∈ C.supp)
    (hmates : ∀ C ∈ F, ∀ e ∈ mates C, e.1 ∈ C.supp ∧ e.2 ∈ C.supp)
    (hcover : ∀ C ∈ F, ∀ t ∈ C.supp,
      t ∈ P C ∨ ∃ e ∈ mates C, t = e.1 ∨ t = e.2) :
    let B := (F.biUnion P).image Subtype.val
    let O := (F.toList.flatMap mates).map (fun e => ((e.1 : V),(e.2 : V)))
    (∀ C ∈ F, ∀ t : evenVertices G, t ∈ C.supp →
      (t : V) ∈ B ∨ ∃ e ∈ O, (t : V) = e.1 ∨ (t : V) = e.2) ∧
    (∀ t ∈ B, ∃ C ∈ F, ∃ p : evenVertices G, p ∈ C.supp ∧ (p : V) = t) ∧
    (∀ e ∈ O, ∃ C ∈ F, ∃ p q : evenVertices G,
      p ∈ C.supp ∧ q ∈ C.supp ∧ e = ((p : V),(q : V))) := by
  classical
  dsimp only
  refine ⟨?_,?_,?_⟩
  · intro C hC t ht
    rcases hcover C hC t ht with hp | ⟨e,he,hte⟩
    · exact Or.inl (Finset.mem_image.mpr
        ⟨t,Finset.mem_biUnion.mpr ⟨C,hC,hp⟩,rfl⟩)
    · refine Or.inr ⟨((e.1 : V),(e.2 : V)),?_,?_⟩
      · exact List.mem_map.mpr ⟨e,List.mem_flatMap.mpr
          ⟨C,Finset.mem_toList.mpr hC,he⟩,rfl⟩
      · rcases hte with hte | hte
        · exact Or.inl (congrArg Subtype.val hte)
        · exact Or.inr (congrArg Subtype.val hte)
  · intro t ht
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨C,hC,hpC⟩ := Finset.mem_biUnion.mp hp
    exact ⟨C,hC,p,hsupp C hC p hpC,rfl⟩
  · intro e he
    obtain ⟨f,hf,rfl⟩ := List.mem_map.mp he
    obtain ⟨C,hC,hfC⟩ := List.mem_flatMap.mp hf
    have hCF := Finset.mem_toList.mp hC
    exact ⟨C,hCF,f.1,f.2,(hmates C hCF f hfC).1,
      (hmates C hCF f hfC).2,rfl⟩

/-- Distinct original even components supply the separation guard for
the joint ordinary witness. The two corridor centres are originally odd;
the first-side selected leaves and mates lie in the windmill component. -/
theorem long_ordinary_component_avoids_windmill_packet
    (C Z : (evenSubgraph G).ConnectedComponent) (hZ : Z ≠ C)
    (u v : V) (huOdd : Odd (G.degree u)) (hvOdd : Odd (G.degree v))
    (S : Finset V) (N : List (V × V))
    (hS : ∀ t ∈ S, t ∈ Subtype.val '' C.supp)
    (hN : ∀ e ∈ N, e.1 ∈ Subtype.val '' C.supp ∧ e.2 ∈ Subtype.val '' C.supp) :
    ∀ t : evenVertices G, t ∈ Z.supp →
      (t : V) ≠ u ∧ (t : V) ∉ insert v S ∧
      ∀ e ∈ N, (t : V) ≠ e.1 ∧ (t : V) ≠ e.2 := by
  classical
  intro t ht
  have htu : (t : V) ≠ u := fun hh =>
    (Nat.not_even_iff_odd.mpr huOdd) (hh ▸ t.property)
  have htv : (t : V) ≠ v := fun hh =>
    (Nat.not_even_iff_odd.mpr hvOdd) (hh ▸ t.property)
  have hout : (t : V) ∉ Subtype.val '' C.supp := by
    rintro ⟨w,hw,hwt⟩
    have hwt' : w = t := Subtype.val_injective hwt
    have htC : t ∈ C.supp := hwt' ▸ hw
    exact hZ (SimpleGraph.ConnectedComponent.eq_of_common_vertex ht htC)
  refine ⟨htu,?_,?_⟩
  · simp only [Finset.mem_insert]
    exact not_or.mpr ⟨htv,fun hh => hout (hS t hh)⟩
  · intro e he
    exact ⟨fun hh => hout (hh.symm ▸ (hN e he).1),
      fun hh => hout (hh.symm ▸ (hN e he).2)⟩

end Gallai.TwoException
