/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.OrdinaryStarMateBoundary
public import Gallai.TwoException.OrdinaryFiniteMateAssembly

@[expose] public section

/-! # Original component labels for assembled puncture contacts -/
namespace Gallai.TwoException
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
noncomputable local instance assembledBoundaryComponentEq : DecidableEq (evenSubgraph G).ConnectedComponent :=
  Classical.decEq _
noncomputable local instance assembledBoundaryAdj (u : V) (B : Finset V) (M : List (V × V)) :
    DecidableRel (ordinaryMatePuncture (starPuncture G u B) M).Adj :=
  fun _ _ => Classical.propDecidable _

/-- Each actual auxiliary component meets the centre, the hub, or a vertex
of a selected original ordinary component. The labels are recovered from
the concrete finite spoke union and flattened mate list. -/
theorem ordinary_assembled_component_contact
    (hconn : G.Connected) (u x : V)
    (F : Finset (evenSubgraph G).ConnectedComponent)
    (P : (evenSubgraph G).ConnectedComponent → Finset (evenVertices G))
    (mates : (evenSubgraph G).ConnectedComponent → List (evenVertices G × evenVertices G))
    (hsupp : ∀ C ∈ F, ∀ t ∈ P C, t ∈ C.supp)
    (hmates : ∀ C ∈ F, ∀ e ∈ mates C, e.1 ∈ C.supp ∧ e.2 ∈ C.supp) :
    let B := insert x ((F.biUnion P).image Subtype.val)
    let M := (F.toList.flatMap mates).map (fun e => ((e.1 : V),(e.2 : V)))
    ∀ K : (ordinaryMatePuncture (starPuncture G u B) M).ConnectedComponent,
      u ∈ K.supp ∨ x ∈ K.supp ∨
      ∃ C ∈ F, ∃ t : evenVertices G, t ∈ C.supp ∧ (t : V) ∈ K.supp := by
  classical
  dsimp only
  intro K
  obtain ⟨t,htK,ht⟩ := ordinary_star_mates_component_meets_boundary hconn u
    (insert x ((F.biUnion P).image Subtype.val))
    ((F.toList.flatMap mates).map (fun e => ((e.1 : V),(e.2 : V)))) K
  rcases ht with htu | htB | hmate
  · exact Or.inl (htu ▸ htK)
  · rcases Finset.mem_insert.mp htB with htx | htU
    · exact Or.inr (Or.inl (htx ▸ htK))
    · obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp htU
      obtain ⟨C,hC,hvC⟩ := Finset.mem_biUnion.mp hv
      exact Or.inr (Or.inr ⟨C,hC,v,hsupp C hC v hvC,htK⟩)
  · obtain ⟨e,he,hte⟩ := hmate
    obtain ⟨f,hf,rfl⟩ := List.mem_map.mp he
    obtain ⟨C,hC,hfC⟩ := List.mem_flatMap.mp hf
    have hCF := Finset.mem_toList.mp hC
    obtain ⟨hl,hr⟩ := hmates C hCF f hfC
    rcases hte with hlEq | hrEq
    · rw [hlEq] at htK
      exact Or.inr (Or.inr ⟨C,hCF,f.1,hl,htK⟩)
    · rw [hrEq] at htK
      exact Or.inr (Or.inr ⟨C,hCF,f.2,hr,htK⟩)

end Gallai.TwoException
