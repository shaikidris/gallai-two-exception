/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.OrdinaryAuxiliaryFloors
public import Gallai.TwoException.OrdinaryProtectedDegree
public import Gallai.TwoException.ComponentWitnessAssembly

@[expose] public section

/-! # Complete component floors for the hub-deleting ordinary auxiliary -/
namespace Gallai.TwoException
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
noncomputable local instance auxiliaryEndpointEq : DecidableEq (evenSubgraph G).ConnectedComponent :=
  Classical.decEq _
noncomputable local instance auxiliaryEndpointAdj (u : V) (B : Finset V) (M : List (V × V)) :
    DecidableRel (ordinaryMatePuncture (starPuncture G u B) M).Adj :=
  fun _ _ => Classical.propDecidable _

/-- The actual ordinary auxiliary admits a protected endpoint decomposition.
Only original preparation data are supplied, not auxiliary budgets. -/
theorem bare_ordinary_auxiliary_endpoint
    (h : V) (x : evenVertices G) (H : BareMinimalCounterexample G h (x : V))
    (u : V) (hu : Odd (G.degree u)) (hxu : G.Adj u x)
    (S : Finset (evenVertices G)) (hS : ∀ t ∈ S, G.Adj u t)
    (hSh : ∀ t ∈ S, (t : V) ≠ h)
    (F special : Finset (evenSubgraph G).ConnectedComponent)
    (P : (evenSubgraph G).ConnectedComponent → Finset (evenVertices G))
    (mates : (evenSubgraph G).ConnectedComponent → List (evenVertices G × evenVertices G))
    (hP : ∀ C ∈ F, P C ⊆ ordinaryComponentPacket G S C)
    (hlen : ∀ C ∈ F, (mates C).length ≤ 1)
    (hmates : ∀ C ∈ F, ∀ e ∈ mates C,
      G.Adj e.1 e.2 ∧ e.1 ∈ C.supp ∧ e.2 ∈ C.supp ∧ e.1 ∉ P C ∧ e.2 ∉ P C)
    (hx : ∀ C ∈ F, x ∉ C.supp)
    (htouched : ∀ t ∈ S, (evenSubgraph G).connectedComponentMk t ∈ F)
    (hcover : ∀ C ∈ F, ∀ t ∈ ordinaryComponentPacket G S C,
      t ∈ P C ∨ ∃ e ∈ mates C, t = e.1 ∨ t = e.2)
    (hclass : ∀ t, G.Adj u t → ∀ ht : Even (G.degree t),
      t = (x : V) ∨ t = h ∨ (⟨t,ht⟩ : evenVertices G) ∈ S)
    (hregular : ∀ C ∈ F, C ∉ special → ∀ t, t ∈ C.supp →
      t ∈ P C ∨ ∃ e ∈ mates C, t = e.1 ∨ t = e.2)
    (hspecial : ∀ C ∈ F, C ∈ special → ∃ a b c : evenVertices G,
      C.supp = {a,b,c} ∧ a ∈ P C ∧ b ∈ P C ∧ mates C = [] ∧
      G.Adj a c ∧ G.Adj b c ∧ ¬ G.Adj c u) :
    let B := insert (x : V) ((F.biUnion P).image Subtype.val)
    let M := (F.toList.flatMap mates).map (fun e => ((e.1 : V),(e.2 : V)))
    ∃ D : Decomposition (ordinaryMatePuncture (starPuncture G u B) M),
      D.size ≤ (Fintype.card V + 1) / 2 ∧ 2 ≤ D.endpointCount h := by
  classical
  have hd := bare_ordinary_assembled_protected_degree h x H u hu S hSh F P mates hP
    (fun C hC e he => (hmates C hC e he).1)
  have hc := bare_ordinary_assembled_cap h x H u hu hxu S hS F P mates hP hlen
    hmates hx htouched hcover hclass
  have hf := bare_ordinary_auxiliary_component_floors h x H u hu hxu S hS F special
    P mates hP hlen hmates hx htouched hcover hclass hregular hspecial
  rcases H.counterexample.1 with ⟨_,_,hhpos,hhEven,_,_,_⟩
  dsimp only at hd hc hf ⊢
  apply assemble_one_ceiling_of_component_floors _ h
  · rw [hd]; exact hhpos
  · rw [hd]; exact hhEven
  · exact hc
  · intro K _; exact hf K

end Gallai.TwoException
