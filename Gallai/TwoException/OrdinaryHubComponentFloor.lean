/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.OrdinaryHubPrivateSelection
public import Gallai.TwoException.OrdinaryRetainedHubSpoke
public import Gallai.TwoException.ContactPunctureWitness

@[expose] public section

/-! # Actual hub component floors after ordinary preparations -/
namespace Gallai.TwoException
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
noncomputable local instance hubFloorComponentEq : DecidableEq (evenSubgraph G).ConnectedComponent :=
  Classical.decEq _
noncomputable local instance hubFloorAdj (u : V) (B : Finset V) (M : List (V × V)) :
    DecidableRel (ordinaryMatePuncture (starPuncture G u B) M).Adj :=
  fun _ _ => Classical.propDecidable _

/-- In the hub-only contact branch, an actual retained private supplies
the hub component's floor. The auxiliary parity profile and global cap are
inputs from the simultaneous-preparation consumers, not a floor premise. -/
theorem bare_ordinary_hub_component_floor
    (h : V) (x : evenVertices G) (H : BareMinimalCounterexample G h (x : V))
    (u : V) (hu : Odd (G.degree u)) (B : Finset V)
    (S : Finset (evenVertices G))
    (F : Finset (evenSubgraph G).ConnectedComponent)
    (mates : (evenSubgraph G).ConnectedComponent → List (evenVertices G × evenVertices G))
    (htouched : ∀ t ∈ S, (evenSubgraph G).connectedComponentMk t ∈ F)
    (hx : ∀ C ∈ F, x ∉ C.supp)
    (hsupp : ∀ C ∈ F, ∀ e ∈ mates C, e.1 ∈ C.supp ∧ e.2 ∈ C.supp)
    (hclass : ∀ t, G.Adj u t → ∀ ht : Even (G.degree t),
      t = (x : V) ∨ t = h ∨ (⟨t,ht⟩ : evenVertices G) ∈ S) :
    let M := (F.toList.flatMap mates).map (fun e => ((e.1 : V),(e.2 : V)))
    let J := ordinaryMatePuncture (starPuncture G u B) M
    (∀ t, Even (J.degree t) → Even (G.degree t) ∨ t = u) →
    Odd (J.degree x) →
    (∀ t, Even (J.degree t) → eDegree J t ≤ 3) →
    ∀ K : J.ConnectedComponent, (x : V) ∈ K.supp →
      HasPathBudget (J.induce K.supp) (Fintype.card K.supp / 2) := by
  classical
  dsimp only
  intro hprofile hxOdd hcap K hxK
  obtain ⟨p,hxp,hp,hpu⟩ := bare_ordinary_hub_private_selection h x H u S F
    htouched hx hclass
  have hretained := ordinary_retained_hub_spoke u hu B x p hxp F mates hsupp hx
  have hpK := K.mem_supp_of_adj_mem_supp hxK hretained
  have hsub : ordinaryMatePuncture (starPuncture G u B)
      ((F.toList.flatMap mates).map (fun e => ((e.1 : V),(e.2 : V)))) ≤ G :=
    (ordinaryMatePuncture_le _).trans (fun _ _ ha => ha.1)
  have hw := private_eDegree_le_one_of_odd_hub_except_centre u x p hsub hprofile
    x.property hxOdd hxp.symm hp (fun ha => hpu (hsub ha))
  exact contact_component_floor_of_eDegree_le_one hcap K p hpK hw

end Gallai.TwoException
