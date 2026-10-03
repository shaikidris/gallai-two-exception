/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.ContactPunctureAssembly

@[expose] public section

/-! # Component floors for a contact star and a deleted mate edge -/
namespace Gallai.TwoException
open scoped Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
noncomputable local instance mateAssemblyStarAdj (u : V) (B : Finset V) :
    DecidableRel (starPuncture G u B).Adj := fun _ _ => Classical.propDecidable _
noncomputable local instance mateAssemblyDeleteAdj (u p q : V) (B : Finset V) :
    DecidableRel ((starPuncture G u B).deleteEdges {s(p,q)}).Adj :=
  fun _ _ => Classical.propDecidable _

/-- The deleted mate endpoints and the exceptional hub are separate roles.
Every component meets the deletion boundary; each possible contact supplies
a non-SET witness, using a retained private when the contact is the hub. -/
theorem contact_mate_floor_of_boundary_data
    (hconn : G.Connected) (h u x p q : V) (B : Finset V)
    (hkeep : ∀ t, Even (((starPuncture G u B).deleteEdges {s(p,q)}).degree t) →
      Even (G.degree t))
    (hcap : ∀ t, Even (((starPuncture G u B).deleteEdges {s(p,q)}).degree t) →
      eDegree ((starPuncture G u B).deleteEdges {s(p,q)}) t ≤ 3)
    (hxEven : Even (G.degree x))
    (hxOdd : Odd (((starPuncture G u B).deleteEdges {s(p,q)}).degree x))
    (hcentre : eDegree ((starPuncture G u B).deleteEdges {s(p,q)}) u = 0)
    (hhzero : eDegree G h = 0)
    (hpx : G.Adj p x) (hp : eDegree G p = 2)
    (hqx : G.Adj q x) (hq : eDegree G q = 2)
    (hleaves : ∀ t ∈ B, t = x ∨ t = h ∨ (G.Adj t x ∧ eDegree G t = 2))
    (r : V) (hxr : ((starPuncture G u B).deleteEdges {s(p,q)}).Adj x r)
    (hrx : G.Adj r x) (hr : eDegree G r = 2) :
    HasPathBudget ((starPuncture G u B).deleteEdges {s(p,q)})
      (Fintype.card V / 2) := by
  classical
  have hsub : (starPuncture G u B).deleteEdges {s(p,q)} ≤ G :=
    fun _ _ ha => ha.1.1
  apply floor_of_components
  intro C
  obtain ⟨t, htC, ht⟩ := contact_spoke_component_meets_boundary hconn u p q B C
  rcases ht with htu | htp | htq | htB
  · subst t
    apply contact_component_floor_of_eDegree_le_one hcap C u htC
    omega
  · subst t
    exact contact_private_component_floor_without_parity hsub hkeep hcap C x p htC
      hxEven hxOdd hpx hp
  · subst t
    exact contact_private_component_floor_without_parity hsub hkeep hcap C x q htC
      hxEven hxOdd hqx hq
  · rcases hleaves t htB with htx | hth | ⟨htx, htdeg⟩
    · subst t
      have hrC := C.mem_supp_of_adj_mem_supp htC hxr
      exact contact_private_component_floor_without_parity hsub hkeep hcap C x r hrC
        hxEven hxOdd hrx hr
    · subst t
      apply contact_component_floor_of_eDegree_le_one hcap C h htC
      have hz := bare_isolate_puncture_eDegree_zero hsub hkeep h hhzero
      omega
    · exact contact_private_component_floor_without_parity hsub hkeep hcap C x t htC
        hxEven hxOdd htx htdeg

end Gallai.TwoException
