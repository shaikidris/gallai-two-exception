/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.ContactPunctureWitness
public import Gallai.Operations.ComponentAssembly

@[expose] public section

/-! # Component assembly for star/spoke contact punctures -/
namespace Gallai.TwoException
open scoped Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable local instance assemblyStarAdj (u : V) (B : Finset V) :
    DecidableRel (starPuncture G u B).Adj := fun _ _ => Classical.propDecidable _
noncomputable local instance assemblyDeleteAdj (u x q : V) (B : Finset V) :
    DecidableRel ((starPuncture G u B).deleteEdges {s(x,q)}).Adj :=
  fun _ _ => Classical.propDecidable _

/-- Boundary coverage and a retained private at the hub assemble actual
component floors, including components separated by the puncture. -/
theorem contact_spoke_floor_of_boundary_data
    (hconn : G.Connected) (h u x q : V) (B : Finset V)
    (hkeep : ∀ t, Even (((starPuncture G u B).deleteEdges {s(x,q)}).degree t) →
      Even (G.degree t))
    (hcap : ∀ t, Even (((starPuncture G u B).deleteEdges {s(x,q)}).degree t) →
      eDegree ((starPuncture G u B).deleteEdges {s(x,q)}) t ≤ 3)
    (hxEven : Even (G.degree x))
    (hxOdd : Odd (((starPuncture G u B).deleteEdges {s(x,q)}).degree x))
    (hcentre : eDegree ((starPuncture G u B).deleteEdges {s(x,q)}) u = 0)
    (hhzero : eDegree G h = 0) (hxq : G.Adj x q) (hq : eDegree G q = 2)
    (hleaves : ∀ t ∈ B, t = h ∨ (G.Adj t x ∧ eDegree G t = 2))
    (p : V) (hxp : ((starPuncture G u B).deleteEdges {s(x,q)}).Adj x p)
    (hpx : G.Adj p x) (hp : eDegree G p = 2) :
    HasPathBudget ((starPuncture G u B).deleteEdges {s(x,q)})
      (Fintype.card V / 2) := by
  classical
  have hsub : (starPuncture G u B).deleteEdges {s(x,q)} ≤ G :=
    fun _ _ ha => ha.1.1
  apply floor_of_components
  intro C
  obtain ⟨t, htC, ht⟩ := contact_spoke_component_meets_boundary hconn u x q B C
  rcases ht with htu | htx | htq | htB
  · subst t
    apply contact_component_floor_of_eDegree_le_one hcap C u htC
    omega
  · subst t
    have hpC := C.mem_supp_of_adj_mem_supp htC hxp
    exact contact_private_component_floor_without_parity hsub hkeep hcap C x p hpC
      hxEven hxOdd hpx hp
  · subst t
    exact contact_private_component_floor_without_parity hsub hkeep hcap C x q htC
      hxEven hxOdd hxq.symm hq
  · rcases hleaves t htB with he | ⟨htx, htdeg⟩
    · subst t
      apply contact_component_floor_of_eDegree_le_one hcap C h htC
      have hz := bare_isolate_puncture_eDegree_zero hsub hkeep h hhzero
      omega
    · exact contact_private_component_floor_without_parity hsub hkeep hcap C x t htC
        hxEven hxOdd htx htdeg

end Gallai.TwoException
