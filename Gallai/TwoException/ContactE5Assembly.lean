/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.ContactE5Boundary
public import Gallai.Operations.ComponentAssembly

@[expose] public section

/-! # Component floors for E5's spoke and mate preparation -/
namespace Gallai.TwoException
open scoped Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
noncomputable local instance E5AssemblyStarAdj (u : V) (B : Finset V) :
    DecidableRel (starPuncture G u B).Adj := fun _ _ => Classical.propDecidable _
noncomputable local instance E5AssemblySpokeAdj (u x s : V) (B : Finset V) :
    DecidableRel ((starPuncture G u B).deleteEdges {s(x,s)}).Adj :=
  fun _ _ => Classical.propDecidable _
noncomputable local instance E5AssemblyMateAdj (u x s p q : V) (B : Finset V) :
    DecidableRel (((starPuncture G u B).deleteEdges {s(x,s)}).deleteEdges
      {s(q,p)}).Adj := fun _ _ => Classical.propDecidable _

/-- Actual boundary contacts give a non-SET witness in every component.
The hub component uses a retained private; both mate endpoints and the
deleted-spoke endpoint are degree-two privates of the odd hub. -/
theorem contact_E5_floor_of_boundary_data
    (hconn : G.Connected) (h u x s p q : V) (B : Finset V)
    (hkeep : ∀ t,
      Even ((((starPuncture G u B).deleteEdges {s(x,s)}).deleteEdges {s(q,p)}).degree t) →
      Even (G.degree t))
    (hcap : ∀ t,
      Even ((((starPuncture G u B).deleteEdges {s(x,s)}).deleteEdges {s(q,p)}).degree t) →
      eDegree (((starPuncture G u B).deleteEdges {s(x,s)}).deleteEdges {s(q,p)}) t ≤ 3)
    (hxEven : Even (G.degree x))
    (hxOdd : Odd ((((starPuncture G u B).deleteEdges {s(x,s)}).deleteEdges {s(q,p)}).degree x))
    (hcentre : eDegree (((starPuncture G u B).deleteEdges {s(x,s)}).deleteEdges {s(q,p)}) u = 0)
    (hhzero : eDegree G h = 0)
    (hsx : G.Adj s x) (hs : eDegree G s = 2)
    (hpx : G.Adj p x) (hp : eDegree G p = 2)
    (hqx : G.Adj q x) (hq : eDegree G q = 2)
    (hleaves : ∀ t ∈ B, t = h ∨ (G.Adj t x ∧ eDegree G t = 2))
    (r : V)
    (hxr : (((starPuncture G u B).deleteEdges {s(x,s)}).deleteEdges {s(q,p)}).Adj x r)
    (hrx : G.Adj r x) (hr : eDegree G r = 2) :
    HasPathBudget (((starPuncture G u B).deleteEdges {s(x,s)}).deleteEdges {s(q,p)})
      (Fintype.card V / 2) := by
  classical
  have hsub : ((starPuncture G u B).deleteEdges {s(x,s)}).deleteEdges {s(q,p)} ≤ G :=
    fun _ _ ha => ha.1.1.1
  apply floor_of_components
  intro C
  obtain ⟨t, htC, ht⟩ := contact_E5_component_meets_boundary hconn u x s p q B C
  simp only [Finset.mem_insert] at ht
  rcases ht with htu | htx | hts | htq | htp | htB
  · subst t
    apply contact_component_floor_of_eDegree_le_one hcap C u htC
    omega
  · subst t
    have hrC := C.mem_supp_of_adj_mem_supp htC hxr
    exact contact_private_component_floor_without_parity hsub hkeep hcap C x r hrC
      hxEven hxOdd hrx hr
  · subst t
    exact contact_private_component_floor_without_parity hsub hkeep hcap C x s htC
      hxEven hxOdd hsx hs
  · subst t
    exact contact_private_component_floor_without_parity hsub hkeep hcap C x q htC
      hxEven hxOdd hqx hq
  · subst t
    exact contact_private_component_floor_without_parity hsub hkeep hcap C x p htC
      hxEven hxOdd hpx hp
  · rcases hleaves t htB with hth | ⟨htx, htdeg⟩
    · subst t
      apply contact_component_floor_of_eDegree_le_one hcap C h htC
      have hz := bare_isolate_puncture_eDegree_zero hsub hkeep h hhzero
      omega
    · exact contact_private_component_floor_without_parity hsub hkeep hcap C x t htC
        hxEven hxOdd htx htdeg

end Gallai.TwoException
