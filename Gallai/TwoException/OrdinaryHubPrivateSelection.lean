/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.BareWindmill

@[expose] public section

/-! # Private witnesses in the hub-only contact branch -/
namespace Gallai.TwoException
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
noncomputable local instance hubPrivateComponentEq : DecidableEq (evenSubgraph G).ConnectedComponent :=
  Classical.decEq _

/-- The actual exceptional hub has a private neighbour. In the hub-only
contact branch every such private avoids the centre; ordinary contacts
belong to components excluding the hub. -/
theorem bare_ordinary_hub_private_selection
    (h : V) (x : evenVertices G) (H : BareMinimalCounterexample G h (x : V))
    (u : V) (S : Finset (evenVertices G))
    (F : Finset (evenSubgraph G).ConnectedComponent)
    (htouched : ∀ t ∈ S, (evenSubgraph G).connectedComponentMk t ∈ F)
    (hx : ∀ C ∈ F, x ∉ C.supp)
    (hclass : ∀ t, G.Adj u t → ∀ ht : Even (G.degree t),
      t = (x : V) ∨ t = h ∨ (⟨t,ht⟩ : evenVertices G) ∈ S) :
    ∃ p : evenVertices G, (evenSubgraph G).Adj x p ∧
      eDegree G p = 2 ∧ ¬ G.Adj p u := by
  classical
  have hgt := BareCounterexample.exception_gt_three H.counterexample
  have hn : (evenNeighbors G x).Nonempty := by
    apply Finset.card_pos.mp
    change 0 < eDegree G x
    omega
  obtain ⟨p,hp⟩ := hn
  obtain ⟨hxp,hpEven⟩ := (mem_evenNeighbors (G := G) x p).mp hp
  let pe : evenVertices G := ⟨p,hpEven⟩
  have hAdj : (evenSubgraph G).Adj x pe := hxp
  have hpx : p ≠ (x : V) := hxp.ne.symm
  have hd := bare_hub_private_eDegree_eq_two h x pe H hAdj.reachable hpx
  refine ⟨pe,hAdj,hd,?_⟩
  intro hpu
  rcases hclass p hpu.symm hpEven with he | he | hpS
  · exact hpx he
  · rcases H.counterexample.1 with ⟨_,_,_,_,_,hhzero,_⟩
    change eDegree G p = 2 at hd
    rw [he] at hd
    omega
  · have hF := htouched pe hpS
    have hpC : pe ∈ ((evenSubgraph G).connectedComponentMk pe).supp :=
      (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).mpr rfl
    exact hx _ hF
      (((evenSubgraph G).connectedComponentMk pe).mem_supp_of_adj_mem_supp hpC hAdj.symm)

end Gallai.TwoException
