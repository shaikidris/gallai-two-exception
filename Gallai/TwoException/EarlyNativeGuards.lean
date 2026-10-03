/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.BareWindmill
public import Gallai.TwoException.OrdinaryPendingBound

@[expose] public section

/-! # Native leaf guards for early contact restoration -/
namespace Gallai.TwoException
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
noncomputable local instance earlyNativeHalfAdj (u : V) (B A : Finset V) :
    DecidableRel ((starPuncture G u B) ⊔ A.sup (SimpleGraph.edge u)).Adj :=
  fun _ _ => Classical.propDecidable _

/-- In the bare minimum counterexample, every original even vertex other
than the exceptional hub has E-degree at most two. The protected isolate,
hub component and ordinary components are handled separately. -/
theorem bare_nonhub_eDegree_le_two
    (h : V) (x w : evenVertices G) (H : BareMinimalCounterexample G h (x : V))
    (hwx : (w : V) ≠ (x : V)) : eDegree G (w : V) ≤ 2 := by
  classical
  by_cases hwh : (w : V) = h
  · rcases H.counterexample.1 with ⟨_,_,_,_,_,hhzero,_⟩
    rw [hwh,hhzero]
    omega
  · by_cases hr : (evenSubgraph G).Reachable x w
    · exact le_of_eq (bare_hub_private_eDegree_eq_two h x w H hr hwx)
    · let C := (evenSubgraph G).connectedComponentMk w
      have hw : w ∈ C.supp :=
        (SimpleGraph.ConnectedComponent.mem_supp_iff C w).mpr rfl
      have hx : x ∉ C.supp := by
        intro hx
        have he := (SimpleGraph.ConnectedComponent.mem_supp_iff C x).mp hx
        exact hr (SimpleGraph.ConnectedComponent.eq.mp he)
      exact bare_ordinary_eDegree_le_two h x w H C hx hw hwh

/-- An actual contact packet avoiding the exceptional hub needs no
separate degree-cap or passing-count premise in the early schedule. -/
theorem bare_early_half_star_pending_le_two
    (h : V) (x : evenVertices G) (H : BareMinimalCounterexample G h (x : V))
    (u : V) (B A : Finset V) (hAB : A ⊆ B)
    (hadj : ∀ t ∈ B, G.Adj u t)
    (hleaves : ∀ t ∈ B, Even (G.degree t)) (hxB : (x : V) ∉ B)
    (E : Decomposition ((starPuncture G u B) ⊔ A.sup (SimpleGraph.edge u))) :
    ∀ w ∈ B \ A, passingNeighborCount E w ≤ 2 := by
  apply actual_contact_half_star_pending_le_two u B A hAB hadj hleaves
  intro t ht
  exact bare_nonhub_eDegree_le_two h x ⟨t,hleaves t ht⟩ H
    (fun he => hxB (he ▸ ht))

end Gallai.TwoException
