/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.EarlySelectedSingleContradiction

@[expose] public section

/-! # Canonical original contacts and touched ordinary components -/
namespace Gallai.TwoException
open scoped Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
noncomputable local instance canonicalContactComponents :
    DecidableEq (evenSubgraph G).ConnectedComponent := Classical.decEq _

/-- Original even contacts other than the protected vertex and the hub. -/
noncomputable def earlyOriginalContacts (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : V) (x : evenVertices G) (u : V) : Finset (evenVertices G) := by
  classical
  exact Finset.univ.filter fun t => G.Adj u t ∧ (t : V) ≠ h ∧ (t : V) ≠ x

/-- Components touched by original contacts, excluding the hub component. -/
noncomputable def earlyOrdinaryContactComponents (G : SimpleGraph V)
    [DecidableRel G.Adj] (h : V) (x : evenVertices G) (u : V) :
    Finset (evenSubgraph G).ConnectedComponent := by
  classical
  exact ((earlyOriginalContacts G h x u).image
    (evenSubgraph G).connectedComponentMk).filter fun Z => x ∉ Z.supp

/-- Canonical contacts satisfy the classification and coverage used by the
selected early consumer. A hub-component contact is a private windmill
contact; every other contact has its component in the ordinary family. -/
theorem bare_early_canonical_contact_guards
    (h u : V) (x : evenVertices G) (H : BareMinimalCounterexample G h (x : V)) :
    let S := earlyOriginalContacts G h x u
    let F := earlyOrdinaryContactComponents G h x u
    (F ⊆ S.image (evenSubgraph G).connectedComponentMk) ∧
    (∀ Z ∈ F, x ∉ Z.supp) ∧
    (∀ t, G.Adj u t → ∀ ht : Even (G.degree t),
      t = (x : V) ∨ t = h ∨ (⟨t,ht⟩ : evenVertices G) ∈ S) ∧
    (∀ t ∈ S, G.Adj u t ∧ (t : V) ≠ h) ∧
    (∀ t ∈ S, (t : V) ∈ windmillPrivateSet x (windmillContacts x u) ∨
      (evenSubgraph G).connectedComponentMk t ∈ F) := by
  classical
  dsimp only
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro Z hZ
    exact (Finset.mem_filter.mp hZ).1
  · intro Z hZ
    exact (Finset.mem_filter.mp hZ).2
  · intro t ht he
    by_cases hx : t = (x : V)
    · exact Or.inl hx
    by_cases hh : t = h
    · exact Or.inr (Or.inl hh)
    exact Or.inr (Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_univ _,ht,hh,hx⟩))
  · intro t ht
    have hp := (Finset.mem_filter.mp ht).2
    exact ⟨hp.1,hp.2.1⟩
  · intro t ht
    have hp := (Finset.mem_filter.mp ht).2
    let Z := (evenSubgraph G).connectedComponentMk t
    by_cases hxZ : x ∈ Z.supp
    · have hreach : (evenSubgraph G).Reachable x t :=
        SimpleGraph.ConnectedComponent.eq.mp
          ((SimpleGraph.ConnectedComponent.mem_supp_iff Z x).mp hxZ)
      have hxt := bare_hub_component_nonhub_adjacent_to_hub h x t H Z hxZ hreach hp.2.2
      let a : {a : evenVertices G // (evenSubgraph G).Adj x a} := ⟨t,hxt⟩
      apply Or.inl
      exact (mem_windmillPrivateSet x _ _).mpr
        ⟨a,Finset.mem_filter.mpr ⟨Finset.mem_univ a,hp.1⟩,rfl⟩
    · apply Or.inr
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_image.mpr ⟨t,ht,rfl⟩,hxZ⟩

/-- The actual sole-single early profile is impossible in the two-or-more
ordinary-component regime with even baseline or an eligible T2. Contact and
component classification are canonical, not caller-supplied certificates. -/
theorem bare_canonical_early_sole_single_impossible
    (h u : V) (x : evenVertices G) (H : BareMinimalCounterexample G h (x : V))
    (f : {a : evenVertices G // (evenSubgraph G).Adj x a} →
      {a : evenVertices G // (evenSubgraph G).Adj x a})
    (hinv : Function.Involutive f)
    (hedge : ∀ a b, (evenSubgraph G).Adj a.val b.val ↔ f a = b)
    (P : Finset {a : evenVertices G // (evenSubgraph G).Adj x a})
    (hindex : ∀ a, ∃! r, r ∈ P ∧ (a = r ∨ a = f r))
    (p : {a : evenVertices G // (evenSubgraph G).Adj x a})
    (hpC : p ∈ windmillContacts x u) (hfpC : f p ∉ windmillContacts x u)
    (hsingle : ∀ r ∈ singleContactPetals f P (windmillContacts x u),
      ∀ a ∈ windmillContacts x u ∩ ({r,f r} : Finset _), a = p)
    (huOdd : Odd (G.degree u)) (hux : ¬ G.Adj u x)
    (hN : 2 ≤ #(earlyOrdinaryContactComponents G h x u))
    (havailable :
      let S := earlyOriginalContacts G h x u
      let F := earlyOrdinaryContactComponents G h x u
      Even (#(windmillContacts x u) + #F + 2 * #(F.filter
        (fun Z => #(ordinaryComponentPacket G S Z) = 3))) ∨
        (F.filter (fun Z => #(ordinaryComponentPacket G S Z) = 2)).Nonempty) : False := by
  obtain ⟨hF,hx,hclass,hS,hcover⟩ := bare_early_canonical_contact_guards h u x H
  exact bare_selected_early_sole_single_impossible h u x H f hinv hedge P hindex
    p hpC hfpC hsingle (earlyOriginalContacts G h x u)
    (earlyOrdinaryContactComponents G h x u) hF hx hclass hS hcover
    huOdd hux hN havailable

end Gallai.TwoException
