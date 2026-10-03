/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.EarlyCanonicalMultipleContradiction
public import Gallai.TwoException.EarlyCanonicalHubAllDoubleResidual
public import Gallai.TwoException.EarlySelectedOddHubContradiction

@[expose] public section

/-! # Complete multiple-component no-hub-contact contradiction -/
namespace Gallai.TwoException
open scoped Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
noncomputable local instance canonicalMultipleHubComponents :
    DecidableEq (evenSubgraph G).ConnectedComponent := Classical.decEq _

/-- Canonical original contacts with a hub contact and at least two
ordinary components contradict bare minimality. Both the single-contact and
all-double profiles, all packet choices and auxiliary budgets are derived. -/
theorem bare_canonical_multiple_hub_impossible
    (h u : V) (x : evenVertices G) (H : BareMinimalCounterexample G h (x : V))
    (C : (evenSubgraph G).ConnectedComponent) (hxC : x ∈ C.supp)
    (f : {a : evenVertices G // (evenSubgraph G).Adj x a} →
      {a : evenVertices G // (evenSubgraph G).Adj x a})
    (hinv : Function.Involutive f)
    (hedge : ∀ a b, (evenSubgraph G).Adj a.val b.val ↔ f a = b)
    (P : Finset {a : evenVertices G // (evenSubgraph G).Adj x a})
    (hindex : ∀ a, ∃! r, r ∈ P ∧ (a = r ∨ a = f r))
    (p : {a : evenVertices G // (evenSubgraph G).Adj x a})
    (hup : G.Adj u p.val.val) (hu : Odd (G.degree u)) (hux : G.Adj u x)
    (hN : 2 ≤ #(earlyOrdinaryContactComponents G h x u)) : False := by
  classical
  obtain ⟨hsingle,hFeven,hnoT2⟩ := bare_canonical_hub_multiple_residual h u x H C hxC
    f hinv hedge P hindex p hup hu hux hN
  obtain ⟨hF,hx,hclass,hS,hcover⟩ := bare_early_canonical_contact_guards h u x H
  exact bare_selected_early_odd_hub_impossible h u x H f hinv hedge P hindex p
    (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hup⟩) hsingle
    (earlyOriginalContacts G h x u) (earlyOrdinaryContactComponents G h x u)
    hF hx hclass hS hcover hu hux hN hFeven hnoT2

/-- Canonical private contact with at least two ordinary components is
reducible, regardless of whether the centre also contacts the hub. -/
theorem bare_canonical_multiple_contacts_impossible
    (h u : V) (x : evenVertices G) (H : BareMinimalCounterexample G h (x : V))
    (C : (evenSubgraph G).ConnectedComponent) (hxC : x ∈ C.supp)
    (f : {a : evenVertices G // (evenSubgraph G).Adj x a} →
      {a : evenVertices G // (evenSubgraph G).Adj x a})
    (hinv : Function.Involutive f)
    (hedge : ∀ a b, (evenSubgraph G).Adj a.val b.val ↔ f a = b)
    (P : Finset {a : evenVertices G // (evenSubgraph G).Adj x a})
    (hindex : ∀ a, ∃! r, r ∈ P ∧ (a = r ∨ a = f r))
    (p : {a : evenVertices G // (evenSubgraph G).Adj x a})
    (hup : G.Adj u p.val.val) (hu : Odd (G.degree u))
    (hN : 2 ≤ #(earlyOrdinaryContactComponents G h x u)) : False := by
  classical
  by_cases hux : G.Adj u x
  · exact bare_canonical_multiple_hub_impossible h u x H C hxC f hinv hedge P
      hindex p hup hu hux hN
  · exact bare_canonical_multiple_no_hub_impossible h u x H C hxC f hinv hedge P
      hindex p hup hu hux hN

end Gallai.TwoException
