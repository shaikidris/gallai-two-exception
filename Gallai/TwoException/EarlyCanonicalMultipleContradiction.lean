/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.EarlyCanonicalAllDoubleResidual
public import Gallai.TwoException.EarlySelectedAllDoubleContradiction

@[expose] public section

/-! # Complete multiple-component no-hub-contact contradiction -/
namespace Gallai.TwoException
open scoped Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
noncomputable local instance canonicalMultipleComponents :
    DecidableEq (evenSubgraph G).ConnectedComponent := Classical.decEq _

/-- Canonical original contacts with no hub contact and at least two
ordinary components contradict bare minimality. Both the single-contact and
all-double profiles, all packet choices and auxiliary budgets are derived. -/
theorem bare_canonical_multiple_no_hub_impossible
    (h u : V) (x : evenVertices G) (H : BareMinimalCounterexample G h (x : V))
    (C : (evenSubgraph G).ConnectedComponent) (hxC : x ∈ C.supp)
    (f : {a : evenVertices G // (evenSubgraph G).Adj x a} →
      {a : evenVertices G // (evenSubgraph G).Adj x a})
    (hinv : Function.Involutive f)
    (hedge : ∀ a b, (evenSubgraph G).Adj a.val b.val ↔ f a = b)
    (P : Finset {a : evenVertices G // (evenSubgraph G).Adj x a})
    (hindex : ∀ a, ∃! r, r ∈ P ∧ (a = r ∨ a = f r))
    (p : {a : evenVertices G // (evenSubgraph G).Adj x a})
    (hup : G.Adj u p.val.val) (hu : Odd (G.degree u)) (hux : ¬ G.Adj u x)
    (hN : 2 ≤ #(earlyOrdinaryContactComponents G h x u)) : False := by
  classical
  have hsingle := bare_canonical_multiple_single_petals_empty h u x H C hxC
    f hinv hedge P hindex p hup hu hux hN
  have hres := bare_canonical_delayed_multiple_residual h u x H C hxC p hup hu hN
  have hp : p ∈ windmillContacts x u :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _,hup⟩
  have hfp : f p ∈ windmillContacts x u := by
    rcases indexed_contact_double_or_single f P (windmillContacts x u) hindex p hp with
      ⟨r,hr,hpr⟩ | ⟨r,hr,_⟩
    · have hd := (Finset.mem_filter.mp hr).2
      rcases hpr with he | he
      · simpa only [he] using hd.2
      · simpa only [he,hinv r] using hd.1
    · rw [hsingle] at hr
      simpa using hr
  obtain ⟨hF,hx,hclass,hS,hcover⟩ := bare_early_canonical_contact_guards h u x H
  exact bare_selected_early_all_double_impossible h u x H f hinv hedge P hindex
    p hp hfp hsingle (earlyOriginalContacts G h x u)
    (earlyOrdinaryContactComponents G h x u) hF hx hclass hS hcover hu hux hN hres.1

end Gallai.TwoException
