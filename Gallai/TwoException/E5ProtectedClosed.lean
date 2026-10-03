/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.E5ProtectedReduction

@[expose] public section

/-! # Selected-petal protected E5 contradiction -/
namespace Gallai.TwoException
open scoped Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Distinct single-petal representatives close the protected E5 branch;
the petal orientations, auxiliary budget and reserves are all derived. -/
theorem bare_windmill_E5_protected_reducible
    (h : V) (x : evenVertices G) (H : BareMinimalCounterexample G h (x : V))
    (u : V)
    (f : {a : evenVertices G // (evenSubgraph G).Adj x a} →
      {a : evenVertices G // (evenSubgraph G).Adj x a})
    (P : Finset {a : evenVertices G // (evenSubgraph G).Adj x a})
    (hinv : Function.Involutive f) (hfree : ∀ a, f a ≠ a)
    (hindex : ∀ a, ∃! r, r ∈ P ∧ (a = r ∨ a = f r))
    (hedge : ∀ a b, (evenSubgraph G).Adj a.val b.val ↔ f a = b)
    (he : Even #(singleContactPetals f P (windmillContacts x u)))
    (hpair : ∃ r ∈ singleContactPetals f P (windmillContacts x u),
      ∃ s ∈ singleContactPetals f P (windmillContacts x u), r ≠ s)
    (huOdd : Odd (G.degree u)) (huh : G.Adj u h)
    (hcontacts : ∀ t, G.Adj u t → Even (G.degree t) →
      t = h ∨ t ∈ ambientWindmillContacts x u) : False := by
  classical
  obtain ⟨p, r, hp, hq, hr, hs, hd⟩ :=
    two_single_contact_petals f hinv P (windmillContacts x u) hindex hpair
  exact bare_windmill_E5_protected_false h x H u f P hinv hfree hindex hedge he
    p r hp hq hr hs hd huOdd huh hcontacts

end Gallai.TwoException
