/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.E4ProtectedReduction

@[expose] public section

/-! # Selected-petal protected E4 contradiction -/
namespace Gallai.TwoException
open scoped Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- An odd single-contact row is reducible in the protected E4 setting;
neither a chosen petal nor an auxiliary decomposition is required. -/
theorem bare_windmill_E4_protected_reducible
    (h : V) (x : evenVertices G) (H : BareMinimalCounterexample G h (x : V))
    (u : V)
    (f : {a : evenVertices G // (evenSubgraph G).Adj x a} →
      {a : evenVertices G // (evenSubgraph G).Adj x a})
    (P : Finset {a : evenVertices G // (evenSubgraph G).Adj x a})
    (hinv : Function.Involutive f) (hfree : ∀ a, f a ≠ a)
    (hindex : ∀ a, ∃! r, r ∈ P ∧ (a = r ∨ a = f r))
    (hedge : ∀ a b, (evenSubgraph G).Adj a.val b.val ↔ f a = b)
    (ho : Odd #(singleContactPetals f P (windmillContacts x u)))
    (huOdd : Odd (G.degree u)) (huh : G.Adj u h) (hux : G.Adj u x)
    (hcontacts : ∀ t, G.Adj u t → Even (G.degree t) →
      t = h ∨ t = (x : V) ∨ t ∈ ambientWindmillContacts x u) : False := by
  classical
  have hpos : 0 < #(singleContactPetals f P (windmillContacts x u)) := by
    obtain ⟨k, hk⟩ := ho
    omega
  obtain ⟨r, hr⟩ := Finset.card_pos.mp hpos
  obtain ⟨p, _, hp, hq⟩ := single_contact_orientation f hinv P (windmillContacts x u) r hr
  exact bare_windmill_E4_protected_false h x H u f P hfree hindex hedge ho
    p hp hq huOdd huh hux hcontacts

end Gallai.TwoException
