/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.E2ProtectedReduction

@[expose] public section

/-! # Selecting the protected E2 reduction -/
namespace Gallai.TwoException
open scoped Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- A double contact chooses the E2 preparation and closes the protected
branch without a supplied petal or path decomposition. -/
theorem bare_windmill_E2_protected_reducible
    (h : V) (x : evenVertices G) (H : BareMinimalCounterexample G h (x : V))
    (u : V)
    (f : {a : evenVertices G // (evenSubgraph G).Adj x a} →
      {a : evenVertices G // (evenSubgraph G).Adj x a})
    (P : Finset {a : evenVertices G // (evenSubgraph G).Adj x a})
    (hinv : Function.Involutive f) (hfree : ∀ a, f a ≠ a)
    (hindex : ∀ a, ∃! r, r ∈ P ∧ (a = r ∨ a = f r))
    (hedge : ∀ a b, (evenSubgraph G).Adj a.val b.val ↔ f a = b)
    (he : Even #(singleContactPetals f P (windmillContacts x u)))
    (hd : (doubleContactPetals f P (windmillContacts x u)).Nonempty)
    (huOdd : Odd (G.degree u)) (huh : G.Adj u h)
    (hcontacts : ∀ t, G.Adj u t → Even (G.degree t) →
      t = h ∨ t ∈ ambientWindmillContacts x u) : False := by
  obtain ⟨p, hp⟩ := hd
  obtain ⟨hpA, hqA⟩ := (Finset.mem_filter.mp hp).2
  exact bare_windmill_E2_protected_false h x H u f P hinv hfree hindex hedge
    he p hpA hqA huOdd huh hcontacts

end Gallai.TwoException
