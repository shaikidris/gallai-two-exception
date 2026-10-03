/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.E1ProtectedSelection
public import Gallai.TwoException.E2ProtectedSelection
public import Gallai.TwoException.E3ProtectedReduction
public import Gallai.TwoException.E4ProtectedClosed
public import Gallai.TwoException.E5ProtectedClosed

@[expose] public section

/-! # Exhaustive protected windmill-contact reduction -/
namespace Gallai.TwoException
open scoped Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Any nonempty windmill contact is reducible when the reserved endpoint
is h and the contact centre meets no other even component. Petal data and
the E1--E5 case are extracted from the actual graph. -/
theorem bare_windmill_protected_contact_false
    (h : V) (x : evenVertices G) (H : BareMinimalCounterexample G h (x : V))
    (C : (evenSubgraph G).ConnectedComponent) (hxC : x ∈ C.supp) (u : V)
    (huOdd : Odd (G.degree u)) (huh : G.Adj u h)
    (hcontact : G.Adj u x ∨
      ∃ a : {a : evenVertices G // (evenSubgraph G).Adj x a}, G.Adj u a.val.val)
    (hcontacts : ∀ t, G.Adj u t → Even (G.degree t) →
      t = h ∨ t = (x : V) ∨ t ∈ ambientWindmillContacts x u) : False := by
  classical
  obtain ⟨f, P, hinv, hfree, hindex, hedge, hc⟩ :=
    bare_windmill_contact_preparation_cases h x H C hxC u hcontact
  change ContactPreparationCases f P (windmillContacts x u) (G.Adj u x) at hc
  have hnarrow : ¬ G.Adj u x → ∀ t, G.Adj u t → Even (G.degree t) →
      t = h ∨ t ∈ ambientWindmillContacts x u := by
    intro hux t hut htEven
    rcases hcontacts t hut htEven with ht | ht | ht
    · exact Or.inl ht
    · exact False.elim (hux (ht ▸ hut))
    · exact Or.inr ht
  rcases hc with ⟨hux, ho, _⟩ | ⟨hux, he, hd⟩ | ⟨hux, he⟩ |
    ⟨hux, ho, _⟩ | ⟨hux, he, _, hp⟩
  · exact bare_windmill_E1_protected_reducible h x H u f P hinv hfree hindex hedge
      ho huOdd huh (hnarrow hux)
  · exact bare_windmill_E2_protected_reducible h x H u f P hinv hfree hindex hedge
      he hd huOdd huh (hnarrow hux)
  · exact bare_windmill_E3_protected_false h x H u f P hfree hindex he
      huOdd huh hux hcontacts
  · exact bare_windmill_E4_protected_reducible h x H u f P hinv hfree hindex hedge
      ho huOdd huh hux hcontacts
  · exact bare_windmill_E5_protected_reducible h x H u f P hinv hfree hindex hedge
      he hp huOdd huh (hnarrow hux)

/-- A surviving protected windmill contact must also meet an even vertex
outside the protected vertex and the windmill contact set. This is the
interface requiring ordinary-component preparation in the bare endgame. -/
theorem bare_windmill_protected_contact_has_external_even_neighbor
    (h : V) (x : evenVertices G) (H : BareMinimalCounterexample G h (x : V))
    (C : (evenSubgraph G).ConnectedComponent) (hxC : x ∈ C.supp) (u : V)
    (huOdd : Odd (G.degree u)) (huh : G.Adj u h)
    (hcontact : G.Adj u x ∨
      ∃ a : {a : evenVertices G // (evenSubgraph G).Adj x a}, G.Adj u a.val.val) :
    ∃ t, G.Adj u t ∧ Even (G.degree t) ∧ t ≠ h ∧ t ≠ (x : V) ∧
      t ∉ ambientWindmillContacts x u := by
  classical
  by_contra hn
  apply bare_windmill_protected_contact_false h x H C hxC u huOdd huh hcontact
  intro t hut htEven
  by_cases hth : t = h
  · exact Or.inl hth
  by_cases htx : t = (x : V)
  · exact Or.inr (Or.inl htx)
  by_cases htA : t ∈ ambientWindmillContacts x u
  · exact Or.inr (Or.inr htA)
  exact False.elim (hn ⟨t, hut, htEven, hth, htx, htA⟩)

end Gallai.TwoException
