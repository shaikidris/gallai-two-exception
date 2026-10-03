/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.EarlyCanonicalContacts
public import Gallai.TwoException.ProtectedContactCoverage

@[expose] public section

/-! # Canonical protected-contact zero-component endgame -/
namespace Gallai.TwoException
open scoped Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
noncomputable local instance canonicalProtectedZeroComponents :
    DecidableEq (evenSubgraph G).ConnectedComponent := Classical.decEq _

/-- The protected-contact schedules exclude zero ordinary components when
the odd contact centre meets h and has a nonempty windmill contact. -/
theorem bare_canonical_protected_zero_impossible
    (h u : V) (x : evenVertices G) (H : BareMinimalCounterexample G h (x : V))
    (C : (evenSubgraph G).ConnectedComponent) (hxC : x ∈ C.supp)
    (hu : Odd (G.degree u)) (huh : G.Adj u h)
    (hcontact : G.Adj u x ∨
      ∃ a : {a : evenVertices G // (evenSubgraph G).Adj x a}, G.Adj u a.val.val)
    (hzero : earlyOrdinaryContactComponents G h x u = ∅) : False := by
  classical
  obtain ⟨_,_,hclass,_,hcover⟩ := bare_early_canonical_contact_guards h u x H
  apply bare_windmill_protected_contact_false h x H C hxC u hu huh hcontact
  intro t ht he
  rcases hclass t ht he with hx | hh | hS
  · exact Or.inr (Or.inl hx)
  · exact Or.inl hh
  · rcases hcover ⟨t,he⟩ hS with hw | ho
    · exact Or.inr (Or.inr hw)
    · rw [hzero] at ho
      simpa using ho

end Gallai.TwoException
