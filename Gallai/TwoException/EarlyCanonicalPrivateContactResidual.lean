/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.EarlyCanonicalT3PositiveCoverage
public import Gallai.TwoException.EarlyCanonicalZeroOrT3
public import Gallai.TwoException.EarlyCanonicalProtectedZero

@[expose] public section

/-! # Exact zero-component residual of a positive private contact -/
namespace Gallai.TwoException
open scoped Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
noncomputable local instance privateResidualComponents :
    DecidableEq (evenSubgraph G).ConnectedComponent := Classical.decEq _

/-- A positive private contact in a bare counterexample meets neither an
ordinary even component nor the protected vertex. Petal data are extracted
from the actual windmill; they are not hypotheses. -/
theorem bare_canonical_private_contact_residual
    (h u : V) (x : evenVertices G) (H : BareMinimalCounterexample G h (x : V))
    (C : (evenSubgraph G).ConnectedComponent) (hxC : x ∈ C.supp)
    (huOdd : Odd (G.degree u)) (hp : (windmillContacts x u).Nonempty) :
    earlyOrdinaryContactComponents G h x u = ∅ ∧ ¬ G.Adj u h := by
  classical
  obtain ⟨p,hpC⟩ := hp
  have hup : G.Adj u p.val.val := (Finset.mem_filter.mp hpC).2
  have hcontact : G.Adj u x ∨
      ∃ a : {a : evenVertices G // (evenSubgraph G).Adj x a}, G.Adj u a.val.val :=
    Or.inr ⟨p,hup⟩
  obtain ⟨f,P,hinv,_,hindex,hedge,_⟩ :=
    bare_windmill_contact_preparation_cases h x H C hxC u hcontact
  have hzero : earlyOrdinaryContactComponents G h x u = ∅ := by
    rcases bare_canonical_early_zero_or_t3 h u x H C hxC f hinv hedge P hindex
      p hup huOdd with hz | ⟨Z,hF,hthree⟩
    · exact hz
    · exact False.elim (bare_canonical_t3_positive_contacts_impossible h u x H
        huOdd ⟨p,hpC⟩ Z hF hthree f hinv hedge P hindex)
  refine ⟨hzero,?_⟩
  intro huh
  exact bare_canonical_protected_zero_impossible h u x H C hxC huOdd huh hcontact hzero

/-- Every even neighbour of an odd centre with a private contact belongs to
the contacted windmill. This supplies the local separation required at the
first internal vertex of the reserved corridor. -/
theorem bare_canonical_private_contact_even_neighbors
    (h u : V) (x : evenVertices G) (H : BareMinimalCounterexample G h (x : V))
    (C : (evenSubgraph G).ConnectedComponent) (hxC : x ∈ C.supp)
    (huOdd : Odd (G.degree u)) (hp : (windmillContacts x u).Nonempty) :
    ∀ t, G.Adj u t → Even (G.degree t) →
      t = (x : V) ∨ t ∈ windmillPrivateSet x (windmillContacts x u) := by
  classical
  obtain ⟨hzero,huh⟩ :=
    bare_canonical_private_contact_residual h u x H C hxC huOdd hp
  obtain ⟨_,_,hcontacts,_,hclasses⟩ := bare_early_canonical_contact_guards h u x H
  intro t hut ht
  rcases hcontacts t hut ht with hx | hh | hs
  · exact Or.inl hx
  · exact False.elim (huh (hh ▸ hut))
  · rcases hclasses ⟨t,ht⟩ hs with hw | ho
    · exact Or.inr hw
    · rw [hzero] at ho
      simpa using ho

end Gallai.TwoException
