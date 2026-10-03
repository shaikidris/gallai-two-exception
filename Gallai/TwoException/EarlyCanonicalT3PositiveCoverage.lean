/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.EarlyCanonicalT3E5Contradiction
public import Gallai.TwoException.EarlyCanonicalT3E1Contradiction
public import Gallai.TwoException.EarlyCanonicalT3HubContradiction

@[expose] public section

/-! # Exhaustive canonical singleton-T3 positive-private-contact coverage -/
namespace Gallai.TwoException
open scoped Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- All hub/non-hub and contact-parity rows are covered for a singleton
three-contact ordinary triangle and positive private contacts. -/
theorem bare_canonical_t3_positive_contacts_impossible
    (h u : V) (x : evenVertices G) (H : BareMinimalCounterexample G h (x : V))
    (huOdd : Odd (G.degree u)) (hp : (windmillContacts x u).Nonempty)
    (Z : (evenSubgraph G).ConnectedComponent)
    (hF : earlyOrdinaryContactComponents G h x u = {Z})
    (hthree : #(ordinaryComponentPacket G (earlyOriginalContacts G h x u) Z) = 3)
    (f : {a : evenVertices G // (evenSubgraph G).Adj x a} →
      {a : evenVertices G // (evenSubgraph G).Adj x a})
    (hinv : Function.Involutive f)
    (hedge : ∀ a b, (evenSubgraph G).Adj a.val b.val ↔ f a = b)
    (P : Finset {a : evenVertices G // (evenSubgraph G).Adj x a})
    (hindex : ∀ a, ∃! r, r ∈ P ∧ (a = r ∨ a = f r)) : False := by
  classical
  by_cases hux : G.Adj u x
  · exact bare_canonical_t3_hub_impossible h u x H huOdd hux hp Z hF hthree
      f hinv hedge P hindex
  · rcases Nat.even_or_odd #(windmillContacts x u) with he | ho
    · obtain ⟨p,r,hpC,hqC,hrC,hsC,hdis,_⟩ :=
        bare_canonical_t3_nonhub_two_single_selection h u x H huOdd hux he hp
          Z hF hthree f hinv hedge P hindex
      exact bare_canonical_t3_nonhub_selected_singles_impossible h u x H huOdd hux he
        Z hF hthree f hinv hedge p r hpC hqC hrC hsC hdis
    · exact bare_canonical_t3_nonhub_odd_impossible h u x H huOdd hux ho
        Z hF hthree f hinv hedge P hindex

end Gallai.TwoException
