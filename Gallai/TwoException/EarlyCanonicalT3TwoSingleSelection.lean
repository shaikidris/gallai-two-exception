/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.EarlyCanonicalT3E2Contradiction

@[expose] public section

/-! # Actual two-single-petal selection in the non-hub T3 residual -/
namespace Gallai.TwoException
open scoped Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Positive even contacts in the canonical non-hub residual supply two
disjoint single petals and the odd star formed by exempting one contact. -/
theorem bare_canonical_t3_nonhub_two_single_selection
    (h u : V) (x : evenVertices G) (H : BareMinimalCounterexample G h (x : V))
    (huOdd : Odd (G.degree u)) (hux : ¬ G.Adj u x)
    (ho : Even #(windmillContacts x u)) (hp : (windmillContacts x u).Nonempty)
    (Z : (evenSubgraph G).ConnectedComponent)
    (hF : earlyOrdinaryContactComponents G h x u = {Z})
    (hthree : #(ordinaryComponentPacket G (earlyOriginalContacts G h x u) Z) = 3)
    (f : {a : evenVertices G // (evenSubgraph G).Adj x a} →
      {a : evenVertices G // (evenSubgraph G).Adj x a})
    (hinv : Function.Involutive f)
    (hedge : ∀ a b, (evenSubgraph G).Adj a.val b.val ↔ f a = b)
    (P : Finset {a : evenVertices G // (evenSubgraph G).Adj x a})
    (hindex : ∀ a, ∃! r, r ∈ P ∧ (a = r ∨ a = f r)) :
    ∃ p r : {a : evenVertices G // (evenSubgraph G).Adj x a},
      p ∈ windmillContacts x u ∧ f p ∉ windmillContacts x u ∧
      r ∈ windmillContacts x u ∧ f r ∉ windmillContacts x u ∧
      Disjoint ({p,f p} : Finset _) {r,f r} ∧
      Odd #((windmillPrivateSet x (windmillContacts x u)).erase p.val.val) := by
  classical
  let C := windmillContacts x u
  have hd := bare_canonical_t3_nonhub_no_double h u x H huOdd hux ho
    Z hF hthree f hinv hedge P
  have hfree : ∀ a, f a ≠ a := by
    intro a he
    exact (evenSubgraph G).irrefl ((hedge a a).mpr he)
  have hc := indexed_petal_contact_card f hfree P C hindex
  change #C = #(singleContactPetals f P C) + 2 * #(doubleContactPetals f P C) at hc
  have hz : doubleContactPetals f P C = ∅ := hd
  rw [hz,Finset.card_empty] at hc
  have hpos : 0 < #C := Finset.card_pos.mpr hp
  have htwo : 1 < #(singleContactPetals f P C) := by
    rw [Nat.even_iff] at ho
    change #C % 2 = 0 at ho
    omega
  obtain ⟨p,r,hpC,hfpC,hrC,hfrC,hdis⟩ := two_single_contact_petals f hinv P C hindex
    (Finset.one_lt_card.mp htwo)
  have hpSet : p.val.val ∈ windmillPrivateSet x C :=
    (mem_windmillPrivateSet x C _).mpr ⟨p,hpC,rfl⟩
  have herase := Finset.card_erase_add_one hpSet
  rw [windmillPrivateSet_card] at herase
  refine ⟨p,r,hpC,hfpC,hrC,hfrC,hdis,?_⟩
  rw [Nat.even_iff] at ho
  rw [Nat.odd_iff]
  change #((windmillPrivateSet x C).erase p.val.val) % 2 = 1
  change #C % 2 = 0 at ho
  omega

end Gallai.TwoException
