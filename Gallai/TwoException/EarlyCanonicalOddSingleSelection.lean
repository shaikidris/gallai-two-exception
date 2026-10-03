/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.EarlyCanonicalT3SingleSelection

@[expose] public section

/-! # Single-petal selection for an odd private-contact star -/
namespace Gallai.TwoException
open scoped Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Odd private-contact cardinality supplies the unpaid mate for the
non-hub E1 schedule, without a minimal-counterexample assumption. -/
theorem odd_private_contacts_single_selection
    (u : V) (x : evenVertices G)
    (f : {a : evenVertices G // (evenSubgraph G).Adj x a} →
      {a : evenVertices G // (evenSubgraph G).Adj x a})
    (hinv : Function.Involutive f)
    (hedge : ∀ a b, (evenSubgraph G).Adj a.val b.val ↔ f a = b)
    (P : Finset {a : evenVertices G // (evenSubgraph G).Adj x a})
    (hindex : ∀ a, ∃! r, r ∈ P ∧ (a = r ∨ a = f r))
    (ho : Odd #(windmillContacts x u)) :
    ∃ p : {a : evenVertices G // (evenSubgraph G).Adj x a},
      p ∈ windmillContacts x u ∧ f p ∉ windmillContacts x u ∧
      G.Adj p.val.val (f p).val.val ∧ ¬ G.Adj u (f p).val.val ∧
      Odd #(windmillPrivateSet x (windmillContacts x u)) := by
  classical
  let C := windmillContacts x u
  have hfree : ∀ a, f a ≠ a := by
    intro a he
    exact (evenSubgraph G).irrefl ((hedge a a).mpr he)
  have hcard := indexed_petal_contact_card f hfree P C hindex
  change #C = #(singleContactPetals f P C) + 2 * #(doubleContactPetals f P C) at hcard
  have hsingleOdd : Odd #(singleContactPetals f P C) := by
    rw [Nat.odd_iff] at ho ⊢
    change #C % 2 = 1 at ho
    omega
  have hn : (singleContactPetals f P C).Nonempty := by
    apply Finset.card_pos.mp
    rw [Nat.odd_iff] at hsingleOdd
    omega
  obtain ⟨r,hr⟩ := hn
  obtain ⟨p,_,hp,hq⟩ := single_contact_orientation f hinv P C r hr
  refine ⟨p,hp,hq,(hedge p (f p)).mpr rfl,?_,?_⟩
  · intro hadj
    exact hq (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hadj⟩)
  · rw [windmillPrivateSet_card]
    exact ho

end Gallai.TwoException
