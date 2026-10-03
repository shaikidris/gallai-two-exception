/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.EarlyCanonicalT3E3Contradiction
public import Gallai.TwoException.EarlySinglePetalCount

@[expose] public section

/-! # Canonical single-petal choice in the remaining T3 hub row -/
namespace Gallai.TwoException
open scoped Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The remaining T3 hub row supplies a contacted private with uncontacted
mate and the odd E4 star obtained by exempting that private. -/
theorem bare_canonical_t3_hub_single_selection
    (h u : V) (x : evenVertices G) (H : BareMinimalCounterexample G h (x : V))
    (huOdd : Odd (G.degree u)) (hux : G.Adj u x)
    (hp : (windmillContacts x u).Nonempty)
    (Z : (evenSubgraph G).ConnectedComponent)
    (hF : earlyOrdinaryContactComponents G h x u = {Z})
    (hthree : #(ordinaryComponentPacket G (earlyOriginalContacts G h x u) Z) = 3)
    (f : {a : evenVertices G // (evenSubgraph G).Adj x a} →
      {a : evenVertices G // (evenSubgraph G).Adj x a})
    (hinv : Function.Involutive f)
    (hedge : ∀ a b, (evenSubgraph G).Adj a.val b.val ↔ f a = b)
    (P : Finset {a : evenVertices G // (evenSubgraph G).Adj x a})
    (hindex : ∀ a, ∃! r, r ∈ P ∧ (a = r ∨ a = f r)) :
    ∃ p : {a : evenVertices G // (evenSubgraph G).Adj x a},
      p ∈ windmillContacts x u ∧ f p ∉ windmillContacts x u ∧
      G.Adj p.val.val (f p).val.val ∧ ¬ G.Adj u (f p).val.val ∧
      Odd #(insert (x : V)
        ((windmillPrivateSet x (windmillContacts x u)).erase p.val.val)) := by
  classical
  let C := windmillContacts x u
  have ho := bare_canonical_t3_hub_contacts_odd h u x H huOdd hux hp Z hF hthree
  change Odd #C at ho
  have hfree : ∀ a, f a ≠ a := by
    intro a he
    exact (evenSubgraph G).irrefl ((hedge a a).mpr he)
  have hcard := indexed_petal_contact_card f hfree P C hindex
  change #C = #(singleContactPetals f P C) + 2 * #(doubleContactPetals f P C) at hcard
  have hsingleOdd : Odd #(singleContactPetals f P C) := by
    rw [Nat.odd_iff] at ho ⊢
    omega
  have hnonempty : (singleContactPetals f P C).Nonempty := by
    apply Finset.card_pos.mp
    rw [Nat.odd_iff] at hsingleOdd
    omega
  obtain ⟨r,hr⟩ := hnonempty
  obtain ⟨p,_,hpC,hfp⟩ := single_contact_orientation f hinv P C r hr
  have hpSet : p.val.val ∈ windmillPrivateSet x C :=
    (mem_windmillPrivateSet x C _).mpr ⟨p,hpC,rfl⟩
  have hparity : Odd #(insert (x : V) ((windmillPrivateSet x C).erase p.val.val)) := by
    have hxnot := hub_not_mem_windmillPrivateSet x C
    have hxErase : (x : V) ∉ (windmillPrivateSet x C).erase p.val.val :=
      fun ht => hxnot (Finset.mem_of_mem_erase ht)
    have hcErase := Finset.card_erase_add_one hpSet
    rw [windmillPrivateSet_card] at hcErase
    rw [Finset.card_insert_of_notMem hxErase,Nat.odd_iff]
    rw [Nat.odd_iff] at ho
    omega
  refine ⟨p,hpC,hfp,(hedge p (f p)).mpr rfl,?_,hparity⟩
  intro hadj
  exact hfp (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hadj⟩)

end Gallai.TwoException
