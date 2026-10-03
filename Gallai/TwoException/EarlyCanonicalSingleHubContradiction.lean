/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.EarlySelectedHubContradiction
public import Gallai.TwoException.EarlyCanonicalDelayedResidual

@[expose] public section

/-! # Canonical single-contact hub branch -/
namespace Gallai.TwoException
open scoped Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
noncomputable local instance canonicalSingleHubComponents :
    DecidableEq (evenSubgraph G).ConnectedComponent := Classical.decEq _

/-- One single-contact petal, a hub contact and at least two ordinary
components contradict bare minimality. Packet parity is derived from the
canonical delayed residual, not supplied as a numerical certificate. -/
theorem bare_canonical_single_hub_impossible
    (h u : V) (x : evenVertices G) (H : BareMinimalCounterexample G h (x : V))
    (Z : (evenSubgraph G).ConnectedComponent) (hxZ : x ∈ Z.supp)
    (f : {a : evenVertices G // (evenSubgraph G).Adj x a} →
      {a : evenVertices G // (evenSubgraph G).Adj x a})
    (hinv : Function.Involutive f)
    (hedge : ∀ a b, (evenSubgraph G).Adj a.val b.val ↔ f a = b)
    (P : Finset {a : evenVertices G // (evenSubgraph G).Adj x a})
    (hindex : ∀ a, ∃! r, r ∈ P ∧ (a = r ∨ a = f r))
    (p : {a : evenVertices G // (evenSubgraph G).Adj x a})
    (hup : G.Adj u p.val.val) (hu : Odd (G.degree u)) (hux : G.Adj u x)
    (hone : #(singleContactPetals f P (windmillContacts x u)) = 1)
    (hsingle : ∀ r ∈ singleContactPetals f P (windmillContacts x u),
      ∀ a ∈ windmillContacts x u ∩ ({r,f r} : Finset _), a = p)
    (hN : 2 ≤ #(earlyOrdinaryContactComponents G h x u)) : False := by
  classical
  have hres := bare_canonical_delayed_multiple_residual h u x H Z hxZ p hup hu hN
  have hfree : ∀ a, f a ≠ a := by
    intro a he
    exact (evenSubgraph G).irrefl ((hedge a a).mpr he)
  have hcard := indexed_petal_contact_card f hfree P (windmillContacts x u) hindex
  change #(windmillContacts x u) =
    #(singleContactPetals f P (windmillContacts x u)) +
    2 * #(doubleContactPetals f P (windmillContacts x u)) at hcard
  rw [hone] at hcard
  have havailable : Even (1 + #(windmillContacts x u) +
      #(earlyOrdinaryContactComponents G h x u) + 2 *
      #((earlyOrdinaryContactComponents G h x u).filter
        (fun C => #(ordinaryComponentPacket G (earlyOriginalContacts G h x u) C) = 3))) ∨
      ((earlyOrdinaryContactComponents G h x u).filter
        (fun C => #(ordinaryComponentPacket G (earlyOriginalContacts G h x u) C) = 2)).Nonempty := by
    apply Or.inl
    have heven := hres.1
    rw [Nat.even_iff] at heven ⊢
    omega
  obtain ⟨hF,hx,hclass,hS,hcover⟩ := bare_early_canonical_contact_guards h u x H
  exact bare_selected_early_hub_impossible h u x H f hinv hedge P hindex p
    (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hup⟩) hsingle
    (earlyOriginalContacts G h x u) (earlyOrdinaryContactComponents G h x u)
    hF hx hclass hS hcover hu hux hN havailable

/-- The unique single-contact petal supplies its own contact vertex. No
distinguished private vertex or contact-selection witness is an input. -/
theorem bare_canonical_one_single_hub_impossible
    (h u : V) (x : evenVertices G) (H : BareMinimalCounterexample G h (x : V))
    (Z : (evenSubgraph G).ConnectedComponent) (hxZ : x ∈ Z.supp)
    (f : {a : evenVertices G // (evenSubgraph G).Adj x a} →
      {a : evenVertices G // (evenSubgraph G).Adj x a})
    (hinv : Function.Involutive f)
    (hedge : ∀ a b, (evenSubgraph G).Adj a.val b.val ↔ f a = b)
    (P : Finset {a : evenVertices G // (evenSubgraph G).Adj x a})
    (hindex : ∀ a, ∃! r, r ∈ P ∧ (a = r ∨ a = f r))
    (hu : Odd (G.degree u)) (hux : G.Adj u x)
    (hone : #(singleContactPetals f P (windmillContacts x u)) = 1)
    (hN : 2 ≤ #(earlyOrdinaryContactComponents G h x u)) : False := by
  classical
  let C := windmillContacts x u
  obtain ⟨r,hr⟩ := Finset.card_eq_one.mp hone
  have hrmem : r ∈ singleContactPetals f P C := by
    rw [hr]; exact Finset.mem_singleton_self r
  have hprofile := (Finset.mem_filter.mp hrmem).2
  have hchoose : ∃ p ∈ C, ∀ s ∈ singleContactPetals f P C,
      ∀ a ∈ C ∩ ({s,f s} : Finset _), a = p := by
    rcases hprofile with hleft | hright
    · refine ⟨r,hleft.1,?_⟩
      intro s hs a ha
      have hsr : s = r := by rw [hr] at hs; exact Finset.mem_singleton.mp hs
      subst s
      obtain ⟨haC,haPair⟩ := Finset.mem_inter.mp ha
      rcases Finset.mem_insert.mp haPair with ha | ha
      · exact ha
      · exact False.elim (hleft.2 (Finset.mem_singleton.mp ha ▸ haC))
    · refine ⟨f r,hright.2,?_⟩
      intro s hs a ha
      have hsr : s = r := by rw [hr] at hs; exact Finset.mem_singleton.mp hs
      subst s
      obtain ⟨haC,haPair⟩ := Finset.mem_inter.mp ha
      rcases Finset.mem_insert.mp haPair with ha | ha
      · exact False.elim (hright.1 (ha ▸ haC))
      · exact Finset.mem_singleton.mp ha
  obtain ⟨p,hp,hsingle⟩ := hchoose
  exact bare_canonical_single_hub_impossible h u x H Z hxZ f hinv hedge P hindex p
    (Finset.mem_filter.mp hp).2 hu hux hone hsingle hN

end Gallai.TwoException
