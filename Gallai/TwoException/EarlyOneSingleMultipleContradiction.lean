/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.EarlyOneSingleResidual
public import Gallai.TwoException.EarlySelectedOddSingleContradiction

@[expose] public section

/-! # Canonical one-single branch with multiple ordinary components -/
namespace Gallai.TwoException
open scoped Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
noncomputable local instance oneSingleMultipleComponents :
    DecidableEq (evenSubgraph G).ConnectedComponent := Classical.decEq _

/-- With at least two touched ordinary components, a canonical one-single
contact profile is impossible. Both baseline parities are covered; no packet,
auxiliary decomposition, recipient reserve or T2 availability is assumed. -/
theorem bare_canonical_one_single_multiple_impossible
    (h u : V) (x : evenVertices G) (H : BareMinimalCounterexample G h (x : V))
    (f : {a : evenVertices G // (evenSubgraph G).Adj x a} →
      {a : evenVertices G // (evenSubgraph G).Adj x a})
    (hinv : Function.Involutive f)
    (hedge : ∀ a b, (evenSubgraph G).Adj a.val b.val ↔ f a = b)
    (P : Finset {a : evenVertices G // (evenSubgraph G).Adj x a})
    (hindex : ∀ a, ∃! r, r ∈ P ∧ (a = r ∨ a = f r))
    (hone : #(singleContactPetals f P (windmillContacts x u)) = 1)
    (huOdd : Odd (G.degree u)) (hux : ¬ G.Adj u x)
    (hN : 2 ≤ #(earlyOrdinaryContactComponents G h x u)) : False := by
  classical
  let S := earlyOriginalContacts G h x u
  let F := earlyOrdinaryContactComponents G h x u
  let C := windmillContacts x u
  obtain ⟨hFeven,hnoT2⟩ := bare_canonical_one_single_residual
    h u x H f hinv hedge P hindex hone huOdd hux hN
  have hfree : ∀ a, f a ≠ a := by
    intro a he
    exact (evenSubgraph G).irrefl ((hedge a a).mpr he)
  obtain ⟨p,hpC,hfpC,hsingle⟩ :=
    one_single_contact_selection f hinv P C hone
  have hcard := indexed_petal_contact_card f hfree P C hindex
  change #C = #(singleContactPetals f P C) + 2 * #(doubleContactPetals f P C) at hcard
  have hCodd : Odd #C := by
    change #(singleContactPetals f P C) = 1 at hone
    rw [hone] at hcard
    rw [Nat.odd_iff]
    omega
  have hnotTwo : ∀ Z ∈ F, #(ordinaryComponentPacket G S Z) ≠ 2 := by
    intro Z hZ he
    have hm : Z ∈ F.filter (fun Z => #(ordinaryComponentPacket G S Z) = 2) :=
      Finset.mem_filter.mpr ⟨hZ,he⟩
    rw [hnoT2] at hm
    simpa using hm
  obtain ⟨hF,hx,hclass,hS,hcover⟩ := bare_early_canonical_contact_guards h u x H
  exact bare_selected_early_odd_star_sole_single_impossible h u x H f hinv hedge P hindex
    p hpC hfpC hsingle S F hF hx hclass hS hcover huOdd hux hN hCodd hFeven hnotTwo

end Gallai.TwoException
