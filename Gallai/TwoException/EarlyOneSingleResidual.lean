/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.EarlySoleSingleSelection

@[expose] public section

/-! # Exact residual of the canonical one-single early branch -/
namespace Gallai.TwoException
open scoped Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
noncomputable local instance oneSingleResidualComponents :
    DecidableEq (evenSubgraph G).ConnectedComponent := Classical.decEq _

/-- In the canonical one-single profile with at least two ordinary
components, bare minimality forces even ordinary count and absence of a
two-contact triangle. This identifies the odd-star alternative precisely. -/
theorem bare_canonical_one_single_residual
    (h u : V) (x : evenVertices G) (H : BareMinimalCounterexample G h (x : V))
    (f : {a : evenVertices G // (evenSubgraph G).Adj x a} →
      {a : evenVertices G // (evenSubgraph G).Adj x a})
    (hinv : Function.Involutive f)
    (hedge : ∀ a b, (evenSubgraph G).Adj a.val b.val ↔ f a = b)
    (P : Finset {a : evenVertices G // (evenSubgraph G).Adj x a})
    (hindex : ∀ a, ∃! r, r ∈ P ∧ (a = r ∨ a = f r))
    (hone : #(singleContactPetals f P (windmillContacts x u)) = 1)
    (huOdd : Odd (G.degree u)) (hux : ¬ G.Adj u x)
    (hN : 2 ≤ #(earlyOrdinaryContactComponents G h x u)) :
    let S := earlyOriginalContacts G h x u
    let F := earlyOrdinaryContactComponents G h x u
    Even #F ∧ (F.filter (fun Z => #(ordinaryComponentPacket G S Z) = 2)) = ∅ := by
  classical
  let S := earlyOriginalContacts G h x u
  let F := earlyOrdinaryContactComponents G h x u
  let C := windmillContacts x u
  have hfree : ∀ a, f a ≠ a := by
    intro a he
    exact (evenSubgraph G).irrefl ((hedge a a).mpr he)
  have hcard := indexed_petal_contact_card f hfree P C hindex
  change #C = #(singleContactPetals f P C) + 2 * #(doubleContactPetals f P C) at hcard
  have hCodd : Odd #C := by
    change #(singleContactPetals f P C) = 1 at hone
    rw [hone] at hcard
    rw [Nat.odd_iff]
    omega
  have hNoT2 : ¬ (F.filter (fun Z => #(ordinaryComponentPacket G S Z) = 2)).Nonempty := by
    intro ht
    exact bare_canonical_one_single_impossible h u x H f hinv hedge P hindex
      hone huOdd hux hN (Or.inr ht)
  have hFeven : Even #F := by
    apply Nat.not_odd_iff_even.mp
    intro ho
    apply bare_canonical_one_single_impossible h u x H f hinv hedge P hindex
      hone huOdd hux hN
    apply Or.inl
    change Even (#C + #F + 2 * #(F.filter
      (fun Z => #(ordinaryComponentPacket G S Z) = 3)))
    rw [Nat.even_iff]
    rw [Nat.odd_iff] at ho hCodd
    omega
  exact ⟨hFeven,Finset.not_nonempty_iff_eq_empty.mp hNoT2⟩

end Gallai.TwoException
