/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.EarlyCanonicalContacts

@[expose] public section

/-! # Sole-single orientation from the exact petal count -/
namespace Gallai.TwoException
open scoped Finset

/-- One single-contact representative determines one contacted private
vertex, including when the mate rather than the representative is contacted. -/
theorem one_single_contact_selection
    {N : Type*} [DecidableEq N] (f : N → N) (hinv : Function.Involutive f)
    (P A : Finset N) (hone : #(singleContactPetals f P A) = 1) :
    ∃ p, p ∈ A ∧ f p ∉ A ∧
      ∀ r ∈ singleContactPetals f P A, ∀ a ∈ A ∩ ({r,f r} : Finset N), a = p := by
  obtain ⟨r,hr⟩ := Finset.card_eq_one.mp hone
  have hrmem : r ∈ singleContactPetals f P A := by rw [hr]; simp
  obtain ⟨p,hpr,hp,hfp⟩ := single_contact_orientation f hinv P A r hrmem
  refine ⟨p,hp,hfp,?_⟩
  intro s hs a ha
  have hsr : s = r := by rw [hr] at hs; exact Finset.mem_singleton.mp hs
  subst s
  obtain ⟨haA,haPair⟩ := Finset.mem_inter.mp ha
  have har : a = r ∨ a = f r := by simpa only [Finset.mem_insert,Finset.mem_singleton] using haPair
  rcases hpr with rfl | rfl
  · rcases har with he | he
    · exact he
    · exact False.elim (hfp (he ▸ haA))
  · rcases har with he | he
    · exact False.elim (hfp (by simpa only [hinv r] using (he ▸ haA)))
    · exact he

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
noncomputable local instance soleSelectionComponents :
    DecidableEq (evenSubgraph G).ConnectedComponent := Classical.decEq _

/-- The exact one-single profile invokes canonical early restoration
without an orientation or uniqueness certificate supplied by the caller. -/
theorem bare_canonical_one_single_impossible
    (h u : V) (x : evenVertices G) (H : BareMinimalCounterexample G h (x : V))
    (f : {a : evenVertices G // (evenSubgraph G).Adj x a} →
      {a : evenVertices G // (evenSubgraph G).Adj x a})
    (hinv : Function.Involutive f)
    (hedge : ∀ a b, (evenSubgraph G).Adj a.val b.val ↔ f a = b)
    (P : Finset {a : evenVertices G // (evenSubgraph G).Adj x a})
    (hindex : ∀ a, ∃! r, r ∈ P ∧ (a = r ∨ a = f r))
    (hone : #(singleContactPetals f P (windmillContacts x u)) = 1)
    (huOdd : Odd (G.degree u)) (hux : ¬ G.Adj u x)
    (hN : 2 ≤ #(earlyOrdinaryContactComponents G h x u))
    (havailable :
      let S := earlyOriginalContacts G h x u
      let F := earlyOrdinaryContactComponents G h x u
      Even (#(windmillContacts x u) + #F + 2 * #(F.filter
        (fun Z => #(ordinaryComponentPacket G S Z) = 3))) ∨
        (F.filter (fun Z => #(ordinaryComponentPacket G S Z) = 2)).Nonempty) : False := by
  obtain ⟨p,hp,hfp,hsingle⟩ := one_single_contact_selection f hinv P
    (windmillContacts x u) hone
  exact bare_canonical_early_sole_single_impossible h u x H f hinv hedge P hindex
    p hp hfp hsingle huOdd hux hN havailable

end Gallai.TwoException
