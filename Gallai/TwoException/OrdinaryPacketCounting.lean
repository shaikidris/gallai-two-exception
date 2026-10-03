/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.OrdinaryFailureContribution

@[expose] public section

/-! # Selected-minus-pending bounds for ordinary triangle packets -/
namespace Gallai.TwoException
open scoped Finset
variable {V : Type*} [DecidableEq V]

/-- A three-contact packet contributes at least one when each pending
contact forces the other two contacts to be selected. -/
theorem ordinary_three_packet_contribution
    (L A : Finset V) (hcard : #L = 3)
    (hforced : ∀ w ∈ L \ A, L.erase w ⊆ A) :
    #(L \ A) + 1 ≤ #(L ∩ A) := by
  classical
  by_cases hp : (L \ A).Nonempty
  · obtain ⟨w, hw⟩ := hp
    have hwL := (Finset.mem_sdiff.mp hw).1
    have hsub : L.erase w ⊆ L ∩ A := by
      intro t ht
      exact Finset.mem_inter.mpr ⟨Finset.mem_of_mem_erase ht, hforced w hw ht⟩
    have hc := Finset.card_le_card hsub
    have he := Finset.card_erase_of_mem hwL
    have hs := Finset.card_sdiff_add_card_inter L A
    omega
  · have hz : L \ A = ∅ := Finset.not_nonempty_iff_eq_empty.mp hp
    have hs := Finset.card_sdiff_add_card_inter L A
    simp only [hz, Finset.card_empty] at hs ⊢
    omega

/-- A special two-contact packet contributes nonnegatively when at least
one contact must be selected. It is the unique packet allowed zero gain. -/
theorem ordinary_special_packet_contribution
    (L A : Finset V) (hcard : #L = 2) (hselected : (L ∩ A).Nonempty) :
    #(L \ A) ≤ #(L ∩ A) := by
  have hp := Finset.card_pos.mpr hselected
  have hs := Finset.card_sdiff_add_card_inter L A
  omega

end Gallai.TwoException
