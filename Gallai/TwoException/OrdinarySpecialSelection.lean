/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.OrdinarySpecialPacket

@[expose] public section

/-! # Parity-dependent selection of a special two-contact preparation -/
namespace Gallai.TwoException
open scoped Finset

/-- Switching one regular T2 packet to special adds one star deletion.
Choose at most one eligible packet, only when needed, so every surviving
regular T2 has an even total deletion count. The special packet count is
bounded by the resulting centre reserve indicator. -/
theorem select_special_ordinary_packet
    {I : Type*} [DecidableEq I] (eligible : Finset I) (k : ℕ) :
    ∃ special : Finset I,
      special ⊆ eligible ∧ #special ≤ 1 ∧
      (Even k → special = ∅) ∧
      ((eligible \ special).Nonempty → Even (k + #special)) ∧
      #special ≤ (if Even (k + #special) then 1 else 0) := by
  classical
  by_cases hk : Even k
  · refine ⟨∅, Finset.empty_subset _, by simp, fun _ => rfl, ?_, ?_⟩
    · intro _
      simpa using hk
    · simp
  · by_cases he : eligible.Nonempty
    · obtain ⟨i, hi⟩ := he
      have hodd : Odd k := (Nat.even_or_odd k).resolve_left hk
      have hnext : Even (k + 1) := by
        rw [Nat.odd_iff] at hodd
        rw [Nat.even_iff]
        omega
      refine ⟨{i}, Finset.singleton_subset_iff.mpr hi, by simp, ?_, ?_, ?_⟩
      · intro h
        exact False.elim (hk h)
      · intro _
        simpa using hnext
      · simpa [hnext]
    · have hz : eligible = ∅ := Finset.not_nonempty_iff_eq_empty.mp he
      refine ⟨∅, Finset.empty_subset _, by simp, ?_, ?_, ?_⟩
      · intro h
        exact False.elim (hk h)
      · intro hs
        simp [hz] at hs
      · simp

end Gallai.TwoException
