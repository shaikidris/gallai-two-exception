/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.Inputs.NormalizedRestore
public import Gallai.Inputs.AllOddReturn

@[expose] public section

/-! # Direct proof of the at-most-one-even-vertex path decomposition bound

The stronger induction permits isolated vertices and normalizes every endpoint
count. All reduction and return operations are proved in the imported modules.
-/

namespace Gallai

universe u

private theorem normalized_by_excess (n : ℕ) :
    ∀ (V : Type u) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      degreeExcess G = n →
      Set.Subsingleton {v | 0 < G.degree v ∧ Even (G.degree v)} →
      ∃ D : Decomposition G, ∀ v, D.endpointCount v = G.degree v % 2 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro V _ _ G _ hsize huniq
    classical
    by_cases hz : degreeExcess G = 0
    · exact exists_normalized_of_degreeExcess_zero hz
    by_cases hex : ∃ x, 0 < G.degree x ∧ Even (G.degree x)
    · obtain ⟨x, hpos, heven⟩ := hex
      have hx : 2 ≤ G.degree x := by
        have he := Nat.even_iff.mp heven
        omega
      obtain ⟨y, hxy⟩ := (G.degree_pos_iff_exists_adj x).mp hpos
      have hxuniq : ∀ v, 0 < G.degree v → Even (G.degree v) → v = x :=
        fun v hp he => huniq ⟨hp, he⟩ ⟨hpos, heven⟩
      have hu := (unique_even_after_delete x y hxy heven hxuniq).2
      have hsmall : degreeExcess (G.deleteEdges {s(x, y)}) < n := by
        rw [← hsize]
        exact degreeExcess_delete_lt G x y hxy hx
      obtain ⟨D, hn⟩ := ih _ hsmall V (G.deleteEdges {s(x, y)}) rfl
        (fun a ha b hb => (hu a ha.1 ha.2).trans (hu b hb.1 hb.2).symm)
      obtain ⟨E, _, he⟩ := D.restore_unique_even_normalized x y hxy heven hxuniq hn
      exact ⟨E, he⟩
    · have hodd : ∀ v, 0 < G.degree v → Odd (G.degree v) := by
        intro v hp
        apply Nat.not_even_iff_odd.mp
        exact fun he => hex ⟨v, hp, he⟩
      have hxexists : ∃ x, 2 ≤ G.degree x := by
        by_contra h
        apply hz
        apply (degreeExcess_eq_zero_iff G).mpr
        intro v
        by_contra hv
        exact h ⟨v, by omega⟩
      obtain ⟨x, hx⟩ := hxexists
      have hx3 : 3 ≤ G.degree x := by
        have ho := Nat.odd_iff.mp (hodd x (by omega))
        omega
      obtain ⟨y, hxy⟩ := (G.degree_pos_iff_exists_adj x).mp (by omega)
      let : DecidableRel (leafTransfer G x y).Adj := fun _ _ => Classical.propDecidable _
      have hu := (leafTransfer_unique_positive_even G x y hxy hx3 hodd).2.2
      have hsmall : degreeExcess (leafTransfer G x y) < n := by
        rw [← hsize]
        exact degreeExcess_leafTransfer_lt G x y hxy hx
      obtain ⟨D, hn⟩ := ih _ hsmall (V ⊕ Unit) (leafTransfer G x y) rfl
        (fun a ha b hb => (hu a ha.1 ha.2).trans (hu b hb.1 hb.2).symm)
      obtain ⟨E, _, he⟩ := D.restore_all_odd_normalized G x y hxy hx3 hodd hn
      exact ⟨E, he⟩

/-- At most one positive even vertex suffices for a decomposition with exactly
one endpoint at each odd vertex and none at any even vertex. -/
theorem exists_normalized_of_unique_positive_even {V : Type u} [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (huniq : Set.Subsingleton {v | 0 < G.degree v ∧ Even (G.degree v)}) :
    ∃ D : Decomposition G, ∀ v, D.endpointCount v = G.degree v % 2 :=
  normalized_by_excess (degreeExcess G) V G rfl huniq

/-- Lovasz's floor bound, with isolated vertices permitted in the stronger domain. -/
theorem pathBudget_of_unique_positive_even {V : Type u} [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (huniq : Set.Subsingleton {v | 0 < G.degree v ∧ Even (G.degree v)}) :
    HasPathBudget G (Fintype.card V / 2) := by
  obtain ⟨D, hn⟩ := exists_normalized_of_unique_positive_even G huniq
  exact ⟨D, D.size_le_half_of_normalized hn⟩

/-- The literal at-most-one-even-vertex floor bound, with no connectivity assumption. -/
theorem pathBudget_of_at_most_one_even {V : Type u} [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (huniq : Set.Subsingleton {v | Even (G.degree v)}) :
    HasPathBudget G (Fintype.card V / 2) :=
  pathBudget_of_unique_positive_even G (fun _ ha _ hb => huniq ha.2 hb.2)

end Gallai
