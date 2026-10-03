/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.Structure.OneExceptionStarPuncture

@[expose] public section

/-! # Retaining an off-hub exception through an even-star puncture -/

namespace Gallai

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Fix the finite adjacency decision used for exceptional-star degree counts. -/
noncomputable local instance starExceptionAdj (u : V) :
    DecidableRel (evenStarPuncture G u).Adj := fun _ _ => Classical.propDecidable _

/-- The punctured centre has E-degree zero; every other even vertex inherits
its bound, except the same permitted exception x. -/
theorem evenStarPuncture_cap_except (u x : V)
    (hcap : ∀ v, Even (G.degree v) → v ≠ x → eDegree G v ≤ 3) :
    ∀ v, Even ((evenStarPuncture G u).degree v) → v ≠ x →
      eDegree (evenStarPuncture G u) v ≤ 3 := by
  classical
  intro v hv hvx
  by_cases hvu : v = u
  · subst v
    have hz : evenNeighbors (evenStarPuncture G u) u = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro w hw
      obtain ⟨ha, he⟩ := (mem_evenNeighbors u w).mp hw
      exact evenStarPuncture_no_even_neighbor G u w ha he
    simp [eDegree, hz]
  · have he := (evenStarPuncture_even_off_center G u v hvu hv).1
    apply (Finset.card_le_card (s := evenNeighbors (evenStarPuncture G u) v)
      (t := evenNeighbors G v) ?_).trans (hcap v he hvx)
    intro w hw
    obtain ⟨ha, he⟩ := (mem_evenNeighbors v w).mp hw
    have hwu : w ≠ u := by
      intro h
      subst w
      exact evenStarPuncture_no_even_neighbor G u v ha.symm hv
    exact (mem_evenNeighbors v w).mpr ⟨ha.1,
      (evenStarPuncture_even_off_center G u w hwu he).1⟩

/-- If the punctured centre `u` is adjacent to the only other exceptional
vertex `x`, then both are odd after the full even-star puncture.  Thus a
two-exception subcubic cap becomes an unconditional cap on the puncture. -/
theorem evenStarPuncture_cap_two_exceptions (u x : V) (hux : G.Adj u x)
    (hcap : ∀ v, Even (G.degree v) → v ≠ u → v ≠ x → eDegree G v ≤ 3) :
    ∀ v, Even ((evenStarPuncture G u).degree v) →
      eDegree (evenStarPuncture G u) v ≤ 3 := by
  classical
  intro v hv
  by_cases hvu : v = u
  · subst v
    have hz : evenNeighbors (evenStarPuncture G u) u = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro w hw
      obtain ⟨ha, he⟩ := (mem_evenNeighbors u w).mp hw
      exact evenStarPuncture_no_even_neighbor G u w ha he
    simp [eDegree, hz]
  by_cases hvx : v = x
  · subst v
    exact (Nat.not_even_iff_odd.mpr
      (evenStarPuncture_odd_neighbor G u x hux)) hv |>.elim
  have he := (evenStarPuncture_even_off_center G u v hvu hv).1
  apply (Finset.card_le_card (s := evenNeighbors (evenStarPuncture G u) v)
    (t := evenNeighbors G v) ?_).trans (hcap v he hvu hvx)
  intro w hw
  obtain ⟨ha, he⟩ := (mem_evenNeighbors v w).mp hw
  have hwu : w ≠ u := by
    intro h
    subst w
    exact evenStarPuncture_no_even_neighbor G u v ha.symm hv
  exact (mem_evenNeighbors v w).mpr ⟨ha.1,
    (evenStarPuncture_even_off_center G u w hwu he).1⟩

/-- A positive E-degree deletes an actual edge, giving the strict measure for
recursion on the spanning puncture, without a supplied strictness witness. -/
theorem evenStarPuncture_edge_count_lt (u : V) (hp : 0 < eDegree G u) :
    (evenStarPuncture G u).edgeFinset.card < G.edgeFinset.card := by
  classical
  obtain ⟨v, hv⟩ := Finset.card_pos.mp hp
  have hlt : evenStarPuncture G u < G := by
    refine lt_of_le_not_ge (fun _ _ h => h.1) ?_
    intro hle
    exact starPuncture_missing G u (evenNeighbors G u) (by simp) v hv
      (hle ((mem_evenNeighbors u v).mp hv).1)
  have h := Finset.card_lt_card (SimpleGraph.edgeFinset_strict_mono hlt)
  simpa only [SimpleGraph.edgeFinset, ← Set.ncard_eq_toFinset_card'] using h

end Gallai
