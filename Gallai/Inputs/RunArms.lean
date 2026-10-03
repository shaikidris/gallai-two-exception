/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.Inputs.Predecessor

@[expose] public section

/-! # Actual arms and exact carrier fibres of the existing run inventory -/

namespace Gallai.Decomposition

open scoped Finset

universe u

variable {V : Type u} {G : SimpleGraph V} [DecidableEq V]

/-- Orient the actual nonempty arm represented by a run toward its hub. -/
def runArm (D : Decomposition G) (a : V) : D.RunSlot a → NonemptyPath G
  | .inl i => (D.path i.val).toward a
  | .inr (i, false) =>
    (D.path i.val).takeTo a (Finset.mem_filter.mp i.property).2.1
      (Finset.mem_filter.mp i.property).2.2.1
  | .inr (i, true) =>
    ((D.path i.val).dropFrom a (Finset.mem_filter.mp i.property).2.1
      (Finset.mem_filter.mp i.property).2.2.2.symm).reverse

/-- Arm orientation realizes exactly the endpoint used in the predecessor relation. -/
theorem runArm_start (D : Decomposition G) (a : V) (r : D.RunSlot a) :
    (D.runArm a r).start = D.runEndpoint a r := by
  rcases r with i | ⟨i, b⟩
  · simp only [runArm, runEndpoint, NonemptyPath.toward]
    split <;> rfl
  · cases b <;> rfl

/-- Every oriented arm finishes at the same hub. -/
theorem runArm_finish (D : Decomposition G) (a : V) (r : D.RunSlot a) :
    (D.runArm a r).finish = a := by
  rcases r with i | ⟨i, b⟩
  · exact (D.path i.val).toward_finish a (Finset.mem_filter.mp i.property).2
  · cases b <;> rfl

/-- The arm's final predecessor is the neighbour recorded by the run inventory. -/
theorem runArm_predecessor (D : Decomposition G) (a : V) (r : D.RunSlot a) :
    (D.runArm a r).walk.reverse.snd = D.runNeighbor a r := by
  rcases r with i | ⟨i, b⟩
  · rfl
  · cases b
    · rfl
    · exact congrArg SimpleGraph.Walk.snd (SimpleGraph.Walk.reverse_reverse _)

/-- All oriented runs belonging to one old carrier. -/
def ownerRuns (D : Decomposition G) (a : V) (i : Fin D.size) : Finset (D.RunSlot a) :=
  Finset.univ.filter (fun r => D.runOwner a r = i)

/-- A terminal carrier has precisely its one terminal run. -/
theorem ownerRuns_terminal (D : Decomposition G) (a : V) (i : D.TerminalIndex a) :
    D.ownerRuns a i.val = {Sum.inl i} := by
  ext r
  simp only [ownerRuns, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  constructor
  · intro ho
    rcases r with j | ⟨j, b⟩
    · exact congrArg Sum.inl (Subtype.ext ho)
    · change j.val = i.val at ho
      have hj : j.val ∈ D.terminalCarriers a := ho.symm ▸ i.property
      exact False.elim ((Finset.disjoint_left.mp (D.disjoint_terminal_through a)) hj j.property)
  · rintro rfl
    rfl

/-- A through carrier has exactly its two sides, even when both are selected. -/
theorem ownerRuns_through (D : Decomposition G) (a : V) (i : D.ThroughIndex a) :
    D.ownerRuns a i.val = {Sum.inr (i, false), Sum.inr (i, true)} := by
  ext r
  simp only [ownerRuns, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro ho
    rcases r with j | ⟨j, b⟩
    · change j.val = i.val at ho
      have hj : j.val ∈ D.throughCarriers a := ho.symm ▸ i.property
      exact False.elim ((Finset.disjoint_left.mp (D.disjoint_terminal_through a)) j.property hj)
    · have hj : j = i := Subtype.ext ho
      subst j
      cases b <;> simp
  · rintro (rfl | rfl) <;> rfl

/-- An avoiding carrier has no hub runs. -/
theorem ownerRuns_avoiding (D : Decomposition G) (a : V) (i : Fin D.size)
    (ha : a ∉ (D.path i).walk.support) : D.ownerRuns a i = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro r hr
  have ho := (Finset.mem_filter.mp hr).2
  exact ha (ho ▸ D.runOwner_contains_hub a r)

/-- Owner fibres partition every selected-run sum without duplicating a through carrier. -/
theorem sum_ownerRuns (D : Decomposition G) (a : V) (f : D.RunSlot a → ℕ) :
    (∑ i : Fin D.size, ∑ r ∈ D.ownerRuns a i, f r) = ∑ r, f r := by
  simp only [ownerRuns, Finset.sum_filter]
  rw [Finset.sum_comm]
  simp

end Gallai.Decomposition
