/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Paths

@[expose] public section

/-!
# Nonempty simple paths and edge partitions

This project-local representation uses Mathlib walks and unordered edges.
Decompositions have finitely many indexed paths and cover each graph edge
exactly once. Isolated vertices contribute no path.
-/

namespace Gallai

universe u

variable {V : Type u} (G : SimpleGraph V)

/-- A simple graph path containing at least one edge. -/
structure NonemptyPath where
  /-- Initial vertex of the chosen orientation. -/
  start : V
  /-- Final vertex of the chosen orientation. -/
  finish : V
  /-- Underlying Mathlib walk. -/
  walk : G.Walk start finish
  /-- No vertex repeats along the walk. -/
  isPath : walk.IsPath
  /-- At least one edge is traversed. -/
  nonempty : ¬ walk.Nil

/-- A nonempty simple path cannot have equal endpoints. -/
theorem NonemptyPath.start_ne_finish (P : NonemptyPath G) : P.start ≠ P.finish := by
  intro h
  exact P.nonempty (P.isPath.nil_iff_eq.mpr h)

/-- An indexed edge partition into nonempty simple paths. -/
structure Decomposition where
  /-- Number of nonempty paths. -/
  size : ℕ
  /-- Indexed family of paths. -/
  path : Fin size → NonemptyPath G
  /-- Every graph edge occurs on exactly one indexed path. -/
  covers : ∀ e ∈ G.edgeSet, ∃! i, e ∈ (path i).walk.edges

/-- The edgeless graph has a decomposition with no paths. -/
def Decomposition.empty : Decomposition (⊥ : SimpleGraph V) where
  size := 0
  path := Fin.elim0
  covers := by simp

/-- The empty decomposition uses zero paths. -/
@[simp] theorem Decomposition.empty_size :
    (Decomposition.empty : Decomposition (⊥ : SimpleGraph V)).size = 0 := rfl

/-- Existence of a decomposition within a budget, without choosing a minimum. -/
def HasPathBudget (k : ℕ) : Prop := ∃ D : Decomposition G, D.size ≤ k

/-- Zero paths suffice for the edgeless graph on any vertex type. -/
theorem empty_hasPathBudget : HasPathBudget (⊥ : SimpleGraph V) 0 :=
  ⟨Decomposition.empty, Nat.le_refl 0⟩

end Gallai
