/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.Operations.EraseCarrier
public import Mathlib.Combinatorics.SimpleGraph.Operations
public import Mathlib.Algebra.BigOperators.Option
public import Mathlib.Data.Fintype.Option

@[expose] public section

/-! # Insert a missing edge as one additional nonempty path -/

namespace Gallai.Decomposition

universe u
variable {V : Type u} {G : SimpleGraph V}

def edgePath (a b : V) (hab : a ≠ b) :
    NonemptyPath (G ⊔ SimpleGraph.edge a b) where
  start := a
  finish := b
  walk := .cons (Or.inr (by simp [SimpleGraph.edge_adj, hab])) .nil
  isPath := by simp [SimpleGraph.Walk.cons_isPath_iff, hab]
  nonempty := SimpleGraph.Walk.not_nil_cons

def insertEdgeFamily (D : Decomposition G) (a b : V) (hab : a ≠ b) :
    Option (Fin D.size) → NonemptyPath (G ⊔ SimpleGraph.edge a b)
  | none => edgePath a b hab
  | some i => (D.path i).transfer _ (fun _ he =>
      SimpleGraph.edgeSet_mono le_sup_left ((D.path i).walk.edges_subset_edgeSet he))

theorem insertEdgeFamily_covers (D : Decomposition G) (a b : V)
    (hab : a ≠ b) (hm : ¬ G.Adj a b) :
    ∀ e ∈ (G ⊔ SimpleGraph.edge a b).edgeSet,
      ∃! i, e ∈ (insertEdgeFamily D a b hab i).walk.edges := by
  intro e he
  have hf : s(a, b) ∉ G.edgeSet := hm
  rw [SimpleGraph.edgeSet_sup, SimpleGraph.edgeSet_edge_of_ne hab] at he
  rcases he with he | he
  · obtain ⟨i, hi, hu⟩ := D.covers e he
    refine ⟨some i, ?_, ?_⟩
    · simpa [insertEdgeFamily] using hi
    · intro j hj
      cases j with
      | none =>
        have hj : e = s(a, b) := by simpa [insertEdgeFamily, edgePath] using hj
        exact (hf (hj ▸ he)).elim
      | some j =>
        exact congrArg some (hu j (by simpa [insertEdgeFamily] using hj))
  · have he : e = s(a, b) := he
    subst e
    refine ⟨none, by simp [insertEdgeFamily, edgePath], ?_⟩
    intro j hj
    cases j with
    | none => rfl
    | some j =>
      have hj : s(a, b) ∈ (D.path j).walk.edges := by simpa [insertEdgeFamily] using hj
      exact (hf ((D.path j).walk.edges_subset_edgeSet hj)).elim

/-- Add a missing edge as its own path; existing carriers need no support avoidance. -/
noncomputable def insertEdge (D : Decomposition G) (a b : V)
    (hab : a ≠ b) (hm : ¬ G.Adj a b) : Decomposition (G ⊔ SimpleGraph.edge a b) :=
  ofFamily (insertEdgeFamily D a b hab) (insertEdgeFamily_covers D a b hab hm)

/-- Inserting the one-edge carrier increases the size by exactly one. -/
theorem insertEdge_size (D : Decomposition G) (a b : V)
    (hab : a ≠ b) (hm : ¬ G.Adj a b) : (D.insertEdge a b hab hm).size = D.size + 1 := by
  simp [insertEdge]

/-- The new path adds one endpoint at each end and changes no other endpoint count. -/
theorem insertEdge_endpointCount [DecidableEq V] (D : Decomposition G) (a b w : V)
    (hab : a ≠ b) (hm : ¬ G.Adj a b) :
    (D.insertEdge a b hab hm).endpointCount w = D.endpointCount w +
      (if a = w then 1 else 0) + (if b = w then 1 else 0) := by
  rw [insertEdge, ofFamily_endpointCount]
  rw [show (Finset.univ : Finset (Option (Fin D.size))) =
    Finset.insertNone Finset.univ by ext i; cases i <;> simp, Finset.sum_insertNone]
  simp only [insertEdgeFamily, edgePath, NonemptyPath.transfer, endpointCount]
  by_cases ha : a = w <;> by_cases hb : b = w
  all_goals
    simp only [ha, hb, if_true, if_false, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    congr 2

end Gallai.Decomposition
