/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.Structure.LeafTransfer
public import Gallai.Operations.Suppression

@[expose] public section

/-! # Exact graph identity for the all-odd auxiliary return -/

namespace Gallai

universe u
variable {V : Type u}

/-- Close the transferred leaf by restoring the donor-to-new-vertex edge. -/
abbrev closedLeafTransfer (G : SimpleGraph V) (x y : V) : SimpleGraph (V ⊕ Unit) :=
  leafTransfer G x y ⊔ SimpleGraph.edge (.inl x) (.inr ())

/-- The closed auxiliary has exactly the prescribed neighbours at its new vertex. -/
theorem closedLeafTransfer_adj_new (G : SimpleGraph V) (x y : V) (v : V ⊕ Unit) :
    (closedLeafTransfer G x y).Adj (.inr ()) v ↔ v = .inl x ∨ v = .inl y := by
  rw [SimpleGraph.sup_adj, leafTransfer_adj_new]
  cases v <;> simp [SimpleGraph.edge_adj, eq_comm, or_comm]

/-- The removed old edge is still absent after closing the new leaf. -/
theorem closedLeafTransfer_missing (G : SimpleGraph V) (x y : V) :
    ¬ (closedLeafTransfer G x y).Adj (.inl x) (.inl y) := by
  rw [SimpleGraph.sup_adj, leafTransfer_adj_old]
  simp [SimpleGraph.deleteEdges_adj, SimpleGraph.edge_adj]

/-- Suppressing the new vertex restores precisely the graph image of G. -/
theorem closedLeafTransfer_suppressed (G : SimpleGraph V) (x y : V) (hxy : G.Adj x y) :
    suppressedGraph (closedLeafTransfer G x y) (.inr ()) (.inl x) (.inl y) =
      G.map (Function.Embedding.inl : V ↪ V ⊕ Unit) := by
  classical
  ext a b
  cases a with
  | inl a =>
    cases b with
    | inl b =>
      have h := congrArg (fun J : SimpleGraph V => J.Adj a b)
        (delete_edge_sup_edge G x y hxy)
      simpa [suppressedGraph, closedLeafTransfer, leafTransfer, SimpleGraph.deleteEdges_adj,
        SimpleGraph.edge_adj, SimpleGraph.map_adj] using h
    | inr b =>
      cases b
      simp [suppressedGraph, SimpleGraph.deleteEdges_adj, SimpleGraph.map_adj]
  | inr a =>
    cases a
    simp [suppressedGraph, SimpleGraph.deleteEdges_adj, SimpleGraph.map_adj]

variable [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Local classical adjacency decision for finite degrees of the closed auxiliary. -/
noncomputable local instance (x y : V) : DecidableRel (closedLeafTransfer G x y).Adj :=
  fun _ _ => Classical.propDecidable _

omit [DecidableRel G.Adj] in
/-- The new vertex has degree exactly two when the old ends are distinct. -/
theorem closedLeafTransfer_degree_new (x y : V) (hxy : x ≠ y) :
    (closedLeafTransfer G x y).degree (.inr ()) = 2 := by
  have hs : (closedLeafTransfer G x y).neighborFinset (.inr ()) = {.inl x, .inl y} := by
    ext v
    simp only [SimpleGraph.mem_neighborFinset, closedLeafTransfer_adj_new,
      Finset.mem_insert, Finset.mem_singleton]
  rw [← SimpleGraph.card_neighborFinset_eq_degree, hs]
  simp [hxy]

omit [DecidableRel G.Adj] in
/-- A closed auxiliary decomposition with no new-vertex endpoints returns to
the exact image of G, preserving size and every endpoint multiplicity. -/
theorem Decomposition.suppress_closedLeafTransfer (x y : V) (hxy : G.Adj x y)
    (D : Decomposition (closedLeafTransfer G x y)) (hz : D.endpointCount (.inr ()) = 0) :
    ∃ E : Decomposition (G.map (Function.Embedding.inl : V ↪ V ⊕ Unit)),
      E.size = D.size ∧ ∀ v, E.endpointCount v = D.endpointCount v := by
  -- Transport all dependent witness properties together with the graph identity.
  have hresult := D.suppress_degree_two (.inr ()) (.inl x) (.inl y)
    (by simpa using hxy.ne) (closedLeafTransfer_degree_new G x y hxy.ne) hz
    (fun v h => (closedLeafTransfer_adj_new G x y v).mp h)
    (closedLeafTransfer_missing G x y)
  rw [closedLeafTransfer_suppressed G x y hxy] at hresult
  exact hresult

end Gallai
