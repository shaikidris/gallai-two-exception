/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.Operations.EraseCarrier
public import Mathlib.Data.Nat.Find

@[expose] public section

/-!
# The attained path number of a finite graph

Every edge can be used as a singleton path. Thus a finite graph has a
decomposition, and its least attainable path budget is a genuine minimum.
Isolated vertices contribute nothing, including when the vertex type is empty.
-/

namespace Gallai

universe u

variable {V : Type u} {G : SimpleGraph V}

/-- Each graph edge is the exact edge list of a nonempty simple path. -/
theorem exists_singleEdgePath (e : Sym2 V) (he : e ∈ G.edgeSet) :
    ∃ P : NonemptyPath G, P.walk.edges = [e] := by
  induction e using Sym2.ind with
  | _ a b =>
    have hab : G.Adj a b := he
    refine ⟨⟨a, b, .cons hab .nil, ?_, ?_⟩, by simp⟩
    · simp [SimpleGraph.Walk.cons_isPath_iff, hab.ne]
    · simp

/-- A finite graph admits a path decomposition, by taking each edge separately. -/
theorem exists_pathBudget [Fintype V] (G : SimpleGraph V) :
    ∃ k, HasPathBudget G k := by
  classical
  let paths (e : G.edgeSet) : NonemptyPath G :=
    (exists_singleEdgePath (G := G) e.val e.property).choose
  have hedges (e : G.edgeSet) : (paths e).walk.edges = [e.val] :=
    (exists_singleEdgePath (G := G) e.val e.property).choose_spec
  have hcover : ∀ e ∈ G.edgeSet, ∃! i, e ∈ (paths i).walk.edges := by
    intro e he
    refine ⟨⟨e, he⟩, ?_, ?_⟩
    · simp [hedges]
    · intro i hi
      simp only [hedges, List.mem_singleton] at hi
      exact Subtype.ext hi.symm
  let D := Decomposition.ofFamily paths hcover
  exact ⟨D.size, D, le_rfl⟩

/-- The minimum number of nonempty simple paths partitioning all graph edges. -/
noncomputable def pathNumber [Fintype V] (G : SimpleGraph V) : ℕ := by
  classical
  exact Nat.find (exists_pathBudget G)

/-- The minimum path budget is itself attained as a budget. -/
theorem pathNumber_hasPathBudget [Fintype V] (G : SimpleGraph V) :
    HasPathBudget G (pathNumber G) := by
  classical
  exact Nat.find_spec (exists_pathBudget G)

/-- Every decomposition has at least the minimum number of paths. -/
theorem pathNumber_le_size [Fintype V] (D : Decomposition G) :
    pathNumber G ≤ D.size := by
  classical
  exact Nat.find_min' (exists_pathBudget G) ⟨D, le_rfl⟩

/-- A finite graph has a decomposition whose size is exactly its path number. -/
theorem exists_minimumDecomposition [Fintype V] (G : SimpleGraph V) :
    ∃ D : Decomposition G, D.size = pathNumber G := by
  obtain ⟨D, hD⟩ := pathNumber_hasPathBudget G
  exact ⟨D, le_antisymm hD (pathNumber_le_size D)⟩

/-- A budget suffices exactly when it is at least the minimum path number. -/
theorem hasPathBudget_iff_pathNumber_le [Fintype V] (k : ℕ) :
    HasPathBudget G k ↔ pathNumber G ≤ k := by
  constructor
  · rintro ⟨D, hD⟩
    exact (pathNumber_le_size D).trans hD
  · intro h
    obtain ⟨D, hD⟩ := pathNumber_hasPathBudget G
    exact ⟨D, hD.trans h⟩

/-- Edgeless finite graphs have path number zero, regardless of isolated vertices. -/
@[simp] theorem pathNumber_bot [Fintype V] : pathNumber (⊥ : SimpleGraph V) = 0 :=
  Nat.eq_zero_of_le_zero ((hasPathBudget_iff_pathNumber_le 0).mp empty_hasPathBudget)

/-- A graph with an edge has positive path number. -/
theorem pathNumber_pos_of_adj [Fintype V] {a b : V} (hab : G.Adj a b) :
    0 < pathNumber G := by
  obtain ⟨D, hD⟩ := exists_minimumDecomposition G
  obtain ⟨i, _, _⟩ := D.covers s(a, b) hab
  have hi := i.isLt
  omega

end Gallai
