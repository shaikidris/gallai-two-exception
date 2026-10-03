/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
public import Mathlib.Combinatorics.SimpleGraph.Operations
public import Mathlib.Algebra.Ring.Parity

@[expose] public section

/-! # Exact degree changes under deletion of one edge -/

namespace Gallai

open scoped Finset

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- At the first endpoint, deleting an edge erases exactly its other endpoint. -/
theorem neighborFinset_delete_edge (x y : V) :
    (G.deleteEdges {s(x, y)}).neighborFinset x = (G.neighborFinset x).erase y := by
  ext v
  simp only [SimpleGraph.mem_neighborFinset, Finset.mem_erase,
    SimpleGraph.deleteEdges_adj, Set.mem_singleton_iff, Sym2.eq_iff]
  constructor
  · rintro ⟨h, hn⟩
    exact ⟨fun hv => hn (Or.inl ⟨True.intro, hv⟩), h⟩
  · rintro ⟨hn, h⟩
    refine ⟨h, ?_⟩
    rintro (⟨_, hv⟩ | ⟨hx, hv⟩)
    · exact hn hv
    · exact h.ne hv.symm

/-- Deleting an existing edge decreases either incident degree by exactly one. -/
theorem degree_delete_edge_add_one (x y : V) (hxy : G.Adj x y) :
    (G.deleteEdges {s(x, y)}).degree x + 1 = G.degree x := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree,
    neighborFinset_delete_edge G, ← G.card_neighborFinset_eq_degree x]
  exact Finset.card_erase_add_one ((G.mem_neighborFinset x y).mpr hxy)

/-- At the other named endpoint, deleting an existing edge also decreases the
degree by exactly one.  This avoids rewriting dependent degree expressions by
the symmetry of an unordered edge. -/
theorem neighborFinset_delete_edge_other (x y : V) :
    (G.deleteEdges {s(x, y)}).neighborFinset y = (G.neighborFinset y).erase x := by
  ext v
  simp only [SimpleGraph.mem_neighborFinset, Finset.mem_erase,
    SimpleGraph.deleteEdges_adj, Set.mem_singleton_iff, Sym2.eq_iff]
  constructor
  · rintro ⟨h, hn⟩
    refine ⟨?_, h⟩
    intro hv
    exact hn (Or.inr ⟨True.intro, hv⟩)
  · rintro ⟨hv, h⟩
    refine ⟨h, ?_⟩
    rintro (⟨_, hvy⟩ | ⟨_, hvx⟩)
    · exact h.ne hvy.symm
    · exact hv hvx

/-- The degree formula at the second named endpoint of a deleted edge. -/
theorem degree_delete_edge_add_one_other (x y : V) (hxy : G.Adj x y) :
    (G.deleteEdges {s(x, y)}).degree y + 1 = G.degree y := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree,
    neighborFinset_delete_edge_other G, ← G.card_neighborFinset_eq_degree y]
  exact Finset.card_erase_add_one ((G.mem_neighborFinset y x).mpr hxy.symm)

/-- Off the two ends, deletion preserves degree. -/
theorem degree_delete_edge_of_ne (x y v : V) (hx : v ≠ x) (hy : v ≠ y) :
    (G.deleteEdges {s(x, y)}).degree v = G.degree v := by
  have hn : (G.deleteEdges {s(x, y)}).neighborFinset v = G.neighborFinset v := by
    ext w
    simp [SimpleGraph.deleteEdges_adj, hx, hy]
  simpa only [SimpleGraph.card_neighborFinset_eq_degree] using congrArg Finset.card hn

omit [Fintype V] [DecidableRel G.Adj] in
/-- Deleting and restoring an existing edge gives the original graph. -/
theorem delete_edge_sup_edge (x y : V) (hxy : G.Adj x y) :
    G.deleteEdges {s(x, y)} ⊔ SimpleGraph.edge x y = G := by
  ext u v
  simp only [SimpleGraph.sup_adj, SimpleGraph.deleteEdges_adj, Set.mem_singleton_iff,
    Sym2.eq_iff, SimpleGraph.edge_adj]
  constructor
  · rintro (⟨h, _⟩ | ⟨h, _⟩)
    · exact h
    · rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hxy
      · exact hxy.symm
  · intro h
    by_cases he : (u = x ∧ v = y) ∨ (u = y ∧ v = x)
    · exact Or.inr ⟨he, h.ne⟩
    · exact Or.inl ⟨h, he⟩

end Gallai
