/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.Structure.LeafTransfer
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

@[expose] public section

/-! # A decreasing measure for the direct Lovasz induction -/

namespace Gallai

open scoped BigOperators

universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Degree excess above one, with isolated vertices contributing zero. -/
def degreeExcess : ℕ := ∑ v, (G.degree v - 1)

omit [DecidableEq V] in
/-- The zero-measure graphs are precisely matchings together with isolates. -/
theorem degreeExcess_eq_zero_iff : degreeExcess G = 0 ↔ ∀ v, G.degree v ≤ 1 := by
  simp [degreeExcess, Finset.sum_eq_zero_iff, Nat.sub_eq_zero_iff_le]

/-- Edge deletion at a vertex of degree at least two strictly decreases excess. -/
theorem degreeExcess_delete_lt (x y : V) (hxy : G.Adj x y) (hx : 2 ≤ G.degree x) :
    degreeExcess (G.deleteEdges {s(x, y)}) < degreeExcess G := by
  apply Finset.sum_lt_sum
  · intro v _
    have hd := SimpleGraph.degree_le_of_le (v := v)
      (show G.deleteEdges {s(x, y)} ≤ G from fun _ _ h => h.1)
    omega
  · refine ⟨x, Finset.mem_univ x, ?_⟩
    have hd := degree_delete_edge_add_one G x y hxy
    omega

/-- Local adjacency decision, preserving the standard neighbour Fintype. -/
noncomputable local instance (x y : V) : DecidableRel (leafTransfer G x y).Adj :=
  fun _ _ => Classical.propDecidable _

/-- Replacing an edge by a new leaf edge strictly decreases the same measure. -/
theorem degreeExcess_leafTransfer_lt (x y : V) (hxy : G.Adj x y)
    (hx : 2 ≤ G.degree x) : degreeExcess (leafTransfer G x y) < degreeExcess G := by
  unfold degreeExcess
  rw [Fintype.sum_sum_type]
  simp only [Fintype.sum_unique]
  change (∑ v, ((leafTransfer G x y).degree (.inl v) - 1)) +
    ((leafTransfer G x y).degree (.inr ()) - 1) < ∑ v, (G.degree v - 1)
  rw [leafTransfer_degree_new, Nat.sub_self, Nat.add_zero]
  apply Finset.sum_lt_sum
  · intro v _
    by_cases hv : v = x
    · subst v
      have hd := leafTransfer_degree_donor G x y hxy
      omega
    · rw [leafTransfer_degree_other G x y v hxy hv]
  · refine ⟨x, Finset.mem_univ x, ?_⟩
    have hd := leafTransfer_degree_donor G x y hxy
    omega

end Gallai
