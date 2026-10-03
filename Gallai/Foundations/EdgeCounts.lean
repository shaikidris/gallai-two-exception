/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.Foundations.Endpoints
public import Mathlib.Data.List.Nodup
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

@[expose] public section

/-! # Exact edge multiplicities and unique carrier coverage -/

namespace Gallai.Decomposition

open scoped Finset

universe u

variable {V : Type u} {G : SimpleGraph V} [DecidableEq V]

/-- The total multiplicity of any edge in a decomposition is its graph membership indicator. -/
theorem sum_edge_count [DecidableRel G.Adj] (D : Decomposition G) (e : Sym2 V) :
    (∑ i : Fin D.size, (D.path i).walk.edges.count e) = if e ∈ G.edgeSet then 1 else 0 := by
  classical
  by_cases he : e ∈ G.edgeSet
  · obtain ⟨i, hi, hu⟩ := D.covers e he
    rw [if_pos he, Finset.sum_eq_single i]
    · exact List.count_eq_one_of_mem (D.path i).isPath.isTrail.edges_nodup hi
    · intro j _ hji
      exact List.count_eq_zero.mpr (fun hj => hji (hu j hj))
    · simp
  · rw [if_neg he]
    apply Finset.sum_eq_zero
    intro i _
    exact List.count_eq_zero.mpr (fun hi => he ((D.path i).walk.edges_subset_edgeSet hi))

/-- A finite family with total multiplicity one on each graph edge has unique carrier coverage. -/
theorem unique_cover_of_edge_count {n : ℕ} (paths : Fin n → NonemptyPath G)
    (hcount : ∀ e ∈ G.edgeSet, (∑ i, (paths i).walk.edges.count e) = 1) :
    ∀ e ∈ G.edgeSet, ∃! i, e ∈ (paths i).walk.edges := by
  classical
  intro e he
  have ht := hcount e he
  have hex : ∃ i, e ∈ (paths i).walk.edges := by
    by_contra hn
    have hz : (∑ i, (paths i).walk.edges.count e) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      exact List.count_eq_zero.mpr (fun hi => hn ⟨i, hi⟩)
    omega
  obtain ⟨i, hi⟩ := hex
  refine ⟨i, hi, ?_⟩
  intro j hj
  by_contra hji
  have hle : (paths j).walk.edges.count e + (paths i).walk.edges.count e ≤
      ∑ k, (paths k).walk.edges.count e := by
    simpa only [Finset.sum_pair hji] using
      (Finset.sum_le_sum_of_subset (f := fun k => (paths k).walk.edges.count e)
        (Finset.subset_univ ({j, i} : Finset (Fin n))))
  have hci := List.count_pos_iff.mpr hi
  have hcj := List.count_pos_iff.mpr hj
  omega

/-- Construct a decomposition on the original index type from literal edge-count identities. -/
def ofEdgeCounts {n : ℕ} (paths : Fin n → NonemptyPath G)
    (hcount : ∀ e ∈ G.edgeSet, (∑ i, (paths i).walk.edges.count e) = 1) : Decomposition G where
  size := n
  path := paths
  covers := unique_cover_of_edge_count paths hcount

end Gallai.Decomposition
