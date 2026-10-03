/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Data.Finset.Lattice.Fold

@[expose] public section

/-! # Unions of deletion pieces meeting only at a hub

Each piece is supported on its own part and a shared hub. Disjoint parts
ensure that a non-hub vertex keeps exactly its local neighbourhood in the
union. These are graph facts, independent of a path decomposition.
-/

namespace Gallai

variable {V I : Type*}

/-- Away from the hub, an actual vertex in one part only sees that part's
deletion graph in the finite union. -/
theorem hub_piece_union_adj_iff (s : Finset I) (K : I → SimpleGraph V)
    (P : I → Set V) (u : V)
    (hd : (s : Set I).Pairwise fun i j => Disjoint (P i) (P j))
    (hs : ∀ i ∈ s, ∀ v w, (K i).Adj v w → v = u ∨ v ∈ P i)
    (i : I) (hi : i ∈ s) (v w : V) (hvu : v ≠ u) (hv : v ∈ P i) :
    (s.sup K).Adj v w ↔ (K i).Adj v w := by
  rw [Finset.sup_eq_iSup]
  simp only [SimpleGraph.iSup_adj]
  constructor
  · rintro ⟨j, hj, h⟩
    have hvj := (hs j hj v w h).resolve_left hvu
    have hji : j = i := by
      by_contra hn
      exact Set.disjoint_left.mp (hd hj hi hn) hvj hv
    subst j
    exact h
  · exact fun h => ⟨i, hi, h⟩

/-- A non-hub vertex outside every selected part is inactive in the union. -/
theorem hub_piece_union_not_adj (s : Finset I) (K : I → SimpleGraph V)
    (P : I → Set V) (u : V)
    (hs : ∀ i ∈ s, ∀ v w, (K i).Adj v w → v = u ∨ v ∈ P i)
    (v w : V) (hvu : v ≠ u) (hv : ∀ i ∈ s, v ∉ P i) :
    ¬ (s.sup K).Adj v w := by
  rw [Finset.sup_eq_iSup]
  simp only [SimpleGraph.iSup_adj]
  rintro ⟨i, hi, h⟩
  exact hv i hi ((hs i hi v w h).resolve_left hvu)

variable [Fintype V]

/-- Adjacency decision for the finite union. -/
noncomputable local instance hubUnionAdj (s : Finset I) (K : I → SimpleGraph V) :
    DecidableRel (s.sup K).Adj := fun _ _ => Classical.propDecidable _

/-- Exact degree transfer from the unique local deletion piece. -/
theorem hub_piece_union_degree (s : Finset I) (K : I → SimpleGraph V)
    [∀ i, DecidableRel (K i).Adj] (P : I → Set V) (u : V)
    (hd : (s : Set I).Pairwise fun i j => Disjoint (P i) (P j))
    (hs : ∀ i ∈ s, ∀ v w, (K i).Adj v w → v = u ∨ v ∈ P i)
    (i : I) (hi : i ∈ s) (v : V) (hvu : v ≠ u) (hv : v ∈ P i) :
    (s.sup K).degree v = (K i).degree v := by
  classical
  have hn : (s.sup K).neighborFinset v = (K i).neighborFinset v := by
    ext w
    simp only [SimpleGraph.mem_neighborFinset]
    exact hub_piece_union_adj_iff s K P u hd hs i hi v w hvu hv
  simpa only [SimpleGraph.card_neighborFinset_eq_degree] using congrArg Finset.card hn

/-- If every local piece has degree at most one off the hub, so does the
whole union. Vertices in no selected part are included, with degree zero. -/
theorem hub_piece_union_degree_le_one (s : Finset I) (K : I → SimpleGraph V)
    [∀ i, DecidableRel (K i).Adj] (P : I → Set V) (u : V)
    (hd : (s : Set I).Pairwise fun i j => Disjoint (P i) (P j))
    (hs : ∀ i ∈ s, ∀ v w, (K i).Adj v w → v = u ∨ v ∈ P i)
    (hlocal : ∀ i ∈ s, ∀ v, v ≠ u → (K i).degree v ≤ 1)
    (v : V) (hvu : v ≠ u) : (s.sup K).degree v ≤ 1 := by
  classical
  by_cases hm : ∃ i ∈ s, v ∈ P i
  · obtain ⟨i, hi, hv⟩ := hm
    rw [hub_piece_union_degree s K P u hd hs i hi v hvu hv]
    exact hlocal i hi v hvu
  · have hz : (s.sup K).degree v = 0 := by
      apply Nat.eq_zero_of_not_pos
      intro hp
      obtain ⟨w, hw⟩ := ((s.sup K).degree_pos_iff_exists_adj v).mp hp
      exact hub_piece_union_not_adj s K P u hs v w hvu
        (fun i hi hv => hm ⟨i, hi, hv⟩) hw
    omega

end Gallai
