/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.Structure.LeafTransferReturn
public import Gallai.Inputs.SingleEdge
public import Gallai.Foundations.EndpointBounds
public import Gallai.Operations.RemoveNewVertex

@[expose] public section

/-! # Normalized all-odd return through leaf closure and suppression -/

namespace Gallai

open scoped Finset

universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Local adjacency decision for the finite auxiliary degrees. -/
noncomputable local instance allOddReturnDecidableAdj (x y : V) :
    DecidableRel (leafTransfer G x y).Adj :=
  fun _ _ => Classical.propDecidable _

/-- The normalized auxiliary returns to the original graph image with no
surplus endpoints and no path-count loss. -/
theorem Decomposition.restore_all_odd_image (x y : V) (hxy : G.Adj x y)
    (hx : 3 ≤ G.degree x) (hodd : ∀ v, 0 < G.degree v → Odd (G.degree v))
    (D : Decomposition (leafTransfer G x y))
    (hn : ∀ v, D.endpointCount v = (leafTransfer G x y).degree v % 2) :
    ∃ E : Decomposition (G.map (Function.Embedding.inl : V ↪ V ⊕ Unit)),
      E.size = D.size ∧ ∀ v, E.endpointCount (.inl v) = G.degree v % 2 := by
  obtain ⟨_, heven, huniq⟩ := leafTransfer_unique_positive_even G x y hxy hx hodd
  have hz : D.endpointCount (.inr ()) = 1 := by
    rw [hn, leafTransfer_degree_new]
  have hxzero : D.endpointCount (.inl x) = 0 := by
    rw [hn]
    exact Nat.even_iff.mp heven
  have hp : #{v ∈ (leafTransfer G x y).neighborFinset (.inl x) |
      D.endpointCount v = 0} = 0 := by
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro v hv
    obtain ⟨ha, hzero⟩ := Finset.mem_filter.mp hv
    have ha := ((leafTransfer G x y).mem_neighborFinset _ _).mp ha
    have hpos := ((leafTransfer G x y).degree_pos_iff_exists_adj v).mpr
      ⟨.inl x, ha.symm⟩
    have hvEven : Even ((leafTransfer G x y).degree v) := by
      apply Nat.even_iff.mpr
      rw [← hn v, hzero]
    exact ha.ne (huniq v hpos hvEven).symm
  have hm : ¬ (leafTransfer G x y).Adj (.inl x) (.inr ()) := by
    rw [SimpleGraph.adj_comm, leafTransfer_adj_new]
    simpa using hxy.ne
  obtain ⟨C, hs, hb⟩ := D.single_edge_addibility (.inl x) (.inr ())
    (by simp) hm (by rw [hp, hz]; omega)
  have hcz : C.endpointCount (.inr ()) = 0 := by
    have h := hb (.inr ())
    simp [hz] at h
    omega
  obtain ⟨E, hsize, hend⟩ := C.suppress_closedLeafTransfer G x y hxy hcz
  refine ⟨E, hsize.trans hs, ?_⟩
  intro v
  rw [hend]
  have h := hb (.inl v)
  by_cases hv : v = x
  · subst v
    have ho := hodd x (by omega)
    rw [Nat.odd_iff] at ho
    simp [hxzero] at h
    omega
  · have hd := hn (.inl v)
    rw [leafTransfer_degree_other G x y v hxy hv] at hd
    simpa [Ne.symm hv, hd] using h

/-- The complete all-odd return on the original vertex type. -/
theorem Decomposition.restore_all_odd_normalized (x y : V) (hxy : G.Adj x y)
    (hx : 3 ≤ G.degree x) (hodd : ∀ v, 0 < G.degree v → Odd (G.degree v))
    (D : Decomposition (leafTransfer G x y))
    (hn : ∀ v, D.endpointCount v = (leafTransfer G x y).degree v % 2) :
    ∃ E : Decomposition G, E.size = D.size ∧
      ∀ v, E.endpointCount v = G.degree v % 2 := by
  obtain ⟨R, hs, hv⟩ := D.restore_all_odd_image G x y hxy hx hodd hn
  obtain ⟨E, he, hend⟩ := R.remove_new_vertex G
  exact ⟨E, he.trans hs, fun v => (hend v).trans (hv v)⟩

end Gallai
