/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.Inputs.OneExceptionCutOther
public import Gallai.Structure.OrientedCutPieces

@[expose] public section

/-! # Connectivity after deleting a non-designated even vertex

The strict induction premise is consumed on actual connected induced pieces.
The designated-separator case is deliberately not included in this result.
-/

namespace Gallai

universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

/-- The non-designated-vertex part of FHZ Claim 1, under its strict
minimum-counterexample induction hypothesis. -/
theorem one_exception_delete_other_connected (G : SimpleGraph V)
    [DecidableRel G.Adj] (x : V) (hconn : G.Connected)
    (hxpos : 0 < G.degree x) (hxEven : Even (G.degree x))
    (hcap : ∀ v, Even (G.degree v) → v ≠ x → eDegree G v ≤ 3)
    (hnot : ¬ ∃ D : Decomposition G,
      D.size ≤ (Fintype.card V + 1) / 2 ∧ 2 ≤ D.endpointCount x)
    (hmin : ∀ (W : Type u) [Fintype W] [DecidableEq W]
      (J : SimpleGraph W) [DecidableRel J.Adj],
      J.edgeFinset.card < G.edgeFinset.card → J.Connected →
      ∀ y : W, 0 < J.degree y → Even (J.degree y) →
        (∀ v, Even (J.degree v) → v ≠ y → eDegree J v ≤ 3) →
        ∃ D : Decomposition J, D.size ≤ (Fintype.card W + 1) / 2 ∧
          2 ≤ D.endpointCount y)
    (z : V) (hz : Even (G.degree z)) (hzx : z ≠ x) :
    (G.induce {v | v ≠ z}).Connected := by
  classical
  have : Nontrivial V := by
    obtain ⟨w, hw⟩ := (G.degree_pos_iff_exists_adj x).mp hxpos
    exact ⟨⟨x, w, hw.ne⟩⟩
  by_contra hn
  obtain ⟨S, T, hzS, hzT, hxS, hxT, hother, hcover, hinter, hg, _, _⟩ :=
    cut_vertex_pieces_away_from G hconn z x hzx.symm
      ((G.degree_pos_iff_exists_adj z).mp
        (hconn.preconnected.degree_pos_of_nontrivial z)) hn
  let A := (G.induce S).spanningCoe
  let B := (G.induce T).spanningCoe
  have hu : A ⊔ B = G := hg
  have hA : A.support ⊆ S := by
    rintro v ⟨w, hw⟩
    exact ((spanning_induce_adj_iff G S v w).mp hw).2.1
  have hB : B.support ⊆ T := by
    rintro v ⟨w, hw⟩
    exact ((spanning_induce_adj_iff G T v w).mp hw).2.1
  apply one_exception_cut_other_false A B S T z x hzS hzT hxT hxS hother
    hcover hinter hA hB
  · rwa [hu]
  · simpa only [SimpleGraph.degree, SimpleGraph.neighborFinset,
      ← Set.ncard_eq_toFinset_card', hu] using hxEven
  · simpa only [SimpleGraph.degree, SimpleGraph.neighborFinset,
      ← Set.ncard_eq_toFinset_card', hu] using hz
  · simpa only [SimpleGraph.degree, SimpleGraph.neighborFinset,
      ← Set.ncard_eq_toFinset_card', hu] using hcap
  · rwa [hu]
  · intro W _ _ J _ hlt hc y hy he hcappy
    apply hmin W J ?_ hc y hy he hcappy
    simpa only [SimpleGraph.edgeFinset, ← Set.ncard_eq_toFinset_card', hu] using hlt

end Gallai
