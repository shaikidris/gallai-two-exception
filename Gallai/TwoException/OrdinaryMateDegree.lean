/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.OrdinaryMatePuncture

@[expose] public section

/-! # Exact endpoint degrees after disjoint ordinary mate deletions -/
namespace Gallai.TwoException
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
noncomputable local instance mateDegreeAdj (G : SimpleGraph V) (M : List (V × V)) :
    DecidableRel (ordinaryMatePuncture G M).Adj := fun _ _ => Classical.propDecidable _

/-- Every mate endpoint loses exactly one edge, independently of how many
other components were prepared. -/
theorem ordinaryMatePuncture_endpoint_degree
    (M : List (V × V))
    (hdis : M.Pairwise (fun e f =>
      e.1 ≠ f.1 ∧ e.1 ≠ f.2 ∧ e.2 ≠ f.1 ∧ e.2 ≠ f.2))
    (hedges : ∀ e ∈ M, G.Adj e.1 e.2) :
    ∀ e ∈ M,
      (ordinaryMatePuncture G M).degree e.1 + 1 = G.degree e.1 ∧
      (ordinaryMatePuncture G M).degree e.2 + 1 = G.degree e.2 := by
  induction M with
  | nil => simp
  | cons e M ih =>
    rcases List.pairwise_cons.mp hdis with ⟨hhead, htail⟩
    have hpAvoid : ∀ f ∈ M, e.1 ≠ f.1 ∧ e.1 ≠ f.2 :=
      fun f hf => ⟨(hhead f hf).1, (hhead f hf).2.1⟩
    have hqAvoid : ∀ f ∈ M, e.2 ≠ f.1 ∧ e.2 ≠ f.2 :=
      fun f hf => (hhead f hf).2.2
    have hp := ordinaryMatePuncture_degree_of_avoids (G := G) M e.1 hpAvoid
    have hq := ordinaryMatePuncture_degree_of_avoids (G := G) M e.2 hqAvoid
    have heCurrent := (ordinaryMatePuncture_adj_of_avoids (G := G) M e.1 e.2 hpAvoid).mpr
      (hedges e (List.mem_cons_self ..))
    intro f hf
    rcases List.mem_cons.mp hf with hfhead | hf
    · subst f
      constructor
      · have hd := degree_delete_edge_add_one (ordinaryMatePuncture G M) e.1 e.2 heCurrent
        simp only [← SimpleGraph.ncard_neighborSet] at hd hp ⊢
        change (((ordinaryMatePuncture G M).deleteEdges {s(e.1,e.2)}).neighborSet e.1).ncard + 1 =
          (G.neighborSet e.1).ncard
        exact hd.trans hp
      · have hd := degree_delete_edge_add_one_other (ordinaryMatePuncture G M) e.1 e.2 heCurrent
        simp only [← SimpleGraph.ncard_neighborSet] at hd hq ⊢
        change (((ordinaryMatePuncture G M).deleteEdges {s(e.1,e.2)}).neighborSet e.2).ncard + 1 =
          (G.neighborSet e.2).ncard
        exact hd.trans hq
    · obtain ⟨hfp, hfq⟩ := ih htail (fun f hf => hedges f (List.mem_cons_of_mem e hf)) f hf
      have hc := hhead f hf
      constructor
      · have hd := degree_delete_edge_of_ne (ordinaryMatePuncture G M) e.1 e.2 f.1
          hc.1.symm hc.2.2.1.symm
        simp only [← SimpleGraph.ncard_neighborSet] at hd hfp ⊢
        change (((ordinaryMatePuncture G M).deleteEdges {s(e.1,e.2)}).neighborSet f.1).ncard + 1 =
          (G.neighborSet f.1).ncard
        rwa [hd]
      · have hd := degree_delete_edge_of_ne (ordinaryMatePuncture G M) e.1 e.2 f.2
          hc.2.1.symm hc.2.2.2.symm
        simp only [← SimpleGraph.ncard_neighborSet] at hd hfq ⊢
        change (((ordinaryMatePuncture G M).deleteEdges {s(e.1,e.2)}).neighborSet f.2).ncard + 1 =
          (G.neighborSet f.2).ncard
        rwa [hd]

end Gallai.TwoException
