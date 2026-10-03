/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.ContactPunctureWitness

@[expose] public section

/-! # Component contacts for the two-edge E5 preparation -/
namespace Gallai.TwoException
open scoped Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Every component of E5's literal star/spoke/mate puncture meets its
deleted-edge support, even when the intermediate punctures disconnect. -/
theorem contact_E5_component_meets_boundary
    (hconn : G.Connected) (u x s p q : V) (B : Finset V)
    (C : (((starPuncture G u B).deleteEdges {s(x,s)}).deleteEdges
      {s(q,p)}).ConnectedComponent) :
    ∃ t ∈ C.supp, t ∈ insert u (insert x (insert s (insert q (insert p B)))) := by
  classical
  let A := insert u (insert x (insert s (insert q (insert p B))))
  change ∃ t ∈ C.supp, t ∈ A
  by_contra hnone
  have houtside : ∀ t ∈ C.supp, t ∉ A := by
    intro t ht ha
    exact hnone ⟨t, ht, ha⟩
  have hclosed : ∀ r t, r ∈ C.supp → G.Adj r t → t ∈ C.supp := by
    intro r t hr hrt
    have hru : r ≠ u := fun he => houtside r hr (by simp [A, he])
    have hstar : (starPuncture G u B).Adj r t := by
      refine ⟨hrt, ?_⟩
      intro ha
      have hrB := ((star_sup_adj_off_center u B r t hru).mp ha).1
      exact houtside r hr (by simp [A, hrB])
    have hspoke : ((starPuncture G u B).deleteEdges {s(x,s)}).Adj r t := by
      apply SimpleGraph.deleteEdges_adj.mpr
      refine ⟨hstar, ?_⟩
      intro ha
      have heq : s(r,t) = s(x,s) := by simpa using ha
      rcases Sym2.eq_iff.mp heq with he | he
      · exact houtside r hr (by simp [A, he.1])
      · exact houtside r hr (by simp [A, he.1])
    have hmate : (((starPuncture G u B).deleteEdges {s(x,s)}).deleteEdges
        {s(q,p)}).Adj r t := by
      apply SimpleGraph.deleteEdges_adj.mpr
      refine ⟨hspoke, ?_⟩
      intro ha
      have heq : s(r,t) = s(q,p) := by simpa using ha
      rcases Sym2.eq_iff.mp heq with he | he
      · exact houtside r hr (by simp [A, he.1])
      · exact houtside r hr (by simp [A, he.1])
    exact C.mem_supp_of_adj_mem_supp hr hmate
  obtain ⟨w, hw⟩ := C.nonempty_supp
  have hreach : G.Reachable w u := hconn w u
  rw [SimpleGraph.reachable_iff_reflTransGen] at hreach
  have hpreserve : ∀ {v : V}, Relation.ReflTransGen G.Adj w v →
      w ∈ C.supp → v ∈ C.supp := by
    intro v hv hw
    induction hv with
    | refl => exact hw
    | tail _ hab ih => exact hclosed _ _ ih hab
  exact houtside u (hpreserve hreach hw) (by simp [A])

end Gallai.TwoException
