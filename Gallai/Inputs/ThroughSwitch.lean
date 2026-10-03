/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.Inputs.CarrierSwitch

@[expose] public section

/-! # Switching both selected sides of one through carrier -/

namespace Gallai.Decomposition

open scoped Finset

universe u

variable {V : Type u} {G K : SimpleGraph V} [DecidableEq V]

/-- A through carrier remains one path, with both selected run contributions accounted for. -/
theorem exists_switch_through (D : Decomposition G) (a : V) (R : Finset (D.RunSlot a))
    (i : D.ThroughIndex a) (hsub : G ≤ K)
    (hnew : ∀ r ∈ R, K.Adj (D.runEndpoint a r) a) :
    ∃ Q : NonemptyPath K,
      (∀ e, Q.walk.edges.count e +
          D.selectedOwnerSum a R i.val (fun r => if s(a, D.runNeighbor a r) = e then 1 else 0) =
        (D.path i.val).walk.edges.count e +
          D.selectedOwnerSum a R i.val (fun r => if s(a, D.runEndpoint a r) = e then 1 else 0)) ∧
      ∀ w, ((if Q.start = w then 1 else 0) + (if Q.finish = w then 1 else 0)) +
          D.selectedOwnerSum a R i.val (fun r => if D.runEndpoint a r = w then 1 else 0) =
        ((if (D.path i.val).start = w then 1 else 0) +
          (if (D.path i.val).finish = w then 1 else 0)) +
          D.selectedOwnerSum a R i.val (fun r => if D.runNeighbor a r = w then 1 else 0) := by
  classical
  let l : D.RunSlot a := .inr (i, false)
  let t : D.RunSlot a := .inr (i, true)
  let L := D.runArm a l
  let T := D.runArm a t
  have hp := (Finset.mem_filter.mp i.property).2
  have hj : L.finish = T.finish := (D.runArm_finish a l).trans (D.runArm_finish a t).symm
  have hi : ∀ v, v ∈ L.walk.support → v ∈ T.walk.support → v = L.finish := by
    intro v hvL hvT
    change v ∈ ((D.path i.val).dropFrom a hp.1 hp.2.2.symm).walk.reverse.support at hvT
    rw [SimpleGraph.Walk.support_reverse, List.mem_reverse] at hvT
    exact ((D.path i.val).mem_prefix_support_and_suffix_support_iff a hp.1 hp.2.1
      hp.2.2.symm v).mp ⟨hvL, hvT⟩
  obtain ⟨Q, hQs, hQf, hQe⟩ := L.exists_switched_arm_pair T (decide (l ∈ R)) (decide (t ∈ R))
    hj hi
    (fun e he _ => SimpleGraph.edgeSet_mono hsub (L.walk.edges_subset_edgeSet he))
    (fun e he _ => SimpleGraph.edgeSet_mono hsub (T.walk.edges_subset_edgeSet he))
    (fun hm => by
      rw [D.runArm_start, D.runArm_finish]
      exact hnew l (of_decide_eq_true hm))
    (fun hm => by
      rw [D.runArm_start, D.runArm_finish]
      exact hnew t (of_decide_eq_true hm))
  have hparts (e : Sym2 V) : L.walk.edges.count e + T.walk.edges.count e =
      (D.path i.val).walk.edges.count e := by
    change ((D.path i.val).takeTo a hp.1 hp.2.1).walk.edges.count e +
      ((D.path i.val).dropFrom a hp.1 hp.2.2.symm).walk.reverse.edges.count e = _
    rw [SimpleGraph.Walk.edges_reverse, List.count_reverse, ← List.count_append,
      (D.path i.val).prefix_edges_append_suffix_edges a hp.1 hp.2.1 hp.2.2.symm]
  have hLn : L.walk.reverse.snd = D.runNeighbor a l := D.runArm_predecessor a l
  have hTn : T.walk.reverse.snd = D.runNeighbor a t := D.runArm_predecessor a t
  have hLs : L.start = D.runEndpoint a l := D.runArm_start a l
  have hTs : T.start = D.runEndpoint a t := D.runArm_start a t
  have hLf : L.finish = a := D.runArm_finish a l
  have hTf : T.finish = a := D.runArm_finish a t
  refine ⟨Q, ?_, ?_⟩
  · intro e
    have hh := hQe e
    have hswapL : s(D.runEndpoint a l, a) = s(a, D.runEndpoint a l) := Sym2.eq_swap
    have hswapT : s(D.runEndpoint a t, a) = s(a, D.runEndpoint a t) := Sym2.eq_swap
    rw [hLn, hTn, hparts, hLs, hTs, hLf, hTf, hswapL, hswapT] at hh
    have hne : (Sum.inr (i, false) : D.RunSlot a) ≠ Sum.inr (i, true) := by simp
    simpa only [selectedOwnerSum, D.ownerRuns_through, Finset.sum_pair hne,
      decide_eq_true_eq, l, t] using hh
  · intro w
    rw [hQs, hQf, hLn, hTn, hLs, hTs]
    simp only [selectedOwnerSum, D.ownerRuns_through]
    have hlt : l ≠ t := by simp [l, t]
    change ((if (if decide (l ∈ R) then D.runNeighbor a l else D.runEndpoint a l) = w
          then 1 else 0) +
        (if (if decide (t ∈ R) then D.runNeighbor a t else D.runEndpoint a t) = w
          then 1 else 0)) +
      (∑ r ∈ {l, t}, if r ∈ R then (if D.runEndpoint a r = w then 1 else 0) else 0) =
      ((if D.runEndpoint a l = w then 1 else 0) + (if D.runEndpoint a t = w then 1 else 0)) +
      (∑ r ∈ {l, t}, if r ∈ R then (if D.runNeighbor a r = w then 1 else 0) else 0)
    rw [Finset.sum_pair hlt, Finset.sum_pair hlt]
    by_cases hl : l ∈ R <;> by_cases ht : t ∈ R <;>
      simp only [hl, ht, decide_true, decide_false, Bool.false_eq_true, if_false, if_true] <;> omega

end Gallai.Decomposition
