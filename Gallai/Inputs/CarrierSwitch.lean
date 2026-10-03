/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.Inputs.RunArms
public import Gallai.Operations.ArmSwitch

@[expose] public section

/-! # A simultaneous selected-run switch on each original carrier -/

namespace Gallai.Decomposition

open scoped Finset

universe u

variable {V : Type u} {G K : SimpleGraph V} [DecidableEq V]

/-- Selected contributions belonging to one old carrier. -/
def selectedOwnerSum (D : Decomposition G) (a : V) (R : Finset (D.RunSlot a))
    (i : Fin D.size) (f : D.RunSlot a → ℕ) : ℕ :=
  ∑ r ∈ D.ownerRuns a i, if r ∈ R then f r else 0

/-- Summing carrier contributions counts each selected run exactly once. -/
theorem sum_selectedOwnerSum (D : Decomposition G) (a : V) (R : Finset (D.RunSlot a))
    (f : D.RunSlot a → ℕ) :
    (∑ i : Fin D.size, D.selectedOwnerSum a R i f) = ∑ r ∈ R, f r := by
  simp only [selectedOwnerSum]
  rw [D.sum_ownerRuns]
  simp

/-- Simultaneously switch the selected sides of a terminal carrier, preserving one path. -/
theorem exists_switch_terminal (D : Decomposition G) (a : V) (R : Finset (D.RunSlot a))
    (i : D.TerminalIndex a) (hsub : G ≤ K)
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
  let r : D.RunSlot a := .inl i
  let P := D.runArm a r
  obtain ⟨Q, hQs, hQf, _, hQe⟩ := P.exists_switched_arm (decide (r ∈ R))
    (fun e he _ => SimpleGraph.edgeSet_mono hsub (P.walk.edges_subset_edgeSet he))
    (fun hm => by
      rw [D.runArm_start, D.runArm_finish]
      exact hnew r (of_decide_eq_true hm))
  have hPs : P.start = D.runEndpoint a r := D.runArm_start a r
  have hPf : P.finish = a := D.runArm_finish a r
  have hPn : P.walk.reverse.snd = D.runNeighbor a r := D.runArm_predecessor a r
  have hPe (e : Sym2 V) : P.walk.edges.count e = (D.path i.val).walk.edges.count e := by
    change ((D.path i.val).toward a).walk.edges.count e = _
    by_cases hs : (D.path i.val).start = a
    · rw [(D.path i.val).toward_of_start_eq a hs, NonemptyPath.reverse_edges, List.count_reverse]
    · rw [(D.path i.val).toward_of_start_ne a hs]
  have hPend := (D.path i.val).toward_endpoint_contribution a
  refine ⟨Q, ?_, ?_⟩
  · intro e
    have hh := hQe e
    have hswap : s(D.runEndpoint a r, a) = s(a, D.runEndpoint a r) := Sym2.eq_swap
    rw [hPn, hPe, hPf, hPs, hswap] at hh
    simpa only [selectedOwnerSum, D.ownerRuns_terminal, Finset.sum_singleton,
      decide_eq_true_eq, r] using hh
  · intro w
    have hh := hPend w
    change ((if P.start = w then 1 else 0) + (if P.finish = w then 1 else 0)) = _ at hh
    rw [hPs, hPf] at hh
    rw [hQs, hQf, hPn, hPs, hPf]
    simp only [selectedOwnerSum, D.ownerRuns_terminal, Finset.sum_singleton]
    simp only [r] at hh ⊢
    by_cases hm : r ∈ R
    · simp only [r] at hm
      simp only [hm, decide_true, if_true]
      omega
    · simp only [r] at hm
      simp only [hm, decide_false, Bool.false_eq_true, if_false, Nat.add_zero]
      exact hh

end Gallai.Decomposition
