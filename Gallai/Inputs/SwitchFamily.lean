/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.Inputs.ThroughSwitch
public import Gallai.Operations.AddEdge

@[expose] public section

/-! # Simultaneous switched family, including the final avoiding carrier -/

namespace Gallai

open scoped Finset

universe u

variable {V : Type u} {G K : SimpleGraph V} [DecidableEq V]

/-- Extend either endpoint of an avoiding carrier in a specified larger ambient graph. -/
theorem NonemptyPath.exists_extend_in (P : NonemptyPath G) (a v : V)
    (hv : P.start = v ∨ P.finish = v) (ha : a ∉ P.walk.support)
    (hsub : G ≤ K) (hnew : K.Adj a v) :
    ∃ Q : NonemptyPath K,
      (∀ e, Q.walk.edges.count e = P.walk.edges.count e + if s(a, v) = e then 1 else 0) ∧
      ∀ w, ((if Q.start = w then 1 else 0) + (if Q.finish = w then 1 else 0)) +
          (if v = w then 1 else 0) =
        ((if P.start = w then 1 else 0) + (if P.finish = w then 1 else 0)) +
          if a = w then 1 else 0 := by
  classical
  let T := (P.toward v).reverse
  have hTs : T.start = v := P.toward_finish v hv
  have hTa : a ∉ T.walk.support := by
    simpa only [T, NonemptyPath.reverse, SimpleGraph.Walk.support_reverse, List.mem_reverse,
      P.mem_toward_support] using ha
  have hle : G ⊔ SimpleGraph.edge a T.start ≤ K := by
    apply sup_le hsub
    rw [hTs]
    exact (SimpleGraph.edge_le_iff K).mpr (Or.inr hnew)
  let U := T.prependFresh a hTa
  let Q := U.transfer K (fun e he => SimpleGraph.edgeSet_mono hle (U.walk.edges_subset_edgeSet he))
  have hTe (e : Sym2 V) : T.walk.edges.count e = P.walk.edges.count e := by
    simp only [T, NonemptyPath.reverse_edges, List.count_reverse]
    by_cases hs : P.start = v
    · rw [P.toward_of_start_eq v hs, NonemptyPath.reverse_edges, List.count_reverse]
    · rw [P.toward_of_start_ne v hs]
  refine ⟨Q, ?_, ?_⟩
  · intro e
    simp only [Q, NonemptyPath.transfer_edges, U, NonemptyPath.prependFresh_edges,
      List.count_cons, beq_iff_eq, hTs, hTe]
  · intro w
    have ht := P.toward_endpoint_contribution v w
    change ((if T.finish = w then 1 else 0) + (if T.start = w then 1 else 0)) = _ at ht
    rw [hTs] at ht
    change ((if a = w then 1 else 0) + (if T.finish = w then 1 else 0)) + _ = _
    omega

namespace Decomposition

/-- Switch all selected runs owned by one carrier, or transfer an avoiding carrier unchanged. -/
theorem exists_switch_owner (D : Decomposition G) (a : V) (R : Finset (D.RunSlot a))
    (i : Fin D.size) (hsub : G ≤ K) (hnew : ∀ r ∈ R, K.Adj (D.runEndpoint a r) a) :
    ∃ Q : NonemptyPath K,
      (∀ e, Q.walk.edges.count e +
          D.selectedOwnerSum a R i (fun r => if s(a, D.runNeighbor a r) = e then 1 else 0) =
        (D.path i).walk.edges.count e +
          D.selectedOwnerSum a R i (fun r => if s(a, D.runEndpoint a r) = e then 1 else 0)) ∧
      ∀ w, ((if Q.start = w then 1 else 0) + (if Q.finish = w then 1 else 0)) +
          D.selectedOwnerSum a R i (fun r => if D.runEndpoint a r = w then 1 else 0) =
        ((if (D.path i).start = w then 1 else 0) + (if (D.path i).finish = w then 1 else 0)) +
          D.selectedOwnerSum a R i (fun r => if D.runNeighbor a r = w then 1 else 0) := by
  classical
  by_cases ha : a ∈ (D.path i).walk.support
  · rcases (D.mem_support_iff_terminal_or_through a i).mp ha with ht | hp
    · exact D.exists_switch_terminal a R ⟨i, ht⟩ hsub hnew
    · exact D.exists_switch_through a R ⟨i, hp⟩ hsub hnew
  · refine ⟨(D.path i).transfer K (fun e he =>
      SimpleGraph.edgeSet_mono hsub ((D.path i).walk.edges_subset_edgeSet he)), ?_, ?_⟩
    · intro e
      simp only [NonemptyPath.transfer_edges, selectedOwnerSum, D.ownerRuns_avoiding a i ha,
        Finset.sum_empty, Nat.add_zero]
    · intro w
      simp only [selectedOwnerSum, D.ownerRuns_avoiding a i ha, Finset.sum_empty, Nat.add_zero]
      rfl

/-- All local switches and the avoiding extension fit on exactly the old carrier index set. -/
theorem exists_switch_family (D : Decomposition G) (a v : V) (R : Finset (D.RunSlot a))
    (k : Fin D.size) (hv : (D.path k).start = v ∨ (D.path k).finish = v)
    (ha : a ∉ (D.path k).walk.support) (hsub : G ≤ K)
    (hnew : ∀ r ∈ R, K.Adj (D.runEndpoint a r) a) (hav : K.Adj a v) :
    ∃ paths : Fin D.size → NonemptyPath K,
      (∀ i e, (paths i).walk.edges.count e +
          D.selectedOwnerSum a R i (fun r => if s(a, D.runNeighbor a r) = e then 1 else 0) =
        (D.path i).walk.edges.count e +
          D.selectedOwnerSum a R i (fun r => if s(a, D.runEndpoint a r) = e then 1 else 0) +
          if i = k then (if s(a, v) = e then 1 else 0) else 0) ∧
      ∀ i w, ((if (paths i).start = w then 1 else 0) + (if (paths i).finish = w then 1 else 0)) +
          D.selectedOwnerSum a R i (fun r => if D.runEndpoint a r = w then 1 else 0) +
          (if i = k then (if v = w then 1 else 0) else 0) =
        ((if (D.path i).start = w then 1 else 0) + (if (D.path i).finish = w then 1 else 0)) +
          D.selectedOwnerSum a R i (fun r => if D.runNeighbor a r = w then 1 else 0) +
          if i = k then (if a = w then 1 else 0) else 0 := by
  classical
  have hex (i : Fin D.size) : ∃ Q : NonemptyPath K,
      (∀ e, Q.walk.edges.count e +
          D.selectedOwnerSum a R i (fun r => if s(a, D.runNeighbor a r) = e then 1 else 0) =
        (D.path i).walk.edges.count e +
          D.selectedOwnerSum a R i (fun r => if s(a, D.runEndpoint a r) = e then 1 else 0) +
          if i = k then (if s(a, v) = e then 1 else 0) else 0) ∧
      ∀ w, ((if Q.start = w then 1 else 0) + (if Q.finish = w then 1 else 0)) +
          D.selectedOwnerSum a R i (fun r => if D.runEndpoint a r = w then 1 else 0) +
          (if i = k then (if v = w then 1 else 0) else 0) =
        ((if (D.path i).start = w then 1 else 0) + (if (D.path i).finish = w then 1 else 0)) +
          D.selectedOwnerSum a R i (fun r => if D.runNeighbor a r = w then 1 else 0) +
          if i = k then (if a = w then 1 else 0) else 0 := by
    by_cases hik : i = k
    · subst i
      obtain ⟨Q, he, hw⟩ := (D.path k).exists_extend_in a v hv ha hsub hav
      refine ⟨Q, ?_, ?_⟩
      · simpa only [selectedOwnerSum, D.ownerRuns_avoiding a k ha,
          Finset.sum_empty, Nat.add_zero, if_true] using he
      · simpa only [selectedOwnerSum, D.ownerRuns_avoiding a k ha,
          Finset.sum_empty, Nat.add_zero, if_true] using hw
    · obtain ⟨Q, he, hw⟩ := D.exists_switch_owner a R i hsub hnew
      exact ⟨Q, by simpa only [hik, if_false, Nat.add_zero] using he,
        by simpa only [hik, if_false, Nat.add_zero] using hw⟩
  choose paths he hw using hex
  exact ⟨paths, he, hw⟩

end Decomposition

end Gallai
