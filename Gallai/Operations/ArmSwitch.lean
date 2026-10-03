/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.Operations.Rotate

@[expose] public section

/-!
# Independent switching of terminal arms

An arm is oriented toward its hub. Switching it changes its initial endpoint
to the old predecessor of the hub and preserves its support. Two arms of one
carrier may therefore both be switched without being mistaken for two paths.
-/

namespace Gallai.NonemptyPath

universe u

variable {V : Type u} {G K : SimpleGraph V} [DecidableEq V]

/-- A simple path's first arrival at its final endpoint is its whole walk. -/
theorem takeTo_finish_walk (P : NonemptyPath G) :
    (P.takeTo P.finish P.walk.end_mem_support (P.start_ne_finish G)).walk = P.walk := by
  have hn : (P.walk.dropUntil P.finish P.walk.end_mem_support).Nil :=
    (P.isPath.dropUntil P.walk.end_mem_support).nil_iff_eq.mpr rfl
  have h := P.walk.take_spec P.walk.end_mem_support
  rw [hn.eq_nil, SimpleGraph.Walk.append_nil] at h
  exact h

/-- Choose whether to rotate an arm, retaining all support and exact edge multiplicities. -/
theorem exists_switched_arm (P : NonemptyPath G) (flag : Bool)
    (hkeep : ∀ e ∈ P.walk.edges,
      (flag = false ∨ e ≠ s(P.finish, P.walk.reverse.snd)) → e ∈ K.edgeSet)
    (hnew : flag = true → K.Adj P.start P.finish) :
    ∃ Q : NonemptyPath K,
      Q.start = (if flag then P.walk.reverse.snd else P.start) ∧ Q.finish = P.finish ∧
      (∀ v, v ∈ Q.walk.support ↔ v ∈ P.walk.support) ∧
      ∀ e, Q.walk.edges.count e +
          (if flag then (if s(P.finish, P.walk.reverse.snd) = e then 1 else 0) else 0) =
        P.walk.edges.count e +
          (if flag then (if s(P.start, P.finish) = e then 1 else 0) else 0) := by
  cases flag
  · let Q := P.transfer K (fun e he => hkeep e he (Or.inl rfl))
    refine ⟨Q, rfl, rfl, ?_, ?_⟩
    · intro v
      simp only [Q, transfer_support]
    · intro e
      simp only [Bool.false_eq_true, if_false, Nat.add_zero, Q, transfer_edges]
  · have hp : (P.takeTo P.finish P.walk.end_mem_support (P.start_ne_finish G)).walk.reverse.snd =
        P.walk.reverse.snd := congrArg (fun w => w.reverse.snd) P.takeTo_finish_walk
    have hk : ∀ e ∈ P.walk.edges,
        e ≠ s(P.finish,
          (P.takeTo P.finish P.walk.end_mem_support (P.start_ne_finish G)).walk.reverse.snd) →
            e ∈ K.edgeSet := by
      intro e he hne
      apply hkeep e he (Or.inr ?_)
      simpa only [hp] using hne
    let Q := P.rotateStart P.finish P.walk.end_mem_support (P.start_ne_finish G) hk (hnew rfl)
    refine ⟨Q, hp, rfl, ?_, ?_⟩
    · exact fun v => P.mem_rotateStart_support P.finish P.walk.end_mem_support
        (P.start_ne_finish G) hk (hnew rfl) v
    · intro e
      have h := P.rotateStart_edge_count P.finish P.walk.end_mem_support
        (P.start_ne_finish G) hk (hnew rfl) e
      change Q.walk.edges.count e + (if s(P.finish, _) = e then 1 else 0) =
        P.walk.edges.count e + (if s(P.start, P.finish) = e then 1 else 0) at h
      rw [hp] at h
      exact h

/-- Switch either or both arms and join them into one simple carrier, not two. -/
theorem exists_switched_arm_pair (L R : NonemptyPath G) (left right : Bool)
    (hjoin : L.finish = R.finish)
    (hinter : ∀ v, v ∈ L.walk.support → v ∈ R.walk.support → v = L.finish)
    (hleft : ∀ e ∈ L.walk.edges,
      (left = false ∨ e ≠ s(L.finish, L.walk.reverse.snd)) → e ∈ K.edgeSet)
    (hright : ∀ e ∈ R.walk.edges,
      (right = false ∨ e ≠ s(R.finish, R.walk.reverse.snd)) → e ∈ K.edgeSet)
    (hnewLeft : left = true → K.Adj L.start L.finish)
    (hnewRight : right = true → K.Adj R.start R.finish) :
    ∃ Q : NonemptyPath K,
      Q.start = (if left then L.walk.reverse.snd else L.start) ∧
      Q.finish = (if right then R.walk.reverse.snd else R.start) ∧
      ∀ e, Q.walk.edges.count e +
          ((if left then (if s(L.finish, L.walk.reverse.snd) = e then 1 else 0) else 0) +
           (if right then (if s(R.finish, R.walk.reverse.snd) = e then 1 else 0) else 0)) =
        (L.walk.edges.count e + R.walk.edges.count e) +
          ((if left then (if s(L.start, L.finish) = e then 1 else 0) else 0) +
           (if right then (if s(R.start, R.finish) = e then 1 else 0) else 0)) := by
  obtain ⟨L', hLs, hLf, hLv, hLe⟩ := L.exists_switched_arm left hleft hnewLeft
  obtain ⟨R', hRs, hRf, hRv, hRe⟩ := R.exists_switched_arm right hright hnewRight
  have hj : L'.finish = R'.reverse.start := hLf.trans (hjoin.trans hRf.symm)
  have hi : ∀ v, v ∈ L'.walk.support → v ∈ R'.reverse.walk.support → v = L'.finish := by
    intro v hvL hvR
    have hr : v ∈ R'.walk.support := by
      simpa only [reverse, SimpleGraph.Walk.support_reverse, List.mem_reverse] using hvR
    exact (hinter v ((hLv v).mp hvL) ((hRv v).mp hr)).trans hLf.symm
  refine ⟨L'.append R'.reverse hj hi, hLs, hRs, ?_⟩
  intro e
  rw [append_edges, reverse_edges, List.count_append, List.count_reverse]
  have hl := hLe e
  have hr := hRe e
  omega

end Gallai.NonemptyPath
