/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.Operations.Transport
public import Lean.Elab.Tactic.Omega

@[expose] public section

/-! # Simple concatenation with an exact support-intersection hypothesis -/

namespace Gallai

universe u

variable {V : Type u} {G : SimpleGraph V}

/-- Two simple walks concatenate simply if their only common vertex is the join. -/
theorem isPath_append_of_intersection {a b c : V} (P : G.Walk a b) (Q : G.Walk b c)
    (hp : P.IsPath) (hq : Q.IsPath)
    (hinter : ∀ w, w ∈ P.support → w ∈ Q.support → w = b) : (P.append Q).IsPath := by
  apply SimpleGraph.Walk.IsPath.mk'
  rw [SimpleGraph.Walk.support_append]
  apply List.nodup_append'.mpr
  refine ⟨hp.support_nodup, hq.support_nodup.tail, ?_⟩
  intro w hwP hwQ
  have heq : w = b := hinter w hwP (List.mem_of_mem_tail hwQ)
  have hnot : b ∉ Q.support.tail := by
    have hn := hq.support_nodup
    rw [← Q.cons_tail_support] at hn
    exact (List.nodup_cons.mp hn).1
  exact hnot (heq ▸ hwQ)

/-- Join nonempty simple paths at their only common vertex. -/
def NonemptyPath.append (P Q : NonemptyPath G) (hjoin : P.finish = Q.start)
    (hinter : ∀ w, w ∈ P.walk.support → w ∈ Q.walk.support → w = P.finish) :
    NonemptyPath G where
  start := P.start
  finish := Q.finish
  walk := P.walk.append (Q.walk.copy hjoin.symm rfl)
  isPath := isPath_append_of_intersection _ _ P.isPath
    ((Q.walk.isPath_copy hjoin.symm rfl).mpr Q.isPath)
    (by simpa only [SimpleGraph.Walk.support_copy] using hinter)
  nonempty := by
    intro hn
    exact P.nonempty (SimpleGraph.Walk.nil_append_iff.mp hn).1

/-- Joining preserves every edge, in its original order within each path. -/
theorem NonemptyPath.append_edges (P Q : NonemptyPath G) (hjoin : P.finish = Q.start)
    (hinter : ∀ w, w ∈ P.walk.support → w ∈ Q.walk.support → w = P.finish) :
    (P.append Q hjoin hinter).walk.edges = P.walk.edges ++ Q.walk.edges := by
  change (P.walk.append (Q.walk.copy hjoin.symm rfl)).edges = _
  rw [SimpleGraph.Walk.edges_append, SimpleGraph.Walk.edges_copy]

/-- Joining removes exactly the two endpoint incidences at the join. -/
theorem NonemptyPath.append_endpoint_contribution [DecidableEq V]
    (P Q : NonemptyPath G) (hjoin : P.finish = Q.start)
    (hinter : ∀ w, w ∈ P.walk.support → w ∈ Q.walk.support → w = P.finish) (w : V) :
    ((if (P.append Q hjoin hinter).start = w then 1 else 0) +
      (if (P.append Q hjoin hinter).finish = w then 1 else 0)) +
        (if P.finish = w then 2 else 0 : ℕ) =
    ((if P.start = w then 1 else 0) + (if P.finish = w then 1 else 0)) +
      ((if Q.start = w then 1 else 0) + (if Q.finish = w then 1 else 0)) := by
  change ((if P.start = w then 1 else 0 : ℕ) + (if Q.finish = w then 1 else 0)) +
    (if P.finish = w then 2 else 0) = _
  rw [← hjoin]
  by_cases h : P.finish = w <;> simp only [h, ite_true, ite_false] <;> omega

end Gallai
