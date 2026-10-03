/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.Foundations.Endpoints
public import Lean.Elab.Tactic.Omega

@[expose] public section

/-!
# Splitting a nonempty simple path

The cut is internal, so both pieces remain nonempty. Mathlib supplies the
walk splitting and simplicity proofs; this module records exact edge and
endpoint contracts for decomposition repair and carrier transport.
-/

namespace Gallai.NonemptyPath

universe u

variable {V : Type u} {G : SimpleGraph V} [DecidableEq V]

/-- The nonempty prefix ending at a supported vertex other than the start. -/
def takeTo (P : NonemptyPath G) (v : V) (hv : v ∈ P.walk.support)
    (hs : P.start ≠ v) : NonemptyPath G where
  start := P.start
  finish := v
  walk := P.walk.takeUntil v hv
  isPath := P.isPath.takeUntil hv
  nonempty := SimpleGraph.Walk.not_nil_of_ne hs

/-- The nonempty suffix starting at a supported vertex other than the finish. -/
def dropFrom (P : NonemptyPath G) (v : V) (hv : v ∈ P.walk.support)
    (ht : v ≠ P.finish) : NonemptyPath G where
  start := v
  finish := P.finish
  walk := P.walk.dropUntil v hv
  isPath := P.isPath.dropUntil hv
  nonempty := SimpleGraph.Walk.not_nil_of_ne ht

/-- Concatenating the two pieces recovers the original walk. -/
theorem prefix_append_suffix (P : NonemptyPath G) (v : V)
    (hv : v ∈ P.walk.support) (hs : P.start ≠ v) (ht : v ≠ P.finish) :
    (P.takeTo v hv hs).walk.append (P.dropFrom v hv ht).walk = P.walk :=
  P.walk.take_spec hv

/-- The ordered edge lists of the pieces partition the original edge list. -/
theorem prefix_edges_append_suffix_edges (P : NonemptyPath G) (v : V)
    (hv : v ∈ P.walk.support) (hs : P.start ≠ v) (ht : v ≠ P.finish) :
    (P.takeTo v hv hs).walk.edges ++ (P.dropFrom v hv ht).walk.edges = P.walk.edges := by
  exact (SimpleGraph.Walk.edges_append (P.takeTo v hv hs).walk
    (P.dropFrom v hv ht).walk).symm.trans
      (congrArg SimpleGraph.Walk.edges (P.prefix_append_suffix v hv hs ht))

/-- No edge belongs to both pieces of the split. -/
theorem disjoint_prefix_suffix_edges (P : NonemptyPath G) (v : V)
    (hv : v ∈ P.walk.support) (hs : P.start ≠ v) (ht : v ≠ P.finish) :
    (P.takeTo v hv hs).walk.edges.Disjoint (P.dropFrom v hv ht).walk.edges :=
  P.isPath.isTrail.disjoint_edges_takeUntil_dropUntil hv

/-- The two supports meet exactly at the cut vertex. -/
theorem mem_prefix_support_and_suffix_support_iff (P : NonemptyPath G) (v : V)
    (hv : v ∈ P.walk.support) (hs : P.start ≠ v) (ht : v ≠ P.finish) (w : V) :
    (w ∈ (P.takeTo v hv hs).walk.support ∧ w ∈ (P.dropFrom v hv ht).walk.support) ↔
      w = v := by
  constructor
  · rintro ⟨hleft, hright⟩
    by_contra hne
    have hpath : ((P.takeTo v hv hs).walk.append (P.dropFrom v hv ht).walk).IsPath := by
      rw [P.prefix_append_suffix v hv hs ht]
      exact P.isPath
    exact hpath.ne_of_mem_support_of_append hne hleft hright rfl
  · intro hw
    subst w
    exact ⟨(P.takeTo v hv hs).walk.end_mem_support,
      (P.dropFrom v hv ht).walk.start_mem_support⟩

/-- Splitting adds two endpoint incidences at the cut and none elsewhere. -/
theorem split_endpoint_contribution (P : NonemptyPath G) (v : V)
    (hv : v ∈ P.walk.support) (hs : P.start ≠ v) (ht : v ≠ P.finish) (w : V) :
    ((if (P.takeTo v hv hs).start = w then 1 else 0) +
      (if (P.takeTo v hv hs).finish = w then 1 else 0)) +
    ((if (P.dropFrom v hv ht).start = w then 1 else 0) +
      (if (P.dropFrom v hv ht).finish = w then 1 else 0)) =
    ((if P.start = w then 1 else 0) + (if P.finish = w then 1 else 0)) +
      (if v = w then 2 else 0 : ℕ) := by
  change ((if P.start = w then 1 else 0 : ℕ) + (if v = w then 1 else 0)) +
    ((if v = w then 1 else 0) + (if P.finish = w then 1 else 0)) = _
  by_cases h : v = w <;> simp only [h, if_true, if_false] <;> omega

end Gallai.NonemptyPath
