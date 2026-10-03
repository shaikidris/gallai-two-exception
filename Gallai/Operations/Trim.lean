/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.Operations.Transport
public import Lean.Elab.Tactic.Omega

@[expose] public section

/-!
# Removing the first edge of a simple path

A longer path has a nonempty remainder in the edge-deleted graph. A
single-edge carrier instead disappears; it must not become a counted nil walk.
-/

namespace Gallai.NonemptyPath

universe u

variable {V : Type u} {G : SimpleGraph V}

/-- The first edge followed by the tail edges recovers the whole path. -/
theorem firstEdge_cons_tail_edges (P : NonemptyPath G) :
    s(P.start, P.walk.snd) :: P.walk.tail.edges = P.walk.edges := by
  have h := congrArg SimpleGraph.Walk.edges (P.walk.cons_tail_eq P.nonempty)
  simpa only [SimpleGraph.Walk.edges_cons] using h

/-- Simplicity prevents the first edge from occurring again in the tail. -/
theorem firstEdge_notMem_tail_edges (P : NonemptyPath G) :
    s(P.start, P.walk.snd) ∉ P.walk.tail.edges := by
  have hn := P.isPath.isTrail.edges_nodup
  rw [← P.firstEdge_cons_tail_edges] at hn
  exact (List.nodup_cons.mp hn).1

/-- A path has a nil tail exactly when it contains one edge. -/
theorem tail_nil_iff_length_one (P : NonemptyPath G) :
    P.walk.tail.Nil ↔ P.walk.length = 1 := by
  have hpos := SimpleGraph.Walk.not_nil_iff_lt_length.mp P.nonempty
  rw [← SimpleGraph.Walk.length_eq_zero_iff, SimpleGraph.Walk.length_tail]
  omega

/-- Trim the first edge of a longer path and transport to the edge-deleted graph. -/
def trimFirst (P : NonemptyPath G) (hlong : 1 < P.walk.length) :
    NonemptyPath (G.deleteEdges {s(P.start, P.walk.snd)}) where
  start := P.walk.snd
  finish := P.finish
  walk := P.walk.tail.toDeleteEdge _ P.firstEdge_notMem_tail_edges
  isPath := P.isPath.tail.transfer _
  nonempty := by
    intro hn
    have hlen := hn.length_eq_zero
    simp only [SimpleGraph.Walk.toDeleteEdge, SimpleGraph.Walk.toDeleteEdges,
      SimpleGraph.Walk.length_transfer, SimpleGraph.Walk.length_tail] at hlen
    omega

/-- The trimmed path consists exactly of the old tail edges. -/
@[simp] theorem trimFirst_edges (P : NonemptyPath G) (hlong : 1 < P.walk.length) :
    (P.trimFirst hlong).walk.edges = P.walk.tail.edges :=
  P.walk.tail.edges_transfer _

/-- The old first vertex no longer occurs anywhere on the trimmed carrier. -/
theorem start_notMem_trimFirst_support (P : NonemptyPath G) (hlong : 1 < P.walk.length) :
    P.start ∉ (P.trimFirst hlong).walk.support := by
  change P.start ∉ (P.walk.tail.toDeleteEdge _ P.firstEdge_notMem_tail_edges).support
  rw [SimpleGraph.Walk.support_transfer, P.walk.support_tail_of_not_nil P.nonempty]
  have hn := P.isPath.support_nodup
  rw [← P.walk.cons_tail_support] at hn
  exact (List.nodup_cons.mp hn).1

/-- Trimming exchanges the initial endpoint for the second vertex. -/
theorem trimFirst_endpoint_contribution [DecidableEq V]
    (P : NonemptyPath G) (hlong : 1 < P.walk.length) (w : V) :
    ((if (P.trimFirst hlong).start = w then 1 else 0) +
      (if (P.trimFirst hlong).finish = w then 1 else 0)) +
        (if P.start = w then 1 else 0 : ℕ) =
    ((if P.start = w then 1 else 0) + (if P.finish = w then 1 else 0)) +
      (if P.walk.snd = w then 1 else 0) := by
  change ((if P.walk.snd = w then 1 else 0 : ℕ) + (if P.finish = w then 1 else 0)) +
    (if P.start = w then 1 else 0) = _
  omega

end Gallai.NonemptyPath
