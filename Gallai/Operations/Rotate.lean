/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.Operations.HubRelease
public import Gallai.Operations.Concatenate

@[expose] public section

/-!
# Rotation of one endpoint arm at a supported hub

Remove the spoke immediately before the hub, reverse the released prefix,
and join its old endpoint directly to the hub. The suffix stays unchanged.
The hub may be the final endpoint; the released prefix may have no edges.
-/

namespace Gallai.NonemptyPath

universe u

variable {V : Type u} {G K : SimpleGraph V} [DecidableEq V]

/-- The released prefix and full suffix are vertex-disjoint. -/
theorem releaseLeft_disjoint_dropUntil (P : NonemptyPath G) (a : V)
    (ha : a ∈ P.walk.support) (hs : P.start ≠ a) :
    (P.releaseLeft a ha hs).support.Disjoint (P.walk.dropUntil a ha).support := by
  intro w hwL hwR
  have hp : ((P.walk.takeUntil a ha).append (P.walk.dropUntil a ha)).IsPath := by
    rw [P.walk.take_spec ha]
    exact P.isPath
  have hw := P.releaseLeft_support_subset a ha hs hwL
  have hne : w ≠ a := fun h => P.hub_notMem_releaseLeft a ha hs (h ▸ hwL)
  exact hp.ne_of_mem_support_of_append hne hw hwR rfl

/-- Removing the incoming spoke separates the released prefix from the unchanged suffix. -/
theorem rotation_source_edges (P : NonemptyPath G) (a : V)
    (ha : a ∈ P.walk.support) (hs : P.start ≠ a) :
    (P.releaseLeft a ha hs).edges ++
      s(a, (P.takeTo a ha hs).walk.reverse.snd) :: (P.walk.dropUntil a ha).edges =
        P.walk.edges := by
  have h := congrArg SimpleGraph.Walk.edges (P.walk.take_spec ha)
  rw [SimpleGraph.Walk.edges_append] at h
  change (P.takeTo a ha hs).walk.edges ++ (P.walk.dropUntil a ha).edges = _ at h
  rw [← (P.takeTo a ha hs).reverse_tail_edges_append_spoke] at h
  simp only [List.append_assoc, List.singleton_append] at h
  convert h using 1
  rfl

theorem rotation_left_edges (P : NonemptyPath G) (a : V)
    (ha : a ∈ P.walk.support) (hs : P.start ≠ a)
    (hkeep : ∀ e ∈ P.walk.edges,
      e ≠ s(a, (P.takeTo a ha hs).walk.reverse.snd) → e ∈ K.edgeSet) :
    ∀ e ∈ (P.releaseLeft a ha hs).reverse.edges, e ∈ K.edgeSet := by
  intro e he
  rw [SimpleGraph.Walk.edges_reverse, List.mem_reverse] at he
  apply hkeep e
  · rw [← P.rotation_source_edges a ha hs]
    exact List.mem_append_left _ he
  · intro heq
    exact P.hub_notMem_releaseLeft a ha hs
      ((P.releaseLeft a ha hs).fst_mem_support_of_mem_edges (heq ▸ he))

theorem rotation_right_edges (P : NonemptyPath G) (a : V)
    (ha : a ∈ P.walk.support) (hs : P.start ≠ a)
    (hkeep : ∀ e ∈ P.walk.edges,
      e ≠ s(a, (P.takeTo a ha hs).walk.reverse.snd) → e ∈ K.edgeSet) :
    ∀ e ∈ (P.walk.dropUntil a ha).edges, e ∈ K.edgeSet := by
  intro e he
  apply hkeep e (P.walk.edges_dropUntil_subset_edges ha he)
  intro heq
  have hp : s(a, (P.takeTo a ha hs).walk.reverse.snd) ∈ (P.takeTo a ha hs).walk.edges := by
    have h := (P.takeTo a ha hs).reverse.firstEdge_cons_tail_edges
    change s(a, (P.takeTo a ha hs).walk.reverse.snd) ::
      (P.takeTo a ha hs).walk.reverse.tail.edges = (P.takeTo a ha hs).walk.reverse.edges at h
    have hm : s(a, (P.takeTo a ha hs).walk.reverse.snd) ∈
        (P.takeTo a ha hs).walk.reverse.edges := by
      rw [← h]
      exact List.mem_cons_self
    simpa only [SimpleGraph.Walk.edges_reverse, List.mem_reverse] using hm
  exact P.isPath.isTrail.disjoint_edges_takeUntil_dropUntil ha hp (heq ▸ he)

/-- Rotate the initial arm, supplied with the actual retained edges and replacement edge. -/
def rotateStart (P : NonemptyPath G) (a : V) (ha : a ∈ P.walk.support) (hs : P.start ≠ a)
    (hkeep : ∀ e ∈ P.walk.edges,
      e ≠ s(a, (P.takeTo a ha hs).walk.reverse.snd) → e ∈ K.edgeSet)
    (hnew : K.Adj P.start a) : NonemptyPath K where
  start := (P.takeTo a ha hs).walk.reverse.snd
  finish := P.finish
  walk := ((P.releaseLeft a ha hs).reverse.transfer K (P.rotation_left_edges a ha hs hkeep)).append
    (.cons hnew ((P.walk.dropUntil a ha).transfer K (P.rotation_right_edges a ha hs hkeep)))
  isPath := by
    apply Gallai.isPath_append_of_intersection
    · exact (P.releaseLeft_isPath a ha hs).reverse.transfer _
    · apply SimpleGraph.Walk.IsPath.mk'
      simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_transfer]
      exact List.nodup_cons.mpr
        ⟨fun h => P.releaseLeft_disjoint_dropUntil a ha hs
          (P.releaseLeft a ha hs).start_mem_support h, (P.isPath.dropUntil ha).support_nodup⟩
    · intro w hwL hwR
      simp only [SimpleGraph.Walk.support_transfer, SimpleGraph.Walk.support_reverse,
        List.mem_reverse] at hwL
      simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_transfer,
        List.mem_cons] at hwR
      exact hwR.elim id (fun h => False.elim (P.releaseLeft_disjoint_dropUntil a ha hs hwL h))
  nonempty := fun h => SimpleGraph.Walk.not_nil_cons (SimpleGraph.Walk.nil_append_iff.mp h).2

/-- The rotated path reverses the released prefix and replaces exactly the incoming spoke. -/
theorem rotateStart_edges (P : NonemptyPath G) (a : V) (ha : a ∈ P.walk.support)
    (hs : P.start ≠ a)
    (hkeep : ∀ e ∈ P.walk.edges,
      e ≠ s(a, (P.takeTo a ha hs).walk.reverse.snd) → e ∈ K.edgeSet)
    (hnew : K.Adj P.start a) :
    (P.rotateStart a ha hs hkeep hnew).walk.edges =
      (P.releaseLeft a ha hs).edges.reverse ++ s(P.start, a) :: (P.walk.dropUntil a ha).edges := by
  simp only [rotateStart, SimpleGraph.Walk.edges_append, SimpleGraph.Walk.edges_cons,
    SimpleGraph.Walk.edges_transfer, SimpleGraph.Walk.edges_reverse]

omit [DecidableEq V] in
/-- Reversing a nonempty carrier's terminal-spoke deletion leaves all but its final vertex. -/
theorem reverse_tail_support_append_finish (P : NonemptyPath G) :
    P.walk.reverse.tail.reverse.support ++ [P.finish] = P.walk.support := by
  rw [SimpleGraph.Walk.support_reverse,
    P.walk.reverse.support_tail_of_not_nil P.reverse.nonempty]
  have h := congrArg List.reverse P.walk.reverse.cons_tail_support
  simpa only [SimpleGraph.Walk.support_reverse, List.reverse_cons, List.reverse_reverse] using h

/-- The released prefix and full suffix partition the original support. -/
theorem rotation_support_parts (P : NonemptyPath G) (a : V)
    (ha : a ∈ P.walk.support) (hs : P.start ≠ a) :
    P.walk.support = (P.releaseLeft a ha hs).support ++ (P.walk.dropUntil a ha).support := by
  have h := congrArg SimpleGraph.Walk.support (P.walk.take_spec ha)
  rw [SimpleGraph.Walk.support_append] at h
  change (P.takeTo a ha hs).walk.support ++ (P.walk.dropUntil a ha).support.tail = _ at h
  rw [← (P.takeTo a ha hs).reverse_tail_support_append_finish] at h
  simp only [List.append_assoc, List.singleton_append] at h
  change (P.releaseLeft a ha hs).support ++ a :: (P.walk.dropUntil a ha).support.tail = _ at h
  rw [(P.walk.dropUntil a ha).cons_tail_support] at h
  exact h.symm

/-- Rotation reorders vertices but does not change the carrier's support set. -/
theorem mem_rotateStart_support (P : NonemptyPath G) (a : V) (ha : a ∈ P.walk.support)
    (hs : P.start ≠ a)
    (hkeep : ∀ e ∈ P.walk.edges,
      e ≠ s(a, (P.takeTo a ha hs).walk.reverse.snd) → e ∈ K.edgeSet)
    (hnew : K.Adj P.start a) (v : V) :
    v ∈ (P.rotateStart a ha hs hkeep hnew).walk.support ↔ v ∈ P.walk.support := by
  have hout : (P.rotateStart a ha hs hkeep hnew).walk.support =
      (P.releaseLeft a ha hs).support.reverse ++ (P.walk.dropUntil a ha).support := by
    simp only [rotateStart, SimpleGraph.Walk.support_append, SimpleGraph.Walk.support_cons,
      SimpleGraph.Walk.support_transfer, SimpleGraph.Walk.support_reverse, List.tail_cons]
  rw [hout, P.rotation_support_parts a ha hs]
  simp only [List.mem_append, List.mem_reverse]

/-- Exact edge multiplicity balance for a rotated carrier. -/
theorem rotateStart_edge_count (P : NonemptyPath G) (a : V) (ha : a ∈ P.walk.support)
    (hs : P.start ≠ a)
    (hkeep : ∀ e ∈ P.walk.edges,
      e ≠ s(a, (P.takeTo a ha hs).walk.reverse.snd) → e ∈ K.edgeSet)
    (hnew : K.Adj P.start a) (e : Sym2 V) :
    (P.rotateStart a ha hs hkeep hnew).walk.edges.count e +
        (if s(a, (P.takeTo a ha hs).walk.reverse.snd) = e then 1 else 0) =
      P.walk.edges.count e + if s(P.start, a) = e then 1 else 0 := by
  rw [P.rotateStart_edges a ha hs hkeep hnew, ← P.rotation_source_edges a ha hs]
  simp only [List.count_append, List.count_reverse, List.count_cons, beq_iff_eq]
  split_ifs <;> omega

/-- Rotation transfers one endpoint from the old initial vertex to the removed spoke's leaf. -/
theorem rotateStart_endpoint_contribution (P : NonemptyPath G) (a : V)
    (ha : a ∈ P.walk.support) (hs : P.start ≠ a)
    (hkeep : ∀ e ∈ P.walk.edges,
      e ≠ s(a, (P.takeTo a ha hs).walk.reverse.snd) → e ∈ K.edgeSet)
    (hnew : K.Adj P.start a) (v : V) :
    ((if (P.rotateStart a ha hs hkeep hnew).start = v then 1 else 0) +
      (if (P.rotateStart a ha hs hkeep hnew).finish = v then 1 else 0)) +
        (if P.start = v then 1 else 0) =
    ((if P.start = v then 1 else 0) + (if P.finish = v then 1 else 0)) +
      (if (P.takeTo a ha hs).walk.reverse.snd = v then 1 else 0 : ℕ) := by
  change ((if (P.takeTo a ha hs).walk.reverse.snd = v then 1 else 0 : ℕ) +
      (if P.finish = v then 1 else 0)) + (if P.start = v then 1 else 0) =
    ((if P.start = v then 1 else 0) + (if P.finish = v then 1 else 0)) +
      (if (P.takeTo a ha hs).walk.reverse.snd = v then 1 else 0)
  omega

end Gallai.NonemptyPath
