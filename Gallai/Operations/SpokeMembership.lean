/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.Operations.HubRelease
public import Gallai.Operations.Orient

@[expose] public section

/-!
# The exact spokes used by a simple carrier

At an endpoint a nonempty path has exactly its terminal spoke. At an internal
vertex it has exactly the two distinct HubRelease spokes. This identifies
the fibres of the spoke-ownership dictionary with the literal local runs.
-/

namespace Gallai.NonemptyPath

universe u

variable {V : Type u} {G : SimpleGraph V}

/-- The only spoke at a path's initial vertex is its first edge. -/
theorem first_spoke_iff (P : NonemptyPath G) (v : V) :
    s(P.start, v) ∈ P.walk.edges ↔ v = P.walk.snd := by
  have htail : s(P.start, v) ∉ P.walk.tail.edges := fun he =>
    P.start_notMem_tail_support (P.walk.tail.fst_mem_support_of_mem_edges he)
  rw [← P.firstEdge_cons_tail_edges, List.mem_cons]
  simp only [htail, or_false]
  exact (Sym2.mkEmbedding P.start).injective.eq_iff

/-- The only spoke at a path's final vertex is its last edge. -/
theorem last_spoke_iff (P : NonemptyPath G) (v : V) :
    s(P.finish, v) ∈ P.walk.edges ↔ v = P.walk.reverse.snd := by
  have h := P.reverse.first_spoke_iff v
  simpa only [reverse, SimpleGraph.Walk.edges_reverse, List.mem_reverse] using h

variable [DecidableEq V]

/-- Orienting a terminal carrier identifies its unique spoke at the designated hub. -/
theorem terminal_spoke_iff (P : NonemptyPath G) (x v : V)
    (hx : P.start = x ∨ P.finish = x) :
    s(x, v) ∈ P.walk.edges ↔ v = (P.toward x).walk.reverse.snd := by
  have h := (P.toward x).last_spoke_iff v
  have hend := P.toward_finish x hx
  have hedge := congrArg (fun w => s(w, v)) hend
  rw [hedge] at h
  exact (P.mem_toward_edges x s(x, v)).symm.trans h

/-- An internal hub has exactly the two released spokes on this carrier. -/
theorem through_spoke_iff (P : NonemptyPath G) (x v : V)
    (hx : x ∈ P.walk.support) (hs : P.start ≠ x) (ht : x ≠ P.finish) :
    s(x, v) ∈ P.walk.edges ↔
      v = (P.takeTo x hx hs).walk.reverse.snd ∨ v = (P.dropFrom x hx ht).walk.snd := by
  have hL : s(x, v) ∉ (P.releaseLeft x hx hs).edges := fun he =>
    P.hub_notMem_releaseLeft x hx hs
      ((P.releaseLeft x hx hs).fst_mem_support_of_mem_edges he)
  have hR : s(x, v) ∉ (P.releaseRight x hx ht).edges := fun he =>
    P.hub_notMem_releaseRight x hx ht
      ((P.releaseRight x hx ht).fst_mem_support_of_mem_edges he)
  rw [← P.release_edges x hx hs ht]
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
    hL, hR, false_or]
  exact or_congr (Sym2.mkEmbedding x).injective.eq_iff
    (Sym2.mkEmbedding x).injective.eq_iff

end Gallai.NonemptyPath
