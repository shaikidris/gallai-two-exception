/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.Operations.Split
public import Gallai.Operations.Trim

@[expose] public section

/-!
# Releasing the two spokes of an internal hub occurrence

Removing the local run through a hub leaves two possibly nil old pieces.
They avoid the hub and have disjoint supports, even when the original carrier
visits other anchors. These facts supply, rather than assume, the old-piece
conditions needed for local star replacement.
-/

namespace Gallai.NonemptyPath

universe u

variable {V : Type u} {G : SimpleGraph V}

/-- The first vertex is absent from the raw tail, including a nil tail. -/
theorem start_notMem_tail_support (P : NonemptyPath G) :
    P.start ∉ P.walk.tail.support := by
  rw [P.walk.support_tail_of_not_nil P.nonempty]
  have hn := P.isPath.support_nodup
  rw [← P.walk.cons_tail_support] at hn
  exact (List.nodup_cons.mp hn).1

/-- Trimming the first edge retains only old support vertices. -/
theorem tail_support_subset (P : NonemptyPath G) :
    P.walk.tail.support ⊆ P.walk.support := by
  rw [P.walk.support_tail_of_not_nil P.nonempty]
  exact List.tail_subset _

/-- Removing the last spoke and then appending that spoke recovers the edge list. -/
theorem reverse_tail_edges_append_spoke (P : NonemptyPath G) :
    P.walk.reverse.tail.reverse.edges ++ [s(P.finish, P.walk.reverse.snd)] =
      P.walk.edges := by
  have h := congrArg List.reverse P.reverse.firstEdge_cons_tail_edges
  simpa only [reverse, List.reverse_cons, SimpleGraph.Walk.edges_reverse,
    List.reverse_reverse] using h

variable [DecidableEq V]

/-- The old left piece after removing the spoke immediately before the hub. -/
def releaseLeft (P : NonemptyPath G) (x : V) (hx : x ∈ P.walk.support)
    (hs : P.start ≠ x) : G.Walk P.start (P.takeTo x hx hs).walk.reverse.snd :=
  (P.takeTo x hx hs).walk.reverse.tail.reverse

/-- The old right piece after removing the spoke immediately after the hub. -/
def releaseRight (P : NonemptyPath G) (x : V) (hx : x ∈ P.walk.support)
    (ht : x ≠ P.finish) : G.Walk (P.dropFrom x hx ht).walk.snd P.finish :=
  (P.dropFrom x hx ht).walk.tail

/-- The released left piece remains simple; it is allowed to have no edges. -/
theorem releaseLeft_isPath (P : NonemptyPath G) (x : V)
    (hx : x ∈ P.walk.support) (hs : P.start ≠ x) :
    (P.releaseLeft x hx hs).IsPath :=
  (P.takeTo x hx hs).isPath.reverse.tail.reverse

/-- The released right piece remains simple; it is allowed to have no edges. -/
theorem releaseRight_isPath (P : NonemptyPath G) (x : V)
    (hx : x ∈ P.walk.support) (ht : x ≠ P.finish) :
    (P.releaseRight x hx ht).IsPath := (P.dropFrom x hx ht).isPath.tail

/-- The hub is absent from the released left piece. -/
theorem hub_notMem_releaseLeft (P : NonemptyPath G) (x : V)
    (hx : x ∈ P.walk.support) (hs : P.start ≠ x) :
    x ∉ (P.releaseLeft x hx hs).support := by
  change x ∉ (P.takeTo x hx hs).walk.reverse.tail.reverse.support
  rw [SimpleGraph.Walk.support_reverse, List.mem_reverse]
  exact (P.takeTo x hx hs).reverse.start_notMem_tail_support

/-- The hub is absent from the released right piece. -/
theorem hub_notMem_releaseRight (P : NonemptyPath G) (x : V)
    (hx : x ∈ P.walk.support) (ht : x ≠ P.finish) :
    x ∉ (P.releaseRight x hx ht).support :=
  (P.dropFrom x hx ht).start_notMem_tail_support

/-- Left release retains only vertices from the original prefix. -/
theorem releaseLeft_support_subset (P : NonemptyPath G) (x : V)
    (hx : x ∈ P.walk.support) (hs : P.start ≠ x) :
    (P.releaseLeft x hx hs).support ⊆ (P.takeTo x hx hs).walk.support := by
  intro w hw
  have h := (P.takeTo x hx hs).reverse.tail_support_subset
  have hw' : w ∈ (P.takeTo x hx hs).reverse.walk.tail.support := by
    change w ∈ (P.takeTo x hx hs).walk.reverse.tail.reverse.support at hw
    rw [SimpleGraph.Walk.support_reverse, List.mem_reverse] at hw
    exact hw
  simpa only [reverse, SimpleGraph.Walk.support_reverse, List.mem_reverse] using h hw'

/-- The two released pieces of one simple carrier have disjoint supports. -/
theorem release_supports_disjoint (P : NonemptyPath G) (x : V)
    (hx : x ∈ P.walk.support) (hs : P.start ≠ x) (ht : x ≠ P.finish) :
    (P.releaseLeft x hx hs).support.Disjoint (P.releaseRight x hx ht).support := by
  intro w hwL hwR
  have heq := (P.mem_prefix_support_and_suffix_support_iff x hx hs ht w).mp
    ⟨P.releaseLeft_support_subset x hx hs hwL,
      (P.dropFrom x hx ht).tail_support_subset hwR⟩
  exact P.hub_notMem_releaseLeft x hx hs (heq ▸ hwL)

/-- The released pieces and the two removed spokes partition the original edges. -/
theorem release_edges (P : NonemptyPath G) (x : V)
    (hx : x ∈ P.walk.support) (hs : P.start ≠ x) (ht : x ≠ P.finish) :
    (P.releaseLeft x hx hs).edges ++
      [s(x, (P.takeTo x hx hs).walk.reverse.snd), s(x, (P.dropFrom x hx ht).walk.snd)] ++
      (P.releaseRight x hx ht).edges = P.walk.edges := by
  have hL := (P.takeTo x hx hs).reverse_tail_edges_append_spoke
  have hR := (P.dropFrom x hx ht).firstEdge_cons_tail_edges
  have h := P.prefix_edges_append_suffix_edges x hx hs ht
  rw [← hL, ← hR] at h
  simpa only [releaseLeft, releaseRight, takeTo, dropFrom, List.append_assoc,
    List.cons_append, List.nil_append] using h

/-- The two attachment vertices of a through run are distinct. -/
theorem release_attachments_ne (P : NonemptyPath G) (x : V)
    (hx : x ∈ P.walk.support) (hs : P.start ≠ x) (ht : x ≠ P.finish) :
    (P.takeTo x hx hs).walk.reverse.snd ≠ (P.dropFrom x hx ht).walk.snd := by
  intro heq
  have hwR : (P.takeTo x hx hs).walk.reverse.snd ∈ (P.releaseRight x hx ht).support := by
    rw [heq]
    exact (P.releaseRight x hx ht).start_mem_support
  exact P.release_supports_disjoint x hx hs ht
    (P.releaseLeft x hx hs).end_mem_support
    hwR

/-- Both attachment vertices are neighbours of the released hub. -/
theorem release_attachments_adj (P : NonemptyPath G) (x : V)
    (hx : x ∈ P.walk.support) (hs : P.start ≠ x) (ht : x ≠ P.finish) :
    G.Adj x (P.takeTo x hx hs).walk.reverse.snd ∧
      G.Adj x (P.dropFrom x hx ht).walk.snd :=
  ⟨(P.takeTo x hx hs).reverse.walk.adj_snd (P.takeTo x hx hs).reverse.nonempty,
    (P.dropFrom x hx ht).walk.adj_snd (P.dropFrom x hx ht).nonempty⟩

end Gallai.NonemptyPath
