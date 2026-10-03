/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.Foundations.Decomposition

@[expose] public section

/-!
# Transport of nonempty paths

Changing the ambient graph requires every used edge to remain available.
Changing vertices requires injectivity: a graph homomorphism alone can
identify two vertices of a simple path.
-/

namespace Gallai.NonemptyPath

universe u v

variable {V : Type u} {W : Type v} {G : SimpleGraph V} {H : SimpleGraph W}

/-- Transfer a path to a graph on the same vertices containing all its edges. -/
def transfer (P : NonemptyPath G) (K : SimpleGraph V)
    (h : ∀ e ∈ P.walk.edges, e ∈ K.edgeSet) : NonemptyPath K where
  start := P.start
  finish := P.finish
  walk := P.walk.transfer K h
  isPath := P.isPath.transfer h
  nonempty := SimpleGraph.Walk.not_nil_of_ne (P.start_ne_finish G)

/-- Ambient transfer does not alter the ordered edge list. -/
@[simp] theorem transfer_edges (P : NonemptyPath G) (K : SimpleGraph V)
    (h : ∀ e ∈ P.walk.edges, e ∈ K.edgeSet) :
    (P.transfer K h).walk.edges = P.walk.edges := P.walk.edges_transfer h

/-- Ambient transfer does not alter the ordered vertex list. -/
@[simp] theorem transfer_support (P : NonemptyPath G) (K : SimpleGraph V)
    (h : ∀ e ∈ P.walk.edges, e ∈ K.edgeSet) :
    (P.transfer K h).walk.support = P.walk.support := P.walk.support_transfer h

/-- Injectively map a nonempty simple path through a graph homomorphism. -/
def map (P : NonemptyPath G) (f : G →g H) (hf : Function.Injective f) : NonemptyPath H where
  start := f P.start
  finish := f P.finish
  walk := P.walk.map f
  isPath := P.isPath.map hf
  nonempty := SimpleGraph.Walk.not_nil_of_ne (fun h => P.start_ne_finish G (hf h))

/-- An injective graph map acts on each unordered path edge. -/
@[simp] theorem map_edges (P : NonemptyPath G) (f : G →g H) (hf : Function.Injective f) :
    (P.map f hf).walk.edges = P.walk.edges.map (Sym2.map f) := P.walk.edges_map f

/-- An injective graph map acts on each support vertex. -/
@[simp] theorem map_support (P : NonemptyPath G) (f : G →g H) (hf : Function.Injective f) :
    (P.map f hf).walk.support = P.walk.support.map f := P.walk.support_map f

/-- Reverse the orientation without changing the underlying simple path. -/
def reverse (P : NonemptyPath G) : NonemptyPath G where
  start := P.finish
  finish := P.start
  walk := P.walk.reverse
  isPath := P.isPath.reverse
  nonempty := SimpleGraph.Walk.not_nil_of_ne (P.start_ne_finish G).symm

/-- Reversal reverses the edge list and changes no unordered edges. -/
@[simp] theorem reverse_edges (P : NonemptyPath G) :
    P.reverse.walk.edges = P.walk.edges.reverse := P.walk.edges_reverse

end Gallai.NonemptyPath
