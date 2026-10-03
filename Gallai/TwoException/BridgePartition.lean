/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.Structure.EdgeDeletion
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.Paths

@[expose] public section

/-! # The reachable side of a deleted bridge

For an edge `hx`, the vertices reachable from `h` after deleting `hx` form a
canonical side.  If `hx` is a bridge, no surviving edge crosses this side, and
every original crossing edge is exactly `hx`.  This is the graph-theoretic
interface needed before a bridge case can assemble component decompositions.
-/

namespace Gallai.TwoException

universe u

variable {V : Type u} {G : SimpleGraph V}

/-- The component side of `h` after deleting the edge `hx`. -/
def bridgeSide (G : SimpleGraph V) (h x : V) : Set V :=
  {v | (G.deleteEdges {s(h, x)}).Reachable h v}

theorem mem_bridgeSide_self (h x : V) : h ∈ bridgeSide G h x := by
  change (G.deleteEdges {s(h, x)}).Reachable h h
  exact @SimpleGraph.Reachable.refl V (G.deleteEdges {s(h, x)}) h

theorem not_mem_bridgeSide_other (h x : V) (hbridge : G.IsBridge s(h, x)) :
    x ∉ bridgeSide G h x := by
  exact hbridge

/-- A surviving puncture edge cannot leave the reachable side. -/
theorem not_adj_delete_edge_of_bridgeSide_crossing (h x u v : V)
    (hu : u ∈ bridgeSide G h x)
    (hv : v ∉ bridgeSide G h x) :
    ¬ (G.deleteEdges {s(h, x)}).Adj u v := by
  intro huv
  exact hv (hu.trans huv.reachable)

/-- Under a bridge deletion, every original edge crossing the canonical side
is the deleted bridge edge itself. -/
theorem crossing_adj_eq_deleted_edge (h x u v : V)
    (hu : u ∈ bridgeSide G h x)
    (hv : v ∉ bridgeSide G h x) (huv : G.Adj u v) :
    s(u, v) = s(h, x) := by
  by_contra hne
  apply not_adj_delete_edge_of_bridgeSide_crossing h x u v hu hv
  exact SimpleGraph.deleteEdges_adj.mpr ⟨huv, hne⟩

/-- The canonical bridge side is exactly the support of the puncture component
containing `h`. -/
theorem bridgeSide_eq_component_supp (h x : V) :
    bridgeSide G h x =
      ((G.deleteEdges {s(h, x)}).connectedComponentMk h).supp := by
  ext v
  simp only [bridgeSide, Set.mem_ofPred_eq,
    SimpleGraph.ConnectedComponent.mem_supp_iff,
    SimpleGraph.ConnectedComponent.eq]
  constructor
  · exact SimpleGraph.Reachable.symm
  · exact SimpleGraph.Reachable.symm

/-- In a connected graph, every vertex outside the deleted-edge reachable side
is reachable from the other endpoint without that edge.  A simple `h`--`v`
path must cross the deleted edge; its suffix after `x` avoids `h`, hence avoids
that edge and survives in the puncture. -/
theorem reachable_from_other_of_not_mem_bridgeSide [DecidableEq V]
    (hconn : G.Connected) (h x v : V)
    (hne : h ≠ x) (hv : v ∉ bridgeSide G h x) :
    (G.deleteEdges {s(h, x)}).Reachable x v := by
  apply (hconn.preconnected h v).elim_path
  intro p
  let w : G.Walk h v := p
  have hnot : ¬ (G.deleteEdges {s(h, x)}).Reachable h v := hv
  have he : s(h, x) ∈ w.edges := w.mem_edges_of_not_reachable_deleteEdges hnot
  have hxw : x ∈ w.support := w.snd_mem_support_of_mem_edges he
  have hxwr : x ∈ w.reverse.support := by simpa [w] using hxw
  let q : G.Walk v x := w.reverse.takeUntil x hxwr
  have hqpath : q.IsPath := by
    exact p.isPath.reverse.takeUntil hxwr
  have hnot_hq : h ∉ q.support := by
    simpa only [q] using
      (SimpleGraph.Walk.endpoint_notMem_support_takeUntil p.isPath.reverse hxwr hne)
  have hqedge : s(h, x) ∉ q.edges := by
    intro heq
    exact hnot_hq (q.fst_mem_support_of_mem_edges heq)
  exact (q.toDeleteEdge s(h, x) hqedge).reverse.reachable

/-- A connected graph punctured at a bridge has no components beyond the two
containing the bridge endpoints. -/
theorem puncture_reachable_from_h_or_x [DecidableEq V]
    (hconn : G.Connected) (h x v : V) (hne : h ≠ x) :
    (G.deleteEdges {s(h, x)}).Reachable h v ∨
      (G.deleteEdges {s(h, x)}).Reachable x v := by
  by_cases hv : v ∈ bridgeSide G h x
  · exact Or.inl hv
  · exact Or.inr (reachable_from_other_of_not_mem_bridgeSide hconn h x v hne hv)

end Gallai.TwoException
