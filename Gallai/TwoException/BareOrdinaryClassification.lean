/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.BareOrdinaryCycleReduction
public import Mathlib.Combinatorics.SimpleGraph.Matching

@[expose] public section

/-! # Ordinary components in the bare kernel -/

namespace Gallai.TwoException

universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The spanning graph of an ordinary even component consists of cycles
and isolates. This supplies the standard finite cycle extraction theorem. -/
theorem bare_ordinary_component_isCycles
    (h : V) (z : evenVertices G)
    (H : BareMinimalCounterexample G h (z : V))
    (C : (evenSubgraph G).ConnectedComponent) (hz : z ∉ C.supp) :
    C.toSimpleGraph.spanningCoe.IsCycles := by
  classical
  intro v hn
  obtain ⟨w, hw⟩ := hn
  change C.toSimpleGraph.spanningCoe.Adj v w at hw
  rw [C.adj_spanningCoe_toSimpleGraph] at hw
  have hneighbors : C.toSimpleGraph.spanningCoe.neighborSet v =
      (evenSubgraph G).neighborSet v := by
    ext t
    simp only [SimpleGraph.mem_neighborSet, C.adj_spanningCoe_toSimpleGraph, hw.1,
      true_and]
  rw [hneighbors, SimpleGraph.ncard_neighborSet, ← eDegree_eq_induced_degree]
  have hd := bare_ordinary_degree_zero_or_two z v h H C hz hw.1
  have hpos : 0 < eDegree G (v : V) := by
    rw [eDegree_eq_induced_degree]
    exact hw.2.degree_pos_left
  omega

/-- Every nonisolated ordinary component is the complete support of a
triangle cycle, not merely a component containing a triangle. -/
theorem bare_ordinary_component_triangle_cycle
    (h : V) (z w : evenVertices G)
    (H : BareMinimalCounterexample G h (z : V))
    (C : (evenSubgraph G).ConnectedComponent) (hz : z ∉ C.supp)
    (hw : w ∈ C.supp) (hn : ((evenSubgraph G).neighborSet w).Nonempty) :
    ∃ p : (evenSubgraph G).Walk w w,
      p.IsCycle ∧ p.length = 3 ∧ p.toSubgraph.verts = C.supp := by
  classical
  let K := C.toSimpleGraph.spanningCoe
  have hle : K ≤ evenSubgraph G := by
    intro a b hab
    exact (C.adj_spanningCoe_toSimpleGraph.mp hab).2
  let D := K.connectedComponentMk w
  have hD : D.supp = C.supp := by
    ext v
    constructor
    · intro hv
      have hwD : w ∈ D.supp := by
        rw [SimpleGraph.ConnectedComponent.mem_supp_iff]
      have hr := D.reachable_of_mem_supp hwD hv
      have hrF := hr.some.mapLe hle
      rw [SimpleGraph.ConnectedComponent.mem_supp_iff] at hw ⊢
      exact (SimpleGraph.ConnectedComponent.sound hrF.reachable).symm.trans hw
    · intro hv
      let f : C.toSimpleGraph →g K := {
        toFun := Subtype.val
        map_rel' := by
          intro a b hab
          exact C.adj_spanningCoe_toSimpleGraph.mpr ⟨a.property, hab⟩ }
      have hr := C.reachable_toSimpleGraph hw hv
      have hrK := (hr.some.map f).reachable
      rw [SimpleGraph.ConnectedComponent.mem_supp_iff]
      exact (SimpleGraph.ConnectedComponent.sound hrK).symm
  have hnK : (K.neighborSet w).Nonempty := by
    obtain ⟨v, hv⟩ := hn
    exact ⟨v, C.adj_spanningCoe_toSimpleGraph.mpr ⟨hw, hv⟩⟩
  obtain ⟨p, hp, hverts⟩ :=
    (bare_ordinary_component_isCycles h z H C hz).exists_cycle_toSubgraph_verts_eq_connectedComponentSupp
        (c := D) (v := w) (by
          rw [SimpleGraph.ConnectedComponent.mem_supp_iff]) hnK
  let q := p.mapLe hle
  have hq : q.IsCycle := hp.mapLe hle
  have hlen : q.length = 3 := by
    have hthree := hq.three_le_length
    by_contra hne
    have hlong : 4 ≤ q.length := by omega
    exact bare_ordinary_component_no_long_cycle h z w H C hz hw q hq hlong
  refine ⟨q, hq, hlen, ?_⟩
  rw [← hD, ← hverts]
  ext v
  simp only [SimpleGraph.Walk.mem_verts_toSubgraph]
  change v ∈ (p.mapLe hle).support ↔ v ∈ p.support
  rw [SimpleGraph.Walk.support_mapLe_eq_support]

/-- Every ordinary component is a singleton or exactly a triangle cycle's
vertex set. This is the component normal form used by the endgame. -/
theorem bare_ordinary_component_isolate_or_triangle
    (h : V) (z w : evenVertices G)
    (H : BareMinimalCounterexample G h (z : V))
    (C : (evenSubgraph G).ConnectedComponent) (hz : z ∉ C.supp)
    (hw : w ∈ C.supp) :
    C.supp = {w} ∨ ∃ p : (evenSubgraph G).Walk w w,
      p.IsCycle ∧ p.length = 3 ∧ p.toSubgraph.verts = C.supp := by
  classical
  by_cases hn : ((evenSubgraph G).neighborSet w).Nonempty
  · exact Or.inr (bare_ordinary_component_triangle_cycle h z w H C hz hw hn)
  left
  have hi : (evenSubgraph G).IsIsolated w := by
    intro v hv
    exact hn ⟨v, hv⟩
  ext v
  constructor
  · intro hv
    have hr := C.reachable_of_mem_supp hw hv
    have hnil := hr.some.nil_of_isIsolated_of_mem_support hi hr.some.start_mem_support
    exact Set.mem_singleton_iff.mpr hnil.eq.symm
  · intro hv
    simpa only [Set.mem_singleton_iff.mp hv] using hw

end Gallai.TwoException
