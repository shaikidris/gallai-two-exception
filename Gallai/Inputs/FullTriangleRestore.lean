/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.Inputs.ThreeSpokeRestore
public import Gallai.Structure.EdgeDeletion

@[expose] public section

/-! # Full-triangle restoration with an odd neighbour

The original odd neighbour has no even neighbours. Deleting its edge makes
the hub even, so the three-spoke endpoint reserve can be consumed there.
-/

namespace Gallai

open scoped Finset

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Removing an edge to an odd vertex preserves the hub's even neighbours. -/
theorem odd_edge_hub_evenNeighbors (u v : V) (hv : Odd (G.degree v)) :
    evenNeighbors (G.deleteEdges {s(u, v)}) u = evenNeighbors G u := by
  classical
  ext w
  constructor
  · intro hw
    obtain ⟨ha, he⟩ := (mem_evenNeighbors u w).mp hw
    have hwu : w ≠ u := ha.ne.symm
    have hwv : w ≠ v := by
      intro h
      subst w
      exact (SimpleGraph.deleteEdges_adj.mp ha).2 rfl
    exact (mem_evenNeighbors u w).mpr ⟨(SimpleGraph.deleteEdges_adj.mp ha).1, by
      rwa [degree_delete_edge_of_ne G u v w hwu hwv] at he⟩
  · intro hw
    obtain ⟨ha, he⟩ := (mem_evenNeighbors u w).mp hw
    have hwu : w ≠ u := ha.ne.symm
    have hwv : w ≠ v := by
      intro h
      subst w
      exact Nat.not_even_iff_odd.mpr hv he
    refine (mem_evenNeighbors u w).mpr ⟨?_, ?_⟩
    · simp [SimpleGraph.deleteEdges_adj, ha, hwv, hwu]
    · rwa [degree_delete_edge_of_ne G u v w hwu hwv]

/-- A full three-spoke puncture followed by its odd-neighbour edge restores
at unchanged size. The premises concern only the original graph's degrees. -/
theorem Decomposition.restore_full_triangle_odd_neighbor
    (u v : V) (hu : Odd (G.degree u)) (hv : Odd (G.degree v)) (huv : G.Adj u v)
    (hNv : ∀ w, G.Adj v w → ¬ Even (G.degree w))
    (hthree : eDegree G u = 3)
    (hcap : ∀ w ∈ evenNeighbors G u, eDegree G w ≤ 2)
    (D : Decomposition (evenStarPuncture (G.deleteEdges {s(u, v)}) u)) :
    ∃ P : Decomposition G, P.size = D.size := by
  classical
  let J := G.deleteEdges {s(u, v)}
  have hJu : Even (J.degree u) := by
    have hd := degree_delete_edge_add_one G u v huv
    rw [Nat.odd_iff] at hu
    rw [Nat.even_iff]
    change J.degree u + 1 = G.degree u at hd
    omega
  have hn : evenNeighbors J u = evenNeighbors G u := odd_edge_hub_evenNeighbors u v hv
  have hJthree : eDegree J u = 3 := by
    change #(evenNeighbors J u) = 3
    rw [hn]
    exact hthree
  have hJcap : ∀ w ∈ evenNeighbors J u, eDegree J w ≤ 3 := by
    intro w hw
    rw [hn] at hw
    have hew := ((mem_evenNeighbors u w).mp hw).2
    have hs : evenNeighbors J w ⊆ insert u (evenNeighbors G w) := by
      intro t ht
      by_cases htu : t = u
      · simp [htu]
      obtain ⟨ha, he⟩ := (mem_evenNeighbors w t).mp ht
      have htv : t ≠ v := by
        intro h
        subst t
        exact hNv w (SimpleGraph.deleteEdges_adj.mp ha).1.symm hew
      apply Finset.mem_insert_of_mem
      refine (mem_evenNeighbors w t).mpr ⟨(SimpleGraph.deleteEdges_adj.mp ha).1, ?_⟩
      change Even ((G.deleteEdges {s(u, v)}).degree t) at he
      rwa [degree_delete_edge_of_ne G u v t htu htv] at he
    have hc := Finset.card_le_card hs
    have hi := Finset.card_insert_le u (evenNeighbors G w)
    have hb := hcap w hw
    change #(evenNeighbors G w) ≤ 2 at hb
    change #(evenNeighbors J w) ≤ 3
    omega
  obtain ⟨E, hE, hEu⟩ := D.restore_three_even_spokes_exposing u hJu hJthree hJcap
  have hpass : #{w ∈ J.neighborFinset v | E.endpointCount w = 0} = 0 := by
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro w hw
    obtain ⟨ha, hz⟩ := Finset.mem_filter.mp hw
    have ha := (J.mem_neighborFinset v w).mp ha
    have hwv : w ≠ v := ha.ne.symm
    have hwu : w ≠ u := by
      intro h
      subst w
      have hm : ¬ J.Adj v u := by simp [J, SimpleGraph.deleteEdges_adj, Sym2.eq_swap]
      exact hm ha
    have ho : Odd (J.degree w) := by
      change Odd ((G.deleteEdges {s(u, v)}).degree w)
      rw [degree_delete_edge_of_ne G u v w hwu hwv]
      exact Nat.not_even_iff_odd.mp (hNv w (SimpleGraph.deleteEdges_adj.mp ha).1)
    have hp := E.endpointCount_pos_of_odd_degree w ho
    omega
  have hm : ¬ J.Adj v u := by simp [J, SimpleGraph.deleteEdges_adj, Sym2.eq_swap]
  obtain ⟨P, hP, _⟩ := E.single_edge_addibility (G := J) v u huv.ne.symm hm (by omega)
  have hg : J ⊔ SimpleGraph.edge v u = G := by
    rw [SimpleGraph.edge_comm]
    exact delete_edge_sup_edge G u v huv
  have hout : ∃ P : Decomposition (J ⊔ SimpleGraph.edge v u), P.size = D.size :=
    ⟨P, hP.trans hE⟩
  rwa [hg] at hout

end Gallai
