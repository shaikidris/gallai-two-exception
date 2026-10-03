/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.Operations.Shortcut
public import Gallai.Operations.DecompositionInduce
public import Gallai.Foundations.EdgeCounts
public import Mathlib.Combinatorics.SimpleGraph.Operations

@[expose] public section

/-! # Same-size suppression of an actual two-edge carrier run -/

namespace Gallai

open scoped Finset
universe u
variable {V : Type u} [DecidableEq V] {G : SimpleGraph V}

/-- Suppression keeps the old vertex type, with the middle vertex isolated. -/
def suppressedGraph (G : SimpleGraph V) (z x y : V) : SimpleGraph V :=
  (G ⊔ SimpleGraph.edge x y).deleteEdges {e | z ∈ e}

/-- Restore a missing shortcut and delete the middle vertex's incidences,
using an actual selected run. No path is added and no endpoint moves. -/
theorem Decomposition.suppress_of_run [DecidableRel G.Adj]
    (D : Decomposition G) (i : Fin D.size) (z x y : V)
    (L : G.Walk (D.path i).start x) (R : G.Walk y (D.path i).finish)
    (hxz : G.Adj x z) (hzy : G.Adj z y) (hxy : x ≠ y)
    (hfresh : ¬ G.Adj x y)
    (hrun : (D.path i).walk = L.append (.cons hxz (.cons hzy R)))
    (hother : ∀ j, j ≠ i → z ∉ (D.path j).walk.support) :
    ∃ E : Decomposition (suppressedGraph G z x y), E.size = D.size ∧
      ∀ v, E.endpointCount v = D.endpointCount v := by
  classical
  let K := G ⊔ SimpleGraph.edge x y
  let f : G →g K := SimpleGraph.Hom.ofLE le_sup_left
  have hf : Function.Injective f := by intro a b h; exact h
  have hnew : K.Adj x y := Or.inr (by simp [SimpleGraph.edge_adj, hxy])
  have hp : ((L.map f).append (.cons (f.map_adj hxz) (.cons (f.map_adj hzy) (R.map f)))).IsPath := by
    have h := (D.path i).isPath.map hf
    rw [hrun] at h
    simpa only [SimpleGraph.Walk.map_append, SimpleGraph.Walk.map_cons] using h
  let Q : NonemptyPath K := .shortcut (L.map f) (R.map f)
    (f.map_adj hxz) (f.map_adj hzy) hnew hp
  have hQavoid : z ∉ Q.walk.support :=
    NonemptyPath.shortcut_notMem_support (L.map f) (R.map f)
      (f.map_adj hxz) (f.map_adj hzy) hnew hp
  let raw : Fin D.size → NonemptyPath K := fun j =>
    if j = i then Q else (D.path j).map f hf
  have hav (j : Fin D.size) : z ∉ (raw j).walk.support := by
    by_cases hj : j = i
    · dsimp only [raw]
      rw [if_pos hj]
      exact hQavoid
    · dsimp only [raw]
      rw [if_neg hj, NonemptyPath.map_support]
      simpa [f] using hother j hj
  let paths : Fin D.size → NonemptyPath (suppressedGraph G z x y) := fun j =>
    (raw j).transfer _ (fun e he => by
      rw [suppressedGraph, SimpleGraph.edgeSet_deleteEdges]
      exact ⟨(raw j).walk.edges_subset_edgeSet he,
        fun hz => hav j (SimpleGraph.Walk.mem_support_of_mem_edges he hz)⟩)
  have hedge (j : Fin D.size) : (paths j).walk.edges = (raw j).walk.edges :=
    NonemptyPath.transfer_edges ..
  have hcount (e : Sym2 V) (he : e ∈ (suppressedGraph G z x y).edgeSet) :
      (∑ j, (paths j).walk.edges.count e) = 1 := by
    have he' := he
    rw [suppressedGraph, SimpleGraph.edgeSet_deleteEdges] at he'
    have hz : z ∉ e := he'.2
    have hne1 : s(x, z) ≠ e := fun h => hz (h ▸ (by simp : z ∈ s(x, z)))
    have hne2 : s(z, y) ≠ e := fun h => hz (h ▸ (by simp : z ∈ s(z, y)))
    have hqc : Q.walk.edges.count e = (D.path i).walk.edges.count e +
        if s(x, y) = e then 1 else 0 := by
      have h := NonemptyPath.shortcut_edge_count (L.map f) (R.map f)
        (f.map_adj hxz) (f.map_adj hzy) hnew hp e
      change Q.walk.edges.count e + (if s(x,z) = e then 1 else 0) +
        (if s(z,y) = e then 1 else 0) = _ at h
      simp only [if_neg hne1, if_neg hne2, add_zero] at h
      simpa [Q, hrun, SimpleGraph.Walk.edges_append, SimpleGraph.Walk.edges_cons,
        SimpleGraph.Walk.edges_map, f] using h
    have hj (j : Fin D.size) : (paths j).walk.edges.count e =
        (D.path j).walk.edges.count e + if j = i then (if s(x, y) = e then 1 else 0) else 0 := by
      rw [hedge]
      by_cases hji : j = i
      · subst j
        dsimp only [raw]
        rw [if_pos rfl, if_pos rfl]
        exact hqc
      · dsimp only [raw]
        rw [if_neg hji, if_neg hji, NonemptyPath.map_edges]
        simp [f]
    simp_rw [hj]
    rw [Finset.sum_add_distrib, D.sum_edge_count]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
    by_cases hnewedge : s(x, y) = e
    · have hnot : e ∉ G.edgeSet := by
        rw [← hnewedge, SimpleGraph.mem_edgeSet]
        exact hfresh
      simp [hnewedge, hnot]
    · have hold : e ∈ G.edgeSet := by
        have hk : e ∈ K.edgeSet := he'.1
        change e ∈ (G ⊔ SimpleGraph.edge x y).edgeSet at hk
        rw [SimpleGraph.edgeSet_sup] at hk
        rcases hk with h | h
        · exact h
        · have hh : e = s(x, y) := (by simpa [SimpleGraph.edge] using h :
            e = s(x,y) ∧ ¬ e.IsDiag).1
          exact (hnewedge hh.symm).elim
      simp [hnewedge, hold]
  refine ⟨Decomposition.ofEdgeCounts paths hcount, rfl, ?_⟩
  intro v
  change (∑ j : Fin D.size, _) = _
  apply Finset.sum_congr rfl
  intro j _
  change ((if (paths j).start = v then 1 else 0) +
    if (paths j).finish = v then 1 else 0) = _
  have hs : (paths j).start = (D.path j).start := by
    dsimp only [paths, NonemptyPath.transfer, raw]
    by_cases hj : j = i
    · rw [if_pos hj]
      subst j
      rfl
    · rw [if_neg hj]
      rfl
  have ht : (paths j).finish = (D.path j).finish := by
    dsimp only [paths, NonemptyPath.transfer, raw]
    by_cases hj : j = i
    · rw [if_pos hj]
      subst j
      rfl
    · rw [if_neg hj]
      rfl
  simp only [hs, ht]

omit [DecidableEq V] in
/-- Swapping the named neighbours does not change the suppressed graph. -/
theorem suppressedGraph_comm (G : SimpleGraph V) (z x y : V) :
    suppressedGraph G z x y = suppressedGraph G z y x := by
  unfold suppressedGraph
  rw [SimpleGraph.edge_comm x y]

/-- Suppress a degree-two vertex with zero endpoints, deriving the actual
carrier and its orientation. The isolated vertex remains in the ambient type. -/
theorem Decomposition.suppress_degree_two [Fintype V] [DecidableRel G.Adj]
    (D : Decomposition G) (z x y : V) (hxy : x ≠ y)
    (hd : G.degree z = 2) (hz : D.endpointCount z = 0)
    (hn : ∀ v, G.Adj z v → v = x ∨ v = y) (hfresh : ¬ G.Adj x y) :
    ∃ E : Decomposition (suppressedGraph G z x y), E.size = D.size ∧
      ∀ v, E.endpointCount v = D.endpointCount v := by
  obtain ⟨i, u, v, L, R, hu, hv, he, hpair, hother⟩ :=
    D.exists_suppression_run z x y hd hz hn
  rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact D.suppress_of_run i z u v L R hu hv hxy hfresh he hother
  · rw [suppressedGraph_comm]
    exact D.suppress_of_run i z u v L R hu hv hxy.symm
      (fun h => hfresh h.symm) he hother

/-- Suppress the degree-two vertex and remove it from the ambient vertex type.
The decomposition has the same size and preserves all retained endpoints. -/
theorem Decomposition.suppress_delete_degree_two [Fintype V] [DecidableRel G.Adj]
    (D : Decomposition G) (z x y : V) (hxy : x ≠ y)
    (hd : G.degree z = 2) (hz : D.endpointCount z = 0)
    (hn : ∀ v, G.Adj z v → v = x ∨ v = y) (hfresh : ¬ G.Adj x y) :
    ∃ E : Decomposition ((suppressedGraph G z x y).induce {v | v ≠ z}),
      E.size = D.size ∧
      ∀ v : {v : V // v ≠ z}, E.endpointCount v = D.endpointCount v.val := by
  obtain ⟨E, hsize, hend⟩ := D.suppress_degree_two z x y hxy hd hz hn hfresh
  have hiso : ∀ v, ¬ (suppressedGraph G z x y).Adj z v := by
    intro v
    simp [suppressedGraph, SimpleGraph.deleteEdges_adj]
  obtain ⟨R, hr, hv⟩ := E.remove_isolated z hiso
  exact ⟨R, hr.trans hsize, fun v => (hv v).trans (hend v.val)⟩

end Gallai
