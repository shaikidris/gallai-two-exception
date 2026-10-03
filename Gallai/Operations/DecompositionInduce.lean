/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.Operations.DecompositionMap
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

@[expose] public section

/-! # Restricting a path decomposition to an induced vertex set -/

namespace Gallai

universe u
variable {V : Type u} {G : SimpleGraph V}

/-- Restrict a nonempty path whose whole support lies in the retained set. -/
def NonemptyPath.induce (P : NonemptyPath G) (s : Set V)
    (hs : ∀ v ∈ P.walk.support, v ∈ s) : NonemptyPath (G.induce s) where
  start := ⟨P.start, hs _ P.walk.start_mem_support⟩
  finish := ⟨P.finish, hs _ P.walk.end_mem_support⟩
  walk := P.walk.induce s hs
  isPath := by
    apply (SimpleGraph.Walk.isPath_map_iff_of_injective
      (f := (SimpleGraph.Embedding.induce (G := G) s).toHom)
      (SimpleGraph.Embedding.induce (G := G) s).injective).mp
    rw [SimpleGraph.Walk.map_induce]
    exact P.isPath
  nonempty := SimpleGraph.Walk.not_nil_of_ne
    (fun h => P.start_ne_finish G (congrArg Subtype.val h))

/-- Induced edges correspond exactly to their original unordered edges. -/
theorem NonemptyPath.induce_edge_iff (P : NonemptyPath G) (s : Set V)
    (hs : ∀ v ∈ P.walk.support, v ∈ s) (e : Sym2 s) :
    e ∈ (P.induce s hs).walk.edges ↔ Sym2.map Subtype.val e ∈ P.walk.edges := by
  have h := congrArg SimpleGraph.Walk.edges (P.walk.map_induce hs)
  rw [SimpleGraph.Walk.edges_map] at h
  change List.map (Sym2.map Subtype.val) (P.induce s hs).walk.edges = P.walk.edges at h
  rw [← h]
  constructor
  · intro he
    exact List.mem_map.mpr ⟨e, he, rfl⟩
  · intro he
    obtain ⟨a, ha, heq⟩ := List.mem_map.mp he
    exact (Sym2.map.injective Subtype.val_injective heq) ▸ ha

/-- Restrict the entire family, retaining its original index set. -/
def Decomposition.induce (D : Decomposition G) (s : Set V)
    (hs : ∀ i v, v ∈ (D.path i).walk.support → v ∈ s) : Decomposition (G.induce s) where
  size := D.size
  path i := (D.path i).induce s (hs i)
  covers := by
    intro e he
    have he' : Sym2.map Subtype.val e ∈ G.edgeSet :=
      (SimpleGraph.Embedding.induce (G := G) s).toHom.map_mem_edgeSet he
    obtain ⟨i, hi, hu⟩ := D.covers _ he'
    refine ⟨i, ((D.path i).induce_edge_iff s (hs i) e).mpr hi, ?_⟩
    intro j hj
    exact hu j (((D.path j).induce_edge_iff s (hs j) e).mp hj)

/-- Restriction changes no path count. -/
@[simp] theorem Decomposition.induce_size (D : Decomposition G) (s : Set V)
    (hs : ∀ i v, v ∈ (D.path i).walk.support → v ∈ s) :
    (D.induce s hs).size = D.size := rfl

/-- Every retained vertex keeps its original endpoint count. -/
@[simp] theorem Decomposition.induce_endpointCount [DecidableEq V]
    (D : Decomposition G) (s : Set V)
    (hs : ∀ i v, v ∈ (D.path i).walk.support → v ∈ s) (v : s) :
    (D.induce s hs).endpointCount v = D.endpointCount v.val := by
  simp [Decomposition.endpointCount, Decomposition.induce, NonemptyPath.induce,
    Subtype.ext_iff]
  rfl

/-- Transport across equal induced vertex sets, preserving size and every endpoint count. -/
theorem Decomposition.induce_set_congr [DecidableEq V] {s t : Set V}
    (D : Decomposition (G.induce s)) (h : s = t) :
    ∃ E : Decomposition (G.induce t), E.size = D.size ∧
      ∀ v : s, E.endpointCount ⟨v.val, h ▸ v.property⟩ = D.endpointCount v := by
  subst t
  exact ⟨D, rfl, fun _ => rfl⟩

/-- An isolated vertex cannot occur on a nonempty carrier. -/
theorem NonemptyPath.notMem_support_of_isolated (P : NonemptyPath G) (z : V)
    (hz : ∀ v, ¬ G.Adj z v) : z ∉ P.walk.support := by
  intro h
  obtain ⟨v, _, hv⟩ := SimpleGraph.adj_of_mem_walk_support P.walk P.nonempty h
  exact hz v hv

/-- Remove an isolated vertex from the ambient type, with no change to the
path count or endpoint multiplicities of retained vertices. -/
theorem Decomposition.remove_isolated [DecidableEq V] (D : Decomposition G)
    (z : V) (hz : ∀ v, ¬ G.Adj z v) :
    ∃ E : Decomposition (G.induce {v | v ≠ z}), E.size = D.size ∧
      ∀ v : {v : V // v ≠ z}, E.endpointCount v = D.endpointCount v.val := by
  have hs : ∀ i v, v ∈ (D.path i).walk.support → v ∈ {v | v ≠ z} := by
    intro i v hv he
    exact (D.path i).notMem_support_of_isolated z hz (he ▸ hv)
  exact ⟨D.induce _ hs, rfl, fun v => D.induce_endpointCount _ hs v⟩

end Gallai
