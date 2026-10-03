/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.BareOrdinaryClassification
public import Gallai.TwoException.OrdinaryTriangleComponent

@[expose] public section

/-! # Explicit ordinary triangles from the bare kernel classification -/
namespace Gallai.TwoException
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Extract labelled vertices and the complete support of an ordinary
nonisolated component. These are the inputs of the restoration consumer. -/
theorem bare_ordinary_component_triangle_vertices
    (h : V) (z w : evenVertices G)
    (H : BareMinimalCounterexample G h (z : V))
    (C : (evenSubgraph G).ConnectedComponent) (hz : z ∉ C.supp)
    (hw : w ∈ C.supp) (hn : ((evenSubgraph G).neighborSet w).Nonempty) :
    ∃ b c : evenVertices G, C.supp = {w, b, c} ∧
      G.Adj w b ∧ G.Adj b c ∧ G.Adj c w := by
  classical
  obtain ⟨p, hp, hlen, hverts⟩ :=
    bare_ordinary_component_triangle_cycle h z w H C hz hw hn
  refine ⟨p.getVert 1, p.getVert 2, ?_, ?_, ?_, ?_⟩
  · rw [← hverts]
    ext t
    rw [SimpleGraph.Walk.mem_verts_toSubgraph]
    constructor
    · intro ht
      obtain ⟨n, hn, hnl⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp ht
      have hcases : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 := by omega
      rcases hcases with rfl | rfl | rfl | rfl
      · simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
        exact Or.inl (hn.symm.trans p.getVert_zero)
      · simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
        exact Or.inr (Or.inl hn.symm)
      · simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
        exact Or.inr (Or.inr hn.symm)
      · have he : p.getVert 3 = w := p.getVert_of_length_le (by omega)
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
        exact Or.inl (hn.symm.trans he)
    · intro ht
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ht
      rcases ht with rfl | rfl | rfl
      · exact p.start_mem_support
      · exact p.getVert_mem_support 1
      · exact p.getVert_mem_support 2
  · simpa using p.adj_getVert_succ (i := 0) (by omega)
  · exact p.adj_getVert_succ (i := 1) (by omega)
  · have he : p.getVert 3 = w := p.getVert_of_length_le (by omega)
    change (evenSubgraph G).Adj (p.getVert 2) w
    simpa only [he] using p.adj_getVert_succ (i := 2) (by omega)

end Gallai.TwoException
