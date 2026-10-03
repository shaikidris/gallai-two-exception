/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.Operations.Transport
public import Gallai.Foundations.Endpoints

@[expose] public section

/-! # Injective transport of an entire path decomposition -/

namespace Gallai.Decomposition

universe u v

variable {V : Type u} {W : Type v} {G : SimpleGraph V}

/-- Map the whole family to the graph image. Vertices outside the image are isolated. -/
def map (D : Decomposition G) (f : V ↪ W) : Decomposition (G.map f) where
  size := D.size
  path i := (D.path i).map (SimpleGraph.Embedding.map f G).toHom
    (SimpleGraph.Embedding.map f G).injective
  covers := by
    intro e he
    rw [SimpleGraph.edgeSet_map] at he
    obtain ⟨a, ha, rfl⟩ := he
    obtain ⟨i, hi, hu⟩ := D.covers a ha
    refine ⟨i, ?_, ?_⟩
    · dsimp only
      rw [NonemptyPath.map_edges]
      exact List.mem_map.mpr ⟨a, hi, rfl⟩
    · intro j hj
      rw [NonemptyPath.map_edges] at hj
      obtain ⟨b, hb, heq⟩ := List.mem_map.mp hj
      have hab : b = a := Sym2.map.injective f.injective heq
      exact hu j (hab ▸ hb)

/-- Injective transport preserves the number of paths exactly. -/
@[simp] theorem map_size (D : Decomposition G) (f : V ↪ W) :
    (D.map f).size = D.size := rfl

/-- Each old vertex keeps its endpoint multiplicity at its image. -/
@[simp] theorem map_endpointCount [DecidableEq V] [DecidableEq W]
    (D : Decomposition G) (f : V ↪ W) (x : V) :
    (D.map f).endpointCount (f x) = D.endpointCount x := by
  simp [endpointCount, map, NonemptyPath.map, f.injective.eq_iff]
  rfl

/-- A vertex outside the image occurs on no mapped carrier. -/
theorem map_endpointCount_of_notMem_range [DecidableEq W]
    (D : Decomposition G) (f : V ↪ W) (w : W) (hw : w ∉ Set.range f) :
    (D.map f).endpointCount w = 0 := by
  have hn : ∀ x, f x ≠ w := fun x h => hw ⟨x, h⟩
  simp [endpointCount, map, NonemptyPath.map, hn]

end Gallai.Decomposition
