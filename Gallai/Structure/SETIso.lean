/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.Structure.SET

@[expose] public section

/-! # Transport of the literal SET predicate

Used when the core of an attached ESET is a nested subtype of its original
component. Transport preserves the entire even-neighbour condition.
-/

namespace Gallai

variable {V W : Type*} [Fintype V] [Fintype W]
variable {G : SimpleGraph V} {H : SimpleGraph W}
variable [DecidableRel G.Adj] [DecidableRel H.Adj]

/-- Graph isomorphisms preserve even-neighbour counts, not just degree. -/
theorem eDegree_iso (f : G ≃g H) (v : V) : eDegree H (f v) = eDegree G v := by
  classical
  have hm : (evenNeighbors G v).map f.toEquiv.toEmbedding = evenNeighbors H (f v) := by
    ext w
    constructor
    · intro hw
      obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hw
      obtain ⟨hadj, he⟩ := (mem_evenNeighbors v a).mp ha
      exact (mem_evenNeighbors (f v) (f a)).mpr ⟨f.map_rel_iff.mpr hadj, by simpa using he⟩
    · intro hw
      obtain ⟨ha, he⟩ := (mem_evenNeighbors (f v) w).mp hw
      refine Finset.mem_map.mpr ⟨f.symm w, ?_, f.apply_symm_apply w⟩
      apply (mem_evenNeighbors v (f.symm w)).mpr
      constructor
      · simpa using f.symm.map_rel_iff.mpr ha
      · simpa using he
  have hc := congrArg Finset.card hm
  simpa only [Finset.card_map, eDegree] using hc.symm

/-- The SET predicate is invariant under a graph isomorphism. -/
theorem IsSET.iso (h : IsSET G) (f : G ≃g H) : IsSET H := by
  classical
  constructor
  · have hm : (Finset.univ.filter fun v => Even (G.degree v)).map f.toEquiv.toEmbedding =
        Finset.univ.filter fun w => Even (H.degree w) := by
      ext w
      constructor
      · intro hw
        obtain ⟨v, hv, rfl⟩ := Finset.mem_map.mp hw
        simpa using hv
      · intro hw
        refine Finset.mem_map.mpr ⟨f.symm w, ?_, f.apply_symm_apply w⟩
        simpa using hw
    have hc := congrArg Finset.card hm
    simpa only [Finset.card_map, h.card_even] using hc.symm
  · intro a b ha hb hab
    have hadj := h.even_clique (f.symm a) (f.symm b) (by simpa using ha)
      (by simpa using hb) (fun he => hab (f.symm.injective he))
    simpa using f.map_rel_iff.mpr hadj
  · intro v hv
    have hp := h.odd_neighbors (f.symm v) (by simpa using hv)
    simpa only [eDegree_iso, f.apply_symm_apply] using
      (show 2 ≤ eDegree H (f (f.symm v)) by rw [eDegree_iso]; exact hp)

end Gallai
