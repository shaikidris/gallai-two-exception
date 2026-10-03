/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.Inputs.SingleEdge

@[expose] public section

/-! # Two edges at an isolated vertex, with no increase in path count -/

namespace Gallai.Decomposition

open scoped Finset

universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Two donors supply a fresh degree-two vertex with two endpoint occurrences. -/
theorem attach_two_edges (D : Decomposition G) (z a b : V)
    (hza : z ≠ a) (hzb : z ≠ b) (hab : a ≠ b)
    (hz : ∀ v, ¬ G.Adj z v)
    (ha : 0 < D.endpointCount a) (hb : 2 ≤ D.endpointCount b) :
    ∃ E : Decomposition ((G ⊔ SimpleGraph.edge z a) ⊔ SimpleGraph.edge z b),
      E.size = D.size ∧ E.endpointCount z = D.endpointCount z + 2 := by
  classical
  have hzero : #{v ∈ G.neighborFinset z | D.endpointCount v = 0} = 0 := by
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro v hv
    exact hz v ((G.mem_neighborFinset z v).mp (Finset.mem_filter.mp hv).1)
  obtain ⟨E₁, hs₁, hv₁⟩ := D.single_edge_addibility z a hza (hz a)
    (by rw [hzero]; exact ha)
  have hE₁z : E₁.endpointCount z = D.endpointCount z + 1 := by
    simpa [Ne.symm hza] using hv₁ z
  have hE₁b : E₁.endpointCount b = D.endpointCount b := by
    simpa [hab, hzb] using hv₁ b
  have hmissing : ¬ (G ⊔ SimpleGraph.edge z a).Adj z b := by
    rintro (h | h)
    · exact hz b h
    · simp [SimpleGraph.edge_adj, Ne.symm hab, hza] at h
  have hsmall :
      #{v ∈ (G ⊔ SimpleGraph.edge z a).neighborFinset z | E₁.endpointCount v = 0} ≤ 1 := by
    have hsub :
        ((G ⊔ SimpleGraph.edge z a).neighborFinset z).filter
          (fun v => E₁.endpointCount v = 0) ⊆ {a} := by
      intro v hv
      have hv := ((G ⊔ SimpleGraph.edge z a).mem_neighborFinset z v).mp
        (Finset.mem_filter.mp hv).1
      rcases hv with hv | hv
      · exact (hz v hv).elim
      · have hva : v = a := (by simpa [SimpleGraph.edge_adj, hza] using hv :
          v = a ∧ z ≠ v).1
        exact Finset.mem_singleton.mpr hva
    have hc := Finset.card_le_card hsub
    simpa using hc
  obtain ⟨E₂, hs₂, hv₂⟩ := E₁.single_edge_addibility z b hzb hmissing (by omega)
  refine ⟨E₂, hs₂.trans hs₁, ?_⟩
  have he : E₂.endpointCount z = E₁.endpointCount z + 1 := by
    simpa [Ne.symm hzb] using hv₂ z
  omega

end Gallai.Decomposition
