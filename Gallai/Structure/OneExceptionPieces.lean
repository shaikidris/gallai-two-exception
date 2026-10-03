/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.Structure.OneVertexSeparation

@[expose] public section

/-! # Inheriting one-exception hypotheses on separator pieces

Only the named vertex may violate the E-degree cap. Ambient isolates are
handled separately, so they do not create spurious parity hypotheses.
-/

namespace Gallai

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G H : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel H.Adj]

/-- A piece of a union at an even separator inherits the cap away from the
original exception, including vertices that are isolated in that piece. -/
theorem one_exception_cap_right (z x : V)
    (hz : Even ((G ⊔ H).degree z))
    (hmeet : ∀ w, (∃ a, G.Adj w a) → (∃ b, H.Adj w b) → w = z)
    (hcap : ∀ v, Even ((G ⊔ H).degree v) → v ≠ x → eDegree (G ⊔ H) v ≤ 3) :
    ∀ v, Even (H.degree v) → v ≠ x → eDegree H v ≤ 3 := by
  intro v hv hvx
  by_cases hp : ∃ w, H.Adj v w
  · exact (eDegree_le_one_vertex_union G H z v hmeet (Or.inl hz)).trans
      (hcap v (even_positive_in_one_vertex_union G H z v hmeet (Or.inl hz) hv hp) hvx)
  · have hn : H.neighborFinset v = ∅ := by
      ext w
      simp only [SimpleGraph.mem_neighborFinset, Finset.notMem_empty, iff_false]
      exact fun hw => hp ⟨w, hw⟩
    have hd : H.degree v = 0 := by
      rw [← H.card_neighborFinset_eq_degree, hn, Finset.card_empty]
    have he := eDegree_le_degree (G := H) v
    omega

/-- Restricting the right piece to its actual vertex set preserves the
one-exception cap, with the exceptional label interpreted in the ambient graph. -/
theorem one_exception_cap_induced_right (S : Set V) [DecidablePred (· ∈ S)]
    (z x : V) (hs : H.support ⊆ S)
    (hz : Even ((G ⊔ H).degree z))
    (hmeet : ∀ w, (∃ a, G.Adj w a) → (∃ b, H.Adj w b) → w = z)
    (hcap : ∀ v, Even ((G ⊔ H).degree v) → v ≠ x → eDegree (G ⊔ H) v ≤ 3) :
    ∀ v : S, Even ((H.induce S).degree v) → v.val ≠ x →
      eDegree (H.induce S) v ≤ 3 := by
  intro v hv hvx
  rw [eDegree_induce_of_support_subset H S hs v]
  apply one_exception_cap_right G H z x hz hmeet hcap v.val ?_ hvx
  rwa [SimpleGraph.degree_induce_of_support_subset hs v] at hv

end Gallai
