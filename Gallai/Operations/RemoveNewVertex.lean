/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.Operations.DecompositionInduce

@[expose] public section

/-! # Return from an injective image with one isolated new vertex -/

namespace Gallai

universe u
variable {V : Type u}

/-- The complement of the new sum vertex is exactly the original vertex type. -/
noncomputable def retainedInlEquiv : V ≃ {w : V ⊕ Unit // w ≠ .inr ()} :=
  Equiv.ofBijective (fun v => ⟨.inl v, by simp⟩) (by
    constructor
    · intro a b h
      exact Sum.inl.inj (congrArg Subtype.val h)
    · rintro ⟨w, hw⟩
      cases w with
      | inl v => exact ⟨v, rfl⟩
      | inr v => cases v; exact (hw rfl).elim)

/-- Restricting the graph image and mapping back gives the original graph. -/
theorem map_retainedInl_inverse (G : SimpleGraph V) :
    ((G.map (Function.Embedding.inl : V ↪ V ⊕ Unit)).induce
      {w | w ≠ (Sum.inr () : V ⊕ Unit)}).map
      (retainedInlEquiv (V := V)).symm.toEmbedding = G := by
  ext a b
  rw [SimpleGraph.map_adj]
  constructor
  · rintro ⟨u, v, h, ha, hb⟩
    have hu : u = retainedInlEquiv a :=
      retainedInlEquiv.symm.injective (ha.trans (retainedInlEquiv.symm_apply_apply a).symm)
    have hv : v = retainedInlEquiv b :=
      retainedInlEquiv.symm.injective (hb.trans (retainedInlEquiv.symm_apply_apply b).symm)
    subst u
    subst v
    change (G.map (Function.Embedding.inl : V ↪ V ⊕ Unit)).Adj (.inl a) (.inl b) at h
    simpa using h
  · intro h
    refine ⟨retainedInlEquiv a, retainedInlEquiv b, ?_, ?_, ?_⟩
    · change (G.map (Function.Embedding.inl : V ↪ V ⊕ Unit)).Adj (.inl a) (.inl b)
      simpa using h
    · exact retainedInlEquiv.symm_apply_apply a
    · exact retainedInlEquiv.symm_apply_apply b

/-- Every decomposition of the graph image returns to G with unchanged size
and old endpoint multiplicities, including when V is empty. -/
theorem Decomposition.remove_new_vertex [DecidableEq V] (G : SimpleGraph V)
    (D : Decomposition (G.map (Function.Embedding.inl : V ↪ V ⊕ Unit))) :
    ∃ E : Decomposition G, E.size = D.size ∧
      ∀ v, E.endpointCount v = D.endpointCount (.inl v) := by
  classical
  obtain ⟨R, hs, hv⟩ := D.remove_isolated (.inr ()) (by
    intro v
    simp [SimpleGraph.map_adj])
  have hresult : ∃ E : Decomposition
      (((G.map (Function.Embedding.inl : V ↪ V ⊕ Unit)).induce
        {w | w ≠ (Sum.inr () : V ⊕ Unit)}).map
        (retainedInlEquiv (V := V)).symm.toEmbedding),
      E.size = D.size ∧ ∀ v, E.endpointCount v = D.endpointCount (.inl v) := by
    refine ⟨R.map retainedInlEquiv.symm.toEmbedding, hs, ?_⟩
    intro v
    have h := R.map_endpointCount retainedInlEquiv.symm.toEmbedding (retainedInlEquiv v)
    have hv' : R.endpointCount (retainedInlEquiv v) = D.endpointCount (.inl v) :=
      hv (retainedInlEquiv v)
    simpa using h.trans hv'
  rw [map_retainedInl_inverse] at hresult
  exact hresult

end Gallai
