/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.Inputs.TwoTriangleRemaining
public import Gallai.Inputs.PartialTriangleRestore

@[expose] public section

/-! # Partial-left, partial-right restoration in Claim 10 -/

namespace Gallai

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Restore all five deleted edges in the partial/partial case. The hub
reserve for the last two edges is produced by the three-edge prefix. -/
theorem Decomposition.restore_two_triangle_partial_left (f : Fin 8 ↪ V)
    (hle : twoTriangleDeletion false false f ≤ G)
    (h0 : Odd (G.degree (f 0))) (h1 : Odd (G.degree (f 1)))
    (he : ∀ i : Fin 8, i ≠ 0 → i ≠ 1 → Even (G.degree (f i)))
    (hN : ∀ t : Fin 8, t = 0 ∨ t = 1 ∨ t = 6 → ∀ w,
      G.Adj (f t) w → Even (G.degree w) → ∃ i : Fin 8, f i = w)
    (hn07 : ¬ G.Adj (f 0) (f 7)) (hn17 : ¬ G.Adj (f 1) (f 7))
    (hn05 : ¬ G.Adj (f 0) (f 5)) (hn04 : ¬ G.Adj (f 0) (f 4))
    (hNa : ∀ w, G.Adj (f 2) w → Even (G.degree w) → w = f 3 ∨ w = f 4)
    (hNc : ∀ w, G.Adj (f 4) w → Even (G.degree w) → w = f 2 ∨ w = f 3)
    (D : Decomposition (G \ twoTriangleDeletion false false f)) :
    ∃ P : Decomposition G, P.size = D.size := by
  have hr := D.restore_two_triangle_prefix false f hle h0 h1 he hN hn07 hn17 hn05
  rw [twoTrianglePrefix_graph G false f hle, twoTriangleLeftDeletion_partial] at hr
  obtain ⟨E, hE, hEu⟩ := hr
  have ha : G.Adj (f 0) (f 2) := hle (SimpleGraph.map_adj_apply.mpr
    (twoTriangleTemplate_required false false).2.1)
  have hbc : G.Adj (f 3) (f 4) := hle (SimpleGraph.map_adj_apply.mpr (by decide))
  obtain ⟨P, hP⟩ := E.restore_partial_triangle (f 0) (f 2) (f 3) (f 4)
    (by simp [f.injective.eq_iff]) ha hbc
    (he 2 (by decide) (by decide)) (he 3 (by decide) (by decide))
    (he 4 (by decide) (by decide)) hNa hNc hn04 (by omega)
  exact ⟨P, hP.trans hE⟩

end Gallai
