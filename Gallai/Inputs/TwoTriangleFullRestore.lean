/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.Inputs.TwoTriangleRemaining
public import Gallai.Inputs.ThreeSpokeRestore

@[expose] public section

/-! # Full-left, partial-right restoration in Claim 10 -/

namespace Gallai

open scoped Finset

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The concrete prefix supplies the reserve for full-left-star restoration;
no reserve or favourable intermediate decomposition is assumed. -/
theorem Decomposition.restore_two_triangle_full_left (f : Fin 8 ↪ V)
    (hle : twoTriangleDeletion true false f ≤ G)
    (h0 : Odd (G.degree (f 0))) (h1 : Odd (G.degree (f 1)))
    (he : ∀ i : Fin 8, i ≠ 0 → i ≠ 1 → Even (G.degree (f i)))
    (hN : ∀ t : Fin 8, t = 0 ∨ t = 1 ∨ t = 6 → ∀ w,
      G.Adj (f t) w → Even (G.degree w) → ∃ i : Fin 8, f i = w)
    (hn07 : ¬ G.Adj (f 0) (f 7)) (hn17 : ¬ G.Adj (f 1) (f 7))
    (hn05 : ¬ G.Adj (f 0) (f 5))
    (hS : evenNeighbors G (f 0) = {f 2, f 3, f 4})
    (hcap : ∀ v ∈ evenNeighbors G (f 0), eDegree G v ≤ 2)
    (D : Decomposition (G \ twoTriangleDeletion true false f)) :
    ∃ P : Decomposition G, P.size = D.size ∧ 2 ≤ P.endpointCount (f 0) := by
  classical
  have hr := D.restore_two_triangle_prefix true f hle h0 h1 he hN hn07 hn17 hn05
  rw [twoTrianglePrefix_graph G true f hle, twoTriangleLeftDeletion_full, ← hS] at hr
  obtain ⟨E, hE, hEu⟩ := hr
  have hthree : eDegree G (f 0) = 3 := by
    change #(evenNeighbors G (f 0)) = 3
    rw [hS]
    simp [f.injective.eq_iff]
  obtain ⟨P, hP, hPu⟩ := E.restore_three_even_spokes_of_leaf_cap_two
    (f 0) hthree hcap (by omega)
  exact ⟨P, hP.trans hE, hPu⟩

end Gallai
