/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.Inputs.TwoTriangleRemaining
public import Gallai.Inputs.TwoFullStarRestore

@[expose] public section

/-! # Full/full two-triangle reconstruction -/

namespace Gallai

open scoped Finset

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The nested star punctures are exactly the seven-edge template deletion. -/
theorem twoTriangleFullFull_puncture (f : Fin 8 ↪ V)
    (hS : evenNeighbors G (f 0) = {f 2, f 3, f 4})
    (hT : evenNeighbors G (f 1) = {f 5, f 6, f 7}) :
    starPuncture (starPuncture (evenStarPuncture G (f 1)) (f 0) {f 1})
      (f 0) (evenNeighbors G (f 0)) = G \ twoTriangleDeletion true true f := by
  unfold evenStarPuncture starPuncture
  rw [hS, hT, twoTriangleDeletion_full_split]
  ext u v
  simp only [SimpleGraph.sdiff_adj, SimpleGraph.sup_adj, Finset.sup_singleton]
  tauto

/-- Full/full reconstruction consumes the actual seven-edge puncture witness
without assuming any endpoint reserve or carrier compatibility. -/
theorem Decomposition.restore_two_triangle_full_full (f : Fin 8 ↪ V)
    (hu : Odd (G.degree (f 0))) (hv : Odd (G.degree (f 1)))
    (huv : G.Adj (f 0) (f 1))
    (hS : evenNeighbors G (f 0) = {f 2, f 3, f 4})
    (hT : evenNeighbors G (f 1) = {f 5, f 6, f 7})
    (hcapU : ∀ w ∈ evenNeighbors G (f 0), eDegree G w ≤ 2)
    (hcapV : ∀ w ∈ evenNeighbors G (f 1), eDegree G w ≤ 2)
    (D : Decomposition (G \ twoTriangleDeletion true true f)) :
    ∃ P : Decomposition G, P.size = D.size ∧ 2 ≤ P.endpointCount (f 1) := by
  classical
  have hs : eDegree G (f 0) = 3 := by
    change #(evenNeighbors G (f 0)) = 3
    rw [hS]
    simp [f.injective.eq_iff]
  have ht : eDegree G (f 1) = 3 := by
    change #(evenNeighbors G (f 1)) = 3
    rw [hT]
    simp [f.injective.eq_iff]
  have hd : Disjoint (evenNeighbors G (f 0)) (evenNeighbors G (f 1)) := by
    rw [hS, hT]
    simp [Finset.disjoint_left, f.injective.eq_iff]
  have hall : ∀ D' : Decomposition (G \ twoTriangleDeletion true true f),
      ∃ P : Decomposition G, P.size = D'.size ∧ 2 ≤ P.endpointCount (f 1) := by
    rw [← twoTriangleFullFull_puncture f hS hT]
    intro D'
    exact D'.restore_two_full_stars (f 0) (f 1) hu hv huv hs ht hd hcapU hcapV
  exact hall D

end Gallai
