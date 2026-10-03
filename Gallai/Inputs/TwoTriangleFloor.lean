/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.Inputs.TwoTriangleDeletion

@[expose] public section

/-! # Floor witnesses for both two-triangle deletion modes -/

namespace Gallai

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Original odd hubs and even leaves imply odd punctured degree at every
active deleted vertex, in all four partial/full mode combinations. -/
theorem twoTriangleDeletion_odd (leftFull rightFull : Bool) (f : Fin 8 ↪ V)
    (hle : twoTriangleDeletion leftFull rightFull f ≤ G)
    (h0 : Odd (G.degree (f 0))) (h1 : Odd (G.degree (f 1)))
    (he : ∀ i : Fin 8, i ≠ 0 → i ≠ 1 → Even (G.degree (f i)))
    (w : V) (hw : 0 < (twoTriangleDeletion leftFull rightFull f).degree w) :
    Odd ((G \ twoTriangleDeletion leftFull rightFull f).degree w) := by
  obtain ⟨i, rfl⟩ := twoTriangleDeletion_active_image leftFull rightFull f w hw
  have hd := degree_sdiff_add_of_le hle (f i)
  have hf := twoTriangleDeletion_degree leftFull rightFull f i
  rw [twoTriangleTemplate_degree] at hf
  by_cases hi0 : i = 0
  · subst i
    cases leftFull <;> simp only [if_true, Bool.false_eq_true, if_false] at hf <;>
      rw [Nat.odd_iff] at h0 ⊢ <;> omega
  by_cases hi1 : i = 1
  · subst i
    cases rightFull <;> simp only [hi0, if_false, if_true, Bool.false_eq_true] at hf <;>
      rw [Nat.odd_iff] at h1 ⊢ <;> omega
  have hi := he i hi0 hi1
  simp only [hi0, hi1, if_false] at hf
  rw [Nat.even_iff] at hi
  rw [Nat.odd_iff]
  omega

/-- Every originally odd active vertex has a deleted edge to an original
even leaf; this premise of the puncture theorem is derived from the template. -/
theorem twoTriangleDeletion_odd_neighbor (leftFull rightFull : Bool) (f : Fin 8 ↪ V)
    (he : ∀ i : Fin 8, i ≠ 0 → i ≠ 1 → Even (G.degree (f i)))
    (w : V) (ho : Odd (G.degree w))
    (hw : 0 < (twoTriangleDeletion leftFull rightFull f).degree w) :
    ∃ t, (twoTriangleDeletion leftFull rightFull f).Adj w t ∧ Even (G.degree t) := by
  obtain ⟨i, rfl⟩ := twoTriangleDeletion_active_image leftFull rightFull f w hw
  have hr := twoTriangleTemplate_required leftFull rightFull
  by_cases hi0 : i = 0
  · subst i
    exact ⟨f 2, SimpleGraph.map_adj_apply.mpr hr.2.1, he 2 (by decide) (by decide)⟩
  by_cases hi1 : i = 1
  · subst i
    exact ⟨f 5, SimpleGraph.map_adj_apply.mpr hr.2.2, he 5 (by decide) (by decide)⟩
  exact (Nat.not_even_iff_odd.mpr ho (he i hi0 hi1)).elim

/-- The actual two-triangle deletion has a floor witness under strict
minimality. Neither punctured parity nor an initial decomposition is assumed. -/
theorem two_triangle_deletion_floor (leftFull rightFull : Bool) (f : Fin 8 ↪ V)
    (hle : twoTriangleDeletion leftFull rightFull f ≤ G)
    (h0 : Odd (G.degree (f 0))) (h1 : Odd (G.degree (f 1)))
    (he : ∀ i : Fin 8, i ≠ 0 → i ≠ 1 → Even (G.degree (f i)))
    (hconn : G.Connected) (hcap : ∀ w, Even (G.degree w) → eDegree G w ≤ 3)
    (hnot : ¬ HasPathBudget G (Fintype.card V / 2)) (hset : ¬ IsSET G)
    (hmin : ∀ (U : Set V) [DecidablePred (· ∈ U)]
      (J : SimpleGraph U) [DecidableRel J.Adj],
      J.edgeFinset.card < G.edgeFinset.card → J.Connected →
      (∀ w, Even (J.degree w) → eDegree J w ≤ 3) →
      HasPathBudget J (Fintype.card U / 2) ∨ IsSET J) :
    HasPathBudget (G \ twoTriangleDeletion leftFull rightFull f) (Fintype.card V / 2) := by
  have hactive : ∃ a b, (twoTriangleDeletion leftFull rightFull f).Adj a b :=
    ⟨f 0, f 1, SimpleGraph.map_adj_apply.mpr (twoTriangleTemplate_required leftFull rightFull).1⟩
  exact active_odd_puncture_floor hle hactive
    (twoTriangleDeletion_odd leftFull rightFull f hle h0 h1 he)
    (fun w ho hw => twoTriangleDeletion_odd_neighbor leftFull rightFull f he w ho hw)
    hconn hcap hnot hset hmin

end Gallai
