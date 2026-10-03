/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.Foundations.PathNumber
public import Gallai.Foundations.EndpointBounds
public import Gallai.Structure.InductionMeasure

@[expose] public section

/-! # Matching base and normalized endpoint budget for the Lovasz induction -/

namespace Gallai

open scoped BigOperators

universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Maximum degree one forces the exact normalized endpoint vector. -/
theorem Decomposition.endpointCount_eq_mod_two_of_degree_le_one
    (D : Decomposition G) (hdeg : ∀ v, G.degree v ≤ 1) (v : V) :
    D.endpointCount v = G.degree v % 2 := by
  have hb := D.endpointCount_le_degree v
  have hp := D.endpointCount_mod_two v
  have hd := hdeg v
  omega

/-- Zero excess admits an actual decomposition with no surplus endpoints. -/
theorem exists_normalized_of_degreeExcess_zero (hz : degreeExcess G = 0) :
    ∃ D : Decomposition G, ∀ v, D.endpointCount v = G.degree v % 2 := by
  obtain ⟨k, D, _⟩ := exists_pathBudget G
  exact ⟨D, D.endpointCount_eq_mod_two_of_degree_le_one
    ((degreeExcess_eq_zero_iff G).mp hz)⟩

/-- An exact parity endpoint vector supplies the floor path budget. -/
theorem Decomposition.size_le_half_of_normalized (D : Decomposition G)
    (hn : ∀ v, D.endpointCount v = G.degree v % 2) :
    D.size ≤ Fintype.card V / 2 := by
  have hs : ∑ v, D.endpointCount v ≤ Fintype.card V := by
    calc
      ∑ v, D.endpointCount v ≤ ∑ _v : V, 1 := by
        apply Finset.sum_le_sum
        intro v _
        rw [hn v]
        omega
      _ = Fintype.card V := by simp
  rw [D.sum_endpointCount] at hs
  omega

/-- The zero-measure induction base includes its path-count conclusion. -/
theorem exists_normalized_budget_of_degreeExcess_zero (hz : degreeExcess G = 0) :
    ∃ D : Decomposition G, D.size ≤ Fintype.card V / 2 ∧
      ∀ v, D.endpointCount v = G.degree v % 2 := by
  obtain ⟨D, hn⟩ := exists_normalized_of_degreeExcess_zero hz
  exact ⟨D, D.size_le_half_of_normalized hn, hn⟩

end Gallai
