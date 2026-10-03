/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.Operations.DecompositionSplit
public import Gallai.Foundations.EndpointBounds

@[expose] public section

/-!
# Exposing positive even vertices by necessary splits

A positive-degree vertex with no endpoint occurrence lies internally on an
actual carrier. Splitting that carrier costs exactly one path and preserves
all other endpoint counts. Two repairs may act on the same original carrier.
-/

namespace Gallai.Decomposition

universe u

variable {V : Type u} {G : SimpleGraph V} [DecidableEq V]

/-- Zero total endpoint multiplicity rules out either endpoint on every carrier. -/
theorem endpoints_ne_of_count_zero (D : Decomposition G) (v : V)
    (hz : D.endpointCount v = 0) (i : Fin D.size) :
    (D.path i).start ≠ v ∧ (D.path i).finish ≠ v := by
  have hi : (if (D.path i).start = v then 1 else 0) +
      (if (D.path i).finish = v then 1 else 0 : ℕ) = 0 :=
    (Finset.sum_eq_zero_iff.mp hz) i (Finset.mem_univ i)
  constructor
  · intro hs
    simp [hs] at hi
  · intro ht
    simp [ht] at hi

variable [Fintype V] [DecidableRel G.Adj]

/-- Positive degree and zero endpoint count supply a carrier passing internally through the vertex. -/
theorem exists_internal_of_count_zero (D : Decomposition G) (v : V)
    (hp : 0 < G.degree v) (hz : D.endpointCount v = 0) :
    ∃ i : Fin D.size, v ∈ (D.path i).walk.support ∧
      (D.path i).start ≠ v ∧ v ≠ (D.path i).finish := by
  obtain ⟨w, hw⟩ := (G.degree_pos_iff_exists_adj v).mp hp
  obtain ⟨i, hi, _⟩ := D.covers s(v, w) hw
  have hends := D.endpoints_ne_of_count_zero v hz i
  exact ⟨i, (D.path i).walk.fst_mem_support_of_mem_edges hi, hends.1, hends.2.symm⟩

/-- Expose a positive even vertex, paying one path exactly when its endpoint count was zero. -/
theorem exists_expose_even (D : Decomposition G) (v : V)
    (hp : 0 < G.degree v) (he : Even (G.degree v)) :
    ∃ E : Decomposition G,
      E.size = D.size + (if D.endpointCount v = 0 then 1 else 0) ∧
      2 ≤ E.endpointCount v ∧
      ∀ w, w ≠ v → E.endpointCount w = D.endpointCount w := by
  by_cases hz : D.endpointCount v = 0
  · obtain ⟨i, hi, hs, ht⟩ := D.exists_internal_of_count_zero v hp hz
    refine ⟨D.splitAt i v hi hs ht, ?_, ?_, ?_⟩
    · simp [hz]
    · rw [splitAt_endpointCount]
      simp [hz]
    · intro w hw
      rw [splitAt_endpointCount]
      simp [hw.symm]
  · refine ⟨D, by simp [hz], ?_, fun _ _ => rfl⟩
    exact D.two_le_endpointCount_of_even_degree v he (Nat.pos_of_ne_zero hz)

/-- Repair both even vertices with precisely the number of initially missing exposures. -/
theorem exists_expose_two_even (D : Decomposition G) (x y : V) (hxy : x ≠ y)
    (hxp : 0 < G.degree x) (hxe : Even (G.degree x))
    (hyp : 0 < G.degree y) (hye : Even (G.degree y)) :
    ∃ E : Decomposition G,
      E.size = D.size + (if D.endpointCount x = 0 then 1 else 0) +
        (if D.endpointCount y = 0 then 1 else 0) ∧
      2 ≤ E.endpointCount x ∧ 2 ≤ E.endpointCount y ∧
      ∀ w, w ≠ x → w ≠ y → E.endpointCount w = D.endpointCount w := by
  obtain ⟨D₁, hsize₁, hx, hother₁⟩ := D.exists_expose_even x hxp hxe
  obtain ⟨D₂, hsize₂, hy, hother₂⟩ := D₁.exists_expose_even y hyp hye
  refine ⟨D₂, ?_, ?_, hy, ?_⟩
  · rw [hsize₂, hother₁ y hxy.symm, hsize₁]
  · rw [hother₂ x hxy]
    exact hx
  · intro w hwx hwy
    rw [hother₂ w hwy, hother₁ w hwx]

end Gallai.Decomposition
