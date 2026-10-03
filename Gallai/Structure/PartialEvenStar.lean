/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.Structure.OneExceptionStarPuncture

@[expose] public section

/-! # Parity and cap supply for a retained-spoke puncture -/

namespace Gallai

open scoped Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Fix adjacency decisions for parity counts in a partial star puncture. -/
noncomputable local instance partialEvenAdj (u : V) (S : Finset V) :
    DecidableRel (starPuncture G u S).Adj := fun _ _ => Classical.propDecidable _

/-- A selected even leaf becomes odd after its spoke is removed. -/
theorem partialEvenStar_odd_leaf (u : V) (S : Finset V)
    (hS : S ⊆ evenNeighbors G u) (v : V) (hv : v ∈ S) :
    Odd ((starPuncture G u S).degree v) := by
  obtain ⟨ha, he⟩ := (mem_evenNeighbors u v).mp (hS hv)
  have hd := starPuncture_degree_leaf G u S v hv ha
  rw [Nat.even_iff] at he
  rw [Nat.odd_iff]
  omega

/-- An odd number of removed spokes makes the even centre odd. -/
theorem partialEvenStar_odd_center (u : V) (S : Finset V)
    (hS : S ⊆ evenNeighbors G u) (hu : Even (G.degree u)) (ho : Odd #S) :
    Odd ((starPuncture G u S).degree u) := by
  have hnot : u ∉ S := fun h => (show u ∉ evenNeighbors G u by simp) (hS h)
  have hd := starPuncture_degree_center G u S hnot
    (hS.trans (Finset.filter_subset _ _))
  rw [Nat.even_iff] at hu
  rw [Nat.odd_iff] at ho ⊢
  omega

/-- The partial odd-star puncture removes the designated exception without
introducing any new even vertices, so every surviving even cap is at most three. -/
theorem partialEvenStar_cap (u : V) (S : Finset V)
    (hS : S ⊆ evenNeighbors G u) (hu : Even (G.degree u)) (ho : Odd #S)
    (hcap : ∀ v, Even (G.degree v) → v ≠ u → eDegree G v ≤ 3) :
    ∀ v, Even ((starPuncture G u S).degree v) → eDegree (starPuncture G u S) v ≤ 3 := by
  have hkeep (v : V) (hv : Even ((starPuncture G u S).degree v)) :
      v ≠ u ∧ Even (G.degree v) := by
    have hvu : v ≠ u := by
      intro h
      subst v
      exact Nat.not_even_iff_odd.mpr (partialEvenStar_odd_center G u S hS hu ho) hv
    have hvS : v ∉ S := fun h =>
      Nat.not_even_iff_odd.mpr (partialEvenStar_odd_leaf G u S hS v h) hv
    refine ⟨hvu, ?_⟩
    rwa [starPuncture_degree_other G u S v hvu hvS] at hv
  intro v hv
  obtain ⟨hvu, hev⟩ := hkeep v hv
  apply (Finset.card_le_card (s := evenNeighbors (starPuncture G u S) v)
    (t := evenNeighbors G v) ?_).trans (hcap v hev hvu)
  intro w hw
  obtain ⟨ha, he⟩ := (mem_evenNeighbors v w).mp hw
  exact (mem_evenNeighbors v w).mpr ⟨ha.1, (hkeep w he).2⟩

/-- The partial odd-star puncture preserves the subcubic E-degree cap away
from one retained exceptional vertex. The centre and selected leaves become
odd; the retained vertex `x` is the only vertex omitted from the cap. -/
theorem partialEvenStar_cap_two_exceptions (u x : V) (S : Finset V)
    (hS : S ⊆ evenNeighbors G u) (hu : Even (G.degree u)) (ho : Odd #S)
    (hcap : ∀ v, Even (G.degree v) → v ≠ u → v ≠ x → eDegree G v ≤ 3) :
    ∀ v, Even ((starPuncture G u S).degree v) → v ≠ x →
      eDegree (starPuncture G u S) v ≤ 3 := by
  have hkeep (v : V) (hv : Even ((starPuncture G u S).degree v)) :
      v ≠ u ∧ Even (G.degree v) := by
    have hvu : v ≠ u := by
      intro h
      subst v
      exact Nat.not_even_iff_odd.mpr (partialEvenStar_odd_center G u S hS hu ho) hv
    have hvS : v ∉ S := fun h =>
      Nat.not_even_iff_odd.mpr (partialEvenStar_odd_leaf G u S hS v h) hv
    refine ⟨hvu, ?_⟩
    rwa [starPuncture_degree_other G u S v hvu hvS] at hv
  intro v hv hvx
  obtain ⟨hvu, hev⟩ := hkeep v hv
  apply (Finset.card_le_card (s := evenNeighbors (starPuncture G u S) v)
    (t := evenNeighbors G v) ?_).trans (hcap v hev hvu hvx)
  intro w hw
  obtain ⟨ha, he⟩ := (mem_evenNeighbors v w).mp hw
  exact (mem_evenNeighbors v w).mpr ⟨ha.1, (hkeep w he).2⟩

/-- When only y's even-neighbour spoke is retained, every other original
neighbour is odd in the puncture. The retained y needs separate endpoint supply. -/
theorem retainedEvenStar_odd_neighbor (u y v : V) (ha : G.Adj u v) (hvy : v ≠ y) :
    Odd ((starPuncture G u ((evenNeighbors G u).erase y)).degree v) := by
  by_cases he : Even (G.degree v)
  · exact partialEvenStar_odd_leaf G u _ (Finset.erase_subset _ _) v
      (Finset.mem_erase.mpr ⟨hvy, (mem_evenNeighbors u v).mpr ⟨ha, he⟩⟩)
  · have hn : v ∉ (evenNeighbors G u).erase y := by
      intro h
      exact he ((mem_evenNeighbors u v).mp (Finset.mem_of_mem_erase h)).2
    rw [starPuncture_degree_other G u _ v ha.ne.symm hn]
    exact Nat.not_even_iff_odd.mp he

end Gallai
