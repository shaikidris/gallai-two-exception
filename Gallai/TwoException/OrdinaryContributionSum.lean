/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.OrdinaryHalfStarProfile
public import Mathlib.Algebra.BigOperators.Ring.Finset

@[expose] public section

/-! # Summation of ordinary packet endpoint contributions -/
namespace Gallai.TwoException
open scoped BigOperators Finset

/-- Sum the regular +1 gains and the special nonnegative gains. The bound
uses natural addition so no selected-minus-pending subtraction is truncated. -/
theorem ordinary_packet_gain_sum
    {I : Type*} [DecidableEq I] (F special : Finset I)
    (selected pending : I → ℕ)
    (hregular : ∀ i ∈ F, i ∉ special → pending i + 1 ≤ selected i)
    (hspecial : ∀ i ∈ F, i ∈ special → pending i ≤ selected i) :
    (∑ i ∈ F, pending i) + #F ≤ (∑ i ∈ F, selected i) + #special := by
  classical
  have hlocal : ∀ i ∈ F, pending i + 1 ≤
      selected i + if i ∈ special then 1 else 0 := by
    intro i hi
    by_cases hs : i ∈ special
    · have h := hspecial i hi hs
      simp only [hs, ite_true]
      omega
    · simpa only [hs, ite_false, Nat.add_zero] using hregular i hi hs
  have hsum := Finset.sum_le_sum hlocal
  have hboole : (∑ i ∈ F, if i ∈ special then (1 : ℕ) else 0) = #(F ∩ special) := by
    rw [Finset.sum_boole]
    congr 1
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hboole] at hsum
  have hc : #(F ∩ special) ≤ #special := Finset.card_le_card Finset.inter_subset_right
  simpa only [Finset.sum_const, smul_eq_mul, Nat.mul_one] using
    hsum.trans (Nat.add_le_add_left hc _)

/-- When exactly the listed packets partition the ordinary contact leaves,
the summed gains give the endgame's literal selected/pending cardinality
bound with at most one exceptional packet. -/
theorem ordinary_contact_gain_of_packet_counts
    {I V : Type*} [DecidableEq I] [DecidableEq V]
    (F special : Finset I) (S A : Finset V) (packet : I → Finset V)
    (hselected : #(S ∩ A) = ∑ i ∈ F, #(packet i ∩ A))
    (hpending : #(S \ A) = ∑ i ∈ F, #(packet i \ A))
    (hregular : ∀ i ∈ F, i ∉ special →
      #(packet i \ A) + 1 ≤ #(packet i ∩ A))
    (hspecial : ∀ i ∈ F, i ∈ special →
      #(packet i \ A) ≤ #(packet i ∩ A)) :
    #(S \ A) + #F ≤ #(S ∩ A) + #special := by
  rw [hselected, hpending]
  exact ordinary_packet_gain_sum F special
    (fun i => #(packet i ∩ A)) (fun i => #(packet i \ A)) hregular hspecial

/-- Disjoint component packets provide the exact selected/pending count
identities required by the global contribution consumer. -/
theorem ordinary_disjoint_packet_counts
    {I V : Type*} [DecidableEq I] [DecidableEq V]
    (F : Finset I) (packet : I → Finset V) (A : Finset V)
    (hdis : (F : Set I).PairwiseDisjoint packet) :
    #(F.biUnion packet ∩ A) = ∑ i ∈ F, #(packet i ∩ A) ∧
    #(F.biUnion packet \ A) = ∑ i ∈ F, #(packet i \ A) := by
  classical
  constructor
  · rw [Finset.biUnion_inter]
    apply Finset.card_biUnion
    intro i hi j hj hij
    exact (hdis hi hj hij).mono Finset.inter_subset_left Finset.inter_subset_left
  · have heq : F.biUnion packet \ A = F.biUnion (fun i => packet i \ A) := by
      ext t
      simp only [Finset.mem_sdiff, Finset.mem_biUnion]
      aesop
    rw [heq]
    apply Finset.card_biUnion
    intro i hi j hj hij
    exact (hdis hi hj hij).mono Finset.sdiff_subset Finset.sdiff_subset

end Gallai.TwoException
