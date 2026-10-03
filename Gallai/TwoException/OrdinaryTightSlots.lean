/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.OrdinaryPacketCounting

@[expose] public section

/-! # Passing-neighbour rigidity in tight ordinary packets -/
namespace Gallai.TwoException
open scoped Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {J : SimpleGraph V} [DecidableRel J.Adj]
noncomputable local instance tightHalfAdj (J : SimpleGraph V) (u : V) (A : Finset V) :
    DecidableRel (J ⊔ A.sup (SimpleGraph.edge u)).Adj :=
  fun _ _ => Classical.propDecidable _

/-- If only two slots can be passing and the count is two, both slots
must have zero endpoints. This derives the local forcing condition. -/
theorem ordinary_tight_slots_zero
    (D : Decomposition J) (a b c : V)
    (houtside : ∀ t, J.Adj a t → t ≠ b → t ≠ c → 0 < D.endpointCount t)
    (htight : passingNeighborCount D a = 2) :
    D.endpointCount b = 0 ∧ D.endpointCount c = 0 := by
  classical
  have hsingle : ∀ v w : V, (v = b ∧ w = c) ∨ (v = c ∧ w = b) →
      0 < D.endpointCount v → passingNeighborCount D a ≤ 1 := by
    intro v w hvw hp
    have hs : {t ∈ J.neighborFinset a | D.endpointCount t = 0} ⊆ {w} := by
      intro t ht
      obtain ⟨htAdj, htZero⟩ := Finset.mem_filter.mp ht
      have hat := (J.mem_neighborFinset a t).mp htAdj
      by_cases htw : t = w
      · exact Finset.mem_singleton.mpr htw
      by_cases htv : t = v
      · subst t
        omega
      rcases hvw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · have h := houtside t hat htv htw
        omega
      · have h := houtside t hat htw htv
        omega
    exact (Finset.card_le_card hs).trans (by simp)
  constructor
  · by_contra hn
    have hp : 0 < D.endpointCount b := by omega
    have h := hsingle b c (Or.inl ⟨rfl, rfl⟩) hp
    omega
  · by_contra hn
    have hp : 0 < D.endpointCount c := by omega
    have h := hsingle c b (Or.inr ⟨rfl, rfl⟩) hp
    omega

/-- A positive slot made passing by a half-star must have been selected. -/
theorem ordinary_half_star_zero_slot_selected
    (D : Decomposition J) (u b : V) (A : Finset V)
    (E : Decomposition (J ⊔ A.sup (SimpleGraph.edge u)))
    (hb : 0 < D.endpointCount b) (hz : E.endpointCount b = 0)
    (hvec : ∀ t, E.endpointCount t + (if t ∈ A then 1 else 0) =
      D.endpointCount t + if u = t then #A else 0) : b ∈ A := by
  by_contra hn
  have he := hvec b
  simp only [hn, ite_false, hz, Nat.zero_add] at he
  split_ifs at he <;> omega

/-- The actual half-star failure profile yields the T3 contribution,
without assuming the combinatorial mate-selection implication. -/
theorem ordinary_three_packet_half_star_contribution
    (D : Decomposition J) (u : V) (L A : Finset V) (hcard : #L = 3)
    (E : Decomposition (J ⊔ A.sup (SimpleGraph.edge u)))
    (hvec : ∀ t, E.endpointCount t + (if t ∈ A then 1 else 0) =
      D.endpointCount t + if u = t then #A else 0)
    (hslots : ∀ w ∈ L \ A, ∃ b c : V, L.erase w = {b, c} ∧
      0 < D.endpointCount b ∧ 0 < D.endpointCount c ∧
      (∀ t, (J ⊔ A.sup (SimpleGraph.edge u)).Adj w t →
        t ≠ b → t ≠ c → 0 < E.endpointCount t) ∧
      passingNeighborCount E w = 2) :
    #(L \ A) + 1 ≤ #(L ∩ A) := by
  apply ordinary_three_packet_contribution L A hcard
  intro w hw t ht
  obtain ⟨b, c, he, hb, hc, hout, htwo⟩ := hslots w hw
  obtain ⟨hbZero, hcZero⟩ := ordinary_tight_slots_zero E w b c hout htwo
  have hbA := ordinary_half_star_zero_slot_selected D u b A E hb hbZero hvec
  have hcA := ordinary_half_star_zero_slot_selected D u c A E hc hcZero hvec
  rw [he] at ht
  simp only [Finset.mem_insert, Finset.mem_singleton] at ht
  rcases ht with rfl | rfl
  · exact hbA
  · exact hcA

end Gallai.TwoException
