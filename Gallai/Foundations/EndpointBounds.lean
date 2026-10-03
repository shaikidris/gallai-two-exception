/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.Foundations.Parity
public import Gallai.Structure.EvenSubgraph
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

@[expose] public section

/-!
# Endpoint supply and degree-four profiles

These are consequences of the edge-partition parity theorem, not additional
assumptions on a decomposition. Positive even degree does not by itself force
positive endpoint multiplicity.
-/

namespace Gallai

universe u

variable {V : Type u} {G : SimpleGraph V} [DecidableEq V]

/-- Each endpoint of a nonempty path requires an incident edge. -/
theorem NonemptyPath.endpointIndicator_le_incident (P : NonemptyPath G) (v : V) :
    (if P.start = v then 1 else 0) + (if P.finish = v then 1 else 0) ≤
      P.walk.edges.countP (fun e => v ∈ e) := by
  have hparity := P.incident_mod_two v
  have hdistinct := P.start_ne_finish G
  by_cases hs : P.start = v
  · have ht : P.finish ≠ v := fun h => hdistinct (hs.trans h.symm)
    simp only [if_pos hs, if_neg ht] at hparity ⊢
    omega
  · by_cases ht : P.finish = v
    · simp only [if_neg hs, if_pos ht] at hparity ⊢
      omega
    · simp only [if_neg hs, if_neg ht]
      omega

variable [Fintype V] [DecidableRel G.Adj]

/-- Endpoint multiplicity cannot exceed ordinary graph degree. -/
theorem Decomposition.endpointCount_le_degree (D : Decomposition G) (v : V) :
    D.endpointCount v ≤ G.degree v := by
  rw [D.degree_eq_sum_incident v]
  exact Finset.sum_le_sum (fun i _ => (D.path i).endpointIndicator_le_incident v)

/-- An odd-degree vertex is an endpoint of at least one decomposition path. -/
theorem Decomposition.endpointCount_pos_of_odd_degree (D : Decomposition G) (v : V)
    (hodd : Odd (G.degree v)) : 0 < D.endpointCount v := by
  have hparity := D.endpointCount_mod_two v
  rw [Nat.odd_iff] at hodd
  omega

/-- If an E-degree-zero vertex is adjacent to `v`, then `v` is odd and hence
is an endpoint of every path decomposition.  This turns an auxiliary
E-degree-zero certificate into the positivity premise of a strict edge
addition without choosing any path carrier. -/
theorem Decomposition.endpointCount_pos_of_neighbor_of_eDegree_zero
    (D : Decomposition G) (u v : V) (huv : G.Adj u v)
    (hzero : eDegree G u = 0) :
    0 < D.endpointCount v := by
  apply D.endpointCount_pos_of_odd_degree v
  apply Nat.not_even_iff_odd.mp
  intro hveven
  have hv : v ∈ evenNeighbors G u := (mem_evenNeighbors u v).mpr ⟨huv, hveven⟩
  have hpos : 0 < eDegree G u := by
    rw [eDegree]
    exact Finset.card_pos.mpr ⟨v, hv⟩
  omega

/-- Positive exposure at an even-degree vertex supplies at least two endpoints. -/
theorem Decomposition.two_le_endpointCount_of_even_degree (D : Decomposition G) (v : V)
    (heven : Even (G.degree v)) (hpos : 0 < D.endpointCount v) :
    2 ≤ D.endpointCount v := by
  have hparity := D.endpointCount_mod_two v
  rw [Nat.even_iff] at heven
  omega

/-- Exposure at least two at an odd-degree vertex actually supplies three endpoints. -/
theorem Decomposition.three_le_endpointCount_of_odd_degree (D : Decomposition G) (v : V)
    (hodd : Odd (G.degree v)) (htwo : 2 ≤ D.endpointCount v) :
    3 ≤ D.endpointCount v := by
  have hparity := D.endpointCount_mod_two v
  rw [Nat.odd_iff] at hodd
  omega

/-- An isolated vertex has no endpoint occurrences. -/
theorem Decomposition.endpointCount_eq_zero_of_degree_zero (D : Decomposition G) (v : V)
    (hdegree : G.degree v = 0) : D.endpointCount v = 0 := by
  have hbound := D.endpointCount_le_degree v
  omega

/-- The three endpoint profiles needed when releasing a degree-four star. -/
theorem Decomposition.degree_four_endpoint_profiles (D : Decomposition G) (v : V)
    (hdegree : G.degree v = 4) :
    D.endpointCount v = 0 ∨ D.endpointCount v = 2 ∨ D.endpointCount v = 4 := by
  have hparity := D.endpointCount_mod_two v
  have hbound := D.endpointCount_le_degree v
  omega

end Gallai
