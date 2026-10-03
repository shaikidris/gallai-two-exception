/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.Structure.SETPuncture
public import Gallai.Operations.InsertEdge

@[expose] public section

/-! # Endpoint-rich decomposition of a single even triangle graph -/

namespace Gallai

open scoped Finset

universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Match the puncture parity API's local finite-neighbour decision. -/
noncomputable local instance setReservePunctureAdj (u : V) :
    DecidableRel (evenStarPuncture G u).Adj := fun _ _ => Classical.propDecidable _

/-- Botler--Sambinelli Lemma 10, SET case: any designated vertex has two endpoints. -/
theorem IsSET.endpoint_reserve (h : IsSET G) (u : V) :
    ∃ P : Decomposition G, P.size ≤ (Fintype.card V + 1) / 2 ∧
      2 ≤ P.endpointCount u := by
  classical
  let S := evenNeighbors G u
  let H := evenStarPuncture G u
  have hu : u ∉ S := by simp [S]
  have hrange : 2 ≤ #S ∧ #S ≤ 3 := by
    rcases h.eDegree_two_or_three u with hs | hs <;> change #S = _ at hs <;> omega
  have hfull : H ⊔ S.sup (SimpleGraph.edge u) = G :=
    starPuncture_restore G u S (fun v hv => ((mem_evenNeighbors u v).mp hv).1)
  obtain ⟨D, hD⟩ := h.puncture_pathBudget u
  obtain ⟨b, hb⟩ := Finset.card_pos.mp (show 0 < #S by omega)
  have hmissing (v : V) (hv : v ∈ S) : ¬ H.Adj u v :=
    starPuncture_missing G u S hu v hv
  have hpositive (v : V) (hv : H.Adj u v ∨ v ∈ S) : 0 < D.endpointCount v := by
    have ha : G.Adj u v := by
      rcases hv with hv | hv
      · exact hv.1
      · exact ((mem_evenNeighbors u v).mp hv).1
    exact D.endpointCount_pos_of_odd_degree v (evenStarPuncture_odd_neighbor G u v ha)
  obtain ⟨A, hAS, hbA, hhalf, E, hE, hvec⟩ :=
    D.prescribed_half_star_addibility u S hu hmissing hpositive b hb
  have huA : u ∉ A := fun ha => hu (hAS ha)
  have hEu : E.endpointCount u = D.endpointCount u + #A := by
    simpa [huA] using hvec u
  have hcount := Finset.card_sdiff_add_card_eq_card hAS
  have hremain : #(S \ A) ≤ 1 := by omega
  have hodd := h.odd_order
  rw [Nat.odd_iff] at hodd
  have hbudget : D.size + 1 ≤ (Fintype.card V + 1) / 2 := by omega
  by_cases hz : S \ A = ∅
  · have hSA : S ⊆ A := Finset.sdiff_eq_empty_iff_subset.mp hz
    have hEq : A = S := Finset.Subset.antisymm hAS hSA
    have hg : H ⊔ A.sup (SimpleGraph.edge u) = G := by rw [hEq]; exact hfull
    have hout : ∃ P : Decomposition (H ⊔ A.sup (SimpleGraph.edge u)),
        P.size ≤ (Fintype.card V + 1) / 2 ∧ 2 ≤ P.endpointCount u := by
      refine ⟨E, ?_, ?_⟩
      · omega
      · have hc : #A = #S := congrArg Finset.card hEq
        omega
    rwa [hg] at hout
  · have hone : #(S \ A) = 1 := by
      have hp := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hz)
      omega
    obtain ⟨v, hv⟩ := Finset.card_eq_one.mp hone
    have hvR : v ∈ S \ A := by rw [hv]; simp
    obtain ⟨hvS, hvA⟩ := Finset.mem_sdiff.mp hvR
    have huv : u ≠ v := ((mem_evenNeighbors u v).mp hvS).1.ne
    have hm : ¬ (H ⊔ A.sup (SimpleGraph.edge u)).Adj u v := by
      rintro (ha | ha)
      · exact hmissing v hvS ha
      · exact hvA ((star_sup_adj_center u A huA v).mp ha)
    have hSA : A ∪ {v} = S := by
      rw [← hv]
      exact Finset.union_sdiff_of_subset hAS
    have hg : (H ⊔ A.sup (SimpleGraph.edge u)) ⊔ SimpleGraph.edge u v = G := by
      have hs := congrArg (fun B : Finset V => B.sup (SimpleGraph.edge u)) hSA
      simp only [Finset.sup_union, Finset.sup_singleton] at hs
      rw [sup_assoc, hs]
      exact hfull
    have hout : ∃ P : Decomposition ((H ⊔ A.sup (SimpleGraph.edge u)) ⊔
        SimpleGraph.edge u v), P.size ≤ (Fintype.card V + 1) / 2 ∧
        2 ≤ P.endpointCount u := by
      refine ⟨E.insertEdge u v huv hm, ?_, ?_⟩
      · rw [Decomposition.insertEdge_size]
        omega
      · rw [Decomposition.insertEdge_endpointCount]
        simp only [ite_true, Ne.symm huv, if_false, Nat.add_zero]
        have hp : 0 < #A := Finset.card_pos.mpr ⟨b, hbA⟩
        omega
    rwa [hg] at hout

end Gallai
