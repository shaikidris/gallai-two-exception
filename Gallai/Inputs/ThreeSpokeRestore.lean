/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.Structure.SETPuncture

@[expose] public section

/-! # Free restoration of three even-neighbour spokes -/

namespace Gallai

open scoped Finset

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Match the parity API's local decision instance for the even-star puncture. -/
noncomputable local instance punctureAdj (u : V) :
    DecidableRel (evenStarPuncture G u).Adj := fun _ _ => Classical.propDecidable _

/-- A positive hub reserve restores three even-neighbour spokes when every
leaf has at most two other even neighbours. No hub parity is assumed. -/
theorem Decomposition.restore_three_even_spokes_with_reserve (u : V)
    (hthree : eDegree G u = 3)
    (hcap : ∀ v ∈ evenNeighbors G u, #((evenNeighbors G v).erase u) ≤ 2)
    (D : Decomposition (evenStarPuncture G u))
    (hDu : 0 < D.endpointCount u) :
    ∃ P : Decomposition G, P.size = D.size ∧ 2 ≤ P.endpointCount u := by
  classical
  let S := evenNeighbors G u
  let H := evenStarPuncture G u
  have hu : u ∉ S := by simp [S]
  have hS : #S = 3 := hthree
  have hfull : H ⊔ S.sup (SimpleGraph.edge u) = G :=
    starPuncture_restore G u S (fun v hv => ((mem_evenNeighbors u v).mp hv).1)
  have hmissing (v : V) (hv : v ∈ S) : ¬ H.Adj u v :=
    starPuncture_missing G u S hu v hv
  have hpositive (v : V) (hv : H.Adj u v ∨ v ∈ S) : 0 < D.endpointCount v := by
    apply D.endpointCount_pos_of_odd_degree
    apply evenStarPuncture_odd_neighbor G u v
    rcases hv with hv | hv
    · exact hv.1
    · exact ((mem_evenNeighbors u v).mp hv).1
  obtain ⟨b, hb⟩ := Finset.card_pos.mp (show 0 < #S by omega)
  obtain ⟨A, hAS, _, hhalf, E, hE, hvec⟩ :=
    D.prescribed_half_star_addibility u S hu hmissing hpositive b hb
  have huA : u ∉ A := fun ha => hu (hAS ha)
  have hEu : E.endpointCount u = D.endpointCount u + #A := by
    simpa [huA] using hvec u
  have hcount := Finset.card_sdiff_add_card_eq_card hAS
  have hremain : #(S \ A) ≤ 1 := by omega
  by_cases hz : S \ A = ∅
  · have hEq : A = S := Finset.Subset.antisymm hAS (Finset.sdiff_eq_empty_iff_subset.mp hz)
    have hg : H ⊔ A.sup (SimpleGraph.edge u) = G := by rw [hEq]; exact hfull
    have hout : ∃ P : Decomposition (H ⊔ A.sup (SimpleGraph.edge u)),
        P.size = D.size ∧ 2 ≤ P.endpointCount u := ⟨E, hE, by omega⟩
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
    have hle : H ⊔ A.sup (SimpleGraph.edge u) ≤ G := by
      rw [← hg]
      exact le_sup_left
    have hpass : #{w ∈ (H ⊔ A.sup (SimpleGraph.edge u)).neighborFinset v |
        E.endpointCount w = 0} ≤ 2 := by
      have hs : {w ∈ (H ⊔ A.sup (SimpleGraph.edge u)).neighborFinset v |
          E.endpointCount w = 0} ⊆ (evenNeighbors G v).erase u := by
        intro w hw
        obtain ⟨hwa, hwz⟩ := Finset.mem_filter.mp hw
        have hwa := ((H ⊔ A.sup (SimpleGraph.edge u)).mem_neighborFinset v w).mp hwa
        have hwu : w ≠ u := by intro he; subst w; omega
        refine Finset.mem_erase.mpr ⟨hwu, (mem_evenNeighbors v w).mpr ⟨hle hwa, ?_⟩⟩
        by_cases hwS : w ∈ S
        · exact ((mem_evenNeighbors u w).mp hwS).2
        · have hwA : w ∉ A := fun h => hwS (hAS h)
          have he := hvec w
          simp only [hwA, hwu.symm, if_false, Nat.add_zero, hwz] at he
          have hp := D.endpointCount_mod_two w
          have hd := starPuncture_degree_other G u S w hwu hwS
          rw [Nat.even_iff]
          change H.degree w = G.degree w at hd
          simp only [SimpleGraph.degree, SimpleGraph.neighborFinset,
            ← Set.ncard_eq_toFinset_card', H] at hp hd ⊢
          omega
      exact (Finset.card_le_card hs).trans (hcap v hvS)
    obtain ⟨P, hP, he⟩ := E.single_edge_addibility (G := H ⊔ A.sup (SimpleGraph.edge u))
      v u huv.symm (fun h => hm h.symm)
      (by omega)
    have hg' : (H ⊔ A.sup (SimpleGraph.edge u)) ⊔ SimpleGraph.edge v u = G := by
      rw [SimpleGraph.edge_comm v u]
      exact hg
    have hPu : 2 ≤ P.endpointCount u := by
      have heU := he u
      simp only [huv.symm, if_false, if_true, Nat.add_zero] at heU
      omega
    have hout : ∃ P : Decomposition ((H ⊔ A.sup (SimpleGraph.edge u)) ⊔
        SimpleGraph.edge v u), P.size = D.size ∧ 2 ≤ P.endpointCount u :=
      ⟨P, hP.trans hE, hPu⟩
    rwa [hg'] at hout

/-- Restore three even-neighbour spokes at an even hub, deriving its initial
positive reserve from parity rather than supplying it as a premise. -/
theorem Decomposition.restore_three_even_spokes_exposing (u : V)
    (huEven : Even (G.degree u))
    (hthree : eDegree G u = 3)
    (hcap : ∀ v ∈ evenNeighbors G u, eDegree G v ≤ 3)
    (D : Decomposition (evenStarPuncture G u)) :
    ∃ P : Decomposition G, P.size = D.size ∧ 2 ≤ P.endpointCount u := by
  classical
  have hDu : 0 < D.endpointCount u := by
    apply D.endpointCount_pos_of_odd_degree
    have hd := evenStarPuncture_degree_center G u
    rw [Nat.even_iff] at huEven
    rw [Nat.odd_iff]
    omega
  apply D.restore_three_even_spokes_with_reserve u hthree ?_ hDu
  intro v hv
  have hmem : u ∈ evenNeighbors G v :=
    (mem_evenNeighbors v u).mpr ⟨((mem_evenNeighbors u v).mp hv).1.symm, huEven⟩
  have hn := Finset.card_erase_add_one hmem
  have hb := hcap v hv
  change #(evenNeighbors G v) ≤ 3 at hb
  omega

/-- The leaf E-degree-two form used after Claim 10 constructs a positive
reserve at its odd hub. The supplied decomposition itself is transported. -/
theorem Decomposition.restore_three_even_spokes_of_leaf_cap_two (u : V)
    (hthree : eDegree G u = 3)
    (hcap : ∀ v ∈ evenNeighbors G u, eDegree G v ≤ 2)
    (D : Decomposition (evenStarPuncture G u))
    (hDu : 0 < D.endpointCount u) :
    ∃ P : Decomposition G, P.size = D.size ∧ 2 ≤ P.endpointCount u := by
  apply D.restore_three_even_spokes_with_reserve u hthree ?_ hDu
  intro v hv
  exact (Finset.card_le_card (Finset.erase_subset u (evenNeighbors G v))).trans (hcap v hv)

/-- Any decomposition of the three-spoke puncture at an even hub restores
within the same budget when its even neighbours have E-degree at most three. -/
theorem Decomposition.restore_three_even_spokes (u : V) (huEven : Even (G.degree u))
    (hthree : eDegree G u = 3)
    (hcap : ∀ v ∈ evenNeighbors G u, eDegree G v ≤ 3)
    (D : Decomposition (evenStarPuncture G u)) :
    ∃ P : Decomposition G, P.size = D.size := by
  obtain ⟨P, hP, _⟩ := D.restore_three_even_spokes_exposing u huEven hthree hcap
  exact ⟨P, hP⟩

end Gallai
