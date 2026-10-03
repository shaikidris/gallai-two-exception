/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.Inputs.ThreeSpokeRestore
public import Gallai.Inputs.OutwardStar

@[expose] public section

/-! # Free restoration of an odd number of even-neighbour spokes

The odd half-star rounding supplies the extra endpoint needed to restore all
remaining spokes outward, leaving two endpoints at the designated hub.
-/

namespace Gallai

open scoped Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Use one fixed adjacency decision throughout odd-star reconstruction. -/
noncomputable local instance oddStarRestoreAdj (u : V) :
    DecidableRel (evenStarPuncture G u).Adj := fun _ _ => Classical.propDecidable _

/-- Any odd-size even-neighbour star restores freely from a positive hub
reserve if each leaf has at most two other even neighbours. -/
theorem Decomposition.restore_odd_even_star_with_reserve_preserving (u : V)
    (hodd : Odd (eDegree G u))
    (hcap : ∀ v ∈ evenNeighbors G u, #((evenNeighbors G v).erase u) ≤ 2)
    (D : Decomposition (evenStarPuncture G u)) (hDu : 0 < D.endpointCount u) :
    ∃ P : Decomposition G, P.size = D.size ∧ 2 ≤ P.endpointCount u ∧
      ∀ w, w ≠ u → w ∉ evenNeighbors G u → P.endpointCount w = D.endpointCount w := by
  classical
  let S := evenNeighbors G u
  let H := evenStarPuncture G u
  have hu : u ∉ S := by simp [S]
  have hSodd : Odd #S := hodd
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
  obtain ⟨b, hb⟩ := Finset.card_pos.mp hSodd.pos
  obtain ⟨A, hAS, _, hhalf, E, hE, hvec⟩ :=
    D.prescribed_half_star_addibility u S hu hmissing hpositive b hb
  have huA : u ∉ A := fun ha => hu (hAS ha)
  have hEu : E.endpointCount u = D.endpointCount u + #A := by
    simpa [huA] using hvec u
  have hcount := Finset.card_sdiff_add_card_eq_card hAS
  have hround : #S + 1 ≤ 2 * #A := by
    rw [Nat.odd_iff] at hSodd
    omega
  have hrestore : (H ⊔ A.sup (SimpleGraph.edge u)) ⊔
      (S \ A).sup (SimpleGraph.edge u) = G := by
    rw [sup_assoc, ← Finset.sup_union, Finset.union_sdiff_of_subset hAS]
    exact hfull
  have hle : H ⊔ A.sup (SimpleGraph.edge u) ≤ G := by
    rw [← hrestore]
    exact le_sup_left
  have hpass (v : V) (hv : v ∈ S \ A) :
      #{w ∈ (H ⊔ A.sup (SimpleGraph.edge u)).neighborFinset v |
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
    exact (Finset.card_le_card hs).trans (hcap v (Finset.mem_sdiff.mp hv).1)
  obtain ⟨P, hP, hp⟩ := E.outward_star_addibility u (S \ A) 2
    (fun h => hu (Finset.mem_sdiff.mp h).1)
    (by
      intro v hv h
      obtain ⟨hvS, hvA⟩ := Finset.mem_sdiff.mp hv
      rcases h with h | h
      · exact hmissing v hvS h
      · exact hvA ((star_sup_adj_center u A huA v).mp h))
    hpass (by omega)
  have hPu : 2 ≤ P.endpointCount u := by
    have he : P.endpointCount u + #(S \ A) = E.endpointCount u := by
      simpa [hu] using hp u
    omega
  have hout : ∃ P : Decomposition ((H ⊔ A.sup (SimpleGraph.edge u)) ⊔
      (S \ A).sup (SimpleGraph.edge u)), P.size = D.size ∧ 2 ≤ P.endpointCount u ∧
      ∀ w, w ≠ u → w ∉ evenNeighbors G u → P.endpointCount w = D.endpointCount w := by
    refine ⟨P, hP.trans hE, hPu, ?_⟩
    intro w hwu hwS
    have hwA : w ∉ A := fun h => hwS (hAS h)
    have hwR : w ∉ S \ A := fun h => hwS (Finset.mem_sdiff.mp h).1
    have he := hvec w
    have hf := hp w
    simp only [hwA, hwR, hwu.symm, if_false, Nat.add_zero] at he hf
    exact hf.trans he
  rwa [hrestore] at hout

/-- Count-and-hub projection of the endpoint-preserving odd-star interface. -/
theorem Decomposition.restore_odd_even_star_with_reserve (u : V)
    (hodd : Odd (eDegree G u))
    (hcap : ∀ v ∈ evenNeighbors G u, #((evenNeighbors G v).erase u) ≤ 2)
    (D : Decomposition (evenStarPuncture G u)) (hDu : 0 < D.endpointCount u) :
    ∃ P : Decomposition G, P.size = D.size ∧ 2 ≤ P.endpointCount u := by
  obtain ⟨P, hs, he, _⟩ := D.restore_odd_even_star_with_reserve_preserving u hodd hcap hDu
  exact ⟨P, hs, he⟩

/-- At an even hub with odd E-degree the puncture has odd hub degree, so the
initial reserve is supplied by parity. Leaf cap three includes the hub. -/
theorem Decomposition.restore_odd_even_star_exposing_preserving (u : V)
    (huEven : Even (G.degree u)) (hodd : Odd (eDegree G u))
    (hcap : ∀ v ∈ evenNeighbors G u, eDegree G v ≤ 3)
    (D : Decomposition (evenStarPuncture G u)) :
    ∃ P : Decomposition G, P.size = D.size ∧ 2 ≤ P.endpointCount u ∧
      ∀ w, w ≠ u → w ∉ evenNeighbors G u → P.endpointCount w = D.endpointCount w := by
  have hDu : 0 < D.endpointCount u := by
    apply D.endpointCount_pos_of_odd_degree
    have hd := evenStarPuncture_degree_center G u
    rw [Nat.even_iff] at huEven
    rw [Nat.odd_iff] at hodd ⊢
    omega
  apply D.restore_odd_even_star_with_reserve_preserving u hodd ?_ hDu
  intro v hv
  have hmem : u ∈ evenNeighbors G v :=
    (mem_evenNeighbors v u).mpr ⟨((mem_evenNeighbors u v).mp hv).1.symm, huEven⟩
  have hn := Finset.card_erase_add_one hmem
  have hb := hcap v hv
  change #(evenNeighbors G v) ≤ 3 at hb
  omega

/-- Count-and-hub projection with parity-derived initial reserve. -/
theorem Decomposition.restore_odd_even_star_exposing (u : V)
    (huEven : Even (G.degree u)) (hodd : Odd (eDegree G u))
    (hcap : ∀ v ∈ evenNeighbors G u, eDegree G v ≤ 3)
    (D : Decomposition (evenStarPuncture G u)) :
    ∃ P : Decomposition G, P.size = D.size ∧ 2 ≤ P.endpointCount u := by
  obtain ⟨P, hs, he, _⟩ := D.restore_odd_even_star_exposing_preserving u huEven hodd hcap
  exact ⟨P, hs, he⟩

end Gallai
