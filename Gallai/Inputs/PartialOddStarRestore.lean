/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.Inputs.ThreeSpokeRestore
public import Gallai.Inputs.OutwardStar

@[expose] public section

/-! # Restoration of a partial odd even-neighbour star

Unlike complete puncturing, retained even neighbours require explicit
endpoint supply. The retained-spoke induction provides that supply.
-/

namespace Gallai

open scoped Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Use one fixed adjacency decision throughout partial-star reconstruction. -/
noncomputable local instance partialOddStarAdj (u : V) (S : Finset V) :
    DecidableRel (starPuncture G u S).Adj := fun _ _ => Classical.propDecidable _

/-- Restore any odd subset of the even-neighbour star, using endpoint supply
at every original neighbour, and preserve all off-star endpoint counts. -/
theorem Decomposition.restore_partial_odd_even_star (u : V) (S : Finset V)
    (hS : S ⊆ evenNeighbors G u) (hodd : Odd #S)
    (hcap : ∀ v ∈ S, #((evenNeighbors G v).erase u) ≤ 2)
    (D : Decomposition (starPuncture G u S)) (hDu : 0 < D.endpointCount u)
    (hneighbors : ∀ v, G.Adj u v → 0 < D.endpointCount v) :
    ∃ P : Decomposition G, P.size = D.size ∧ 2 ≤ P.endpointCount u ∧
      ∀ w, w ≠ u → w ∉ S → P.endpointCount w = D.endpointCount w := by
  classical
  let H := starPuncture G u S
  have hu : u ∉ S := fun h => (show u ∉ evenNeighbors G u by simp) (hS h)
  have hSodd : Odd #S := hodd
  have hfull : H ⊔ S.sup (SimpleGraph.edge u) = G :=
    starPuncture_restore G u S (fun v hv => ((mem_evenNeighbors u v).mp (hS hv)).1)
  have hmissing (v : V) (hv : v ∈ S) : ¬ H.Adj u v :=
    starPuncture_missing G u S hu v hv
  have hpositive (v : V) (hv : H.Adj u v ∨ v ∈ S) : 0 < D.endpointCount v := by
    apply hneighbors v
    rcases hv with hv | hv
    · exact hv.1
    · exact ((mem_evenNeighbors u v).mp (hS hv)).1
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
      · exact ((mem_evenNeighbors u w).mp (hS hwS)).2
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
      ∀ w, w ≠ u → w ∉ S → P.endpointCount w = D.endpointCount w := by
    refine ⟨P, hP.trans hE, hPu, ?_⟩
    intro w hwu hwS
    have hwA : w ∉ A := fun h => hwS (hAS h)
    have hwR : w ∉ S \ A := fun h => hwS (Finset.mem_sdiff.mp h).1
    have he := hvec w
    have hf := hp w
    simp only [hwA, hwR, hwu.symm, if_false, Nat.add_zero] at he hf
    exact hf.trans he
  rwa [hrestore] at hout

/-- Restore an odd selected star when one prescribed leaf may have arbitrary
even-neighbour degree.  The prescribed half-star step selects `b` first, so
only leaves left in the complementary outward star need the usual cap two.
This is the precise interface used by the adjacent two-exception parity
argument, where the protected leaf is the other exceptional vertex. -/
theorem Decomposition.restore_partial_odd_even_star_with_protected_leaf
    (u : V) (S : Finset V) (b : V)
    (hS : S ⊆ evenNeighbors G u) (hodd : Odd #S) (hb : b ∈ S)
    (hcap : ∀ v ∈ S, v ≠ b → #((evenNeighbors G v).erase u) ≤ 2)
    (D : Decomposition (starPuncture G u S)) (hDu : 0 < D.endpointCount u)
    (hneighbors : ∀ v, G.Adj u v → 0 < D.endpointCount v) :
    ∃ P : Decomposition G, P.size = D.size ∧ 2 ≤ P.endpointCount u ∧
      ∀ w, w ≠ u → w ∉ S → P.endpointCount w = D.endpointCount w := by
  classical
  let H := starPuncture G u S
  have hu : u ∉ S := fun h => (show u ∉ evenNeighbors G u by simp) (hS h)
  have hfull : H ⊔ S.sup (SimpleGraph.edge u) = G :=
    starPuncture_restore G u S (fun v hv => ((mem_evenNeighbors u v).mp (hS hv)).1)
  have hmissing (v : V) (hv : v ∈ S) : ¬ H.Adj u v :=
    starPuncture_missing G u S hu v hv
  have hpositive (v : V) (hv : H.Adj u v ∨ v ∈ S) : 0 < D.endpointCount v := by
    apply hneighbors v
    rcases hv with hv | hv
    · exact hv.1
    · exact ((mem_evenNeighbors u v).mp (hS hv)).1
  obtain ⟨A, hAS, hbA, hhalf, E, hE, hvec⟩ :=
    D.prescribed_half_star_addibility u S hu hmissing hpositive b hb
  have huA : u ∉ A := fun ha => hu (hAS ha)
  have hEu : E.endpointCount u = D.endpointCount u + #A := by
    simpa [huA] using hvec u
  have hcount := Finset.card_sdiff_add_card_eq_card hAS
  have hround : #S + 1 ≤ 2 * #A := by
    rw [Nat.odd_iff] at hodd
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
      · exact ((mem_evenNeighbors u w).mp (hS hwS)).2
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
    obtain ⟨hvS, hvA⟩ := Finset.mem_sdiff.mp hv
    have hvb : v ≠ b := by
      intro he
      subst v
      exact hvA hbA
    exact (Finset.card_le_card hs).trans (hcap v hvS hvb)
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
      ∀ w, w ≠ u → w ∉ S → P.endpointCount w = D.endpointCount w := by
    refine ⟨P, hP.trans hE, hPu, ?_⟩
    intro w hwu hwS
    have hwA : w ∉ A := fun h => hwS (hAS h)
    have hwR : w ∉ S \ A := fun h => hwS (Finset.mem_sdiff.mp h).1
    have he := hvec w
    have hf := hp w
    simp only [hwA, hwR, hwu.symm, if_false, Nat.add_zero] at he hf
    exact hf.trans he
  rwa [hrestore] at hout


end Gallai
