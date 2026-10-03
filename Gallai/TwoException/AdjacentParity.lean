/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.Inputs.FloorOrSET
public import Gallai.Inputs.SETReserve
public import Gallai.Structure.StarPunctureException
public import Gallai.TwoException.AdjacentEndgame
public import Gallai.TwoException.AdjacentHubOddLift

@[expose] public section

/-! # The parity reduction in Xie's adjacent two-exception theorem

This file formalizes the operative direction of Xie's Claim 2.  If both
adjacent exceptional E-degrees are odd, puncturing the full even-neighbour
star at either hub has a ceiling-budget decomposition.  The prescribed
half-star selects the other hub first, so its unbounded E-degree is not used
by the complementary outward restoration.
-/

namespace Gallai.TwoException

open scoped Finset

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable local instance adjacentParityPunctureAdj (x : V) :
    DecidableRel (evenStarPuncture G x).Adj := fun _ _ => Classical.propDecidable _

/-- The `x` output in Xie's odd/odd parity branch.  The proof keeps every
source-side condition explicit: Claim 1 gives puncture connectivity,
Botler--Sambinelli supplies either a floor decomposition or a SET reserve,
and the prescribed `xy` half-star protects the only leaf without the ordinary
E-degree cap. -/
theorem adjacent_odd_eDegrees_first_endpoint
    (x y : V) (M : AdjacentEdgeMinimalCounterexample G x y)
    (hxodd : Odd (eDegree G x)) (hyodd : Odd (eDegree G y)) :
    ∃ P : Decomposition G, P.size ≤ (Fintype.card V + 1) / 2 ∧
      2 ≤ P.endpointCount x := by
  classical
  rcases M.counterexample.1 with ⟨hconn, hxyne, hxy, hxEven, hyEven, hcap⟩
  let H := evenStarPuncture G x
  let : DecidableRel H.Adj := fun _ _ => Classical.propDecidable _
  have hxdelete : (G.induce {v | v ≠ x}).Connected :=
    adjacent_even_vertex_noncut_edge x x y M hxEven
  have hHconn : H.Connected := by
    simpa only [H] using odd_evenStarPuncture_connected G x hxEven hxodd hxdelete
  have hHcap : ∀ v, Even (H.degree v) → eDegree H v ≤ 3 := by
    simpa only [H] using evenStarPuncture_cap_two_exceptions G x y hxy hcap
  have hxHodd : Odd (H.degree x) := by
    have hd := evenStarPuncture_degree_center G x
    rw [Nat.even_iff] at hxEven
    rw [Nat.odd_iff] at hxodd
    rw [Nat.odd_iff]
    change H.degree x + eDegree G x = G.degree x at hd
    omega
  obtain ⟨D, hDsize⟩ : ∃ D : Decomposition H,
      D.size ≤ (Fintype.card V + 1) / 2 := by
    rcases floor_or_set H hHconn hHcap with hfloor | hset
    · rcases hfloor with ⟨D, hD⟩
      exact ⟨D, by omega⟩
    · obtain ⟨D, hD, _⟩ := hset.endpoint_reserve x
      exact ⟨D, hD⟩
  have hxD : 0 < D.endpointCount x :=
    D.endpointCount_pos_of_odd_degree x hxHodd
  have hyS : y ∈ evenNeighbors G x :=
    (mem_evenNeighbors x y).mpr ⟨hxy, hyEven⟩
  have hleaves : ∀ v ∈ evenNeighbors G x, v ≠ y →
      #((evenNeighbors G v).erase x) ≤ 2 := by
    intro v hv hvy
    obtain ⟨hxv, hvEven⟩ := (mem_evenNeighbors x v).mp hv
    have hvx : v ≠ x := hxv.ne.symm
    have hbound := hcap v hvEven hvx hvy
    have hxmem : x ∈ evenNeighbors G v :=
      (mem_evenNeighbors v x).mpr ⟨hxv.symm, hxEven⟩
    unfold eDegree at hbound
    have hcard := Finset.card_erase_add_one hxmem
    omega
  have hneighbors : ∀ v, G.Adj x v → 0 < D.endpointCount v := by
    intro v hxv
    apply D.endpointCount_pos_of_odd_degree v
    simpa only [H] using evenStarPuncture_odd_neighbor G x v hxv
  obtain ⟨P, hPsize, hxP⟩ :=
    xie_adjacent_odd_puncture_protected_endgame x y (evenNeighbors G x)
      (by intro v hv; exact hv) hxodd hyS hleaves D hxD hneighbors
  exact ⟨P, by
    rw [hPsize]
    exact hDsize, hxP⟩

/-- Xie's Claim 2: an edge-minimal adjacent counterexample cannot have both
exceptional E-degrees odd.  The two endpoint witnesses are constructed by the
preceding theorem and its literal symmetry. -/
theorem adjacent_eDegree_even_or_even
    (x y : V) (M : AdjacentEdgeMinimalCounterexample G x y) :
    Even (eDegree G x) ∨ Even (eDegree G y) := by
  by_contra h
  push_neg at h
  have hxodd : Odd (eDegree G x) := Nat.not_even_iff_odd.mp h.1
  have hyodd : Odd (eDegree G y) := Nat.not_even_iff_odd.mp h.2
  obtain ⟨Dx, hsx, hex⟩ := adjacent_odd_eDegrees_first_endpoint x y M hxodd hyodd
  obtain ⟨Dy, hsy, hey⟩ := adjacent_odd_eDegrees_first_endpoint y x
    (adjacentEdgeMinimalCounterexample_swap M) hyodd hxodd
  exact M.counterexample.2 ⟨⟨Dx, hsx, hex⟩, ⟨Dy, hsy, hey⟩⟩

end Gallai.TwoException
