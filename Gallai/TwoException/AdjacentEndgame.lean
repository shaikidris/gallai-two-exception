/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.Inputs.PartialOddStarRestore
public import Gallai.TwoException.AdjacentMinimality

@[expose] public section

/-!
# Adjacent-two-exception odd-puncture endgame

This is the final reconstruction step in Xie's proof of the adjacent
two-exception endpoint theorem (Theorem 1.4).  The global proof supplies a
decomposition of a puncture at `x` in which every original neighbour of `x`
is exposed.  When the deleted even-neighbour star has odd cardinality,
Fan's prescribed half-star restoration and the complementary outward-star
restoration recover the graph at the same path count.  The statement records
the endpoint preservation at the *other* exceptional vertex `y`, which is the
interface needed by the source proof.

This module deliberately does not assert the global adjacent theorem: deriving
the puncture witness from the minimal-counterexample branches remains the
separate `I-XIE` obligation.
-/

namespace Gallai.TwoException

open scoped Finset

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- An odd partial even-neighbour puncture at `x` can be restored without
changing the endpoint count at a distinct vertex outside the deleted star.
This is the source-level endgame used when Xie's selected `x`-star leaves the
adjacent exceptional vertex `y` retained. -/
theorem xie_adjacent_odd_puncture_endgame
    (x y : V) (S : Finset V)
    (hxy : x ≠ y) (hyS : y ∉ S)
    (hS : S ⊆ evenNeighbors G x) (hodd : Odd #S)
    (hleaves : ∀ v ∈ S, #((evenNeighbors G v).erase x) ≤ 2)
    (D : Decomposition (starPuncture G x S))
    (hxD : 0 < D.endpointCount x)
    (hneighbors : ∀ v, G.Adj x v → 0 < D.endpointCount v) :
    ∃ P : Decomposition G, P.size = D.size ∧ 2 ≤ P.endpointCount x ∧
      P.endpointCount y = D.endpointCount y := by
  obtain ⟨P, hsize, hxP, hpreserve⟩ :=
    D.restore_partial_odd_even_star x S hS hodd hleaves hxD hneighbors
  exact ⟨P, hsize, hxP, hpreserve y hxy.symm hyS⟩

/-- Xie's Claim 2 uses the adjacent exceptional vertex itself as the
prescribed first spoke.  It may have arbitrary E-degree, but the prescribed
half-star contains it, so only the unselected ordinary leaves need the
passing-neighbour cap. -/
theorem xie_adjacent_odd_puncture_protected_endgame
    (x y : V) (S : Finset V)
    (hS : S ⊆ evenNeighbors G x) (hodd : Odd #S) (hyS : y ∈ S)
    (hleaves : ∀ v ∈ S, v ≠ y → #((evenNeighbors G v).erase x) ≤ 2)
    (D : Decomposition (starPuncture G x S))
    (hxD : 0 < D.endpointCount x)
    (hneighbors : ∀ v, G.Adj x v → 0 < D.endpointCount v) :
    ∃ P : Decomposition G, P.size = D.size ∧ 2 ≤ P.endpointCount x := by
  obtain ⟨P, hsize, hxP, _⟩ :=
    D.restore_partial_odd_even_star_with_protected_leaf x S y hS hodd hyS
      hleaves hxD hneighbors
  exact ⟨P, hsize, hxP⟩

/-- The final odd-puncture certificate contradicts an adjacent minimal
counterexample as soon as its puncture decomposition already exposes the
retained hub twice. The source's global induction is responsible for producing
that puncture certificate; this theorem closes the reconstruction exactly. -/
theorem adjacent_odd_puncture_not_minimal
    (x y : V) (S : Finset V) (M : AdjacentMinimalCounterexample G x y)
    (hyS : y ∉ S) (hS : S ⊆ evenNeighbors G x) (hodd : Odd #S)
    (hleaves : ∀ v ∈ S, #((evenNeighbors G v).erase x) ≤ 2)
    (D : Decomposition (starPuncture G x S))
    (hDsize : D.size ≤ (Fintype.card V + 1) / 2)
    (hxD : 0 < D.endpointCount x)
    (hneighbors : ∀ v, G.Adj x v → 0 < D.endpointCount v)
    (hyD : 2 ≤ D.endpointCount y) : False := by
  have hxy : x ≠ y := M.counterexample.1.2.1
  obtain ⟨P, hPsize, hxP, hyP⟩ := xie_adjacent_odd_puncture_endgame x y S hxy hyS
    hS hodd hleaves D hxD hneighbors
  apply M.counterexample.2
  refine ⟨⟨P, ?_, hxP⟩, ⟨P, ?_, ?_⟩⟩
  · rw [hPsize]
    exact hDsize
  · rw [hPsize]
    exact hDsize
  · rw [hyP]
    exact hyD

end Gallai.TwoException
