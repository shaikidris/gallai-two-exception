/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.Inputs.OneException
public import Gallai.Structure.PartialEvenStar
public import Gallai.TwoException.AdjacentEndgame
public import Gallai.TwoException.AdjacentParity

@[expose] public section

/-! # The final even-E-degree branch of Xie's adjacent theorem

After the parity reduction, retain `xy` and puncture all other even-neighbour
spokes at `x`.  The puncture has only `y` as a possible E-degree exception, so
the one-exception endpoint theorem produces the reserve needed by the odd-star
return. -/

namespace Gallai.TwoException

open scoped Finset

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable local instance adjacentFinalPunctureAdj (x y : V) :
    DecidableRel (starPuncture G x ((evenNeighbors G x).erase y)).Adj :=
  fun _ _ => Classical.propDecidable _

/-- The final source branch when `x` has positive even E-degree.  Its output
contains both endpoint witnesses: the return preserves the retained `y`
reserve while producing the new `x` reserve. -/
theorem adjacent_even_eDegree_first_endpoint
    (x y : V) (M : AdjacentEdgeMinimalCounterexample G x y)
    (hxF : Even (eDegree G x)) : AdjacentConclusion G x y := by
  classical
  rcases M.counterexample.1 with ⟨hconn, hxyne, hxy, hxEven, hyEven, hcap⟩
  let S := (evenNeighbors G x).erase y
  let H := starPuncture G x S
  let : DecidableRel H.Adj := fun _ _ => Classical.propDecidable _
  have hS : S ⊆ evenNeighbors G x := Finset.erase_subset _ _
  have hyN : y ∈ evenNeighbors G x :=
    (mem_evenNeighbors x y).mpr ⟨hxy, hyEven⟩
  have hyS : y ∉ S := Finset.notMem_erase _ _
  have hxS : x ∉ S := fun h =>
    (show x ∉ evenNeighbors G x by simp) (hS h)
  have hcard : #S + 1 = eDegree G x := Finset.card_erase_add_one hyN
  have hSodd : Odd #S := by
    rw [Nat.even_iff] at hxF
    rw [Nat.odd_iff]
    omega
  have hxdelete : (G.induce {v | v ≠ x}).Connected :=
    adjacent_even_vertex_noncut_edge x x y M hxEven
  have hretained : H.Adj x y := by
    refine ⟨hxy, ?_⟩
    intro h
    exact hyS ((star_sup_adj_center x S hxS y).mp h)
  have hHconn : H.Connected :=
    starPuncture_connected G x S hxdelete ⟨y, hretained⟩
  have hyHdegree : H.degree y = G.degree y := by
    simpa only [H, SimpleGraph.degree, SimpleGraph.neighborFinset,
      ← Set.ncard_eq_toFinset_card'] using
      starPuncture_degree_other G x S y hxy.ne.symm hyS
  have hyHpos : 0 < H.degree y := by
    rw [hyHdegree]
    exact hxy.degree_pos_right
  have hyHEven : Even (H.degree y) := by rwa [hyHdegree]
  have hHcap : ∀ v, Even (H.degree v) → v ≠ y → eDegree H v ≤ 3 := by
    simpa only [H] using partialEvenStar_cap_two_exceptions G x y S hS hxEven hSodd hcap
  obtain ⟨D, hDsize, hyD⟩ := one_exception_endpoint H y hHconn hyHpos hyHEven hHcap
  have hxHodd : Odd (H.degree x) := by
    simpa only [H] using partialEvenStar_odd_center G x S hS hxEven hSodd
  have hxD : 0 < D.endpointCount x := D.endpointCount_pos_of_odd_degree x hxHodd
  have hneighbors : ∀ v, G.Adj x v → 0 < D.endpointCount v := by
    intro v hxv
    by_cases hvy : v = y
    · subst v
      exact lt_of_lt_of_le (by omega) hyD
    · apply D.endpointCount_pos_of_odd_degree v
      simpa only [S, H] using retainedEvenStar_odd_neighbor G x y v hxv hvy
  have hleafcap : ∀ v ∈ S, #((evenNeighbors G v).erase x) ≤ 2 := by
    intro v hv
    obtain ⟨hxv, hvEven⟩ := (mem_evenNeighbors x v).mp (hS hv)
    have hvx : v ≠ x := hxv.ne.symm
    have hvy : v ≠ y := by
      intro h
      subst v
      exact hyS hv
    have hbound := hcap v hvEven hvx hvy
    have hxmem : x ∈ evenNeighbors G v :=
      (mem_evenNeighbors v x).mpr ⟨hxv.symm, hxEven⟩
    unfold eDegree at hbound
    have hcard' := Finset.card_erase_add_one hxmem
    omega
  obtain ⟨P, hPsize, hxP, hyP⟩ :=
    xie_adjacent_odd_puncture_endgame x y S hxyne hyS hS hSodd hleafcap D hxD hneighbors
  refine ⟨⟨P, ?_, hxP⟩, ⟨P, ?_, ?_⟩⟩
  · rw [hPsize]
    exact hDsize
  · rw [hPsize]
    exact hDsize
  · rw [hyP]
    exact hyD

/-- An edge-minimal adjacent counterexample cannot enter the final
positive-even E-degree branch at either designated hub. -/
theorem adjacent_even_eDegree_not_edge_minimal
    (x y : V) (M : AdjacentEdgeMinimalCounterexample G x y)
    (hxF : Even (eDegree G x)) : False := by
  exact M.counterexample.2 (adjacent_even_eDegree_first_endpoint x y M hxF)

/-- The source-faithful edge-minimal adjacent counterexample is impossible:
Claim 2 supplies an even exceptional E-degree, and the retained-spoke branch
then supplies both required endpoint witnesses. -/
theorem adjacent_edge_minimal_false
    (x y : V) (M : AdjacentEdgeMinimalCounterexample G x y) : False := by
  rcases adjacent_eDegree_even_or_even x y M with hxF | hyF
  · exact adjacent_even_eDegree_not_edge_minimal x y M hxF
  · exact adjacent_even_eDegree_not_edge_minimal y x
      (adjacentEdgeMinimalCounterexample_swap M) hyF

/-- Xie's adjacent two-exception endpoint theorem.  Strong induction on the
number of edges supplies the source-faithful edge-minimal resource, and the
preceding theorem excludes that resource.  The two endpoint outputs are
independent decompositions, exactly as in the published statement. -/
theorem adjacent_endpoint (G : SimpleGraph V) [DecidableRel G.Adj] (x y : V)
    (hG : AdjacentInstance G x y) : AdjacentConclusion G x y := by
  suffices hall : ∀ n : ℕ, ∀ (W : Type u) [Fintype W] [DecidableEq W]
      (J : SimpleGraph W) [DecidableRel J.Adj], J.edgeFinset.card = n →
      ∀ a b : W, AdjacentInstance J a b → AdjacentConclusion J a b by
    exact hall G.edgeFinset.card V G rfl x y hG
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro W _ _ J _ hJ a b hinstance
    by_contra hnot
    apply adjacent_edge_minimal_false (G := J) a b
    refine ⟨⟨hinstance, hnot⟩, ?_⟩
    intro U _ _ K _ c d hlt hK
    exact ih K.edgeFinset.card (by omega) U K rfl c d hK

end Gallai.TwoException
