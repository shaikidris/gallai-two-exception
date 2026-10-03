/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.Structure.SETPuncture
public import Gallai.Inputs.FloorOrSET

@[expose] public section

/-! # Connected star punctures and removal of the sole E-degree exception -/

namespace Gallai

variable {V : Type*} [DecidableEq V] (G : SimpleGraph V)

/-- A star deletion stays connected if deletion of its centre is connected
and one incident edge remains. -/
theorem starPuncture_connected (u : V) (B : Finset V)
    (hc : (G.induce {v | v ≠ u}).Connected)
    (hi : ∃ w, (starPuncture G u B).Adj u w) :
    (starPuncture G u B).Connected := by
  have : Nonempty V := ⟨u⟩
  let H := starPuncture G u B
  let f : (G.induce {v | v ≠ u}) →g H :=
    { toFun := Subtype.val
      map_rel' := by
        intro a b hab
        refine ⟨hab, ?_⟩
        intro hs
        exact b.property ((star_sup_adj_off_center u B a b a.property).mp hs).2 }
  have hr (a b : V) (ha : a ≠ u) (hb : b ≠ u) : H.Reachable a b :=
    (hc.preconnected ⟨a, ha⟩ ⟨b, hb⟩).map f
  obtain ⟨w, hw⟩ := hi
  have reach (v : V) : H.Reachable u v := by
    by_cases hv : v = u
    · subst v; exact SimpleGraph.Reachable.refl _
    · exact hw.reachable.trans (hr w v hw.ne.symm hv)
  exact ⟨fun a b => (reach a).symm.trans (reach b)⟩

variable [Fintype V] [DecidableRel G.Adj]

/-- Fix the finite adjacency decision for the even-star puncture. -/
noncomputable local instance oneExceptionStarPunctureAdj (u : V) :
    DecidableRel (evenStarPuncture G u).Adj := fun _ _ => Classical.propDecidable _

/-- The centre has no even neighbours in the complete even-star puncture. -/
theorem evenStarPuncture_no_even_neighbor (u v : V)
    (ha : (evenStarPuncture G u).Adj u v) :
    ¬ Even ((evenStarPuncture G u).degree v) :=
  Nat.not_even_iff_odd.mpr (evenStarPuncture_odd_neighbor G u v ha.1)

/-- Puncturing the designated star removes the sole E-degree exception. -/
theorem one_exception_evenStarPuncture_cap (u : V)
    (hcap : ∀ v, Even (G.degree v) → v ≠ u → eDegree G v ≤ 3) :
    ∀ v, Even ((evenStarPuncture G u).degree v) →
      eDegree (evenStarPuncture G u) v ≤ 3 := by
  classical
  intro v hv
  by_cases hvu : v = u
  · subst v
    have hz : evenNeighbors (evenStarPuncture G u) u = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro w hw
      obtain ⟨ha, he⟩ := (mem_evenNeighbors u w).mp hw
      exact evenStarPuncture_no_even_neighbor G u w ha he
    simp [eDegree, hz]
  · have he := (evenStarPuncture_even_off_center G u v hvu hv).1
    apply (Finset.card_le_card (s := evenNeighbors (evenStarPuncture G u) v)
      (t := evenNeighbors G v) ?_).trans (hcap v he hvu)
    intro w hw
    obtain ⟨ha, he⟩ := (mem_evenNeighbors v w).mp hw
    have hwu : w ≠ u := by
      intro h
      subst w
      exact evenStarPuncture_no_even_neighbor G u v ha.symm hv
    exact (mem_evenNeighbors v w).mpr ⟨ha.1,
      (evenStarPuncture_even_off_center G u w hwu he).1⟩

/-- A connected designated even-star puncture has a genuine floor budget:
SET is excluded by the centre's complete lack of even neighbours. -/
theorem one_exception_evenStarPuncture_floor (u : V)
    (hcap : ∀ v, Even (G.degree v) → v ≠ u → eDegree G v ≤ 3)
    (hc : (evenStarPuncture G u).Connected) :
    HasPathBudget (evenStarPuncture G u) (Fintype.card V / 2) := by
  rcases floor_or_set (evenStarPuncture G u) hc
    (one_exception_evenStarPuncture_cap G u hcap) with hd | hs
  · exact hd
  · obtain ⟨v, ha, he, _⟩ := hs.even_neighbor_ne u u
    exact (evenStarPuncture_no_even_neighbor G u v ha he).elim

/-- Odd E-degree at an even centre leaves a positive ordinary degree after
puncturing, hence the connected-deletion hypothesis supplies connectivity. -/
theorem odd_evenStarPuncture_connected (u : V) (hu : Even (G.degree u))
    (ho : Odd (eDegree G u)) (hc : (G.induce {v | v ≠ u}).Connected) :
    (evenStarPuncture G u).Connected := by
  apply starPuncture_connected G u (evenNeighbors G u) hc
  apply ((evenStarPuncture G u).degree_pos_iff_exists_adj u).mp
  have hd := evenStarPuncture_degree_center G u
  rw [Nat.even_iff] at hu
  rw [Nat.odd_iff] at ho
  omega

end Gallai
