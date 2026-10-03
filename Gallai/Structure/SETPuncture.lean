/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.Structure.SET
public import Gallai.Structure.StarPuncture
public import Gallai.Inputs.LovaszDirect

@[expose] public section

/-! # Parity of a SET graph after deleting the designated even-neighbour star -/

namespace Gallai

open scoped Finset

universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The actual spanning puncture, not an induced vertex deletion. -/
abbrev evenStarPuncture (u : V) : SimpleGraph V :=
  starPuncture G u (evenNeighbors G u)

/-- Once the hub is discarded, deleting its even-neighbour star leaves the
induced graph unchanged. -/
theorem induce_evenStarPuncture_eq_of_notMem (u : V) (S : Set V) (hu : u ∉ S) :
    (evenStarPuncture G u).induce S = G.induce S :=
  induce_starPuncture_eq_of_notMem G u (evenNeighbors G u) S hu

/-- Named local decision instance for degree statements. -/
noncomputable local instance evenStarPunctureAdj (u : V) :
    DecidableRel (evenStarPuncture G u).Adj := fun _ _ => Classical.propDecidable _

/-- A deleted even leaf becomes odd. -/
theorem evenStarPuncture_odd_leaf (u v : V) (hv : v ∈ evenNeighbors G u) :
    Odd ((evenStarPuncture G u).degree v) := by
  obtain ⟨ha, he⟩ := (mem_evenNeighbors u v).mp hv
  have hd := starPuncture_degree_leaf G u (evenNeighbors G u) v hv ha
  rw [Nat.even_iff] at he
  rw [Nat.odd_iff]
  change (evenStarPuncture G u).degree v + 1 = G.degree v at hd
  omega

/-- Every old neighbour of the hub is odd in the puncture. -/
theorem evenStarPuncture_odd_neighbor (u v : V) (ha : G.Adj u v) :
    Odd ((evenStarPuncture G u).degree v) := by
  by_cases he : Even (G.degree v)
  · exact evenStarPuncture_odd_leaf G u v ((mem_evenNeighbors u v).mpr ⟨ha, he⟩)
  · have hn : v ∉ evenNeighbors G u := by simp [he]
    have hd : (evenStarPuncture G u).degree v = G.degree v :=
      starPuncture_degree_other G u (evenNeighbors G u) v ha.ne.symm hn
    rw [hd]
    exact Nat.not_even_iff_odd.mp he

/-- An even nonhub in the puncture was even and was not adjacent to the hub. -/
theorem evenStarPuncture_even_off_center (u v : V) (hv : v ≠ u)
    (he : Even ((evenStarPuncture G u).degree v)) :
    Even (G.degree v) ∧ v ∉ evenNeighbors G u := by
  by_cases hb : v ∈ evenNeighbors G u
  · exact (Nat.not_even_iff_odd.mpr (evenStarPuncture_odd_leaf G u v hb) he).elim
  · refine ⟨?_, hb⟩
    have hd : (evenStarPuncture G u).degree v = G.degree v :=
      starPuncture_degree_other G u (evenNeighbors G u) v hv hb
    rwa [hd] at he

/-- Hub degree balance in the even-neighbour puncture. -/
theorem evenStarPuncture_degree_center (u : V) :
    (evenStarPuncture G u).degree u + eDegree G u = G.degree u := by
  exact starPuncture_degree_center G u (evenNeighbors G u) (by simp)
    (Finset.filter_subset _ _)

variable {G}

/-- The even vertices not selected for deletion have the complementary count. -/
theorem IsSET.remaining_even_card (h : IsSET G) (u : V) :
    #((Finset.univ.filter fun v => Even (G.degree v)) \ evenNeighbors G u) +
      eDegree G u = 3 := by
  have hs : evenNeighbors G u ⊆ Finset.univ.filter fun v => Even (G.degree v) := by
    intro v hv
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ v, ((mem_evenNeighbors u v).mp hv).2⟩
  simpa [eDegree, h.card_even] using Finset.card_sdiff_add_card_eq_card hs

/-- The SET star puncture satisfies the literal Lovasz parity hypothesis. -/
theorem IsSET.puncture_unique_even (h : IsSET G) (u : V) :
    Set.Subsingleton {v | Even ((evenStarPuncture G u).degree v)} := by
  have hd := evenStarPuncture_degree_center G u
  have hc := h.remaining_even_card u
  have hoff (v : V) (hv : v ≠ u) (he : Even ((evenStarPuncture G u).degree v)) :
      v ∈ (Finset.univ.filter fun w => Even (G.degree w)) \ evenNeighbors G u := by
    obtain ⟨he, hn⟩ := evenStarPuncture_even_off_center G u v hv he
    exact Finset.mem_sdiff.mpr ⟨by simp [he], hn⟩
  by_cases hu : Even (G.degree u)
  · have hall (v : V) (he : Even ((evenStarPuncture G u).degree v)) : v = u := by
      by_contra hv
      obtain ⟨hev, hn⟩ := evenStarPuncture_even_off_center G u v hv he
      exact hn ((mem_evenNeighbors u v).mpr ⟨h.even_clique u v hu hev (Ne.symm hv), hev⟩)
    intro a ha b hb
    exact (hall a ha).trans (hall b hb).symm
  · have ho := Nat.not_even_iff_odd.mp hu
    rw [Nat.odd_iff] at ho
    rcases h.eDegree_two_or_three u with hs | hs
    · have hune : ¬ Even ((evenStarPuncture G u).degree u) := by
        rw [Nat.even_iff]
        omega
      have hsmall : #((Finset.univ.filter fun v => Even (G.degree v)) \
          evenNeighbors G u) ≤ 1 := by omega
      intro a ha b hb
      exact Finset.card_le_one.mp hsmall a (hoff a (by rintro rfl; exact hune ha) ha)
        b (hoff b (by rintro rfl; exact hune hb) hb)
    · have hempty : (Finset.univ.filter fun v => Even (G.degree v)) \
          evenNeighbors G u = ∅ := Finset.card_eq_zero.mp (by omega)
      have hall (v : V) (he : Even ((evenStarPuncture G u).degree v)) : v = u := by
        by_contra hv
        have hm := hoff v hv he
        rw [hempty] at hm
        exact Finset.notMem_empty v hm
      intro a ha b hb
      exact (hall a ha).trans (hall b hb).symm

/-- A real floor-budget decomposition of the puncture, with no connectivity premise. -/
theorem IsSET.puncture_pathBudget (h : IsSET G) (u : V) :
    HasPathBudget (evenStarPuncture G u) (Fintype.card V / 2) :=
  pathBudget_of_at_most_one_even (evenStarPuncture G u) (h.puncture_unique_even u)

end Gallai
