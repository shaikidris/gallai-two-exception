/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.Inputs.OutwardStar
public import Gallai.Structure.StarPuncture

@[expose] public section

/-! # Two-tier outward restoration for the odd-neighbour component claim

The difficult leaves have at most two passing neighbours; the others have
at most one. The endpoint reserve and both bounds refer to the same input
decomposition. This is a restoration interface, not the existence of the
structural puncture supplying that decomposition.
-/

namespace Gallai.Decomposition

open scoped Finset

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Local adjacency decision for the restored finite star. -/
noncomputable local instance extendedStarAdj (u : V) (S : Finset V) :
    DecidableRel (G ⊔ S.sup (SimpleGraph.edge u)).Adj :=
  fun _ _ => Classical.propDecidable _

/-- Batch outward transfer cannot create passing neighbours at an untouched
leaf when the hub retains a positive endpoint count. -/
theorem passing_neighbors_mono_after_outward_star
    (D : Decomposition G) (u : V) (S : Finset V)
    (E : Decomposition (G ⊔ S.sup (SimpleGraph.edge u)))
    (he : ∀ v, E.endpointCount v + (if u = v then #S else 0) =
      D.endpointCount v + if v ∈ S then 1 else 0)
    (hpos : 0 < E.endpointCount u) (t : V) (htu : t ≠ u) (htS : t ∉ S) :
    #{v ∈ (G ⊔ S.sup (SimpleGraph.edge u)).neighborFinset t |
      E.endpointCount v = 0} ≤
      #{v ∈ G.neighborFinset t | D.endpointCount v = 0} := by
  classical
  apply Finset.card_le_card
  intro v hv
  obtain ⟨hv, hz⟩ := Finset.mem_filter.mp hv
  have hadj := ((G ⊔ S.sup (SimpleGraph.edge u)).mem_neighborFinset t v).mp hv
  have hold : G.Adj t v := by
    rcases hadj with h | h
    · exact h
    · exact (htS ((star_sup_adj_off_center u S t v htu).mp h).1).elim
  have huv : u ≠ v := by
    intro h
    subst v
    omega
  have hh := he v
  simp only [huv, if_false, Nat.add_zero, hz] at hh
  exact Finset.mem_filter.mpr ⟨(G.mem_neighborFinset t v).mpr hold, by omega⟩

/-- Restore a two-passing-neighbour group using the reserve forced by the
triangle counting in Claim 5, including the empty and singleton groups. -/
theorem outward_star_two_passing (D : Decomposition G) (u : V) (S : Finset V)
    (hu : u ∉ S) (hmissing : ∀ v ∈ S, ¬ G.Adj u v)
    (hp : ∀ v ∈ S, #{w ∈ G.neighborFinset v | D.endpointCount w = 0} ≤ 2)
    (hthree : S.Nonempty → 3 ≤ D.endpointCount u)
    (htwice : 2 * #S ≤ D.endpointCount u) :
    ∃ E : Decomposition (G ⊔ S.sup (SimpleGraph.edge u)), E.size = D.size ∧
      ∀ v, E.endpointCount v + (if u = v then #S else 0) =
        D.endpointCount v + if v ∈ S then 1 else 0 := by
  classical
  by_cases hs : S = ∅
  · subst S
    rw [Finset.sup_empty, sup_bot_eq]
    simp only [Finset.card_empty,
      Finset.notMem_empty, if_false, ite_self, Nat.add_zero]
    exact ⟨D, rfl, fun _ => rfl⟩
  · have hne := Finset.nonempty_iff_ne_empty.mpr hs
    have hc : 0 < #S := Finset.card_pos.mpr hne
    have hh := hthree hne
    exact D.outward_star_addibility u S 2 hu hmissing hp (by omega)

/-- Restore disjoint difficult and ordinary leaves at no path-count cost.
The strict total reserve leaves the one endpoint needed for the second tier.
All endpoint changes hold for the constructed common output witness. -/
theorem two_tier_outward_star (D : Decomposition G) (u : V) (S R : Finset V)
    (hu : u ∉ S ∪ R) (hdis : Disjoint S R)
    (hmissing : ∀ v ∈ S ∪ R, ¬ G.Adj u v)
    (hpS : ∀ v ∈ S, #{w ∈ G.neighborFinset v | D.endpointCount w = 0} ≤ 2)
    (hpR : ∀ v ∈ R, #{w ∈ G.neighborFinset v | D.endpointCount w = 0} ≤ 1)
    (hthree : S.Nonempty → 3 ≤ D.endpointCount u)
    (htwice : 2 * #S ≤ D.endpointCount u)
    (hreserve : #S + #R + 1 ≤ D.endpointCount u) :
    ∃ E : Decomposition (G ⊔ (S ∪ R).sup (SimpleGraph.edge u)), E.size = D.size ∧
      ∀ v, E.endpointCount v + (if u = v then #(S ∪ R) else 0) =
        D.endpointCount v + if v ∈ S ∪ R then 1 else 0 := by
  classical
  have huS : u ∉ S := fun h => hu (Finset.mem_union_left R h)
  have huR : u ∉ R := fun h => hu (Finset.mem_union_right S h)
  obtain ⟨E, hsize, he⟩ := D.outward_star_two_passing u S huS
    (fun v hv => hmissing v (Finset.mem_union_left R hv)) hpS hthree htwice
  have heu : E.endpointCount u + #S = D.endpointCount u := by
    simpa only [if_true, huS, if_false, Nat.add_zero] using he u
  have hpos : 0 < E.endpointCount u := by omega
  have hmissR : ∀ v ∈ R, ¬ (G ⊔ S.sup (SimpleGraph.edge u)).Adj u v := by
    intro v hv ha
    rcases ha with h | h
    · exact hmissing v (Finset.mem_union_right S hv) h
    · exact (Finset.disjoint_left.mp hdis
        ((star_sup_adj_off_center u S v u (fun h => huR (h ▸ hv))).mp h.symm).1 hv)
  have hpassR : ∀ v ∈ R,
      #{w ∈ (G ⊔ S.sup (SimpleGraph.edge u)).neighborFinset v |
        E.endpointCount w = 0} ≤ 1 := by
    intro v hv
    exact (D.passing_neighbors_mono_after_outward_star u S E he hpos v
      (fun h => huR (h ▸ hv))
      (fun h => Finset.disjoint_left.mp hdis h hv)).trans (hpR v hv)
  obtain ⟨Q, hQsize, hQ⟩ := E.outward_star_addibility u R 1 huR hmissR hpassR
    (by omega)
  have hg : G ⊔ (S ∪ R).sup (SimpleGraph.edge u) =
      (G ⊔ S.sup (SimpleGraph.edge u)) ⊔ R.sup (SimpleGraph.edge u) := by
    rw [Finset.sup_union, sup_assoc]
  rw [hg]
  refine ⟨Q, hQsize.trans hsize, ?_⟩
  intro v
  have h₁ := he v
  have h₂ := hQ v
  rw [Finset.card_union_of_disjoint hdis]
  have hn : ¬ (v ∈ S ∧ v ∈ R) := fun h => Finset.disjoint_left.mp hdis h.1 h.2
  by_cases huv : u = v <;> by_cases hvS : v ∈ S <;> by_cases hvR : v ∈ R <;>
    simp only [Finset.mem_union, huv, hvS, hvR, if_true, if_false, true_or, or_true,
      false_or, true_and, false_and, not_true_eq_false, Nat.add_zero] at hn h₁ h₂ ⊢ <;>
      omega

end Gallai.Decomposition
