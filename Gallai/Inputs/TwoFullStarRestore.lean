/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.Inputs.ThreeSpokeRestore

@[expose] public section

/-! # Same-budget restoration of two full even-neighbour stars -/

namespace Gallai

open scoped Finset

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Use the same classical adjacency decision throughout nested punctures. -/
noncomputable local instance twoFullStarAdj (A : SimpleGraph V) (u : V) (B : Finset V) :
    DecidableRel (starPuncture A u B).Adj := fun _ _ => Classical.propDecidable _

/-- Restore both three-spoke stars and their hub edge. The intermediate
even hub supplies its own endpoint reserve; none is assumed of the input. -/
theorem Decomposition.restore_two_full_stars (u v : V)
    (hu : Odd (G.degree u)) (hv : Odd (G.degree v)) (huv : G.Adj u v)
    (hthreeU : eDegree G u = 3) (hthreeV : eDegree G v = 3)
    (hdisj : Disjoint (evenNeighbors G u) (evenNeighbors G v))
    (hcapU : ∀ w ∈ evenNeighbors G u, eDegree G w ≤ 2)
    (hcapV : ∀ w ∈ evenNeighbors G v, eDegree G w ≤ 2)
    (D : Decomposition (starPuncture
      (starPuncture (evenStarPuncture G v) u {v}) u (evenNeighbors G u))) :
    ∃ P : Decomposition G, P.size = D.size ∧ 2 ≤ P.endpointCount v := by
  classical
  let J := evenStarPuncture G v
  let K := starPuncture J u {v}
  have hune : u ≠ v := huv.ne
  have huT : u ∉ evenNeighbors G v := by
    intro h
    exact Nat.not_even_iff_odd.mpr hu ((mem_evenNeighbors v u).mp h).2
  have hvS : v ∉ evenNeighbors G u := by
    intro h
    exact Nat.not_even_iff_odd.mpr hv ((mem_evenNeighbors u v).mp h).2
  have hJuv : J.Adj u v := by
    refine ⟨huv, ?_⟩
    intro h
    exact huT ((star_sup_adj_center v (evenNeighbors G v) (by simp) u).mp h.symm)
  have hJle : J ≤ G := fun {_ _} h => h.1
  have hKle : K ≤ J := fun {_ _} h => h.1
  have hKu := starPuncture_degree_center J u {v} (by simp [hune])
    (by simpa only [Finset.singleton_subset_iff, SimpleGraph.mem_neighborFinset] using hJuv)
  have hJu : J.degree u = G.degree u :=
    starPuncture_degree_other G v (evenNeighbors G v) u hune huT
  have hKv := starPuncture_degree_leaf J u {v} v (by simp) hJuv
  have hJv := evenStarPuncture_degree_center G v
  have hKuEven : Even (K.degree u) := by
    rw [Nat.odd_iff] at hu
    rw [Nat.even_iff]
    simp only [Finset.card_singleton] at hKu
    change K.degree u + 1 = J.degree u at hKu
    omega
  have hKvOdd : Odd (K.degree v) := by
    rw [Nat.odd_iff] at hv ⊢
    change K.degree v + 1 = J.degree v at hKv
    change J.degree v + eDegree G v = G.degree v at hJv
    omega
  have hoff (w : V) (hwu : w ≠ u) (hwv : w ≠ v) :
      K.degree w = J.degree w :=
    starPuncture_degree_other J u {v} w hwu (by simpa using hwv)
  have hkeep (w : V) (hwu : w ≠ u) (he : Even (K.degree w)) :
      Even (G.degree w) ∧ w ∉ evenNeighbors G v := by
    have hwv : w ≠ v := by
      rintro rfl
      exact Nat.not_even_iff_odd.mpr hKvOdd he
    rw [hoff w hwu hwv] at he
    exact evenStarPuncture_even_off_center G v w hwv he
  have hS : evenNeighbors K u = evenNeighbors G u := by
    ext w
    constructor
    · intro hw
      obtain ⟨ha, he⟩ := (mem_evenNeighbors u w).mp hw
      exact (mem_evenNeighbors u w).mpr
        ⟨hJle (hKle ha), (hkeep w ha.ne.symm he).1⟩
    · intro hw
      obtain ⟨ha, he⟩ := (mem_evenNeighbors u w).mp hw
      have hwT : w ∉ evenNeighbors G v :=
        fun ht => Finset.disjoint_left.mp hdisj hw ht
      have hwv : w ≠ v := by rintro rfl; exact hvS hw
      have hJw : J.degree w = G.degree w :=
        starPuncture_degree_other G v (evenNeighbors G v) w hwv hwT
      have hKw : Even (K.degree w) := by rw [hoff w ha.ne.symm hwv, hJw]; exact he
      refine (mem_evenNeighbors u w).mpr ⟨⟨⟨ha, ?_⟩, ?_⟩, hKw⟩
      · rw [star_sup_adj_off_center v (evenNeighbors G v) u w hune]
        simp [huT]
      · rw [star_sup_adj_center u {v} (by simp [hune])]
        simpa using hwv
  have hKcap (w : V) (hw : w ∈ evenNeighbors K u) : eDegree K w ≤ 3 := by
    have hs : evenNeighbors K w ⊆ insert u (evenNeighbors G w) := by
      intro t ht
      by_cases htu : t = u
      · simp [htu]
      obtain ⟨ha, he⟩ := (mem_evenNeighbors w t).mp ht
      exact Finset.mem_insert_of_mem ((mem_evenNeighbors w t).mpr
        ⟨hJle (hKle ha), (hkeep t htu he).1⟩)
    have hb := hcapU w (hS ▸ hw)
    have hc := Finset.card_le_card hs
    have hi := Finset.card_insert_le u (evenNeighbors G w)
    change #(evenNeighbors K w) ≤ 3
    change #(evenNeighbors G w) ≤ 2 at hb
    omega
  have hthreeK : eDegree K u = 3 := by
    change #(evenNeighbors K u) = 3
    rw [hS]
    exact hthreeU
  have hcore : ∀ D' : Decomposition (starPuncture K u (evenNeighbors G u)),
      ∃ E : Decomposition K, E.size = D'.size ∧ 2 ≤ E.endpointCount u := by
    rw [← hS]
    intro D'
    exact D'.restore_three_even_spokes_exposing u hKuEven hthreeK hKcap
  obtain ⟨E, hE, hEu⟩ := hcore D
  have hpass : #{w ∈ K.neighborFinset v | E.endpointCount w = 0} = 0 := by
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro w hw
    obtain ⟨ha, hz⟩ := Finset.mem_filter.mp hw
    have ha := (K.mem_neighborFinset v w).mp ha
    have hwu : w ≠ u := by
      intro hwu
      have hh := ha
      rw [hwu] at hh
      exact starPuncture_missing J u {v} (by simp [hune]) v (by simp) hh.symm
    have ho : Odd (K.degree w) := by
      rw [hoff w hwu ha.ne.symm]
      exact evenStarPuncture_odd_neighbor G v w (hJle (hKle ha))
    have hp := E.endpointCount_pos_of_odd_degree w ho
    omega
  have hm : ¬ K.Adj v u :=
    fun h => starPuncture_missing J u {v} (by simp [hune]) v (by simp) h.symm
  obtain ⟨E1, hE1, hvec⟩ := E.single_edge_addibility (G := K)
    v u hune.symm hm (by omega)
  have hE1v : 0 < E1.endpointCount v := by
    have he := hvec v
    simp only [hune, if_false, if_true, Nat.add_zero] at he
    omega
  have hrestore : K ⊔ SimpleGraph.edge v u = J := by
    rw [SimpleGraph.edge_comm v u]
    simpa using starPuncture_restore J u {v} (by simpa using hJuv)
  have hout : ∃ E2 : Decomposition J, E2.size = D.size ∧ 0 < E2.endpointCount v := by
    have hh : ∃ E2 : Decomposition (K ⊔ SimpleGraph.edge v u),
        E2.size = D.size ∧ 0 < E2.endpointCount v :=
      ⟨E1, hE1.trans hE, hE1v⟩
    rwa [hrestore] at hh
  obtain ⟨E2, hE2, hE2v⟩ := hout
  obtain ⟨P, hP, hPv⟩ := E2.restore_three_even_spokes_of_leaf_cap_two
    v hthreeV hcapV hE2v
  exact ⟨P, hP.trans hE2, hPv⟩

end Gallai
