/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.Inputs.OneExceptionDesignatedZero
public import Gallai.Inputs.OneExceptionZeroCaps

@[expose] public section

/-! # Final redesignation and edge restoration for one-exception induction -/

namespace Gallai

open scoped Finset
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

/-- A strict minimum counterexample is impossible: delete an edge to an odd
neighbour, recurse at that newly even neighbour, and restore towards x. -/
theorem one_exception_minimal_false (G : SimpleGraph V)
    [DecidableRel G.Adj] (x : V) (hconn : G.Connected)
    (hxpos : 0 < G.degree x) (hxEven : Even (G.degree x))
    (hcap : ∀ v, Even (G.degree v) → v ≠ x → eDegree G v ≤ 3)
    (hnot : ¬ ∃ D : Decomposition G,
      D.size ≤ (Fintype.card V + 1) / 2 ∧ 2 ≤ D.endpointCount x)
    (hmin : ∀ (W : Type u) [Fintype W] [DecidableEq W]
      (J : SimpleGraph W) [DecidableRel J.Adj],
      J.edgeFinset.card < G.edgeFinset.card → J.Connected →
      ∀ y : W, 0 < J.degree y → Even (J.degree y) →
        (∀ v, Even (J.degree v) → v ≠ y → eDegree J v ≤ 3) →
        ∃ D : Decomposition J, D.size ≤ (Fintype.card W + 1) / 2 ∧
          2 ≤ D.endpointCount y) : False := by
  classical
  have hz := one_exception_designated_eDegree_zero G x hconn hxpos hxEven hcap hnot hmin
  have hc2 := one_exception_cap_two_of_designated_zero G x hconn hxpos hxEven hcap hnot hmin hz
  have hodd (v : V) (ha : G.Adj x v) : Odd (G.degree v) := by
    apply Nat.not_even_iff_odd.mp
    intro he
    have hp : 0 < eDegree G x := Finset.card_pos.mpr
      ⟨v, (mem_evenNeighbors x v).mpr ⟨ha, he⟩⟩
    omega
  obtain ⟨y, hxy⟩ := (G.degree_pos_iff_exists_adj x).mp hxpos
  let J := starPuncture G x {y}
  let : DecidableRel J.Adj := fun _ _ => Classical.propDecidable _
  have hxs : x ∉ ({y} : Finset V) := by simpa using hxy.ne
  have hcx := one_exception_delete_self_connected G x hconn hxpos hxEven hcap hnot hmin
  have hx2 : 2 ≤ G.degree x := by
    have he := hxEven
    rw [Nat.even_iff] at he
    omega
  have hcJ : J.Connected := by
    apply starPuncture_connected G x {y} hcx
    have hcard := Finset.card_erase_add_one ((G.mem_neighborFinset x y).mpr hxy)
    rw [G.card_neighborFinset_eq_degree] at hcard
    obtain ⟨t, ht⟩ := Finset.card_pos.mp (show 0 < #((G.neighborFinset x).erase y) by omega)
    obtain ⟨hty, ht⟩ := Finset.mem_erase.mp ht
    refine ⟨t, (G.mem_neighborFinset x t).mp ht, ?_⟩
    intro h
    exact hty (Finset.mem_singleton.mp ((star_sup_adj_center x {y} hxs t).mp h))
  have hdx : J.degree x + 1 = G.degree x := by
    have h := starPuncture_degree_center G x {y} hxs
      (Finset.singleton_subset_iff.mpr ((G.mem_neighborFinset x y).mpr hxy))
    simpa only [Finset.card_singleton, SimpleGraph.degree, SimpleGraph.neighborFinset,
      ← Set.ncard_eq_toFinset_card', J] using h
  have hxOdd : Odd (J.degree x) := by
    rw [Nat.even_iff] at hxEven
    rw [Nat.odd_iff]
    omega
  have hyEven : Even (J.degree y) := by
    have h := starPuncture_degree_leaf G x {y} y (by simp) hxy
    have ho := hodd y hxy
    rw [Nat.odd_iff] at ho
    rw [Nat.even_iff]
    change J.degree y + 1 = G.degree y at h
    omega
  have hdeg (v : V) (hvx : v ≠ x) (hvy : v ≠ y) : J.degree v = G.degree v := by
    simpa only [SimpleGraph.degree, SimpleGraph.neighborFinset,
      ← Set.ncard_eq_toFinset_card', J] using
      starPuncture_degree_other G x {y} v hvx (by simpa using hvy)
  have hcapJ (v : V) (hv : Even (J.degree v)) (hvy : v ≠ y) : eDegree J v ≤ 3 := by
    have hvx : v ≠ x := by
      intro h
      subst v
      exact Nat.not_even_iff_odd.mpr hxOdd hv
    have hev : Even (G.degree v) := by rwa [hdeg v hvx hvy] at hv
    have hs : evenNeighbors J v ⊆ insert y (evenNeighbors G v) := by
      intro w hw
      by_cases hwy : w = y
      · simp [hwy]
      obtain ⟨ha, he⟩ := (mem_evenNeighbors v w).mp hw
      have hwx : w ≠ x := by
        intro h
        subst w
        exact Nat.not_even_iff_odd.mpr hxOdd he
      apply Finset.mem_insert_of_mem
      refine (mem_evenNeighbors v w).mpr ⟨ha.1, ?_⟩
      rwa [hdeg w hwx hwy] at he
    have hcard := Finset.card_le_card hs
    have hi := Finset.card_insert_le y (evenNeighbors G v)
    have hb := hc2 v hev
    change #(evenNeighbors G v) ≤ 2 at hb
    change #(evenNeighbors J v) ≤ 3
    omega
  have hlt : J.edgeFinset.card < G.edgeFinset.card := by
    have hj : J < G := by
      refine lt_of_le_not_ge (fun _ _ h => h.1) ?_
      intro h
      exact starPuncture_missing G x {y} hxs y (by simp) (h hxy)
    have h := Finset.card_lt_card (SimpleGraph.edgeFinset_strict_mono hj)
    simpa only [SimpleGraph.edgeFinset, ← Set.ncard_eq_toFinset_card'] using h
  have : Nontrivial V := ⟨⟨x, y, hxy.ne⟩⟩
  obtain ⟨D, hd, he⟩ := hmin V J
    (by simpa only [SimpleGraph.edgeFinset, ← Set.ncard_eq_toFinset_card'] using hlt)
    hcJ y (hcJ.preconnected.degree_pos_of_nontrivial y) hyEven hcapJ
  have hpass : #{v ∈ J.neighborFinset x | D.endpointCount v = 0} = 0 := by
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro v hv
    obtain ⟨ha, hvzero⟩ := Finset.mem_filter.mp hv
    have ha := (J.mem_neighborFinset x v).mp ha
    have hvy : v ≠ y := by
      intro h
      subst v
      exact starPuncture_missing G x {y} hxs y (by simp) ha
    have ho : Odd (J.degree v) := by rw [hdeg v ha.ne.symm hvy]; exact hodd v ha.1
    have hp := D.endpointCount_pos_of_odd_degree v ho
    omega
  obtain ⟨P, hs, hp⟩ := D.single_edge_addibility x y hxy.ne
    (starPuncture_missing G x {y} hxs y (by simp)) (by rw [hpass]; omega)
  have hxD := D.endpointCount_pos_of_odd_degree x hxOdd
  have hxP : 2 ≤ P.endpointCount x := by
    have h : P.endpointCount x = D.endpointCount x + 1 := by simpa [hxy.ne.symm] using hp x
    omega
  have hg : J ⊔ SimpleGraph.edge x y = G := by
    simpa only [Finset.sup_singleton] using
      starPuncture_restore G x {y} (by intro v hv; simpa using (Finset.mem_singleton.mp hv) ▸ hxy)
  have hout : ∃ P : Decomposition (J ⊔ SimpleGraph.edge x y),
      P.size ≤ (Fintype.card V + 1) / 2 ∧ 2 ≤ P.endpointCount x := ⟨P, by omega, hxP⟩
  rw [hg] at hout
  exact hnot hout

end Gallai
