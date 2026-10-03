/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.Inputs.OneExceptionOddEDegree
public import Gallai.Inputs.PartialOddStarRestore
public import Gallai.Structure.PartialEvenStar

@[expose] public section

/-! # The designated E-degree is zero in a minimum counterexample

Retain one even-neighbour spoke and recurse at its leaf. The remaining odd
star restores inward/outward using cap three, before any global cap-two claim.
-/

namespace Gallai

open scoped Finset
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

/-- Designated E-degree zero, proved without assuming E-degree parity at its
neighbours. The retained even leaf supplies the missing endpoint input. -/
theorem one_exception_designated_eDegree_zero (G : SimpleGraph V)
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
          2 ≤ D.endpointCount y) : eDegree G x = 0 := by
  classical
  have hpar := one_exception_designated_eDegree_even G x hconn hxpos hxEven hcap hnot hmin
  by_contra hn
  obtain ⟨y, hy⟩ := Finset.card_pos.mp (show 0 < eDegree G x by omega)
  obtain ⟨hxy, hyEven⟩ := (mem_evenNeighbors x y).mp hy
  let S := (evenNeighbors G x).erase y
  let H := starPuncture G x S
  let : DecidableRel H.Adj := fun _ _ => Classical.propDecidable _
  have hS : S ⊆ evenNeighbors G x := Finset.erase_subset _ _
  have hxS : x ∉ S := fun h => (show x ∉ evenNeighbors G x by simp) (hS h)
  have hyS : y ∉ S := Finset.notMem_erase _ _
  have hcard : #S + 1 = eDegree G x := Finset.card_erase_add_one hy
  have ho : Odd #S := by
    rw [Nat.even_iff] at hpar
    rw [Nat.odd_iff]
    omega
  have hcdelete := one_exception_delete_self_connected G x hconn hxpos hxEven hcap hnot hmin
  have hretained : H.Adj x y := by
    refine ⟨hxy, ?_⟩
    intro h
    exact hyS ((star_sup_adj_center x S hxS y).mp h)
  have hcH : H.Connected := starPuncture_connected G x S hcdelete ⟨y, hretained⟩
  have hlt : H.edgeFinset.card < G.edgeFinset.card := by
    have hstrict : H < G := by
      refine lt_of_le_not_ge (fun _ _ h => h.1) ?_
      intro hle
      obtain ⟨v, hv⟩ := Finset.card_pos.mp ho.pos
      exact starPuncture_missing G x S hxS v hv
        (hle ((mem_evenNeighbors x v).mp (hS hv)).1)
    have h := Finset.card_lt_card (SimpleGraph.edgeFinset_strict_mono hstrict)
    simpa only [SimpleGraph.edgeFinset, ← Set.ncard_eq_toFinset_card'] using h
  have hdy : H.degree y = G.degree y := by
    simpa only [SimpleGraph.degree, SimpleGraph.neighborFinset,
      ← Set.ncard_eq_toFinset_card', H] using
      starPuncture_degree_other G x S y hxy.ne.symm hyS
  have hcapH : ∀ v, Even (H.degree v) → eDegree H v ≤ 3 :=
    partialEvenStar_cap G x S hS hxEven ho hcap
  obtain ⟨D, hd, he⟩ := hmin V H
    (by simpa only [SimpleGraph.edgeFinset, ← Set.ncard_eq_toFinset_card'] using hlt)
    hcH y hretained.degree_pos_right
    (by rwa [hdy]) (fun v hv _ => hcapH v hv)
  have hDx : 0 < D.endpointCount x := by
    apply D.endpointCount_pos_of_odd_degree
    exact partialEvenStar_odd_center G x S hS hxEven ho
  have hneighbors (v : V) (hv : G.Adj x v) : 0 < D.endpointCount v := by
    by_cases hvy : v = y
    · subst v
      omega
    · apply D.endpointCount_pos_of_odd_degree
      exact retainedEvenStar_odd_neighbor G x y v hv hvy
  have hleafcap (v : V) (hv : v ∈ S) : #((evenNeighbors G v).erase x) ≤ 2 := by
    obtain ⟨ha, hev⟩ := (mem_evenNeighbors x v).mp (hS hv)
    have hm : x ∈ evenNeighbors G v := (mem_evenNeighbors v x).mpr ⟨ha.symm, hxEven⟩
    have heq := Finset.card_erase_add_one hm
    have hb := hcap v hev ha.ne.symm
    change #(evenNeighbors G v) ≤ 3 at hb
    omega
  obtain ⟨P, hs, hp, _⟩ := D.restore_partial_odd_even_star x S hS ho hleafcap hDx hneighbors
  exact hnot ⟨P, by omega, hp⟩

end Gallai
