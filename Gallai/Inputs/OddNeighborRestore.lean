/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.Inputs.OddNeighborParity
public import Gallai.Inputs.MatchingRestore

@[expose] public section

/-! # Restoring the partial-triangle puncture at unchanged path count

The order is yz towards y, xu towards u, and uv towards v. Nonadjacency of
the spent donors preserves the remaining zero-passing conditions.
-/

namespace Gallai

open scoped Finset

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Every decomposition of the concrete puncture restores within the same
path count. All passing bounds are derived from original neighbourhoods. -/
theorem Decomposition.restore_odd_neighbor_puncture (u v x y z : V)
    (hd : [u, v, x, y, z].Nodup)
    (hle : oddNeighborDeletion u v x y z ≤ G)
    (hu : Odd (G.degree u)) (hv : Odd (G.degree v))
    (hx : Even (G.degree x)) (hy : Even (G.degree y)) (hz : Even (G.degree z))
    (hNu : ∀ w, G.Adj u w → Even (G.degree w) → w = x ∨ w = y)
    (hNv : ∀ w, G.Adj v w → ¬ Even (G.degree w))
    (hNy : ∀ w, G.Adj y w → Even (G.degree w) → w = x ∨ w = z)
    (D : Decomposition (G \ oddNeighborDeletion u v x y z)) :
    ∃ E : Decomposition G, E.size = D.size := by
  classical
  let H := G \ oddNeighborDeletion u v x y z
  have huv : u ≠ v := by simp_all
  have hux : u ≠ x := by simp_all
  have huy : u ≠ y := by simp_all
  have huz : u ≠ z := by simp_all
  have hvx : v ≠ x := by simp_all
  have hvy : v ≠ y := by simp_all
  have hvz : v ≠ z := by simp_all
  have hxy : x ≠ y := by simp_all
  have hxz : x ≠ z := by simp_all
  have hyz : y ≠ z := by simp_all
  obtain ⟨_, _, hx', _, hz', hk⟩ := oddNeighborDeletion_parity u v x y z hd hle hu hv hx hy hz
  obtain ⟨hcu, hcv⟩ := oddNeighborDeletion_centres u v x y z hd hle hu hv hx hy hz hNu hNv
  have hcy : ∀ w, H.Adj y w → ¬ Even (H.degree w) := by
    intro w hyw he
    have hwv : w ≠ v := by
      intro h
      subst w
      exact hNv y hyw.1.symm hy
    rcases hNy w hyw.1 (hk w hwv he) with rfl | rfl
    · exact Nat.not_even_iff_odd.mpr hx' he
    · exact Nat.not_even_iff_odd.mpr hz' he
  have hp (t : V) (hc : ∀ w, H.Adj t w → ¬ Even (H.degree w)) :
      #{w ∈ H.neighborFinset t | D.endpointCount w = 0} = 0 := by
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro w hw
    obtain ⟨ha, he⟩ := Finset.mem_filter.mp hw
    have hpos := D.endpointCount_pos_of_odd_degree w
      (Nat.not_even_iff_odd.mp (hc w ((H.mem_neighborFinset t w).mp ha)))
    omega
  have hpU := hp u hcu
  have hpV := hp v hcv
  have hpY := hp y hcy
  have hmYZ : ¬ H.Adj y z := by
    intro h
    exact h.2 (Or.inr ((SimpleGraph.edge_adj ..).mpr ⟨Or.inl ⟨rfl, rfl⟩, hyz⟩))
  have hDZ : 0 < D.endpointCount z := D.endpointCount_pos_of_odd_degree z hz'
  have hDX : 0 < D.endpointCount x := D.endpointCount_pos_of_odd_degree x hx'
  obtain ⟨D1, hs1, he1⟩ := D.single_edge_addibility (G := H) y z hyz hmYZ (by omega)
  have hnUZ : ¬ G.Adj u z := by
    intro h
    rcases hNu z h hz with h | h
    · exact hxz h.symm
    · exact hyz h.symm
  have hnVZ : ¬ G.Adj v z := fun h => hNv z h hz
  have hnVX : ¬ G.Adj v x := fun h => hNv x h hx
  have hp1U := D.passing_neighbors_mono_of_donor_not_adj (G := H) y z u D1 huy huz he1
    (fun h => hnUZ h.1)
  have hp1V := D.passing_neighbors_mono_of_donor_not_adj (G := H) y z v D1 hvy hvz he1
    (fun h => hnVZ h.1)
  have hD1X : D1.endpointCount x = D.endpointCount x := by
    simpa [hxz.symm, hxy.symm] using he1 x
  have hmUX : ¬ (H ⊔ SimpleGraph.edge y z).Adj u x := by
    rintro (h | h)
    · exact h.2 (Or.inl (Or.inr
        ((SimpleGraph.edge_adj ..).mpr ⟨Or.inl ⟨rfl, rfl⟩, hux⟩)))
    · rcases (SimpleGraph.edge_adj ..).mp h with ⟨h | h, _⟩
      · exact huy h.1
      · exact huz h.1
  obtain ⟨D2, hs2, he2⟩ := D1.single_edge_addibility (G := H ⊔ SimpleGraph.edge y z)
    u x hux hmUX (by omega)
  have hn1VX : ¬ (H ⊔ SimpleGraph.edge y z).Adj v x := by
    rintro (h | h)
    · exact hnVX h.1
    · rcases (SimpleGraph.edge_adj ..).mp h with ⟨h | h, _⟩
      · exact hvy h.1
      · exact hvz h.1
  have hp2V := D1.passing_neighbors_mono_of_donor_not_adj (G := H ⊔ SimpleGraph.edge y z)
    u x v D2 huv.symm hvx he2 hn1VX
  have hD2U : D2.endpointCount u = D1.endpointCount u + 1 := by
    simpa [hux.symm] using he2 u
  have hmVU : ¬ ((H ⊔ SimpleGraph.edge y z) ⊔ SimpleGraph.edge u x).Adj v u := by
    rintro ((h | h) | h)
    · exact h.2 (Or.inl (Or.inl
        ((SimpleGraph.edge_adj ..).mpr ⟨Or.inr ⟨rfl, rfl⟩, huv.symm⟩)))
    · rcases (SimpleGraph.edge_adj ..).mp h with ⟨h | h, _⟩
      · exact hvy h.1
      · exact hvz h.1
    · rcases (SimpleGraph.edge_adj ..).mp h with ⟨h | h, _⟩
      · exact huv.symm h.1
      · exact hvx h.1
  obtain ⟨D3, hs3, _⟩ := D2.single_edge_addibility
    (G := (H ⊔ SimpleGraph.edge y z) ⊔ SimpleGraph.edge u x) v u huv.symm hmVU (by omega)
  have hg : ((H ⊔ SimpleGraph.edge y z) ⊔ SimpleGraph.edge u x) ⊔
      SimpleGraph.edge v u = G := by
    rw [SimpleGraph.edge_comm v u]
    simpa only [H, oddNeighborDeletion, sup_assoc, sup_left_comm, sup_comm] using
      sdiff_sup_cancel hle
  have hout : ∃ E : Decomposition (((H ⊔ SimpleGraph.edge y z) ⊔
      SimpleGraph.edge u x) ⊔ SimpleGraph.edge v u), E.size = D.size :=
    ⟨D3, hs3.trans (hs2.trans hs1)⟩
  rwa [hg] at hout

end Gallai
