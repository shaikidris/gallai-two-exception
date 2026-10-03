/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.Inputs.MatchingRestore
public import Gallai.Inputs.MatchingPuncture
public import Gallai.Foundations.EndpointBounds

@[expose] public section

/-! # Restore a spoke and the opposite triangle edge -/

namespace Gallai

open scoped Finset

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- A supplied reserve at u restores ua and bc at unchanged count. The reserve
is consumed at u; all passing-neighbour conditions are derived from the graph. -/
theorem Decomposition.restore_partial_triangle (u a b c : V)
    (hd : [u, a, b, c].Nodup)
    (hua : G.Adj u a) (hbc : G.Adj b c)
    (hea : Even (G.degree a)) (heb : Even (G.degree b)) (hec : Even (G.degree c))
    (hNa : ∀ w, G.Adj a w → Even (G.degree w) → w = b ∨ w = c)
    (hNc : ∀ w, G.Adj c w → Even (G.degree w) → w = a ∨ w = b)
    (hnuc : ¬ G.Adj u c)
    (D : Decomposition (G \ (SimpleGraph.edge u a ⊔ SimpleGraph.edge b c)))
    (hDu : 0 < D.endpointCount u) :
    ∃ E : Decomposition G, E.size = D.size := by
  classical
  let F := SimpleGraph.edge u a ⊔ SimpleGraph.edge b c
  let H := G \ F
  have huaN : u ≠ a := by simp_all
  have hub : u ≠ b := by simp_all
  have huc : u ≠ c := by simp_all
  have hab : a ≠ b := by simp_all
  have hac : a ≠ c := by simp_all
  have hbcN : b ≠ c := by simp_all
  have hle : F ≤ G := sup_le ((SimpleGraph.edge_le_iff G).mpr (Or.inr hua))
    ((SimpleGraph.edge_le_iff G).mpr (Or.inr hbc))
  have hfua : F.Adj u a := Or.inl
    ((SimpleGraph.edge_adj ..).mpr ⟨Or.inl ⟨rfl, rfl⟩, huaN⟩)
  have hfbc : F.Adj b c := Or.inr
    ((SimpleGraph.edge_adj ..).mpr ⟨Or.inl ⟨rfl, rfl⟩, hbcN⟩)
  have hm : ∀ w, F.degree w ≤ 1 := by
    intro w
    rw [← SimpleGraph.card_neighborFinset_eq_degree]
    apply Finset.card_le_one.mpr
    intro p hp q hq
    have hp := (F.mem_neighborFinset w p).mp hp
    have hq := (F.mem_neighborFinset w q).mp hq
    change (SimpleGraph.edge u a).Adj w p ∨ (SimpleGraph.edge b c).Adj w p at hp
    rcases hp with hp | hp <;>
      rcases (SimpleGraph.edge_adj ..).mp hp with ⟨⟨rfl, rfl⟩ | ⟨rfl, rfl⟩, _⟩ <;>
      simp_all [F, SimpleGraph.edge_adj] <;> aesop
  have hactive (w : V) (hw : 0 < F.degree w) : w = u ∨ w = a ∨ w = b ∨ w = c := by
    obtain ⟨t, ht⟩ := (F.degree_pos_iff_exists_adj w).mp hw
    change (SimpleGraph.edge u a).Adj w t ∨ (SimpleGraph.edge b c).Adj w t at ht
    rcases ht with ht | ht <;>
      rcases (SimpleGraph.edge_adj ..).mp ht with ⟨⟨rfl, rfl⟩ | ⟨rfl, rfl⟩, _⟩ <;> simp
  have hodd (w : V) (he : Even (G.degree w)) (hp : 0 < F.degree w) :
      Odd (H.degree w) := by
    have hc := degree_sdiff_add_of_le hle w
    have hm := hm w
    rw [Nat.even_iff] at he
    rw [Nat.odd_iff]
    change H.degree w + F.degree w = G.degree w at hc
    omega
  have haOdd := hodd a hea hfua.degree_pos_right
  have hbOdd := hodd b heb hfbc.degree_pos_left
  have hcOdd := hodd c hec hfbc.degree_pos_right
  have hkeep (w : V) (hwu : w ≠ u) (hw : Even (H.degree w)) : Even (G.degree w) := by
    by_cases hp : 0 < F.degree w
    · rcases hactive w hp with rfl | rfl | rfl | rfl
      · exact (hwu rfl).elim
      · exact hea
      · exact heb
      · exact hec
    have hc := degree_sdiff_add_of_le hle w
    rw [Nat.even_iff] at hw ⊢
    change H.degree w + F.degree w = G.degree w at hc
    omega
  have hp (t : V) (hn : ¬ H.Adj t u)
      (hNt : ∀ w, G.Adj t w → Even (G.degree w) → w = a ∨ w = b ∨ w = c) :
      #{w ∈ H.neighborFinset t | D.endpointCount w = 0} = 0 := by
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro w hw
    obtain ⟨ha, hz⟩ := Finset.mem_filter.mp hw
    have ha := (H.mem_neighborFinset t w).mp ha
    have hwu : w ≠ u := fun h => hn (h ▸ ha)
    have hv := D.endpointCount_mod_two w
    have he : Even (H.degree w) := by
      rw [Nat.even_iff]
      simp only [SimpleGraph.degree, SimpleGraph.neighborFinset,
        ← Set.ncard_eq_toFinset_card', H, F] at hv ⊢
      omega
    rcases hNt w ha.1 (hkeep w hwu he) with rfl | rfl | rfl
    · exact Nat.not_even_iff_odd.mpr haOdd he
    · exact Nat.not_even_iff_odd.mpr hbOdd he
    · exact Nat.not_even_iff_odd.mpr hcOdd he
  have hpa := hp a (fun h => h.2 hfua.symm)
    (fun w hw he => (hNa w hw he).elim (fun h => Or.inr (Or.inl h)) (fun h => Or.inr (Or.inr h)))
  have hpc := hp c (fun h => hnuc h.1.symm)
    (fun w hw he => (hNc w hw he).elim Or.inl (fun h => Or.inr (Or.inl h)))
  obtain ⟨D1, hs1, he1⟩ := D.single_edge_addibility (G := H) a u huaN.symm
    (fun h => h.2 hfua.symm) (by omega)
  have hpc1 := D.passing_neighbors_mono_of_donor_not_adj (G := H) a u c D1
    hac.symm huc.symm he1 (fun h => hnuc h.1.symm)
  have hbPos := D.endpointCount_pos_of_odd_degree b hbOdd
  have hb1 : D1.endpointCount b = D.endpointCount b := by
    simpa [hub, hab] using he1 b
  have hmissing : ¬ (H ⊔ SimpleGraph.edge a u).Adj c b := by
    rintro (h | h)
    · exact h.2 hfbc.symm
    · rcases (SimpleGraph.edge_adj ..).mp h with ⟨h | h, _⟩
      · exact hac.symm h.1
      · exact huc.symm h.1
  obtain ⟨D2, hs2, _⟩ := D1.single_edge_addibility (G := H ⊔ SimpleGraph.edge a u)
    c b hbcN.symm hmissing (by omega)
  have hg : (H ⊔ SimpleGraph.edge a u) ⊔ SimpleGraph.edge c b = G := by
    rw [SimpleGraph.edge_comm a u, SimpleGraph.edge_comm c b, sup_assoc]
    exact sdiff_sup_cancel hle
  have hout : ∃ E : Decomposition ((H ⊔ SimpleGraph.edge a u) ⊔ SimpleGraph.edge c b),
      E.size = D.size := ⟨D2, hs2.trans hs1⟩
  rwa [hg] at hout

end Gallai
