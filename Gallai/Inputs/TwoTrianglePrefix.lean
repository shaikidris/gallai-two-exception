/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.Inputs.TwoTriangleFloor
public import Gallai.Inputs.MatchingRestore

@[expose] public section

/-! # Claim 10's three-edge restoration prefix -/

namespace Gallai

open scoped Finset

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Restore the partial right triangle and the hub edge. The endpoint reserve
at the left hub is constructed from the actual puncture decomposition. -/
theorem Decomposition.restore_two_triangle_prefix (leftFull : Bool) (f : Fin 8 ↪ V)
    (hle : twoTriangleDeletion leftFull false f ≤ G)
    (h0 : Odd (G.degree (f 0))) (h1 : Odd (G.degree (f 1)))
    (he : ∀ i : Fin 8, i ≠ 0 → i ≠ 1 → Even (G.degree (f i)))
    (hN : ∀ t : Fin 8, t = 0 ∨ t = 1 ∨ t = 6 → ∀ w,
      G.Adj (f t) w → Even (G.degree w) → ∃ i : Fin 8, f i = w)
    (hn07 : ¬ G.Adj (f 0) (f 7)) (hn17 : ¬ G.Adj (f 1) (f 7))
    (hn05 : ¬ G.Adj (f 0) (f 5))
    (D : Decomposition (G \ twoTriangleDeletion leftFull false f)) :
    ∃ E : Decomposition (((G \ twoTriangleDeletion leftFull false f) ⊔
      SimpleGraph.edge (f 6) (f 7)) ⊔ SimpleGraph.edge (f 1) (f 5) ⊔
      SimpleGraph.edge (f 0) (f 1)),
      E.size = D.size ∧ 2 ≤ E.endpointCount (f 0) := by
  classical
  let F := twoTriangleDeletion leftFull false f
  let H := G \ F
  have hne (i j : Fin 8) (h : i ≠ j) : f i ≠ f j := f.injective.ne h
  have hactive (i : Fin 8) : 0 < F.degree (f i) := by
    rw [twoTriangleDeletion_degree, twoTriangleTemplate_degree]
    cases leftFull <;> split_ifs <;> omega
  have hodd (i : Fin 8) : Odd (H.degree (f i)) :=
    twoTriangleDeletion_odd leftFull false f hle h0 h1 he (f i) (hactive i)
  have hpass (t : Fin 8) (ht : t = 0 ∨ t = 1 ∨ t = 6) :
      #{w ∈ H.neighborFinset (f t) | D.endpointCount w = 0} = 0 := by
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro w hw
    obtain ⟨ha, hz⟩ := Finset.mem_filter.mp hw
    have ha := (H.mem_neighborFinset (f t) w).mp ha
    have hp := D.endpointCount_mod_two w
    have hwEven : Even (H.degree w) := by
      rw [Nat.even_iff]
      simp only [SimpleGraph.degree, SimpleGraph.neighborFinset,
        ← Set.ncard_eq_toFinset_card', H, F] at hp ⊢
      omega
    by_cases hd : 0 < F.degree w
    · exact Nat.not_even_iff_odd.mpr
        (twoTriangleDeletion_odd leftFull false f hle h0 h1 he w hd) hwEven
    have hd0 : F.degree w = 0 := by omega
    have hdeg := degree_sdiff_add_of_le hle w
    have hwG : Even (G.degree w) := by
      rw [Nat.even_iff] at hwEven ⊢
      change H.degree w + F.degree w = G.degree w at hdeg
      omega
    obtain ⟨i, rfl⟩ := hN t ht w ha.1 hwG
    exact Nat.not_even_iff_odd.mpr (hodd i) hwEven
  have hp0 := hpass 0 (Or.inl rfl)
  have hp1 := hpass 1 (Or.inr (Or.inl rfl))
  have hp6 := hpass 6 (Or.inr (Or.inr rfl))
  have hpos (i : Fin 8) : 0 < D.endpointCount (f i) :=
    D.endpointCount_pos_of_odd_degree (f i) (hodd i)
  have hf67 : F.Adj (f 6) (f 7) := SimpleGraph.map_adj_apply.mpr
    (by cases leftFull <;> decide)
  have hf15 : F.Adj (f 1) (f 5) := SimpleGraph.map_adj_apply.mpr
    (twoTriangleTemplate_required leftFull false).2.2
  have hf01 : F.Adj (f 0) (f 1) := SimpleGraph.map_adj_apply.mpr
    (twoTriangleTemplate_required leftFull false).1
  have hm67 : ¬ H.Adj (f 6) (f 7) := fun h => h.2 hf67
  obtain ⟨D1, hs1, he1⟩ := D.single_edge_addibility (G := H)
    (f 6) (f 7) (hne 6 7 (by decide)) hm67 (by have := hpos 7; omega)
  have hp10 := D.passing_neighbors_mono_of_donor_not_adj (G := H)
    (f 6) (f 7) (f 0) D1 (hne 0 6 (by decide)) (hne 0 7 (by decide)) he1
    (fun h => hn07 h.1)
  have hp11 := D.passing_neighbors_mono_of_donor_not_adj (G := H)
    (f 6) (f 7) (f 1) D1 (hne 1 6 (by decide)) (hne 1 7 (by decide)) he1
    (fun h => hn17 h.1)
  have hD15 : D1.endpointCount (f 5) = D.endpointCount (f 5) := by
    simpa [hne 7 5 (by decide), hne 6 5 (by decide)] using he1 (f 5)
  have hD10 : D1.endpointCount (f 0) = D.endpointCount (f 0) := by
    simpa [hne 7 0 (by decide), hne 6 0 (by decide)] using he1 (f 0)
  have hm15 : ¬ (H ⊔ SimpleGraph.edge (f 6) (f 7)).Adj (f 1) (f 5) := by
    rintro (h | h)
    · exact h.2 hf15
    · rcases (SimpleGraph.edge_adj ..).mp h with ⟨h | h, _⟩
      · exact hne 1 6 (by decide) h.1
      · exact hne 1 7 (by decide) h.1
  obtain ⟨D2, hs2, he2⟩ := D1.single_edge_addibility
    (G := H ⊔ SimpleGraph.edge (f 6) (f 7))
    (f 1) (f 5) (hne 1 5 (by decide)) hm15 (by have := hpos 5; omega)
  have hn105 : ¬ (H ⊔ SimpleGraph.edge (f 6) (f 7)).Adj (f 0) (f 5) := by
    rintro (h | h)
    · exact hn05 h.1
    · rcases (SimpleGraph.edge_adj ..).mp h with ⟨h | h, _⟩
      · exact hne 0 6 (by decide) h.1
      · exact hne 0 7 (by decide) h.1
  have hp20 := D1.passing_neighbors_mono_of_donor_not_adj
    (G := H ⊔ SimpleGraph.edge (f 6) (f 7)) (f 1) (f 5) (f 0) D2
    (hne 0 1 (by decide)) (hne 0 5 (by decide)) he2 hn105
  have hD21 : D2.endpointCount (f 1) = D1.endpointCount (f 1) + 1 := by
    simpa [hne 5 1 (by decide)] using he2 (f 1)
  have hD20 : D2.endpointCount (f 0) = D1.endpointCount (f 0) := by
    simpa [hne 5 0 (by decide), hne 1 0 (by decide)] using he2 (f 0)
  have hm01 : ¬ ((H ⊔ SimpleGraph.edge (f 6) (f 7)) ⊔
      SimpleGraph.edge (f 1) (f 5)).Adj (f 0) (f 1) := by
    rintro ((h | h) | h)
    · exact h.2 hf01
    · rcases (SimpleGraph.edge_adj ..).mp h with ⟨h | h, _⟩
      · exact hne 0 6 (by decide) h.1
      · exact hne 0 7 (by decide) h.1
    · rcases (SimpleGraph.edge_adj ..).mp h with ⟨h | h, _⟩
      · exact hne 0 1 (by decide) h.1
      · exact hne 0 5 (by decide) h.1
  obtain ⟨D3, hs3, he3⟩ := D2.single_edge_addibility
    (G := (H ⊔ SimpleGraph.edge (f 6) (f 7)) ⊔ SimpleGraph.edge (f 1) (f 5))
    (f 0) (f 1) (hne 0 1 (by decide)) hm01 (by omega)
  refine ⟨D3, hs3.trans (hs2.trans hs1), ?_⟩
  have hD30 : D3.endpointCount (f 0) = D2.endpointCount (f 0) + 1 := by
    simpa [hne 1 0 (by decide)] using he3 (f 0)
  have := hpos 0
  omega

end Gallai
