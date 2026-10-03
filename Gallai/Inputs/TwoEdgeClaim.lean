/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.Inputs.EvenMatchingRestore
public import Gallai.Inputs.FanPunctureFloor

@[expose] public section

/-! # The four-vertex nontriangle reduction -/

namespace Gallai

open scoped Finset

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Four distinct even vertices in consecutive degree-two position yield a
reducible two-edge puncture. Extra same-side edges are allowed. -/
theorem two_edge_even_chain_contradiction (u a b c : V)
    (hua : u ≠ a) (hub : u ≠ b) (huc : u ≠ c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (huaE : G.Adj u a) (hbcE : G.Adj b c)
    (heu : Even (G.degree u)) (hea : Even (G.degree a))
    (heb : Even (G.degree b)) (hec : Even (G.degree c))
    (hNu : ∀ v, G.Adj u v → Even (G.degree v) → v = a ∨ v = b)
    (hNb : ∀ v, G.Adj b v → Even (G.degree v) → v = u ∨ v = c)
    (hconn : G.Connected) (hcap : ∀ v, Even (G.degree v) → eDegree G v ≤ 3)
    (hnot : ¬ HasPathBudget G (Fintype.card V / 2)) (hset : ¬ IsSET G)
    (hmin : ∀ (U : Set V) [DecidablePred (· ∈ U)]
      (J : SimpleGraph U) [DecidableRel J.Adj],
      J.edgeFinset.card < G.edgeFinset.card → J.Connected →
      (∀ v, Even (J.degree v) → eDegree J v ≤ 3) →
      HasPathBudget J (Fintype.card U / 2) ∨ IsSET J) : False := by
  classical
  let F := SimpleGraph.edge u a ⊔ SimpleGraph.edge b c
  let S : Finset (V × V) := {(u, a), (b, c)}
  have hau := hua.symm
  have hbu := hub.symm
  have hcu := huc.symm
  have hba := hab.symm
  have hca := hac.symm
  have hcb := hbc.symm
  have hF : F = S.sup (fun e => SimpleGraph.edge e.1 e.2) := by simp [F, S]
  have hle : F ≤ G := sup_le ((SimpleGraph.edge_le_iff G).mpr (Or.inr huaE))
    ((SimpleGraph.edge_le_iff G).mpr (Or.inr hbcE))
  have hfua : F.Adj u a := Or.inl ((SimpleGraph.edge_adj ..).mpr ⟨Or.inl ⟨rfl, rfl⟩, hua⟩)
  have hfbc : F.Adj b c := Or.inr ((SimpleGraph.edge_adj ..).mpr ⟨Or.inl ⟨rfl, rfl⟩, hbc⟩)
  have hm : ∀ v, F.degree v ≤ 1 := by
    intro v
    rw [← SimpleGraph.card_neighborFinset_eq_degree]
    apply Finset.card_le_one.mpr
    intro p hp q hq
    have hp := (F.mem_neighborFinset v p).mp hp
    have hq := (F.mem_neighborFinset v q).mp hq
    change (SimpleGraph.edge u a).Adj v p ∨ (SimpleGraph.edge b c).Adj v p at hp
    rcases hp with hp | hp <;>
      rcases (SimpleGraph.edge_adj ..).mp hp with ⟨⟨rfl, rfl⟩ | ⟨rfl, rfl⟩, _⟩ <;>
      simp_all [F, SimpleGraph.edge_adj]
  have he : ∀ v, 0 < F.degree v → Even (G.degree v) := by
    intro v hv
    obtain ⟨w, hw⟩ := (F.degree_pos_iff_exists_adj v).mp hv
    change (SimpleGraph.edge u a).Adj v w ∨ (SimpleGraph.edge b c).Adj v w at hw
    rcases hw with hw | hw <;>
      rcases (SimpleGraph.edge_adj ..).mp hw with ⟨⟨rfl, rfl⟩ | ⟨rfl, rfl⟩, _⟩ <;> assumption
  have hcrossu : ¬ G.Adj u c := by
    intro h
    rcases hNu c h hec with h | h
    · exact hac h.symm
    · exact hbc h.symm
  have hcrossb : ¬ G.Adj b a := by
    intro h
    rcases hNb a h hea with h | h
    · exact hua h.symm
    · exact hac h
  have hends : ∀ e ∈ S, e.1 ≠ e.2 := by
    intro e heS
    simp only [S, Finset.mem_insert, Finset.mem_singleton] at heS
    rcases heS with rfl | rfl <;> assumption
  have hsep : ∀ e ∈ S, ∀ f ∈ S, e ≠ f →
      e.1 ≠ f.1 ∧ e.1 ≠ f.2 ∧ e.2 ≠ f.1 ∧ e.2 ≠ f.2 := by
    intro e heS f hfS hef
    simp only [S, Finset.mem_insert, Finset.mem_singleton] at heS hfS
    rcases heS with rfl | rfl <;> rcases hfS with rfl | rfl <;> simp_all
  have hcross : ∀ e ∈ S, ∀ f ∈ S, e ≠ f → ¬ G.Adj e.1 f.2 := by
    intro e heS f hfS hef
    simp only [S, Finset.mem_insert, Finset.mem_singleton] at heS hfS
    rcases heS with rfl | rfl <;> rcases hfS with rfl | rfl <;> simp_all
  have hcover : ∀ e ∈ S, ∀ v, G.Adj e.1 v → Even (G.degree v) → 0 < F.degree v := by
    intro e heS v hv hev
    simp only [S, Finset.mem_insert, Finset.mem_singleton] at heS
    rcases heS with rfl | rfl
    · rcases hNu v hv hev with rfl | rfl
      · exact hfua.degree_pos_right
      · exact hfbc.degree_pos_left
    · rcases hNb v hv hev with rfl | rfl
      · exact hfua.degree_pos_left
      · exact hfbc.degree_pos_right
  obtain ⟨D, hD⟩ := matching_puncture_floor hle ⟨u, a, hfua⟩ hm he
    hconn hcap hnot hset hmin
  obtain ⟨P, hP⟩ := D.restore_even_matching S hF hle hm he hends hsep hcross hcover
  exact hnot ⟨P, hP.le.trans hD⟩

end Gallai
