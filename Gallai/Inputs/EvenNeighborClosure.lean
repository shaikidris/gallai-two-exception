/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.Inputs.TwoEdgeClaim
public import Gallai.Inputs.ThreeSpokeClaim

@[expose] public section

/-! # Closing the even-neighbour pair in a minimal counterexample -/

namespace Gallai

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Two known distinct even neighbours exhaust an E-degree-two neighbourhood. -/
theorem even_neighbors_pair_of_degree_two (u a b : V) (hd : eDegree G u = 2)
    (ha : a ∈ evenNeighbors G u) (hb : b ∈ evenNeighbors G u) (hab : a ≠ b) :
    ∀ v, G.Adj u v → Even (G.degree v) → v = a ∨ v = b := by
  classical
  have hs : ({a, b} : Finset V) = evenNeighbors G u := by
    apply Finset.eq_of_subset_of_card_le
    · simpa only [Finset.insert_subset_iff, Finset.singleton_subset_iff] using And.intro ha hb
    · simpa [hab, eDegree] using hd.le
  intro v hv he
  have hm := (mem_evenNeighbors u v).mpr ⟨hv, he⟩
  simpa only [← hs, Finset.mem_insert, Finset.mem_singleton] using hm

/-- Distinct even neighbours of an even vertex must be adjacent under guarded
minimality. The second deleted edge and all four distinct vertices are derived. -/
theorem minimal_counterexample_even_neighbor_clique
    (hconn : G.Connected) (hcap : ∀ v, Even (G.degree v) → eDegree G v ≤ 3)
    (hnot : ¬ HasPathBudget G (Fintype.card V / 2)) (hset : ¬ IsSET G)
    (hmin : ∀ (U : Set V) [DecidablePred (· ∈ U)]
      (J : SimpleGraph U) [DecidableRel J.Adj],
      J.edgeFinset.card < G.edgeFinset.card → J.Connected →
      (∀ v, Even (J.degree v) → eDegree J v ≤ 3) →
      HasPathBudget J (Fintype.card U / 2) ∨ IsSET J)
    (u a b : V) (hu : Even (G.degree u))
    (ha : a ∈ evenNeighbors G u) (hb : b ∈ evenNeighbors G u) (hab : a ≠ b) :
    G.Adj a b := by
  classical
  by_contra hn
  obtain ⟨hua, hea⟩ := (mem_evenNeighbors u a).mp ha
  obtain ⟨hub, heb⟩ := (mem_evenNeighbors u b).mp hb
  have hdu : eDegree G u = 2 := by
    rcases minimal_counterexample_even_eDegree_zero_or_two hconn hcap hnot hset hmin u hu
      with h | h
    · have hp := Finset.card_pos.mpr ⟨a, ha⟩
      change 0 < eDegree G u at hp
      omega
    · exact h
  have hbu : u ∈ evenNeighbors G b := (mem_evenNeighbors b u).mpr ⟨hub.symm, hu⟩
  have hdb : eDegree G b = 2 := by
    rcases minimal_counterexample_even_eDegree_zero_or_two hconn hcap hnot hset hmin b heb
      with h | h
    · have hp := Finset.card_pos.mpr ⟨u, hbu⟩
      change 0 < eDegree G b at hp
      omega
    · exact h
  have hc : 0 < ((evenNeighbors G b).erase u).card := by
    have hh := Finset.card_erase_add_one hbu
    change (evenNeighbors G b).card = 2 at hdb
    omega
  obtain ⟨c, hc⟩ := Finset.card_pos.mp hc
  obtain ⟨hcu, hc⟩ := Finset.mem_erase.mp hc
  obtain ⟨hbc, hec⟩ := (mem_evenNeighbors b c).mp hc
  have hac : a ≠ c := by
    intro h
    subst c
    exact hn hbc.symm
  exact two_edge_even_chain_contradiction u a b c hua.ne hub.ne hcu.symm hab hac hbc.ne
    hua hbc hu hea heb hec
    (even_neighbors_pair_of_degree_two u a b hdu ha hb hab)
    (even_neighbors_pair_of_degree_two b u c hdb hbu hc hcu.symm)
    hconn hcap hnot hset hmin

end Gallai
