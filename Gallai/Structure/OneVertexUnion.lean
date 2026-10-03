/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.Structure.EvenSubgraph
public import Lean.Elab.Tactic.Omega

@[expose] public section

/-! # Parity inheritance at a single active intersection

Ambient isolates are not silently treated as vertices of a graph piece.
Evenness inheritance therefore requires positive degree, while E-degree
inheritance handles isolated vertices separately.
-/

namespace Gallai

universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G H : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel H.Adj]

/-- An isolated left vertex keeps its right degree in the union. -/
theorem degree_union_of_left_isolated (v : V) (hv : ∀ w, ¬ G.Adj v w) :
    (G ⊔ H).degree v = H.degree v := by
  have hzero : G.neighborFinset v = ∅ := by ext w; simp [hv w]
  rw [← SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.neighborFinset_sup, hzero]
  simp

/-- Under the favourable joint parity, positive-degree even vertices are inherited. -/
theorem even_positive_in_one_vertex_union (u v : V)
    (hmeet : ∀ w, (∃ a, G.Adj w a) → (∃ b, H.Adj w b) → w = u)
    (hparity : Even ((G ⊔ H).degree u) ∨ Odd (H.degree u))
    (hv : Even (H.degree v)) (hpos : ∃ w, H.Adj v w) :
    Even ((G ⊔ H).degree v) := by
  by_cases h : v = u
  · subst v
    rcases hparity with he | ho
    · exact he
    · exact (Nat.not_even_iff_odd.mpr ho hv).elim
  · have hi : ∀ w, ¬ G.Adj v w := fun w hw => h (hmeet v ⟨w, hw⟩ hpos)
    rw [degree_union_of_left_isolated G H v hi]
    exact hv

/-- Every even neighbour on the right remains even in the union. -/
theorem evenNeighbors_subset_one_vertex_union (u v : V)
    (hmeet : ∀ w, (∃ a, G.Adj w a) → (∃ b, H.Adj w b) → w = u)
    (hparity : Even ((G ⊔ H).degree u) ∨ Odd (H.degree u)) :
    evenNeighbors H v ⊆ evenNeighbors (G ⊔ H) v := by
  intro w hw
  obtain ⟨hadj, heven⟩ := (mem_evenNeighbors v w).mp hw
  exact (mem_evenNeighbors v w).mpr ⟨Or.inr hadj,
    even_positive_in_one_vertex_union G H u w hmeet hparity heven ⟨v, hadj.symm⟩⟩

/-- The right E-degree is bounded by the union E-degree, including at isolates. -/
theorem eDegree_le_one_vertex_union (u v : V)
    (hmeet : ∀ w, (∃ a, G.Adj w a) → (∃ b, H.Adj w b) → w = u)
    (hparity : Even ((G ⊔ H).degree u) ∨ Odd (H.degree u)) :
    eDegree H v ≤ eDegree (G ⊔ H) v :=
  Finset.card_le_card (evenNeighbors_subset_one_vertex_union G H u v hmeet hparity)

/-- The induced-even degree cap passes to the right piece under favourable joint parity. -/
theorem even_degree_cap_one_vertex_union (u : V) (c : ℕ)
    (hmeet : ∀ w, (∃ a, G.Adj w a) → (∃ b, H.Adj w b) → w = u)
    (hparity : Even ((G ⊔ H).degree u) ∨ Odd (H.degree u))
    (hcap : ∀ v, Even ((G ⊔ H).degree v) → eDegree (G ⊔ H) v ≤ c) :
    ∀ v, Even (H.degree v) → eDegree H v ≤ c := by
  intro v hv
  by_cases hp : ∃ w, H.Adj v w
  · exact (eDegree_le_one_vertex_union G H u v hmeet hparity).trans
      (hcap v (even_positive_in_one_vertex_union G H u v hmeet hparity hv hp))
  · have hn : H.neighborFinset v = ∅ := by
      ext w
      simp only [SimpleGraph.mem_neighborFinset, Finset.notMem_empty, iff_false]
      exact fun hw => hp ⟨w, hw⟩
    have hd : H.degree v = 0 := by
      rw [← H.card_neighborFinset_eq_degree, hn, Finset.card_empty]
    have he := eDegree_le_degree (G := H) v
    omega

omit [Fintype V] in
/-- Graph pieces meeting at one vertex have total order equal to their sum minus one. -/
theorem card_union_of_single_inter (S T : Finset V) (u : V) (hi : S ∩ T = {u}) :
    (S ∪ T).card + 1 = S.card + T.card := by
  have h := Finset.card_union_add_card_inter S T
  simpa only [hi, Finset.card_singleton] using h

/-- A hanging ceiling budget and a floor budget, saving one path, give the union floor. -/
theorem ceiling_floor_one_vertex_budget (a b n : ℕ)
    (hn : n + 1 = a + b) : (a + 1) / 2 + b / 2 - 1 ≤ n / 2 := by omega

/-- Two ceiling budgets, saving two paths, give the union floor. -/
theorem two_ceilings_one_vertex_budget (a b n : ℕ)
    (hn : n + 1 = a + b) : (a + 1) / 2 + (b + 1) / 2 - 2 ≤ n / 2 := by omega

end Gallai
