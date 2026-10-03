/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
public import Mathlib.Data.Set.Card
public import Lean.Elab.Tactic.Omega

@[expose] public section

/-! # Complete components from local neighbour closure -/

namespace Gallai

variable {V : Type*} {K : SimpleGraph V}

/-- Closing each pair of neighbours makes reachable distinct vertices adjacent. -/
theorem reachable_eq_or_adj_of_neighbor_clique
    (hc : ∀ u a b, K.Adj u a → K.Adj u b → a ≠ b → K.Adj a b)
    {a b : V} (hr : K.Reachable a b) : a = b ∨ K.Adj a b := by
  obtain ⟨p⟩ := hr
  induction p with
  | nil => exact Or.inl rfl
  | @cons a b c hab p ih =>
    rcases ih with h | h
    · subst c
      exact Or.inr hab
    · by_cases he : a = c
      · exact Or.inl he
      · exact Or.inr (hc b a c hab.symm h he)

/-- Local neighbour closure implies literal completeness on every component. -/
theorem component_complete_of_neighbor_clique
    (hc : ∀ u a b, K.Adj u a → K.Adj u b → a ≠ b → K.Adj a b)
    (C : K.ConnectedComponent) : C.toSimpleGraph = ⊤ := by
  apply top_unique
  intro a b hab
  have hn : a.val ≠ b.val := fun h => hab (Subtype.ext h)
  exact (reachable_eq_or_adj_of_neighbor_clique hc
    (C.reachable_of_mem_supp a.property b.property)).resolve_left hn

variable [Fintype V] [DecidableEq V] [DecidableRel K.Adj]

/-- Complete components in a zero-or-two-degree graph have one or three vertices.
Both cardinality and completeness are retained for later structural consumers. -/
theorem components_singleton_or_triangle
    (hd : ∀ v, K.degree v = 0 ∨ K.degree v = 2)
    (hc : ∀ u a b, K.Adj u a → K.Adj u b → a ≠ b → K.Adj a b)
    (C : K.ConnectedComponent) :
    (C.supp.ncard = 1 ∨ C.supp.ncard = 3) ∧ C.toSimpleGraph = ⊤ := by
  classical
  have ht := component_complete_of_neighbor_clique hc C
  obtain ⟨v, hv⟩ := C.nonempty_supp
  let w : C.supp := ⟨v, hv⟩
  have hdeg : (K.induce C.supp).degree w = K.degree v :=
    K.degree_induce_of_neighborSet_subset
      (fun _ h => C.mem_supp_of_adj_mem_supp hv h)
  have ht' : K.induce C.supp = ⊤ := ht
  have htop : (K.induce C.supp).degree w = Fintype.card C.supp - 1 := by
    simp only [SimpleGraph.degree, SimpleGraph.neighborFinset,
      ← Set.ncard_eq_toFinset_card', ht']
    simpa only [SimpleGraph.degree, SimpleGraph.neighborFinset,
      ← Set.ncard_eq_toFinset_card'] using (SimpleGraph.complete_graph_degree w)
  have hcard : C.supp.ncard = Fintype.card C.supp := by
    rw [Set.ncard_eq_toFinset_card', Set.toFinset_card]
  have hpos : 0 < Fintype.card C.supp := Fintype.card_pos_iff.mpr ⟨w⟩
  have hvd := hd v
  refine ⟨?_, ht⟩
  omega

end Gallai
