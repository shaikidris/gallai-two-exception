/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.Inputs.ComponentDeletionSplit
public import Gallai.Inputs.MatchingRestore
public import Gallai.Foundations.EndpointBounds

@[expose] public section

/-! # Parity-certified restoration of the actual opposite matching

The only extra case condition concerns the hub's parity or its adjacency to
recipients. No decomposition or passing-free choice is assumed.
-/

namespace Gallai

open scoped Finset

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {u : V}

/-- Decision instance for degrees in the actual deletion. -/
noncomputable local instance unionAdj
    (d : ∀ C : (evenSubgraph G).ConnectedComponent, ComponentDeletionChoice G u C) :
    DecidableRel (componentDeletionUnion d).Adj := fun _ _ => Classical.propDecidable _

omit [DecidableEq V] in
/-- Every vertex of a component with an opposite pair is incident with a
selected edge, including triangle vertices not adjacent to the hub. -/
theorem ComponentDeletionChoice.pair_component_active
    {C : (evenSubgraph G).ConnectedComponent} (d : ComponentDeletionChoice G u C)
    (e : V × V) (he : e ∈ d.pairs) (v : V) (hv : v ∈ evenComponentVertices C) :
    ∃ w, d.graph.Adj v w := by
  classical
  cases d with
  | untouched => simp [ComponentDeletionChoice.pairs] at he
  | isolate => simp [ComponentDeletionChoice.pairs] at he
  | triangle a b c hab hac hbc hC habE hacE hbcE hua ho =>
    by_cases h : G.Adj u c
    · simp [ComponentDeletionChoice.pairs, h] at he
    obtain ⟨t, ht, rfl⟩ := hv
    rcases (hC t).mp ht with hta | htb | htc
    · subst t
      refine ⟨u, ?_⟩
      change (triangleHubDeletion G u a b c).Adj a u
      simp only [triangleHubDeletion, h, if_false, SimpleGraph.sup_adj]
      exact Or.inl ((SimpleGraph.edge_adj ..).mpr ⟨Or.inr ⟨rfl, rfl⟩, hua.ne.symm⟩)
    · subst t
      refine ⟨c, ?_⟩
      change (triangleHubDeletion G u a b c).Adj b c
      simp only [triangleHubDeletion, h, if_false, SimpleGraph.sup_adj]
      exact Or.inr ((SimpleGraph.edge_adj ..).mpr ⟨Or.inl ⟨rfl, rfl⟩, hbcE.ne⟩)
    · subst t
      refine ⟨b, ?_⟩
      change (triangleHubDeletion G u a b c).Adj c b
      simp only [triangleHubDeletion, h, if_false, SimpleGraph.sup_adj]
      exact Or.inr ((SimpleGraph.edge_adj ..).mpr ⟨Or.inr ⟨rfl, rfl⟩, hbcE.ne.symm⟩)

/-- The actual family inherits off-hub parity without extra shape premises. -/
theorem componentDeletionUnion_parity
    (d : ∀ C : (evenSubgraph G).ConnectedComponent, ComponentDeletionChoice G u C)
    (hu : Odd (G.degree u)) :
    (∀ v, v ≠ u → 0 < (componentDeletionUnion d).degree v →
      Odd ((G \ componentDeletionUnion d).degree v)) ∧
    (∀ v, v ≠ u → Even ((G \ componentDeletionUnion d).degree v) → Even (G.degree v)) := by
  classical
  exact component_piece_puncture_parity Finset.univ (fun C => (d C).graph) u
    (fun C _ => (d C).graph_le) (fun C _ => (d C).supported hu)
    (fun C _ => (d C).degree_le_one hu)

/-- Every original even neighbour of an opposite recipient is active in the
actual deletion: it lies in that recipient's whole triangle component. -/
theorem componentDeletionPairs_neighbor_active
    (d : ∀ C : (evenSubgraph G).ConnectedComponent, ComponentDeletionChoice G u C)
    (e : V × V) (he : e ∈ componentDeletionPairs d)
    (v : V) (ha : G.Adj e.1 v) (hv : Even (G.degree v)) :
    0 < (componentDeletionUnion d).degree v := by
  classical
  obtain ⟨C, _, he⟩ := Finset.mem_biUnion.mp he
  have hm := mem_evenComponent_of_adj C ((d C).pair_data e he).2.2.1 ha hv
  obtain ⟨w, hw⟩ := (d C).pair_component_active e he v hm
  apply SimpleGraph.Adj.degree_pos_left (w := w)
  exact (Finset.le_sup (f := fun C => (d C).graph) (Finset.mem_univ C)) hw

/-- The oriented pair is an actual removed edge, and both endpoints are even. -/
theorem componentDeletionPairs_edge_data
    (d : ∀ C : (evenSubgraph G).ConnectedComponent, ComponentDeletionChoice G u C)
    (e : V × V) (he : e ∈ componentDeletionPairs d) :
    e.1 ≠ e.2 ∧ (componentDeletionUnion d).Adj e.1 e.2 ∧
      Even (G.degree e.1) ∧ Even (G.degree e.2) ∧ ¬ G.Adj u e.2 := by
  classical
  obtain ⟨C, _, he⟩ := Finset.mem_biUnion.mp he
  have hd := (d C).pair_data e he
  have ha : (d C).graph.Adj e.1 e.2 := by
    rw [(d C).graph_eq_split]
    exact Or.inr ((Finset.le_sup (f := fun e : V × V => SimpleGraph.edge e.1 e.2) he)
      ((SimpleGraph.edge_adj ..).mpr ⟨Or.inl ⟨rfl, rfl⟩, hd.1⟩))
  exact ⟨hd.1, (Finset.le_sup (f := fun C => (d C).graph) (Finset.mem_univ C)) ha,
    even_of_mem_evenComponent C hd.2.2.1,
    even_of_mem_evenComponent C hd.2.2.2.1, hd.2.2.2.2⟩

/-- In either source case, no neighbour of an opposite recipient is passing.
The assertion holds for every decomposition of the actual puncture. -/
theorem Decomposition.no_passing_component_pair
    (d : ∀ C : (evenSubgraph G).ConnectedComponent, ComponentDeletionChoice G u C)
    (hu : Odd (G.degree u)) (D : Decomposition (G \ componentDeletionUnion d))
    (e : V × V) (he : e ∈ componentDeletionPairs d)
    (hcase : ¬ G.Adj u e.1 ∨ Odd ((G \ componentDeletionUnion d).degree u)) :
    #{v ∈ (G \ componentDeletionUnion d).neighborFinset e.1 | D.endpointCount v = 0} = 0 := by
  classical
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro v hv
  obtain ⟨ha, hz⟩ := Finset.mem_filter.mp hv
  have ha := ((G \ componentDeletionUnion d).mem_neighborFinset e.1 v).mp ha
  have hp := D.endpointCount_mod_two v
  have hev : Even ((G \ componentDeletionUnion d).degree v) := by
    rw [Nat.even_iff]
    omega
  by_cases hvu : v = u
  · subst v
    rcases hcase with hn | ho
    · exact hn ha.1.symm
    · exact Nat.not_even_iff_odd.mpr ho hev
  · obtain ⟨ho, hk⟩ := componentDeletionUnion_parity d hu
    have hg := hk v hvu hev
    exact Nat.not_even_iff_odd.mpr
      (ho v hvu (componentDeletionPairs_neighbor_active d e he v ha.1 hg)) hev

/-- Restore every opposite edge with exact size and endpoint transfer, under
the explicit graph-side case condition, not a favourable-decomposition premise. -/
theorem Decomposition.restore_component_pairs
    (d : ∀ C : (evenSubgraph G).ConnectedComponent, ComponentDeletionChoice G u C)
    (hu : Odd (G.degree u)) (D : Decomposition (G \ componentDeletionUnion d))
    (hcase : (∀ e ∈ componentDeletionPairs d, ¬ G.Adj u e.1) ∨
      Odd ((G \ componentDeletionUnion d).degree u)) :
    ∃ E : Decomposition ((G \ componentDeletionUnion d) ⊔
        (componentDeletionPairs d).sup (fun e => SimpleGraph.edge e.1 e.2)),
      E.size = D.size ∧ ∀ v,
        E.endpointCount v + (∑ e ∈ componentDeletionPairs d, if e.2 = v then 1 else 0) =
          D.endpointCount v + ∑ e ∈ componentDeletionPairs d, if e.1 = v then 1 else 0 := by
  classical
  have hd := componentDeletionPairs_edge_data d
  apply D.matching_addibility (componentDeletionPairs d)
    (fun e he => (hd e he).1) (componentDeletionPairs_separated d)
  · intro e he ha
    exact ha.2 (hd e he).2.1
  · intro e he f hf hef ha
    exact componentDeletionPairs_cross_not_adj d e he f hf hef ha.1
  · intro e he
    apply D.no_passing_component_pair d hu e he
    exact hcase.imp (fun h => h e he) id
  · intro e he
    apply D.endpointCount_pos_of_odd_degree
    apply (componentDeletionUnion_parity d hu).1 e.2
    · intro h
      exact Nat.not_even_iff_odd.mpr hu (h ▸ (hd e he).2.2.2.1)
    · exact (hd e he).2.1.degree_pos_right

end Gallai
