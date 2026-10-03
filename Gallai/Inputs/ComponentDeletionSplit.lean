/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.Inputs.ComponentDeletionFloor
public import Mathlib.Data.Finset.Lattice.Union

@[expose] public section

/-! # Spokes and oriented opposite edges of the actual component puncture

Opposite edges are oriented from recipient to donor. Their separation follows
from actual even components, rather than a favourable matching assumption.
-/

namespace Gallai

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {u : V}

namespace ComponentDeletionChoice

variable {C : (evenSubgraph G).ConnectedComponent}

/-- Leaves whose hub spokes are removed by this choice. -/
def leaves : ComponentDeletionChoice G u C → Finset V
  | .untouched _ => ∅
  | .isolate a _ _ => {(a : V)}
  | .triangle a b c _ _ _ _ _ _ _ _ _ =>
    if G.Adj u c then {(a : V), (b : V), (c : V)} else {(a : V)}

/-- At most one opposite edge, oriented with the second endpoint as donor. -/
def pairs : ComponentDeletionChoice G u C → Finset (V × V)
  | .untouched _ => ∅
  | .isolate _ _ _ => ∅
  | .triangle _ b c _ _ _ _ _ _ _ _ _ => if G.Adj u c then ∅ else {((b : V), (c : V))}

/-- The partition used by opposite-edge restoration followed by star restoration. -/
theorem graph_eq_split (d : ComponentDeletionChoice G u C) :
    d.graph = d.leaves.sup (SimpleGraph.edge u) ⊔
      d.pairs.sup (fun e => SimpleGraph.edge e.1 e.2) := by
  cases d with
  | untouched => simp [graph, leaves, pairs]
  | isolate => simp [graph, leaves, pairs]
  | triangle a b c =>
    by_cases h : G.Adj u c <;>
      simp [graph, leaves, pairs, triangleHubDeletion, h, sup_assoc]

/-- Each selected spoke exists and its leaf belongs to its actual even component. -/
theorem leaf_data (d : ComponentDeletionChoice G u C) (v : V) (hv : v ∈ d.leaves) :
    G.Adj u v ∧ v ∈ evenComponentVertices C := by
  cases d with
  | untouched => simp [leaves] at hv
  | isolate a hC ha =>
    have he : v = a := by simpa [leaves] using hv
    subst v
    exact ⟨ha, a, by simp [hC], rfl⟩
  | triangle a b c hab hac hbc hC habE hacE hbcE hua ho =>
    by_cases h : G.Adj u c
    · simp only [leaves, h, if_true, Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl | rfl
      · exact ⟨hua, a, (hC a).mpr (Or.inl rfl), rfl⟩
      · exact ⟨ho h, b, (hC b).mpr (Or.inr (Or.inl rfl)), rfl⟩
      · exact ⟨h, c, (hC c).mpr (Or.inr (Or.inr rfl)), rfl⟩
    · have he : v = a := by simpa [leaves, h] using hv
      subst v
      exact ⟨hua, a, (hC a).mpr (Or.inl rfl), rfl⟩

omit [DecidableEq V] in
/-- Opposite endpoints are distinct even vertices in this component; the donor
is not a hub neighbour, including the two-neighbour triangle case. -/
theorem pair_data (d : ComponentDeletionChoice G u C) (e : V × V) (he : e ∈ d.pairs) :
    e.1 ≠ e.2 ∧ G.Adj e.1 e.2 ∧ e.1 ∈ evenComponentVertices C ∧
      e.2 ∈ evenComponentVertices C ∧ ¬ G.Adj u e.2 := by
  cases d with
  | untouched => simp [pairs] at he
  | isolate => simp [pairs] at he
  | triangle a b c hab hac hbc hC habE hacE hbcE hua ho =>
    by_cases h : G.Adj u c
    · simp [pairs, h] at he
    · have heq : e = ((b : V), (c : V)) := by simpa [pairs, h] using he
      subst e
      exact ⟨fun h => hbc (Subtype.ext h), hbcE,
        ⟨b, (hC b).mpr (Or.inr (Or.inl rfl)), rfl⟩,
        ⟨c, (hC c).mpr (Or.inr (Or.inr rfl)), rfl⟩, h⟩

omit [DecidableEq V] in
/-- A component contributes at most one oriented opposite edge. -/
theorem pair_unique (d : ComponentDeletionChoice G u C) (e f : V × V)
    (he : e ∈ d.pairs) (hf : f ∈ d.pairs) : e = f := by
  cases d with
  | untouched => simp [pairs] at he
  | isolate => simp [pairs] at he
  | triangle a b c =>
    by_cases h : G.Adj u c
    · simp [pairs, h] at he
    · have heq : e = ((b : V), (c : V)) := by simpa [pairs, h] using he
      have hfq : f = ((b : V), (c : V)) := by simpa [pairs, h] using hf
      exact heq.trans hfq.symm

end ComponentDeletionChoice

/-- All hub leaves selected by the actual component family. -/
noncomputable def componentDeletionLeaves
    (d : ∀ C : (evenSubgraph G).ConnectedComponent, ComponentDeletionChoice G u C) :
    Finset V := by
  classical
  exact Finset.univ.biUnion (fun C => (d C).leaves)

/-- All oriented opposite edges selected by the actual component family. -/
noncomputable def componentDeletionPairs
    (d : ∀ C : (evenSubgraph G).ConnectedComponent, ComponentDeletionChoice G u C) :
    Finset (V × V) := by
  classical
  exact Finset.univ.biUnion (fun C => (d C).pairs)

/-- The assembled puncture is exactly the selected star plus opposite matching. -/
theorem componentDeletionUnion_eq_split
    (d : ∀ C : (evenSubgraph G).ConnectedComponent, ComponentDeletionChoice G u C) :
    componentDeletionUnion d = (componentDeletionLeaves d).sup (SimpleGraph.edge u) ⊔
      (componentDeletionPairs d).sup (fun e => SimpleGraph.edge e.1 e.2) := by
  classical
  simp only [componentDeletionUnion, componentDeletionLeaves, componentDeletionPairs,
    Finset.sup_biUnion, ComponentDeletionChoice.graph_eq_split]
  exact Finset.sup_sup

/-- Distinct opposite pairs have all four endpoints separated. -/
theorem componentDeletionPairs_separated
    (d : ∀ C : (evenSubgraph G).ConnectedComponent, ComponentDeletionChoice G u C)
    (e : V × V) (he : e ∈ componentDeletionPairs d)
    (f : V × V) (hf : f ∈ componentDeletionPairs d) (hef : e ≠ f) :
    e.1 ≠ f.1 ∧ e.1 ≠ f.2 ∧ e.2 ≠ f.1 ∧ e.2 ≠ f.2 := by
  classical
  obtain ⟨C, _, he⟩ := Finset.mem_biUnion.mp he
  obtain ⟨D, _, hf⟩ := Finset.mem_biUnion.mp hf
  have hCD : C ≠ D := by
    rintro rfl
    exact hef ((d C).pair_unique e f he hf)
  have hd := Set.disjoint_left.mp (evenComponentVertices_disjoint C D hCD)
  have he' := (d C).pair_data e he
  have hf' := (d D).pair_data f hf
  exact ⟨fun h => hd he'.2.2.1 (h.symm ▸ hf'.2.2.1),
    fun h => hd he'.2.2.1 (h.symm ▸ hf'.2.2.2.1),
    fun h => hd he'.2.2.2.1 (h.symm ▸ hf'.2.2.1),
    fun h => hd he'.2.2.2.1 (h.symm ▸ hf'.2.2.2.1)⟩

/-- Distinct pairs have no recipient-to-donor edge in the original graph. -/
theorem componentDeletionPairs_cross_not_adj
    (d : ∀ C : (evenSubgraph G).ConnectedComponent, ComponentDeletionChoice G u C)
    (e : V × V) (he : e ∈ componentDeletionPairs d)
    (f : V × V) (hf : f ∈ componentDeletionPairs d) (hef : e ≠ f) :
    ¬ G.Adj e.1 f.2 := by
  classical
  obtain ⟨C, _, he⟩ := Finset.mem_biUnion.mp he
  obtain ⟨D, _, hf⟩ := Finset.mem_biUnion.mp hf
  have hCD : C ≠ D := by
    rintro rfl
    exact hef ((d C).pair_unique e f he hf)
  have he' := (d C).pair_data e he
  have hf' := (d D).pair_data f hf
  intro ha
  have hm := mem_evenComponent_of_adj C he'.2.2.1 ha
    (even_of_mem_evenComponent D hf'.2.2.2.1)
  exact Set.disjoint_left.mp (evenComponentVertices_disjoint C D hCD) hm hf'.2.2.2.1

end Gallai
