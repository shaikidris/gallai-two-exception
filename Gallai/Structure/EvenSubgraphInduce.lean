/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.Structure.EvenSubgraph

@[expose] public section

/-! # Even-neighbour counts on the actual vertex set

Restricting to a set containing every active vertex removes only ambient
isolates. It preserves degrees and the complete even-neighbour incidence.
-/

namespace Gallai

universe u
variable {V : Type u} [Fintype V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
variable (S : Set V) [DecidablePred (· ∈ S)]

/-- A neighbour-closed vertex set preserves the complete even-neighbour finset.
Unlike whole-support restriction, this applies to an individual component. -/
theorem evenNeighbors_map_induce_of_closed
    (hs : ∀ v ∈ S, G.neighborSet v ⊆ S) (v : S) :
    (evenNeighbors (G.induce S) v).map (Function.Embedding.subtype _) =
      evenNeighbors G v.val := by
  ext w
  constructor
  · intro hw
    obtain ⟨q, hq, heq⟩ := Finset.mem_map.mp hw
    change q.val = w at heq
    subst w
    obtain ⟨ha, he⟩ := (mem_evenNeighbors v q).mp hq
    refine (mem_evenNeighbors v.val q.val).mpr ⟨ha, ?_⟩
    rwa [SimpleGraph.degree_induce_of_neighborSet_subset (hs q q.property)] at he
  · intro hw
    obtain ⟨ha, he⟩ := (mem_evenNeighbors v.val w).mp hw
    let q : S := ⟨w, hs v v.property ha⟩
    refine Finset.mem_map.mpr ⟨q, (mem_evenNeighbors v q).mpr ⟨ha, ?_⟩, rfl⟩
    rw [SimpleGraph.degree_induce_of_neighborSet_subset (hs q q.property)]
    exact he

/-- Restriction to a neighbour-closed set preserves each retained E-degree. -/
theorem eDegree_induce_of_closed (hs : ∀ v ∈ S, G.neighborSet v ⊆ S) (v : S) :
    eDegree (G.induce S) v = eDegree G v.val := by
  have h := congrArg Finset.card (evenNeighbors_map_induce_of_closed G S hs v)
  simpa only [Finset.card_map, eDegree] using h

/-- A neighbour-closed component inherits the ambient even-vertex degree cap. -/
theorem even_degree_cap_induce_of_closed (hs : ∀ v ∈ S, G.neighborSet v ⊆ S)
    (c : ℕ) (hc : ∀ v, Even (G.degree v) → eDegree G v ≤ c) :
    ∀ v, Even ((G.induce S).degree v) → eDegree (G.induce S) v ≤ c := by
  intro v hv
  rw [eDegree_induce_of_closed G S hs v]
  apply hc
  rwa [SimpleGraph.degree_induce_of_neighborSet_subset (hs v v.property)] at hv

/-- The even neighbours in the induced actual graph map exactly to the original
even neighbours when all active vertices are retained. -/
theorem evenNeighbors_map_induce_of_support_subset (hs : G.support ⊆ S) (v : S) :
    (evenNeighbors (G.induce S) v).map (Function.Embedding.subtype _) =
      evenNeighbors G v.val := by
  ext w
  constructor
  · intro hw
    obtain ⟨q, hq, rfl⟩ := Finset.mem_map.mp hw
    obtain ⟨ha, he⟩ := (mem_evenNeighbors v q).mp hq
    apply (mem_evenNeighbors v.val q.val).mpr
    refine ⟨ha, ?_⟩
    rwa [SimpleGraph.degree_induce_of_support_subset hs q] at he
  · intro hw
    obtain ⟨ha, he⟩ := (mem_evenNeighbors v.val w).mp hw
    have hwS : w ∈ S := hs ⟨v.val, ha.symm⟩
    let q : S := ⟨w, hwS⟩
    refine Finset.mem_map.mpr ⟨q, ?_, rfl⟩
    apply (mem_evenNeighbors v q).mpr
    refine ⟨ha, ?_⟩
    rw [SimpleGraph.degree_induce_of_support_subset hs q]
    exact he

/-- Removing only ambient isolates preserves the E-degree exactly. -/
theorem eDegree_induce_of_support_subset (hs : G.support ⊆ S) (v : S) :
    eDegree (G.induce S) v = eDegree G v.val := by
  have h := congrArg Finset.card (evenNeighbors_map_induce_of_support_subset G S hs v)
  simpa only [Finset.card_map, eDegree] using h

/-- The even-vertex E-degree cap descends to the actual induced graph. -/
theorem even_degree_cap_induce_of_support_subset (hs : G.support ⊆ S) (c : ℕ)
    (hcap : ∀ v, Even (G.degree v) → eDegree G v ≤ c) :
    ∀ v, Even ((G.induce S).degree v) → eDegree (G.induce S) v ≤ c := by
  intro v hv
  rw [eDegree_induce_of_support_subset G S hs v]
  apply hcap v.val
  rwa [SimpleGraph.degree_induce_of_support_subset hs v] at hv

end Gallai
