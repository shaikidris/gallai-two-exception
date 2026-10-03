/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.Inputs.ComponentModifiedDifficult

@[expose] public section

/-! # Local component labels for modified-star passing neighbours -/

namespace Gallai

open scoped Finset

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {u : V}

/-- Only the exceptional component acquires the new recipient spoke. -/
noncomputable def componentModifiedLocalLeaves
    (d : ∀ C : (evenSubgraph G).ConnectedComponent, ComponentDeletionChoice G u C)
    (C₀ : (evenSubgraph G).ConnectedComponent) (e : V × V)
    (C : (evenSubgraph G).ConnectedComponent) : Finset V := by
  classical
  exact if C = C₀ then componentExceptionalLeaves d C₀ e else (d C).leaves

/-- A locally witnessed opposite pair is in the actual global matching. -/
theorem componentDeletionPairs_mem_of_local
    (d : ∀ C : (evenSubgraph G).ConnectedComponent, ComponentDeletionChoice G u C)
    (C : (evenSubgraph G).ConnectedComponent) (e : V × V) (he : e ∈ (d C).pairs) :
    e ∈ componentDeletionPairs d := by
  classical
  exact Finset.mem_biUnion.mpr ⟨C, Finset.mem_univ C, he⟩

/-- Every enlarged local leaf stays in its actual even component. -/
theorem componentModifiedLocalLeaves_supported
    (d : ∀ C : (evenSubgraph G).ConnectedComponent, ComponentDeletionChoice G u C)
    (C₀ : (evenSubgraph G).ConnectedComponent) (e : V × V) (he : e ∈ (d C₀).pairs)
    (C : (evenSubgraph G).ConnectedComponent) (v : V)
    (hv : v ∈ componentModifiedLocalLeaves d C₀ e C) : v ∈ evenComponentVertices C := by
  classical
  by_cases h : C = C₀
  · subst C
    exact componentExceptionalLeaves_supported d C₀ e he v
      (by simpa [componentModifiedLocalLeaves] using hv)
  · exact ((d C).leaf_data v (by simpa [componentModifiedLocalLeaves, h] using hv)).2

/-- An enlarged global leaf is originally even. -/
theorem componentModifiedLeaves_even
    (d : ∀ C : (evenSubgraph G).ConnectedComponent, ComponentDeletionChoice G u C)
    (e : V × V) (he : e ∈ componentDeletionPairs d) (v : V)
    (hv : v ∈ insert e.1 (componentDeletionLeaves d)) : Even (G.degree v) := by
  classical
  rcases Finset.mem_insert.mp hv with h | h
  · exact h ▸ (componentDeletionPairs_edge_data d e he).2.2.1
  · obtain ⟨C, _, hv⟩ := Finset.mem_biUnion.mp h
    exact even_of_mem_evenComponent C ((d C).leaf_data v hv).2

/-- Component membership localizes enlarged global leaves as well. -/
theorem componentModifiedLocalLeaves_of_global
    (d : ∀ C : (evenSubgraph G).ConnectedComponent, ComponentDeletionChoice G u C)
    (C₀ : (evenSubgraph G).ConnectedComponent) (e : V × V) (he : e ∈ (d C₀).pairs)
    (C : (evenSubgraph G).ConnectedComponent) (v : V)
    (hvC : v ∈ evenComponentVertices C)
    (hv : v ∈ insert e.1 (componentDeletionLeaves d)) :
    v ∈ componentModifiedLocalLeaves d C₀ e C := by
  classical
  by_cases hC : C = C₀
  · subst C
    simp only [componentModifiedLocalLeaves, if_true, componentExceptionalLeaves]
    rcases Finset.mem_insert.mp hv with h | h
    · exact Finset.mem_insert.mpr (Or.inl h)
    · exact Finset.mem_insert_of_mem (componentDeletionLeaves_local d C₀ v hvC h)
  · simp only [componentModifiedLocalLeaves, hC, if_false]
    rcases Finset.mem_insert.mp hv with h | h
    · exact (Set.disjoint_left.mp (evenComponentVertices_disjoint C C₀ hC)
        hvC (h ▸ ((d C₀).pair_data e he).2.2.1)).elim
    · exact componentDeletionLeaves_local d C v hvC h

/-- Each enlarged global leaf belongs to one of the modified local leaf sets. -/
theorem componentModifiedLocalLeaves_exists
    (d : ∀ C : (evenSubgraph G).ConnectedComponent, ComponentDeletionChoice G u C)
    (C₀ : (evenSubgraph G).ConnectedComponent) (e : V × V) (v : V)
    (hv : v ∈ insert e.1 (componentDeletionLeaves d)) :
    ∃ C, v ∈ componentModifiedLocalLeaves d C₀ e C := by
  classical
  rcases Finset.mem_insert.mp hv with h | h
  · refine ⟨C₀, ?_⟩
    simp [componentModifiedLocalLeaves, componentExceptionalLeaves, h]
  · obtain ⟨C, _, hv⟩ := Finset.mem_biUnion.mp h
    refine ⟨C, ?_⟩
    by_cases hC : C = C₀
    · subst C
      simp [componentModifiedLocalLeaves, componentExceptionalLeaves, hv]
    · simpa [componentModifiedLocalLeaves, hC] using hv

/-- Decision instance for modified puncture parity. -/
noncomputable local instance modifiedLocalAdj
    (d : ∀ C : (evenSubgraph G).ConnectedComponent, ComponentDeletionChoice G u C)
    (e : V × V) : DecidableRel (componentModifiedDeletion d e).Adj :=
  fun _ _ => Classical.propDecidable _

/-- All off-hub neighbours of local leaves are odd in the initial modified
puncture, with the sole possible exception of the untouched donor. -/
theorem componentModifiedLocalLeaves_neighbor_odd
    (d : ∀ C : (evenSubgraph G).ConnectedComponent, ComponentDeletionChoice G u C)
    (hu : Odd (G.degree u)) (C₀ : (evenSubgraph G).ConnectedComponent)
    (e : V × V) (he : e ∈ (d C₀).pairs) (ha : G.Adj u e.1)
    (C : (evenSubgraph G).ConnectedComponent) (v : V)
    (hv : v ∈ componentModifiedLocalLeaves d C₀ e C)
    (w : V) (hvw : G.Adj v w) (hwu : w ≠ u) (hwe : w ≠ e.2) :
    Odd ((G \ componentModifiedDeletion d e).degree w) := by
  classical
  have heg := componentDeletionPairs_mem_of_local d C₀ e he
  obtain ⟨ho, hk⟩ := componentModifiedDeletion_parity d hu e heg ha
  by_cases hwEven : Even (G.degree w)
  · have hwC := mem_evenComponent_of_adj C
      (componentModifiedLocalLeaves_supported d C₀ e he C v hv) hvw hwEven
    have hactive : ∃ t, (d C).graph.Adj w t := by
      by_cases hC : C = C₀
      · subst C
        exact (d C₀).pair_component_active e he w hwC
      · exact (d C).leaf_component_active hu v
          (by simpa [componentModifiedLocalLeaves, hC] using hv) w hwC
    obtain ⟨t, ht⟩ := hactive
    apply ho w hwu
    apply componentModifiedDeletion_active_of_old d e heg ha w hwe
    exact SimpleGraph.Adj.degree_pos_left
      ((Finset.le_sup (f := fun C => (d C).graph) (Finset.mem_univ C)) ht)
  · exact Nat.not_even_iff_odd.mp (fun h => hwEven (hk w hwu h))

end Gallai
