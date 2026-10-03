/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.Inputs.ComponentDifficultLeaves

@[expose] public section

/-! # Passing neighbours after actual matching and inward restoration

The initial puncture supplies every off-hub neighbour of a selected leaf.
The exact endpoint vector confines subsequent losses to restored leaves and
opposite donors, retaining the component containing each loss.
-/

namespace Gallai

open scoped Finset

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {u : V}

/-- Decision instance for the initial selected-edge puncture. -/
noncomputable local instance componentPassingUnionAdj
    (d : ∀ C : (evenSubgraph G).ConnectedComponent, ComponentDeletionChoice G u C) :
    DecidableRel (componentDeletionUnion d).Adj := fun _ _ => Classical.propDecidable _

/-- Every vertex of a component contributing a leaf is active in its deletion. -/
theorem ComponentDeletionChoice.leaf_component_active
    {C : (evenSubgraph G).ConnectedComponent} (d : ComponentDeletionChoice G u C)
    (hu : Odd (G.degree u)) (v : V) (hv : v ∈ d.leaves)
    (w : V) (hw : w ∈ evenComponentVertices C) : ∃ t, d.graph.Adj w t := by
  classical
  cases d with
  | untouched => simp [ComponentDeletionChoice.leaves] at hv
  | isolate a hC ha =>
    obtain ⟨t, ht, rfl⟩ := hw
    have ht : t = a := by simpa [hC] using ht
    subst t
    exact ⟨u, (SimpleGraph.edge_adj ..).mpr ⟨Or.inr ⟨rfl, rfl⟩, ha.ne.symm⟩⟩
  | triangle a b c hab hac hbc hC habE hacE hbcE hua ho =>
    let d' : ComponentDeletionChoice G u C :=
      .triangle a b c hab hac hbc hC habE hacE hbcE hua ho
    by_cases h : G.Adj u c
    · have huw : G.Adj u w := by
        obtain ⟨t, ht, rfl⟩ := hw
        rcases (hC t).mp ht with ht | ht | ht
        · exact ht ▸ hua
        · exact ht ▸ ho h
        · exact ht ▸ h
      have hp := d'.covers_neighbor hu w hw huw
      exact (d'.graph.degree_pos_iff_exists_adj w).mp hp
    · exact d'.pair_component_active ((b : V), (c : V))
        (by simp [d', ComponentDeletionChoice.pairs, h]) w hw

/-- An off-hub neighbour of a selected leaf is odd in the initial puncture. -/
theorem componentDeletionLeaves_neighbor_odd
    (d : ∀ C : (evenSubgraph G).ConnectedComponent, ComponentDeletionChoice G u C)
    (hu : Odd (G.degree u)) (v : V) (hv : v ∈ componentDeletionLeaves d)
    (w : V) (ha : G.Adj v w) (hwu : w ≠ u) :
    Odd ((G \ componentDeletionUnion d).degree w) := by
  classical
  obtain ⟨ho, hk⟩ := componentDeletionUnion_parity d hu
  by_cases he : Even (G.degree w)
  · obtain ⟨C, _, hv⟩ := Finset.mem_biUnion.mp hv
    have hw := mem_evenComponent_of_adj C ((d C).leaf_data v hv).2 ha he
    obtain ⟨t, ht⟩ := (d C).leaf_component_active hu v hv w hw
    apply ho w hwu
    exact SimpleGraph.Adj.degree_pos_left
      ((Finset.le_sup (f := fun C => (d C).graph) (Finset.mem_univ C)) ht)
  · exact Nat.not_even_iff_odd.mp (fun h => he (hk w hwu h))

/-- A global selected leaf in a given component belongs to its local leaf set. -/
theorem componentDeletionLeaves_local
    (d : ∀ C : (evenSubgraph G).ConnectedComponent, ComponentDeletionChoice G u C)
    (C : (evenSubgraph G).ConnectedComponent) (w : V)
    (hw : w ∈ evenComponentVertices C) (hs : w ∈ componentDeletionLeaves d) :
    w ∈ (d C).leaves := by
  classical
  obtain ⟨D, _, hs⟩ := Finset.mem_biUnion.mp hs
  by_cases h : D = C
  · subst D
    exact hs
  · exact (Set.disjoint_left.mp (evenComponentVertices_disjoint D C h)
      ((d D).leaf_data w hs).2 hw).elim

/-- The component of a donor determines the actual local opposite pair. -/
theorem componentDeletionPairs_local_of_snd
    (d : ∀ C : (evenSubgraph G).ConnectedComponent, ComponentDeletionChoice G u C)
    (C : (evenSubgraph G).ConnectedComponent) (e : V × V)
    (he : e ∈ componentDeletionPairs d) (hw : e.2 ∈ evenComponentVertices C) :
    e ∈ (d C).pairs := by
  classical
  obtain ⟨D, _, he⟩ := Finset.mem_biUnion.mp he
  by_cases h : D = C
  · subst D
    exact he
  · exact (Set.disjoint_left.mp (evenComponentVertices_disjoint D C h)
      ((d D).pair_data e he).2.2.2.1 hw).elim

/-- Exact endpoint accounting localizes every passing neighbour to a selected
leaf or an opposite donor in the same component. The hub is excluded by its
positive endpoint reserve. No passing-free carrier is assumed. -/
theorem Decomposition.component_passing_subset
    (d : ∀ C : (evenSubgraph G).ConnectedComponent, ComponentDeletionChoice G u C)
    (hu : Odd (G.degree u)) (D : Decomposition (G \ componentDeletionUnion d))
    {K : SimpleGraph V} [DecidableRel K.Adj] (hKG : K ≤ G) (Q : Decomposition K)
    (B : Finset V) (hB : B ⊆ componentDeletionLeaves d)
    (hqu : 0 < Q.endpointCount u)
    (hbal : ∀ w, Q.endpointCount w + (if w ∈ B then 1 else 0) +
        (∑ e ∈ componentDeletionPairs d, if e.2 = w then 1 else 0) =
      D.endpointCount w + (∑ e ∈ componentDeletionPairs d, if e.1 = w then 1 else 0) +
        if u = w then #B else 0)
    (C : (evenSubgraph G).ConnectedComponent) (v : V) (hv : v ∈ (d C).leaves) :
    {w ∈ K.neighborFinset v | Q.endpointCount w = 0} ⊆
      (((d C).leaves ∩ B) ∪ (d C).pairs.image Prod.snd).erase v := by
  classical
  have hvS : v ∈ componentDeletionLeaves d :=
    Finset.mem_biUnion.mpr ⟨C, Finset.mem_univ C, hv⟩
  intro w hw
  obtain ⟨ha, hz⟩ := Finset.mem_filter.mp hw
  have ha := (K.mem_neighborFinset v w).mp ha
  have hwu : w ≠ u := fun h => by subst w; omega
  have hp := D.endpointCount_pos_of_odd_degree w
    (componentDeletionLeaves_neighbor_odd d hu v hvS w (hKG ha) hwu)
  have hloss : w ∈ B ∨ ∃ e ∈ componentDeletionPairs d, e.2 = w := by
    by_cases hwB : w ∈ B
    · exact Or.inl hwB
    right
    by_contra hn
    have hs : (∑ e ∈ componentDeletionPairs d, if e.2 = w then 1 else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro e he
      have hew : e.2 ≠ w := fun h => hn ⟨e, he, h⟩
      simp [hew]
    have hb := hbal w
    simp only [hz, hwB, if_false, hs] at hb
    omega
  have heven : Even (G.degree w) := by
    rcases hloss with h | ⟨e, he, hew⟩
    · obtain ⟨E, _, hw⟩ := Finset.mem_biUnion.mp (hB h)
      exact even_of_mem_evenComponent E ((d E).leaf_data w hw).2
    · exact hew ▸ (componentDeletionPairs_edge_data d e he).2.2.2.1
  have hwC := mem_evenComponent_of_adj C ((d C).leaf_data v hv).2 (hKG ha) heven
  apply Finset.mem_erase.mpr
  refine ⟨ha.ne.symm, ?_⟩
  rcases hloss with h | ⟨e, he, hew⟩
  · exact Finset.mem_union_left _ (Finset.mem_inter.mpr
      ⟨componentDeletionLeaves_local d C w hwC (hB h), h⟩)
  · exact Finset.mem_union_right _ (Finset.mem_image.mpr
      ⟨e, componentDeletionPairs_local_of_snd d C e he (hew.symm ▸ hwC), hew⟩)

end Gallai
