/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.Inputs.ComponentHalfStar

@[expose] public section

/-! # Counting difficult residual leaves in actual full triangle components

Each difficult leaf charges two distinct selected spokes in its own component.
Disjoint actual components make these charges simultaneous.
-/

namespace Gallai

open scoped Finset

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {u : V}

namespace ComponentDeletionChoice

variable {C : (evenSubgraph G).ConnectedComponent}

/-- Every touched component contributes at least one selected spoke. -/
theorem leaves_nonempty_of_touched (d : ComponentDeletionChoice G u C)
    (ht : ∃ v : evenVertices G, v ∈ C.supp ∧ G.Adj u v) : d.leaves.Nonempty := by
  cases d with
  | untouched hn => exact (hn ht).elim
  | isolate a => exact ⟨a, Finset.mem_singleton_self _⟩
  | triangle a b c =>
    refine ⟨a, ?_⟩
    by_cases h : G.Adj u c <;> simp [leaves, h]

/-- A full three-spoke piece is difficult when exactly two spokes are restored. -/
def difficultLeaves (d : ComponentDeletionChoice G u C) (B : Finset V) : Finset V :=
  if #d.leaves = 3 ∧ #(d.leaves ∩ B) = 2 then d.leaves \ B else ∅

/-- Membership retains the full-piece and two-selected-spoke conditions. -/
theorem mem_difficultLeaves (d : ComponentDeletionChoice G u C) (B : Finset V) (v : V) :
    v ∈ d.difficultLeaves B ↔
      #d.leaves = 3 ∧ #(d.leaves ∩ B) = 2 ∧ v ∈ d.leaves ∧ v ∉ B := by
  unfold difficultLeaves
  split_ifs <;> simp_all [Finset.mem_sdiff]

/-- A difficult leaf is a still missing spoke in its component. -/
theorem difficultLeaves_subset (d : ComponentDeletionChoice G u C) (B : Finset V) :
    d.difficultLeaves B ⊆ d.leaves \ B := by
  intro v hv
  have h := (d.mem_difficultLeaves B v).mp hv
  exact Finset.mem_sdiff.mpr h.2.2

/-- Each active difficult piece contributes one leaf, charged to two selected spokes. -/
theorem difficultLeaves_charge (d : ComponentDeletionChoice G u C) (B : Finset V) :
    2 * #(d.difficultLeaves B) ≤ #(d.leaves ∩ B) := by
  unfold difficultLeaves
  split_ifs with h
  · have hc := Finset.card_sdiff_add_card_inter d.leaves B
    omega
  · simp

end ComponentDeletionChoice

/-- The graph's two touched components supply the reserve theorem's premise
for every actual choice family, not a specially selected family. -/
theorem componentDeletionLeaves_two_touched
    (d : ∀ C : (evenSubgraph G).ConnectedComponent, ComponentDeletionChoice G u C)
    (ht : ∃ C D : (evenSubgraph G).ConnectedComponent, C ≠ D ∧
      (∃ v : evenVertices G, v ∈ C.supp ∧ G.Adj u v) ∧
      (∃ v : evenVertices G, v ∈ D.supp ∧ G.Adj u v)) :
    ∃ C D : (evenSubgraph G).ConnectedComponent,
      C ≠ D ∧ (d C).leaves.Nonempty ∧ (d D).leaves.Nonempty := by
  obtain ⟨C, D, hCD, hC, hD⟩ := ht
  exact ⟨C, D, hCD, (d C).leaves_nonempty_of_touched hC,
    (d D).leaves_nonempty_of_touched hD⟩

/-- Leaf sets of different actual even components are disjoint. -/
theorem componentDeletionLeaves_disjoint
    (d : ∀ C : (evenSubgraph G).ConnectedComponent, ComponentDeletionChoice G u C)
    (C D : (evenSubgraph G).ConnectedComponent) (hCD : C ≠ D) :
    Disjoint (d C).leaves (d D).leaves := by
  apply Finset.disjoint_left.mpr
  intro v hv hw
  exact Set.disjoint_left.mp (evenComponentVertices_disjoint C D hCD)
    ((d C).leaf_data v hv).2 ((d D).leaf_data v hw).2

/-- The difficult group assembled from the actual component pieces. -/
noncomputable def componentDifficultLeaves
    (d : ∀ C : (evenSubgraph G).ConnectedComponent, ComponentDeletionChoice G u C)
    (B : Finset V) : Finset V := by
  classical
  exact Finset.univ.biUnion (fun C => (d C).difficultLeaves B)

/-- All difficult leaves lie in the remaining selected star. -/
theorem componentDifficultLeaves_subset
    (d : ∀ C : (evenSubgraph G).ConnectedComponent, ComponentDeletionChoice G u C)
    (B : Finset V) : componentDifficultLeaves d B ⊆ componentDeletionLeaves d \ B := by
  classical
  intro v hv
  obtain ⟨C, _, hv⟩ := Finset.mem_biUnion.mp hv
  obtain ⟨hv, hn⟩ := Finset.mem_sdiff.mp ((d C).difficultLeaves_subset B hv)
  exact Finset.mem_sdiff.mpr
    ⟨Finset.mem_biUnion.mpr ⟨C, Finset.mem_univ C, hv⟩, hn⟩

/-- The two selected spokes charged by every difficult leaf are disjoint
across actual components. Thus the global charge is at most the selected set. -/
theorem componentDifficultLeaves_charge
    (d : ∀ C : (evenSubgraph G).ConnectedComponent, ComponentDeletionChoice G u C)
    (B : Finset V) : 2 * #(componentDifficultLeaves d B) ≤ #B := by
  classical
  have hhard : ((Finset.univ : Finset (evenSubgraph G).ConnectedComponent) : Set _).PairwiseDisjoint
      (fun C => (d C).difficultLeaves B) := by
    intro C _ D _ hCD
    apply Finset.disjoint_left.mpr
    intro v hv hw
    exact Finset.disjoint_left.mp (componentDeletionLeaves_disjoint d C D hCD)
      (Finset.mem_sdiff.mp ((d C).difficultLeaves_subset B hv)).1
      (Finset.mem_sdiff.mp ((d D).difficultLeaves_subset B hw)).1
  have hsel : ((Finset.univ : Finset (evenSubgraph G).ConnectedComponent) : Set _).PairwiseDisjoint
      (fun C => (d C).leaves ∩ B) := by
    intro C _ D _ hCD
    apply Finset.disjoint_left.mpr
    intro v hv hw
    exact Finset.disjoint_left.mp (componentDeletionLeaves_disjoint d C D hCD)
      (Finset.mem_inter.mp hv).1 (Finset.mem_inter.mp hw).1
  calc
    2 * #(componentDifficultLeaves d B) =
        ∑ C : (evenSubgraph G).ConnectedComponent, 2 * #((d C).difficultLeaves B) := by
      rw [componentDifficultLeaves, Finset.card_biUnion hhard, Finset.mul_sum]
    _ ≤ ∑ C : (evenSubgraph G).ConnectedComponent, #((d C).leaves ∩ B) :=
      Finset.sum_le_sum (fun C _ => (d C).difficultLeaves_charge B)
    _ = #(Finset.univ.biUnion (fun C => (d C).leaves ∩ B)) :=
      (Finset.card_biUnion hsel).symm
    _ ≤ #B := by
      apply Finset.card_le_card
      intro v hv
      obtain ⟨C, _, hv⟩ := Finset.mem_biUnion.mp hv
      exact (Finset.mem_inter.mp hv).2

/-- A difficult full triangle and any other touched component require at
least four selected-star leaves before the inward restoration. -/
theorem componentDifficultLeaves_four_le
    (d : ∀ C : (evenSubgraph G).ConnectedComponent, ComponentDeletionChoice G u C)
    (B : Finset V) (hh : (componentDifficultLeaves d B).Nonempty)
    (htwo : ∃ C D : (evenSubgraph G).ConnectedComponent,
      C ≠ D ∧ (d C).leaves.Nonempty ∧ (d D).leaves.Nonempty) :
    4 ≤ #(componentDeletionLeaves d) := by
  classical
  obtain ⟨v, hv⟩ := hh
  obtain ⟨C, _, hv⟩ := Finset.mem_biUnion.mp hv
  have hfull := ((d C).mem_difficultLeaves B v).mp hv
  obtain ⟨C₀, D₀, hne, hC₀, hD₀⟩ := htwo
  have hother : ∃ E : (evenSubgraph G).ConnectedComponent,
      E ≠ C ∧ (d E).leaves.Nonempty := by
    by_cases h : C₀ = C
    · subst C₀
      exact ⟨D₀, hne.symm, hD₀⟩
    · exact ⟨C₀, h, hC₀⟩
  obtain ⟨E, hEC, w, hw⟩ := hother
  have hwn : w ∉ (d C).leaves := fun h =>
    Finset.disjoint_left.mp (componentDeletionLeaves_disjoint d E C hEC) hw h
  have hs : insert w (d C).leaves ⊆ componentDeletionLeaves d := by
    apply Finset.insert_subset
    · exact Finset.mem_biUnion.mpr ⟨E, Finset.mem_univ E, hw⟩
    · intro t ht
      exact Finset.mem_biUnion.mpr ⟨C, Finset.mem_univ C, ht⟩
  have hc := Finset.card_le_card hs
  rw [Finset.card_insert_of_notMem hwn, hfull.1] at hc
  exact hc

/-- The inward count and strict residual reserve imply all scalar reserve
conditions needed by the two-tier outward theorem, for the actual difficult group. -/
theorem componentDifficultLeaves_reserve
    (d : ∀ C : (evenSubgraph G).ConnectedComponent, ComponentDeletionChoice G u C)
    (B : Finset V) (q : ℕ) (hB : B ⊆ componentDeletionLeaves d)
    (hselected : #B ≤ q) (hreserve : #(componentDeletionLeaves d \ B) < q)
    (htwo : ∃ C D : (evenSubgraph G).ConnectedComponent,
      C ≠ D ∧ (d C).leaves.Nonempty ∧ (d D).leaves.Nonempty) :
    2 * #(componentDifficultLeaves d B) ≤ q ∧
      ((componentDifficultLeaves d B).Nonempty → 3 ≤ q) ∧
      #(componentDifficultLeaves d B) +
        #((componentDeletionLeaves d \ B) \ componentDifficultLeaves d B) + 1 ≤ q := by
  refine ⟨(componentDifficultLeaves_charge d B).trans hselected, ?_, ?_⟩
  · intro hh
    have hfour := componentDifficultLeaves_four_le d B hh htwo
    have hc := Finset.card_sdiff_add_card_eq_card hB
    omega
  · have hc := Finset.card_sdiff_add_card_eq_card (componentDifficultLeaves_subset d B)
    omega

end Gallai
