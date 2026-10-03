/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.Inputs.ComponentExceptionalLeaves

@[expose] public section

/-! # The exceptional triangle's one-unit difficult-leaf deficit

Ordinary difficult leaves charge two restored spokes outside the exceptional
component. Its own difficult leaf charges one spoke and the initial endpoint.
-/

namespace Gallai

open scoped Finset

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {u : V}

/-- Ordinary full-triangle difficulties together with a lone exceptional spoke. -/
noncomputable def componentModifiedDifficultLeaves
    (d : ∀ C : (evenSubgraph G).ConnectedComponent, ComponentDeletionChoice G u C)
    (C : (evenSubgraph G).ConnectedComponent) (e : V × V) (B : Finset V) : Finset V := by
  classical
  exact componentDifficultLeaves d B ∪
    if #(componentExceptionalLeaves d C e \ B) = 1 then
      componentExceptionalLeaves d C e \ B else ∅

/-- Membership exposes exactly the exceptional lone-residual condition. -/
theorem mem_componentModifiedDifficultLeaves
    (d : ∀ C : (evenSubgraph G).ConnectedComponent, ComponentDeletionChoice G u C)
    (C : (evenSubgraph G).ConnectedComponent) (e : V × V) (B : Finset V) (v : V) :
    v ∈ componentModifiedDifficultLeaves d C e B ↔
      v ∈ componentDifficultLeaves d B ∨
        #(componentExceptionalLeaves d C e \ B) = 1 ∧
          v ∈ componentExceptionalLeaves d C e ∧ v ∉ B := by
  classical
  unfold componentModifiedDifficultLeaves
  split_ifs <;> simp_all [Finset.mem_sdiff]

/-- Every modified difficult leaf is an un-restored enlarged-star spoke. -/
theorem componentModifiedDifficultLeaves_subset
    (d : ∀ C : (evenSubgraph G).ConnectedComponent, ComponentDeletionChoice G u C)
    (C : (evenSubgraph G).ConnectedComponent) (e : V × V) (B : Finset V) :
    componentModifiedDifficultLeaves d C e B ⊆
      (insert e.1 (componentDeletionLeaves d)) \ B := by
  intro v hv
  rcases (mem_componentModifiedDifficultLeaves d C e B v).mp hv with h | ⟨_, h, hn⟩
  · obtain ⟨h, hn⟩ := Finset.mem_sdiff.mp (componentDifficultLeaves_subset d B h)
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_insert_of_mem h, hn⟩
  · exact Finset.mem_sdiff.mpr ⟨componentExceptionalLeaves_subset d C e h, hn⟩

/-- Ordinary charges avoid the exceptional set, and its lone residual leaf
costs at most one additional unit beyond the restored spokes. -/
theorem componentModifiedDifficultLeaves_charge
    (d : ∀ C : (evenSubgraph G).ConnectedComponent, ComponentDeletionChoice G u C)
    (C : (evenSubgraph G).ConnectedComponent) (e : V × V) (he : e ∈ (d C).pairs)
    (B : Finset V) : 2 * #(componentModifiedDifficultLeaves d C e B) ≤ #B + 1 := by
  classical
  have hord := componentDifficultLeaves_charge d (B \ componentExceptionalLeaves d C e)
  rw [componentDifficultLeaves_sdiff_exceptional d C e he B] at hord
  by_cases h : #(componentExceptionalLeaves d C e \ B) = 1
  · have hcard := componentExceptionalLeaves_card d C e he
    have heq := Finset.card_sdiff_add_card_inter (componentExceptionalLeaves d C e) B
    have htotal := Finset.card_sdiff_add_card_inter B (componentExceptionalLeaves d C e)
    rw [Finset.inter_comm B] at htotal
    have hunion := Finset.card_union_le (componentDifficultLeaves d B)
      (componentExceptionalLeaves d C e \ B)
    simp only [componentModifiedDifficultLeaves, h, if_true]
    omega
  · simp only [componentModifiedDifficultLeaves, h, if_false, Finset.union_empty]
    have hsub := Finset.card_le_card (Finset.sdiff_subset :
      B \ componentExceptionalLeaves d C e ⊆ B)
    omega

/-- All scalar gates for the two-tier outward consumer follow from actual
difficult-leaf charges and the enlarged half-star's one extra endpoint. -/
theorem componentModifiedDifficultLeaves_reserve
    (d : ∀ C : (evenSubgraph G).ConnectedComponent, ComponentDeletionChoice G u C)
    (C : (evenSubgraph G).ConnectedComponent) (e : V × V) (he : e ∈ (d C).pairs)
    (B : Finset V) (q : ℕ) (hB : B ⊆ insert e.1 (componentDeletionLeaves d))
    (hhalf : #(insert e.1 (componentDeletionLeaves d)) ≤ 2 * #B)
    (hsize : 4 ≤ #(insert e.1 (componentDeletionLeaves d))) (hq : #B + 1 ≤ q) :
    2 * #(componentModifiedDifficultLeaves d C e B) ≤ q ∧ 3 ≤ q ∧
      #(componentModifiedDifficultLeaves d C e B) +
        #(((insert e.1 (componentDeletionLeaves d)) \ B) \
          componentModifiedDifficultLeaves d C e B) + 1 ≤ q := by
  have hcharge := componentModifiedDifficultLeaves_charge d C e he B
  have hrem := Finset.card_sdiff_add_card_eq_card hB
  have hsplit := Finset.card_sdiff_add_card_eq_card
    (componentModifiedDifficultLeaves_subset d C e B)
  omega

end Gallai
