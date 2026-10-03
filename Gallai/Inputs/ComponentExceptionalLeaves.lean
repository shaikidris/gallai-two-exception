/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.Inputs.ComponentModifiedHalfStar

@[expose] public section

/-! # Keeping the exceptional triangle's two selected leaves labelled -/

namespace Gallai

open scoped Finset

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {u : V}

/-- An opposite pair occurs only in a partial triangle with one original spoke. -/
theorem ComponentDeletionChoice.pair_leaves_card
    {C : (evenSubgraph G).ConnectedComponent} (d : ComponentDeletionChoice G u C)
    (e : V × V) (he : e ∈ d.pairs) : #d.leaves = 1 := by
  cases d with
  | untouched => simp [ComponentDeletionChoice.pairs] at he
  | isolate => simp [ComponentDeletionChoice.pairs] at he
  | triangle a b c hab hac hbc hC habE hacE hbcE hua ho =>
    by_cases h : G.Adj u c
    · simp [ComponentDeletionChoice.pairs, h] at he
    · simp [ComponentDeletionChoice.leaves, h]

/-- The two selected leaves in the component where the opposite edge was retained. -/
def componentExceptionalLeaves
    (d : ∀ C : (evenSubgraph G).ConnectedComponent, ComponentDeletionChoice G u C)
    (C : (evenSubgraph G).ConnectedComponent) (e : V × V) : Finset V :=
  insert e.1 (d C).leaves

/-- The exceptional set has exactly two leaves. -/
theorem componentExceptionalLeaves_card
    (d : ∀ C : (evenSubgraph G).ConnectedComponent, ComponentDeletionChoice G u C)
    (C : (evenSubgraph G).ConnectedComponent) (e : V × V) (he : e ∈ (d C).pairs) :
    #(componentExceptionalLeaves d C e) = 2 := by
  rw [componentExceptionalLeaves,
    Finset.card_insert_of_notMem ((d C).pair_fst_not_leaf e he),
    (d C).pair_leaves_card e he]

/-- Both exceptional leaves stay in their actual even component. -/
theorem componentExceptionalLeaves_supported
    (d : ∀ C : (evenSubgraph G).ConnectedComponent, ComponentDeletionChoice G u C)
    (C : (evenSubgraph G).ConnectedComponent) (e : V × V) (he : e ∈ (d C).pairs)
    (v : V) (hv : v ∈ componentExceptionalLeaves d C e) :
    v ∈ evenComponentVertices C := by
  rcases Finset.mem_insert.mp hv with h | h
  · exact h ▸ ((d C).pair_data e he).2.2.1
  · exact ((d C).leaf_data v h).2

/-- Exceptional leaves are among the actual enlarged selected star. -/
theorem componentExceptionalLeaves_subset
    (d : ∀ C : (evenSubgraph G).ConnectedComponent, ComponentDeletionChoice G u C)
    (C : (evenSubgraph G).ConnectedComponent) (e : V × V) :
    componentExceptionalLeaves d C e ⊆ insert e.1 (componentDeletionLeaves d) := by
  classical
  intro v hv
  rcases Finset.mem_insert.mp hv with h | h
  · exact Finset.mem_insert.mpr (Or.inl h)
  · exact Finset.mem_insert.mpr (Or.inr
      (Finset.mem_biUnion.mpr ⟨C, Finset.mem_univ C, h⟩))

/-- Other components' selected leaves cannot consume an exceptional charge. -/
theorem componentExceptionalLeaves_disjoint
    (d : ∀ C : (evenSubgraph G).ConnectedComponent, ComponentDeletionChoice G u C)
    (C : (evenSubgraph G).ConnectedComponent) (e : V × V) (he : e ∈ (d C).pairs)
    (D : (evenSubgraph G).ConnectedComponent) (hDC : D ≠ C) :
    Disjoint (d D).leaves (componentExceptionalLeaves d C e) := by
  apply Finset.disjoint_left.mpr
  intro v hv hw
  exact Set.disjoint_left.mp (evenComponentVertices_disjoint D C hDC)
    ((d D).leaf_data v hv).2 (componentExceptionalLeaves_supported d C e he v hw)

/-- Removing exceptional selections does not change any ordinary difficult leaf.
The exceptional component was a partial, not a full, triangle. -/
theorem componentDifficultLeaves_sdiff_exceptional
    (d : ∀ C : (evenSubgraph G).ConnectedComponent, ComponentDeletionChoice G u C)
    (C : (evenSubgraph G).ConnectedComponent) (e : V × V) (he : e ∈ (d C).pairs)
    (B : Finset V) :
    componentDifficultLeaves d (B \ componentExceptionalLeaves d C e) =
      componentDifficultLeaves d B := by
  classical
  have hlocal : ∀ D : (evenSubgraph G).ConnectedComponent,
      (d D).difficultLeaves (B \ componentExceptionalLeaves d C e) =
        (d D).difficultLeaves B := by
    intro D
    by_cases hDC : D = C
    · subst D
      simp [ComponentDeletionChoice.difficultLeaves, (d C).pair_leaves_card e he]
    · have hdis := componentExceptionalLeaves_disjoint d C e he D hDC
      have hmem : ∀ v ∈ (d D).leaves, v ∉ componentExceptionalLeaves d C e := by
        intro v hv hw
        exact Finset.disjoint_left.mp hdis hv hw
      have hi : (d D).leaves ∩ (B \ componentExceptionalLeaves d C e) =
          (d D).leaves ∩ B := by
        ext v
        by_cases hv : v ∈ (d D).leaves <;> simp [hv, hmem v]
      have hs : (d D).leaves \ (B \ componentExceptionalLeaves d C e) =
          (d D).leaves \ B := by
        ext v
        by_cases hv : v ∈ (d D).leaves <;> simp [hv, hmem v]
      simp only [ComponentDeletionChoice.difficultLeaves, hi, hs]
  simp only [componentDifficultLeaves, hlocal]

end Gallai
