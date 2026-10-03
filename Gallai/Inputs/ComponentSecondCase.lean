/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.Inputs.ComponentRestore

@[expose] public section

/-! # The witnessed complementary case for modified component deletion

The first restoration case is contradicted using its actual floor puncture.
The surviving opposite edge and enlarged-star reserve are derived together.
-/

namespace Gallai

open scoped Finset

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {u : V}

/-- The recipient of a partial triangle is not one of its selected star leaves. -/
theorem ComponentDeletionChoice.pair_fst_not_leaf
    {C : (evenSubgraph G).ConnectedComponent} (d : ComponentDeletionChoice G u C)
    (e : V × V) (he : e ∈ d.pairs) : e.1 ∉ d.leaves := by
  cases d with
  | untouched => simp [ComponentDeletionChoice.pairs] at he
  | isolate => simp [ComponentDeletionChoice.pairs] at he
  | triangle a b c hab hac hbc hC habE hacE hbcE hua ho =>
    by_cases h : G.Adj u c
    · simp [ComponentDeletionChoice.pairs, h] at he
    · have heq : e = ((b : V), (c : V)) := by
        simpa [ComponentDeletionChoice.pairs, h] using he
      subst e
      have hba : (b : V) ≠ a := fun he => hab (Subtype.ext he.symm)
      simpa [ComponentDeletionChoice.leaves, h] using hba

/-- No global selected spoke duplicates the recipient of an opposite edge. -/
theorem componentDeletionPairs_fst_not_leaf
    (d : ∀ C : (evenSubgraph G).ConnectedComponent, ComponentDeletionChoice G u C)
    (e : V × V) (he : e ∈ componentDeletionPairs d) :
    e.1 ∉ componentDeletionLeaves d := by
  classical
  obtain ⟨C, _, he⟩ := Finset.mem_biUnion.mp he
  intro hv
  exact (d C).pair_fst_not_leaf e he
    (componentDeletionLeaves_local d C e.1 ((d C).pair_data e he).2.2.1 hv)

/-- Two touched actual components contribute at least two distinct selected leaves. -/
theorem componentDeletionLeaves_two_le
    (d : ∀ C : (evenSubgraph G).ConnectedComponent, ComponentDeletionChoice G u C)
    (htwo : ∃ C E : (evenSubgraph G).ConnectedComponent, C ≠ E ∧
      (d C).leaves.Nonempty ∧ (d E).leaves.Nonempty) :
    2 ≤ #(componentDeletionLeaves d) := by
  classical
  obtain ⟨C, E, hCE, ⟨a, ha⟩, ⟨b, hb⟩⟩ := htwo
  have hab : a ≠ b := fun h => Finset.disjoint_left.mp
    (componentDeletionLeaves_disjoint d C E hCE) ha (h.symm ▸ hb)
  have hs : ({a, b} : Finset V) ⊆ componentDeletionLeaves d := by
    intro v hv
    rcases Finset.mem_insert.mp hv with h | h
    · subst v
      exact Finset.mem_biUnion.mpr ⟨C, Finset.mem_univ C, ha⟩
    · have h : v = b := Finset.mem_singleton.mp h
      subst v
      exact Finset.mem_biUnion.mpr ⟨E, Finset.mem_univ E, hb⟩
  simpa [hab] using Finset.card_le_card hs

/-- Inserting the witnessed recipient turns an odd selected star into an
even star with at least four leaves. -/
theorem componentDeletionPairs_insert_reserve
    (d : ∀ C : (evenSubgraph G).ConnectedComponent, ComponentDeletionChoice G u C)
    (e : V × V) (he : e ∈ componentDeletionPairs d)
    (ho : Odd #(componentDeletionLeaves d)) (hsize : 2 ≤ #(componentDeletionLeaves d)) :
    Even #(insert e.1 (componentDeletionLeaves d)) ∧
      4 ≤ #(insert e.1 (componentDeletionLeaves d)) := by
  rw [Finset.card_insert_of_notMem (componentDeletionPairs_fst_not_leaf d e he)]
  rw [Nat.odd_iff] at ho
  rw [Nat.even_iff]
  omega

/-- The first-case contradiction supplies the actual adjacent recipient and
the enlarged-star parity/reserve required by the second source branch. -/
theorem minimal_counterexample_component_second_case
    (d : ∀ C : (evenSubgraph G).ConnectedComponent, ComponentDeletionChoice G u C)
    (hu : Odd (G.degree u))
    (htwo : ∃ C E : (evenSubgraph G).ConnectedComponent, C ≠ E ∧
      (∃ v : evenVertices G, v ∈ C.supp ∧ G.Adj u v) ∧
      (∃ v : evenVertices G, v ∈ E.supp ∧ G.Adj u v))
    (hconn : G.Connected) (hcap : ∀ v, Even (G.degree v) → eDegree G v ≤ 3)
    (hnot : ¬ HasPathBudget G (Fintype.card V / 2)) (hset : ¬ IsSET G)
    (hmin : ∀ (U : Set V) [DecidablePred (· ∈ U)]
      (J : SimpleGraph U) [DecidableRel J.Adj],
      J.edgeFinset.card < G.edgeFinset.card → J.Connected →
      (∀ v, Even (J.degree v) → eDegree J v ≤ 3) →
      HasPathBudget J (Fintype.card U / 2) ∨ IsSET J) :
    ∃ e ∈ componentDeletionPairs d, G.Adj u e.1 ∧
      e.1 ∉ componentDeletionLeaves d ∧ Odd #(componentDeletionLeaves d) ∧
      Even #(insert e.1 (componentDeletionLeaves d)) ∧
      4 ≤ #(insert e.1 (componentDeletionLeaves d)) := by
  classical
  have htouch : ∃ v, Even (G.degree v) ∧ G.Adj u v := by
    obtain ⟨C, E, hCE, ⟨v, _, hv⟩, _⟩ := htwo
    exact ⟨v, v.property, hv⟩
  obtain ⟨D, hD⟩ := componentDeletionUnion_floor d hu htouch hconn hcap hnot hset hmin
  have hcase : ¬ ((∀ e ∈ componentDeletionPairs d, ¬ G.Adj u e.1) ∨
      Even #(componentDeletionLeaves d)) := by
    intro h
    obtain ⟨E, hE⟩ := D.restore_component_puncture d hu h htwo
    exact hnot ⟨E, hE ▸ hD⟩
  have ho : Odd #(componentDeletionLeaves d) :=
    Nat.not_even_iff_odd.mp (fun h => hcase (Or.inr h))
  have hex : ∃ e ∈ componentDeletionPairs d, G.Adj u e.1 := by
    by_contra hn
    apply hcase
    exact Or.inl (fun e he ha => hn ⟨e, he, ha⟩)
  obtain ⟨e, he, ha⟩ := hex
  exact ⟨e, he, ha, componentDeletionPairs_fst_not_leaf d e he, ho,
    componentDeletionPairs_insert_reserve d e he ho
      (componentDeletionLeaves_two_le d (componentDeletionLeaves_two_touched d htwo))⟩

end Gallai
