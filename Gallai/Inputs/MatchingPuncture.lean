/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.Inputs.PreservedSETBoundary
public import Gallai.Structure.EvenSubgraphInduce

@[expose] public section

/-! # Matching-only Fan punctures

The removed graph has degree at most one and every active vertex is even in
the original graph. Derive the parity interface rather than supplying it.
-/

namespace Gallai

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G F : SimpleGraph V} [DecidableRel G.Adj] [DecidableRel F.Adj]

/-- Deleting a subgraph splits every original degree into retained and removed degrees. -/
theorem degree_sdiff_add_of_le (hle : F ≤ G) (v : V) :
    (G \ F).degree v + F.degree v = G.degree v := by
  have hs : F.neighborFinset v ⊆ G.neighborFinset v := by
    intro w hw
    exact (G.mem_neighborFinset v w).mpr (hle ((F.mem_neighborFinset v w).mp hw))
  rw [← SimpleGraph.card_neighborFinset_eq_degree,
    SimpleGraph.neighborFinset_sdiff, Finset.card_sdiff_of_subset hs]
  have hc := Finset.card_le_card hs
  simp only [SimpleGraph.card_neighborFinset_eq_degree] at hc ⊢
  omega

/-- Every endpoint of a deleted even matching becomes odd. -/
theorem matching_puncture_odd (hle : F ≤ G) (hmatch : ∀ v, F.degree v ≤ 1)
    (heven : ∀ v, 0 < F.degree v → Even (G.degree v)) (v : V)
    (hv : 0 < F.degree v) : Odd ((G \ F).degree v) := by
  have hd := degree_sdiff_add_of_le hle v
  have hm := hmatch v
  have he := heven v hv
  rw [Nat.even_iff] at he
  rw [Nat.odd_iff]
  omega

/-- No new even vertex is introduced by deleting an even matching. -/
theorem matching_puncture_even_preserved (hle : F ≤ G) (hmatch : ∀ v, F.degree v ≤ 1)
    (heven : ∀ v, 0 < F.degree v → Even (G.degree v)) (v : V)
    (hv : Even ((G \ F).degree v)) : Even (G.degree v) := by
  by_cases hp : 0 < F.degree v
  · exact False.elim ((Nat.not_even_iff_odd.mpr
      (matching_puncture_odd hle hmatch heven v hp)) hv)
  have hd := degree_sdiff_add_of_le hle v
  have hz : F.degree v = 0 := by omega
  simp only [hz, Nat.add_zero] at hd
  rwa [← hd]

/-- The matching-only branch of Claim 3: no actual component is SET under
the source's strictly smaller-edge minimal-counterexample hypothesis. -/
theorem matching_puncture_component_not_set (hle : F ≤ G)
    (hmatch : ∀ v, F.degree v ≤ 1)
    (heven : ∀ v, 0 < F.degree v → Even (G.degree v))
    (hactive : ∃ a b, F.Adj a b)
    (hconn : G.Connected) (hcap : ∀ v, Even (G.degree v) → eDegree G v ≤ 3)
    (hnot : ¬ HasPathBudget G (Fintype.card V / 2)) (hset : ¬ IsSET G)
    (hmin : ∀ (U : Set V) [DecidablePred (· ∈ U)]
      (J : SimpleGraph U) [DecidableRel J.Adj],
      J.edgeFinset.card < G.edgeFinset.card → J.Connected →
      (∀ v, Even (J.degree v) → eDegree J v ≤ 3) →
      HasPathBudget J (Fintype.card U / 2) ∨ IsSET J)
    (C : (G \ F).ConnectedComponent) [DecidablePred (· ∈ C.supp)] :
    ¬ IsSET ((G \ F).induce C.supp) := by
  have hlt : G \ F < G := by
    refine lt_iff_le_not_ge.mpr ⟨fun _ _ hh => hh.1, ?_⟩
    intro hh
    obtain ⟨a, b, hab⟩ := hactive
    exact (hh (hle hab)).2 hab
  have hc : ∀ v ∈ C.supp, (G \ F).neighborSet v ⊆ C.supp :=
    fun _ hv _ hw => C.mem_supp_of_adj_mem_supp hv hw
  apply preserved_triangle_puncture_not_set hlt C.supp C.nonempty_supp hc
    ?_ ?_ hconn hcap hnot hset hmin
  · intro v hv
    rw [SimpleGraph.degree_induce_of_neighborSet_subset (hc v v.property)] at hv
    exact matching_puncture_even_preserved hle hmatch heven v hv
  · intro v hv w hvw hn
    have hf : F.Adj v w := by
      by_contra hnf
      exact hn ⟨hvw, hnf⟩
    have hp := (F.degree_pos_iff_exists_adj v).mpr ⟨w, hf⟩
    refine ⟨?_, heven v hp⟩
    rw [SimpleGraph.degree_induce_of_neighborSet_subset (hc v hv)]
    exact matching_puncture_odd hle hmatch heven v hp

end Gallai
