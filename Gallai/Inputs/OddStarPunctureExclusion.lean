/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.Inputs.OddStarTwoBoundary
public import Gallai.Inputs.SingleBoundaryParity

@[expose] public section

/-! # Complete SET exclusion for an odd-leaf Fan puncture

Every component is handled: the distinguished leaf is absent, is the only
active boundary, or has a second boundary vertex. No boundary case or SET
attachment is supplied by the caller.
-/

namespace Gallai

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G F : SimpleGraph V} [DecidableRel G.Adj] [DecidableRel F.Adj]

/-- No component of an odd-leaf Fan puncture is SET in a minimal
counterexample. All leaf-present and leaf-absent branches are included. -/
theorem odd_star_puncture_component_not_set_of_weak_centre (hle : F ≤ G) (u z : V)
    (hmatch : ∀ v, v ≠ u → F.degree v ≤ 1)
    (heven : ∀ v, v ≠ u → v ≠ z → 0 < F.degree v → Even (G.degree v))
    (huOdd : Odd (G.degree u)) (hz : Odd (G.degree z))
    (hdz : F.degree z = 1) (huz : F.Adj u z)
    (hcentre : ∀ v, (G \ F).Adj u v → v ≠ z → ¬ Even ((G \ F).degree v))
    (ht : ComponentsAreTriangles (evenSubgraph G))
    (hconn : G.Connected) (hcap : ∀ v, Even (G.degree v) → eDegree G v ≤ 3)
    (hnot : ¬ HasPathBudget G (Fintype.card V / 2)) (hset : ¬ IsSET G)
    (hmin : ∀ (U : Set V) [DecidablePred (· ∈ U)]
      (J : SimpleGraph U) [DecidableRel J.Adj],
      J.edgeFinset.card < G.edgeFinset.card → J.Connected →
      (∀ v, Even (J.degree v) → eDegree J v ≤ 3) →
      HasPathBudget J (Fintype.card U / 2) ∨ IsSET J)
    (C : (G \ F).ConnectedComponent) [DecidablePred (· ∈ C.supp)] :
    ¬ IsSET ((G \ F).induce C.supp) := by
  classical
  intro hC
  obtain ⟨hu, hi⟩ := odd_star_puncture_set_interface_of_weak_centre
    hle u z hmatch heven hz hdz hcentre ht C hC
  obtain ⟨_, ho, hk⟩ := odd_star_puncture_parity hle u z hmatch heven hz hdz
  have hc : ∀ v ∈ C.supp, (G \ F).neighborSet v ⊆ C.supp :=
    fun _ hv _ hw => C.mem_supp_of_adj_mem_supp hv hw
  by_cases hzC : z ∈ C.supp
  · by_cases hex : ∃ y ∈ C.supp, y ≠ z ∧ 0 < F.degree y
    · obtain ⟨y, hyC, hyz, hy⟩ := hex
      exact odd_star_two_boundary_not_set_of_weak_centre hle u z hmatch heven huOdd hz hdz huz
        hcentre ht C hzC y hyC hyz hy hconn hcap hnot hset hmin hC
    · apply single_boundary_odd_even_not_set (G := G) (H := G \ F)
        (fun _ _ hh => hh.1) C.supp z hzC hc ?_ hz (hi hzC).1
        hconn hcap hnot hset hmin hC
      intro v hv w hvw hn
      by_contra hvz
      have hf : F.Adj v w := by
        by_contra hnf
        exact hn ⟨hvw, hnf⟩
      exact hex ⟨v, hv, hvz, hf.degree_pos_left⟩
  · have hlt : G \ F < G := by
      refine lt_iff_le_not_ge.mpr ⟨fun _ _ hh => hh.1, ?_⟩
      intro hh
      exact (hh (hle huz)).2 huz
    apply preserved_triangle_puncture_not_set hlt C.supp C.nonempty_supp hc
      ?_ ?_ hconn hcap hnot hset hmin hC
    · intro v hv
      rw [SimpleGraph.degree_induce_of_neighborSet_subset (hc v v.property)] at hv
      exact hk v (fun he => hu (he ▸ v.property))
        (fun he => hzC (he ▸ v.property)) hv
    · intro v hv w hvw hn
      have hvu : v ≠ u := fun he => hu (he ▸ hv)
      have hvz : v ≠ z := fun he => hzC (he ▸ hv)
      have hf : F.Adj v w := by
        by_contra hnf
        exact hn ⟨hvw, hnf⟩
      refine ⟨?_, heven v hvu hvz hf.degree_pos_left⟩
      rw [SimpleGraph.degree_induce_of_neighborSet_subset (hc v hv)]
      exact ho v hvu hvz hf.degree_pos_left

/-- Original-parity compatibility entry point for the generalized odd-leaf argument. -/
theorem odd_star_puncture_component_not_set (hle : F ≤ G) (u z : V)
    (hmatch : ∀ v, v ≠ u → F.degree v ≤ 1)
    (heven : ∀ v, v ≠ u → v ≠ z → 0 < F.degree v → Even (G.degree v))
    (huOdd : Odd (G.degree u)) (hz : Odd (G.degree z))
    (hdz : F.degree z = 1) (huz : F.Adj u z)
    (hcentre : ∀ v, (G \ F).Adj u v → ¬ Even (G.degree v))
    (ht : ComponentsAreTriangles (evenSubgraph G))
    (hconn : G.Connected) (hcap : ∀ v, Even (G.degree v) → eDegree G v ≤ 3)
    (hnot : ¬ HasPathBudget G (Fintype.card V / 2)) (hset : ¬ IsSET G)
    (hmin : ∀ (U : Set V) [DecidablePred (· ∈ U)]
      (J : SimpleGraph U) [DecidableRel J.Adj],
      J.edgeFinset.card < G.edgeFinset.card → J.Connected →
      (∀ v, Even (J.degree v) → eDegree J v ≤ 3) →
      HasPathBudget J (Fintype.card U / 2) ∨ IsSET J)
    (C : (G \ F).ConnectedComponent) [DecidablePred (· ∈ C.supp)] :
    ¬ IsSET ((G \ F).induce C.supp) := by
  have hc : ∀ v, (G \ F).Adj u v → v ≠ z → ¬ Even ((G \ F).degree v) := by
    intro v huv hvz hev
    exact hcentre v huv
      ((odd_star_puncture_parity hle u z hmatch heven hz hdz).2.2 v huv.ne.symm hvz hev)
  exact odd_star_puncture_component_not_set_of_weak_centre hle u z hmatch heven huOdd hz hdz huz
    hc ht hconn hcap hnot hset hmin C

end Gallai
