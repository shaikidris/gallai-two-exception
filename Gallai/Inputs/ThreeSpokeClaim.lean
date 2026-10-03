/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.Inputs.FanPunctureFloor
public import Gallai.Inputs.ThreeSpokeRestore
public import Gallai.Inputs.UniqueNeighborClaim

@[expose] public section

/-! # Excluding even vertices of E-degree three in a minimal counterexample -/

namespace Gallai

open scoped Finset

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Claim 4's degree-three branch: its star is constructed, its punctured cap
is proved, and the actual floor witness is restored without extra paths. -/
theorem three_even_spoke_contradiction (u : V) (hu : Even (G.degree u))
    (hthree : eDegree G u = 3)
    (hconn : G.Connected) (hcap : ∀ v, Even (G.degree v) → eDegree G v ≤ 3)
    (hnot : ¬ HasPathBudget G (Fintype.card V / 2)) (hset : ¬ IsSET G)
    (hmin : ∀ (U : Set V) [DecidablePred (· ∈ U)]
      (J : SimpleGraph U) [DecidableRel J.Adj],
      J.edgeFinset.card < G.edgeFinset.card → J.Connected →
      (∀ v, Even (J.degree v) → eDegree J v ≤ 3) →
      HasPathBudget J (Fintype.card U / 2) ∨ IsSET J) : False := by
  classical
  let S := evenNeighbors G u
  let F := S.sup (SimpleGraph.edge u)
  let H := G \ F
  have huS : u ∉ S := by simp [S]
  have hle : F ≤ G := by
    apply Finset.sup_le
    intro v hv
    exact (SimpleGraph.edge_le_iff G).mpr
      (Or.inr ((mem_evenNeighbors u v).mp hv).1)
  have hactive : ∃ a b, F.Adj a b := by
    have hc : #S = 3 := hthree
    obtain ⟨v, hv⟩ := Finset.card_pos.mp (show 0 < #S by omega)
    exact ⟨u, v, (star_sup_adj_center u S huS v).mpr hv⟩
  have hm : ∀ v, v ≠ u → F.degree v ≤ 1 := by
    intro v hv
    have hs : F.neighborFinset v ⊆ {u} := by
      intro w hw
      have ha := (F.mem_neighborFinset v w).mp hw
      exact Finset.mem_singleton.mpr ((star_sup_adj_off_center u S v w hv).mp ha).2
    have hc := Finset.card_le_card hs
    simpa only [SimpleGraph.card_neighborFinset_eq_degree, Finset.card_singleton] using hc
  have he : ∀ v, v ≠ u → 0 < F.degree v → Even (G.degree v) := by
    intro v hv hp
    obtain ⟨w, hw⟩ := (F.degree_pos_iff_exists_adj v).mp hp
    exact ((mem_evenNeighbors u v).mp ((star_sup_adj_off_center u S v w hv).mp hw).1).2
  have hc : ∀ v, H.Adj u v → ¬ Even (G.degree v) := by
    intro v hv hev
    exact hv.2 ((star_sup_adj_center u S huS v).mpr
      ((mem_evenNeighbors u v).mpr ⟨hv.1, hev⟩))
  have hkeep : ∀ v, Even (H.degree v) → Even (G.degree v) := by
    intro v hv
    by_cases h : v = u
    · subst v
      exact hu
    · apply (evenStarPuncture_even_off_center G u v h ?_).1
      simpa only [SimpleGraph.degree, SimpleGraph.neighborFinset,
        ← Set.ncard_eq_toFinset_card', H, F, S, evenStarPuncture, starPuncture] using hv
  have hcapP := even_degree_cap_of_even_preserved (G := G) (H := H)
    (fun _ _ h => h.1) hkeep 3 hcap
  obtain ⟨D, hD⟩ := fan_puncture_floor hle hactive
    (Or.inr (Or.inl ⟨u, hm, he, hc⟩)) hcapP hconn hcap hnot hset hmin
  obtain ⟨P, hP⟩ := D.restore_three_even_spokes u hu hthree
    (fun v hv => hcap v ((mem_evenNeighbors u v).mp hv).2)
  exact hnot ⟨P, hP.le.trans hD⟩

/-- The degree part of Claim 4: every even vertex has E-degree zero or two.
This does not yet identify the degree-two components as triangles. -/
theorem minimal_counterexample_even_eDegree_zero_or_two
    (hconn : G.Connected) (hcap : ∀ v, Even (G.degree v) → eDegree G v ≤ 3)
    (hnot : ¬ HasPathBudget G (Fintype.card V / 2)) (hset : ¬ IsSET G)
    (hmin : ∀ (U : Set V) [DecidablePred (· ∈ U)]
      (J : SimpleGraph U) [DecidableRel J.Adj],
      J.edgeFinset.card < G.edgeFinset.card → J.Connected →
      (∀ v, Even (J.degree v) → eDegree J v ≤ 3) →
      HasPathBudget J (Fintype.card U / 2) ∨ IsSET J)
    (u : V) (hu : Even (G.degree u)) : eDegree G u = 0 ∨ eDegree G u = 2 := by
  have hc := hcap u hu
  have h1 := minimal_counterexample_eDegree_ne_one hconn hcap hnot hset hmin u
  have h3 : eDegree G u ≠ 3 := fun h =>
    three_even_spoke_contradiction u hu h hconn hcap hnot hset hmin
  omega

end Gallai
