/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.Inputs.PunctureComponentFloor
public import Gallai.Inputs.PunctureCaps
public import Gallai.Inputs.EvenStarPuncture
public import Gallai.Inputs.OddStarPunctureExclusion

@[expose] public section

/-! # Floor decompositions for the three Fan puncture cases

The three-case compatibility consumer retains its original-parity centre
condition. Separate even-star and odd-star consumers use the literal published
punctured-parity condition. The odd-star consumer retains the explicit
punctured E-degree cap required in the source.
-/

namespace Gallai

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G F : SimpleGraph V} [DecidableRel G.Adj] [DecidableRel F.Adj]

/-- Each of the three restricted Fan puncture interfaces supplies a floor decomposition,
under strictly smaller-edge induction. The shape alternatives concern only
the removed graph and original parity, not a favourable decomposition. -/
theorem fan_puncture_floor (hle : F ≤ G) (hactive : ∃ a b, F.Adj a b)
    (hshape :
      ((∀ v, F.degree v ≤ 1) ∧ (∀ v, 0 < F.degree v → Even (G.degree v))) ∨
      (∃ u, (∀ v, v ≠ u → F.degree v ≤ 1) ∧
        (∀ v, v ≠ u → 0 < F.degree v → Even (G.degree v)) ∧
        (∀ v, (G \ F).Adj u v → ¬ Even (G.degree v))) ∨
      (∃ u z, (∀ v, v ≠ u → F.degree v ≤ 1) ∧
        (∀ v, v ≠ u → v ≠ z → 0 < F.degree v → Even (G.degree v)) ∧
        Odd (G.degree u) ∧ Odd (G.degree z) ∧ F.degree z = 1 ∧ F.Adj u z ∧
        (∀ v, (G \ F).Adj u v → ¬ Even (G.degree v)) ∧
        ComponentsAreTriangles (evenSubgraph G)))
    (hcapP : ∀ v, Even ((G \ F).degree v) → eDegree (G \ F) v ≤ 3)
    (hconn : G.Connected) (hcap : ∀ v, Even (G.degree v) → eDegree G v ≤ 3)
    (hnot : ¬ HasPathBudget G (Fintype.card V / 2)) (hset : ¬ IsSET G)
    (hmin : ∀ (U : Set V) [DecidablePred (· ∈ U)]
      (J : SimpleGraph U) [DecidableRel J.Adj],
      J.edgeFinset.card < G.edgeFinset.card → J.Connected →
      (∀ v, Even (J.degree v) → eDegree J v ≤ 3) →
      HasPathBudget J (Fintype.card U / 2) ∨ IsSET J) :
    HasPathBudget (G \ F) (Fintype.card V / 2) := by
  have hlt : G \ F < G := by
    refine lt_iff_le_not_ge.mpr ⟨fun _ _ hh => hh.1, ?_⟩
    intro hh
    obtain ⟨a, b, hab⟩ := hactive
    exact (hh (hle hab)).2 hab
  apply proper_puncture_floor hlt hcapP hmin
  intro C
  rcases hshape with ⟨hm, he⟩ | ⟨u, hm, he, hc⟩ | ⟨u, z, hm, he, hu, hz, hd, ha, hc, ht⟩
  · exact matching_puncture_component_not_set hle hm he hactive hconn hcap hnot hset hmin C
  · exact even_star_puncture_component_not_set hle u hm he hc hactive
      hconn hcap hnot hset hmin C
  · exact odd_star_puncture_component_not_set hle u z hm he hu hz hd ha hc ht
      hconn hcap hnot hset hmin C

/-- The even-matching case derives its punctured cap internally. -/
theorem matching_puncture_floor (hle : F ≤ G) (hactive : ∃ a b, F.Adj a b)
    (hm : ∀ v, F.degree v ≤ 1) (he : ∀ v, 0 < F.degree v → Even (G.degree v))
    (hconn : G.Connected) (hcap : ∀ v, Even (G.degree v) → eDegree G v ≤ 3)
    (hnot : ¬ HasPathBudget G (Fintype.card V / 2)) (hset : ¬ IsSET G)
    (hmin : ∀ (U : Set V) [DecidablePred (· ∈ U)]
      (J : SimpleGraph U) [DecidableRel J.Adj],
      J.edgeFinset.card < G.edgeFinset.card → J.Connected →
      (∀ v, Even (J.degree v) → eDegree J v ≤ 3) →
      HasPathBudget J (Fintype.card U / 2) ∨ IsSET J) :
    HasPathBudget (G \ F) (Fintype.card V / 2) :=
  fan_puncture_floor hle hactive (Or.inl ⟨hm, he⟩)
    (matching_puncture_cap hle hm he 3 hcap) hconn hcap hnot hset hmin

/-- Even-leaf Fan floor consumer with the literal published centre condition:
the centre has no even neighbour in the puncture, not in the original graph.
The punctured E-degree cap follows internally, including a newly even hub. -/
theorem even_star_puncture_floor (hle : F ≤ G) (u : V)
    (hactive : ∃ a b, F.Adj a b)
    (hmatch : ∀ v, v ≠ u → F.degree v ≤ 1)
    (heven : ∀ v, v ≠ u → 0 < F.degree v → Even (G.degree v))
    (hcentre : ∀ v, (G \ F).Adj u v → ¬ Even ((G \ F).degree v))
    (hconn : G.Connected) (hcap : ∀ v, Even (G.degree v) → eDegree G v ≤ 3)
    (hnot : ¬ HasPathBudget G (Fintype.card V / 2)) (hset : ¬ IsSET G)
    (hmin : ∀ (U : Set V) [DecidablePred (· ∈ U)]
      (J : SimpleGraph U) [DecidableRel J.Adj],
      J.edgeFinset.card < G.edgeFinset.card → J.Connected →
      (∀ v, Even (J.degree v) → eDegree J v ≤ 3) →
      HasPathBudget J (Fintype.card U / 2) ∨ IsSET J) :
    HasPathBudget (G \ F) (Fintype.card V / 2) := by
  have hlt : G \ F < G := by
    refine lt_iff_le_not_ge.mpr ⟨fun _ _ hh => hh.1, ?_⟩
    intro hh
    obtain ⟨a, b, hab⟩ := hactive
    exact (hh (hle hab)).2 hab
  have hcapP := even_degree_cap_of_isolated_exception (G := G) (H := G \ F)
    (fun _ _ h => h.1) u (even_star_puncture_parity hle u hmatch heven).2
    hcentre 3 hcap
  apply proper_puncture_floor hlt hcapP hmin
  intro C
  exact even_star_puncture_component_not_set_of_punctured_centre hle u hmatch heven
    hcentre hactive hconn hcap hnot hset hmin C

/-- Odd-leaf Fan floor consumer with the literal punctured-parity centre
condition. The punctured E-degree cap is explicit, as in the source claim. -/
theorem odd_star_puncture_floor (hle : F ≤ G) (u z : V)
    (hmatch : ∀ v, v ≠ u → F.degree v ≤ 1)
    (heven : ∀ v, v ≠ u → v ≠ z → 0 < F.degree v → Even (G.degree v))
    (huOdd : Odd (G.degree u)) (hz : Odd (G.degree z))
    (hdz : F.degree z = 1) (huz : F.Adj u z)
    (hcentre : ∀ v, (G \ F).Adj u v → ¬ Even ((G \ F).degree v))
    (ht : ComponentsAreTriangles (evenSubgraph G))
    (hcapP : ∀ v, Even ((G \ F).degree v) → eDegree (G \ F) v ≤ 3)
    (hconn : G.Connected) (hcap : ∀ v, Even (G.degree v) → eDegree G v ≤ 3)
    (hnot : ¬ HasPathBudget G (Fintype.card V / 2)) (hset : ¬ IsSET G)
    (hmin : ∀ (U : Set V) [DecidablePred (· ∈ U)]
      (J : SimpleGraph U) [DecidableRel J.Adj],
      J.edgeFinset.card < G.edgeFinset.card → J.Connected →
      (∀ v, Even (J.degree v) → eDegree J v ≤ 3) →
      HasPathBudget J (Fintype.card U / 2) ∨ IsSET J) :
    HasPathBudget (G \ F) (Fintype.card V / 2) := by
  have hlt : G \ F < G := by
    refine lt_iff_le_not_ge.mpr ⟨fun _ _ hh => hh.1, ?_⟩
    intro hh
    exact (hh (hle huz)).2 huz
  apply proper_puncture_floor hlt hcapP hmin
  intro C
  exact odd_star_puncture_component_not_set_of_weak_centre hle u z hmatch heven
    huOdd hz hdz huz (fun v hv _ => hcentre v hv) ht hconn hcap hnot hset hmin C

end Gallai
