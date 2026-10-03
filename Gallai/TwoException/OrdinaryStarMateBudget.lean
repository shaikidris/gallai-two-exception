/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.OrdinaryStarMateCap

@[expose] public section

/-! # Native component floors after simultaneous ordinary preparations -/
namespace Gallai.TwoException
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
noncomputable local instance combinedBudgetAdj (G : SimpleGraph V) (u : V)
    (B : Finset V) (M : List (V × V)) :
    DecidableRel (ordinaryMatePuncture (starPuncture G u B) M).Adj :=
  fun _ _ => Classical.propDecidable _

/-- An original even component covered by deleted star leaves and mate
endpoints becomes entirely odd and supplies a non-SET witness in every
puncture component containing one of its vertices. Both cap and witness
are derived from the actual simultaneous puncture. -/
theorem bare_ordinary_star_mates_component_floor
    (h x : V) (H : BareMinimalCounterexample G h x)
    (u : V) (B : Finset V) (M : List (V × V)) (hxB : x ∈ B)
    (hadj : ∀ t ∈ B, G.Adj u t)
    (hleaves : ∀ t ∈ B, Even (G.degree t))
    (hdis : M.Pairwise (fun e f =>
      e.1 ≠ f.1 ∧ e.1 ≠ f.2 ∧ e.2 ≠ f.1 ∧ e.2 ≠ f.2))
    (havoid : ∀ e ∈ M, e.1 ≠ u ∧ e.2 ≠ u ∧ e.1 ∉ B ∧ e.2 ∉ B)
    (hedges : ∀ e ∈ M, G.Adj e.1 e.2 ∧ Even (G.degree e.1) ∧ Even (G.degree e.2))
    (hcontacts : ∀ t, G.Adj u t → Even (G.degree t) →
      t ∈ B ∨ (∃ e ∈ M, t = e.1 ∨ t = e.2) ∨ t = h)
    (C : (evenSubgraph G).ConnectedComponent) (p : evenVertices G)
    (hpC : p ∈ C.supp)
    (hcovered : ∀ t : evenVertices G, t ∈ C.supp →
      (t : V) ∈ B ∨ ∃ e ∈ M, (t : V) = e.1 ∨ (t : V) = e.2)
    (K : (ordinaryMatePuncture (starPuncture G u B) M).ConnectedComponent)
    (hpK : (p : V) ∈ K.supp) :
    HasPathBudget ((ordinaryMatePuncture (starPuncture G u B) M).induce K.supp)
      (Fintype.card K.supp / 2) := by
  classical
  let J := ordinaryMatePuncture (starPuncture G u B) M
  have hsubM : ∀ L : List (V × V), ordinaryMatePuncture (starPuncture G u B) L ≤ G := by
    intro L
    induction L with
    | nil => exact fun _ _ ha => ha.1
    | cons e L ih => exact fun _ _ ha => ih ha.1
  have hsub : J ≤ G := hsubM M
  have hp := ordinary_star_mates_even_preserved u B M hadj hleaves hdis havoid hedges
  have hl := ordinary_star_mates_leaves_odd u B M hadj hleaves
    (fun e he => ⟨(havoid e he).2.2.1, (havoid e he).2.2.2⟩)
  have hm := ordinary_star_mates_endpoints_odd u B M hdis havoid hedges
  have hodd : ∀ t : evenVertices G, t ∈ C.supp → Odd (J.degree t) := by
    intro t ht
    rcases hcovered t ht with htB | hmate
    · exact hl t htB
    · obtain ⟨e, he, hte⟩ := hmate
      obtain ⟨hpOdd, hqOdd⟩ := hm e he
      dsimp only [J]
      simp only [← SimpleGraph.ncard_neighborSet] at hpOdd hqOdd ⊢
      rcases hte with hte | hte
      · rw [hte]
        exact hpOdd
      · rw [hte]
        exact hqOdd
  have hc := bare_ordinary_star_mates_cap h x H u B M hxB hadj hleaves
    hdis havoid hedges hcontacts
  exact prepared_ordinary_component_floor C p hpC u hsub hp hodd hc K hpK

end Gallai.TwoException
