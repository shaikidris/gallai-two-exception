/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.OrdinaryPacketCoverage

@[expose] public section

/-! # Triangle mate restoration inside simultaneous preparations -/
namespace Gallai.TwoException
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
noncomputable local instance familyRestoreAdj (G : SimpleGraph V) (u : V)
    (B : Finset V) (M : List (V × V)) :
    DecidableRel (ordinaryMatePuncture (starPuncture G u B) M).Adj :=
  fun _ _ => Classical.propDecidable _

/-- Restore any selected ordinary triangle mate in a simultaneous puncture.
All parity and original-neighbourhood guards come from the family and the
whole triangle component; only the schedule's centre reserve is explicit. -/
theorem restore_ordinary_family_triangle_mate
    (u : V) (B : Finset V) (M : List (V × V))
    (hadj : ∀ t ∈ B, G.Adj u t)
    (hleaves : ∀ t ∈ B, Even (G.degree t))
    (hdis : M.Pairwise (fun e f =>
      e.1 ≠ f.1 ∧ e.1 ≠ f.2 ∧ e.2 ≠ f.1 ∧ e.2 ≠ f.2))
    (havoid : ∀ e ∈ M, e.1 ≠ u ∧ e.2 ≠ u ∧ e.1 ∉ B ∧ e.2 ∉ B)
    (hedges : ∀ e ∈ M, G.Adj e.1 e.2 ∧ Even (G.degree e.1) ∧ Even (G.degree e.2))
    (C : (evenSubgraph G).ConnectedComponent) (a b c : evenVertices G)
    (hsupp : C.supp = {a, b, c}) (haB : (a : V) ∈ B)
    (hmate : ((b : V), (c : V)) ∈ M)
    (D : Decomposition (ordinaryMatePuncture (starPuncture G u B) M))
    (hcentre : ¬ (ordinaryMatePuncture (starPuncture G u B) M).Adj b u ∨
      0 < D.endpointCount u) :
    ∃ E : Decomposition ((ordinaryMatePuncture (starPuncture G u B) M) ⊔
      SimpleGraph.edge (b : V) (c : V)), E.size = D.size ∧
      2 ≤ E.endpointCount b ∧
      ∀ t, E.endpointCount t + (if (c : V) = t then 1 else 0) =
        D.endpointCount t + if (b : V) = t then 1 else 0 := by
  classical
  have hsub : ordinaryMatePuncture (starPuncture G u B) M ≤ G :=
    (ordinaryMatePuncture_le M).trans (fun _ _ ha => ha.1)
  obtain ⟨hbOdd, hcOdd⟩ := ordinary_star_mates_endpoints_odd u B M hdis havoid hedges
    ((b : V), (c : V)) hmate
  have haOdd := ordinary_star_mates_leaves_odd u B M hadj hleaves
    (fun e he => ⟨(havoid e he).2.2.1, (havoid e he).2.2.2⟩) a haB
  have hbc : (b : V) ≠ c := (hedges _ hmate).1.ne
  exact restore_ordinary_triangle_mate_of_profile D u a b c hsub hbc
    (ordinaryMatePuncture_missing M _ hmate) hbOdd hcOdd haOdd
    (triangle_component_even_neighbors C a b c hsupp)
    (ordinary_star_mates_even_preserved u B M hadj hleaves hdis havoid hedges) hcentre

end Gallai.TwoException
