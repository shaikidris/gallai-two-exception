/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.EarlyHubAuxiliaryBudget
public import Gallai.TwoException.EarlyPrefixRestoration

@[expose] public section

/-! # Ordinary-prefix preparation with the hub edge still deleted -/
namespace Gallai.TwoException
open scoped Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
noncomputable local instance hubPreparationStar (u : V) (B : Finset V) :
    DecidableRel (starPuncture G u B).Adj := fun _ _ => Classical.propDecidable _
noncomputable local instance hubPreparationAux (u : V) (B : Finset V) (O : List (V × V)) :
    DecidableRel (ordinaryMatePuncture (starPuncture G u B) O).Adj :=
  fun _ _ => Classical.propDecidable _

/-- An even deletion star gives the odd centre reserve needed to restore
the ordinary mates. Every star edge, including the hub edge, stays absent.
The protected endpoint count and centre reserve are unchanged. -/
theorem prepare_early_hub_star
    (u h : V) (B : Finset V) (O : List (V × V))
    (hadj : ∀ t ∈ B, G.Adj u t) (hleaves : ∀ t ∈ B, Even (G.degree t))
    (huOdd : Odd (G.degree u)) (hEvenB : Even #B)
    (hdis : O.Pairwise (fun e f =>
      e.1 ≠ f.1 ∧ e.1 ≠ f.2 ∧ e.2 ≠ f.1 ∧ e.2 ≠ f.2))
    (havoid : ∀ e ∈ O, e.1 ≠ u ∧ e.2 ≠ u ∧ e.1 ∉ B ∧ e.2 ∉ B)
    (hedges : ∀ e ∈ O, G.Adj e.1 e.2 ∧ Even (G.degree e.1) ∧ Even (G.degree e.2))
    (hhAvoid : ∀ e ∈ O, h ≠ e.1 ∧ h ≠ e.2)
    (hpacket : ∀ e ∈ O, ∃ (C : (evenSubgraph G).ConnectedComponent)
      (a b c : evenVertices G), e = ((b : V),(c : V)) ∧
      C.supp = {a,b,c} ∧ (a : V) ∈ B)
    (D : Decomposition (ordinaryMatePuncture (starPuncture G u B) (O ++ [])))
    (hh : 2 ≤ D.endpointCount h) :
    ∃ E : Decomposition (starPuncture G u B), E.size = D.size ∧
      2 ≤ E.endpointCount h ∧ 0 < E.endpointCount u ∧
      (∀ t ∈ B, 0 < E.endpointCount t) ∧
      (∀ e ∈ O, 2 ≤ E.endpointCount e.1) ∧
      E.endpointCount u = D.endpointCount u := by
  classical
  have hu := ordinary_star_mates_centre_reserve u B (O ++ []) hadj huOdd hEvenB
    (by
      intro e he
      simp only [List.append_nil] at he
      exact ⟨(havoid e he).1,(havoid e he).2.1⟩) D
  obtain ⟨E,hs,hcentre,hrec,hkeep⟩ := restore_ordinary_mate_prefix u B hadj hleaves O []
    (by simpa using hdis) (by simpa using havoid) (by simpa using hedges) hpacket D hu
  have hleavesOdd := ordinary_star_mates_leaves_odd u B [] hadj hleaves (by simp)
  have hout : ∃ E : Decomposition (ordinaryMatePuncture (starPuncture G u B) []),
      E.size = D.size ∧ 2 ≤ E.endpointCount h ∧ 0 < E.endpointCount u ∧
      (∀ t ∈ B, 0 < E.endpointCount t) ∧
      (∀ e ∈ O, 2 ≤ E.endpointCount e.1) ∧
      E.endpointCount u = D.endpointCount u := by
    refine ⟨E,hs,(hkeep h hhAvoid).symm ▸ hh,hcentre.symm ▸ hu,?_,hrec,hcentre⟩
    intro t ht
    exact E.endpointCount_pos_of_odd_degree t (hleavesOdd t ht)
  simpa only [ordinaryMatePuncture] using hout

end Gallai.TwoException
