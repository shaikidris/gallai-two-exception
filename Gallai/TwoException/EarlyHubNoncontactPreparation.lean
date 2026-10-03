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
noncomputable local instance hubNoncontactPreparationStar (u : V) (B : Finset V) :
    DecidableRel (starPuncture G u B).Adj := fun _ _ => Classical.propDecidable _
noncomputable local instance hubNoncontactPreparationAux (u : V) (B : Finset V) (O : List (V × V)) :
    DecidableRel (ordinaryMatePuncture (starPuncture G u B) O).Adj :=
  fun _ _ => Classical.propDecidable _

/-- Restore ordinary mates whose recipients avoid the centre. This needs
no centre endpoint reserve and leaves every hub-star edge deleted. -/
theorem prepare_early_hub_star_noncontact
    (u h : V) (B : Finset V) (O : List (V × V))
    (hadj : ∀ t ∈ B, G.Adj u t) (hleaves : ∀ t ∈ B, Even (G.degree t))
        (hdis : O.Pairwise (fun e f =>
      e.1 ≠ f.1 ∧ e.1 ≠ f.2 ∧ e.2 ≠ f.1 ∧ e.2 ≠ f.2))
    (havoid : ∀ e ∈ O, e.1 ≠ u ∧ e.2 ≠ u ∧ e.1 ∉ B ∧ e.2 ∉ B)
    (hedges : ∀ e ∈ O, G.Adj e.1 e.2 ∧ Even (G.degree e.1) ∧ Even (G.degree e.2))
    (hhAvoid : ∀ e ∈ O, h ≠ e.1 ∧ h ≠ e.2)
    (hpacket : ∀ e ∈ O, ∃ (C : (evenSubgraph G).ConnectedComponent)
      (a b c : evenVertices G), e = ((b : V),(c : V)) ∧
      C.supp = {a,b,c} ∧ (a : V) ∈ B)
    (hnoncontact : ∀ e ∈ O, ¬ G.Adj e.1 u)
    (D : Decomposition (ordinaryMatePuncture (starPuncture G u B) (O ++ [])))
    (hh : 2 ≤ D.endpointCount h) :
    ∃ E : Decomposition (starPuncture G u B), E.size = D.size ∧
      2 ≤ E.endpointCount h ∧
      (∀ t ∈ B, 0 < E.endpointCount t) ∧
      (∀ e ∈ O, 2 ≤ E.endpointCount e.1) ∧
      E.endpointCount u = D.endpointCount u := by
  classical
  obtain ⟨E,hs,hcentre,hrec,hkeep⟩ := restore_ordinary_mate_family u B hadj hleaves
    (O ++ []) (by simpa only [List.append_nil] using hdis)
    (by simpa only [List.append_nil] using havoid)
    (by simpa only [List.append_nil] using hedges)
    (by simpa only [List.append_nil] using hpacket) D
    (Or.inr (by simpa only [List.append_nil] using hnoncontact))
  have hleavesOdd := ordinary_star_mates_leaves_odd u B [] hadj hleaves (by simp)
  refine ⟨E,hs,?_,?_,?_,hcentre⟩
  · rw [hkeep h (by simpa only [List.append_nil] using hhAvoid)]; exact hh
  · intro t ht
    apply E.endpointCount_pos_of_odd_degree t
    have ho := hleavesOdd t ht
    simp only [← SimpleGraph.ncard_neighborSet] at ho ⊢
    simpa only [ordinaryMatePuncture] using ho
  · simpa only [List.append_nil] using hrec

end Gallai.TwoException
