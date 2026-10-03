/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.EarlyHubPreparation

@[expose] public section

/-! # Native mixed hub auxiliary followed by preparation -/
namespace Gallai.TwoException
open scoped Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
noncomputable local instance nativeHubPreparationStar (u : V) (B : Finset V) :
    DecidableRel (starPuncture G u B).Adj := fun _ _ => Classical.propDecidable _
noncomputable local instance nativeHubPreparationAux (u : V) (B : Finset V) (M : List (V × V)) :
    DecidableRel (ordinaryMatePuncture (starPuncture G u B) M).Adj :=
  fun _ _ => Classical.propDecidable _

/-- Original mixed packet labels construct the auxiliary budget and restore
its ordinary mates, without assuming any auxiliary decomposition. -/
theorem bare_native_early_hub_preparation
    (h u : V) (x : evenVertices G) (H : BareMinimalCounterexample G h (x : V))
    (B privates : Finset V) (M : List (V × V))
    (F : Finset (evenSubgraph G).ConnectedComponent)
    (hxB : (x : V) ∈ B) (hadj : ∀ t ∈ B, G.Adj u t)
    (hleaves : ∀ t ∈ B, Even (G.degree t))
    (hdis : M.Pairwise (fun e f =>
      e.1 ≠ f.1 ∧ e.1 ≠ f.2 ∧ e.2 ≠ f.1 ∧ e.2 ≠ f.2))
    (havoid : ∀ e ∈ M, e.1 ≠ u ∧ e.2 ≠ u ∧ e.1 ∉ B ∧ e.2 ∉ B)
    (hedges : ∀ e ∈ M, G.Adj e.1 e.2 ∧ Even (G.degree e.1) ∧ Even (G.degree e.2))
    (hcontacts : ∀ t, G.Adj u t → Even (G.degree t) →
      t ∈ B ∨ (∃ e ∈ M, t = e.1 ∨ t = e.2) ∨ t = h)
    (hB : ∀ t ∈ B, t = (x : V) ∨ t ∈ privates ∨
      ∃ C ∈ F, ∃ v : evenVertices G, v ∈ C.supp ∧ (v : V) = t)
    (hM : ∀ e ∈ M, ∀ t, t = e.1 ∨ t = e.2 →
      ∃ C ∈ F, ∃ v : evenVertices G, v ∈ C.supp ∧ (v : V) = t)
    (hprivateNonempty : privates.Nonempty)
    (hprivateCentre : u ∉ privates)
    (hprivates : ∀ t ∈ privates, G.Adj t x ∧ eDegree G t = 2)
    (hprivateContacts : ∀ t ∈ privates, G.Adj t u → t ∈ B)
    (hordinary : ∀ C ∈ F,
      (∀ t : evenVertices G, t ∈ C.supp → (t : V) ∈ B ∨
        ∃ e ∈ M, (t : V) = e.1 ∨ (t : V) = e.2) ∨
      ∃ a b c : evenVertices G, C.supp = {a,b,c} ∧
        (a : V) ∈ B ∧ (b : V) ∈ B ∧ G.Adj a c ∧ G.Adj b c ∧
        (a : V) ≠ u ∧ (b : V) ≠ u ∧ (c : V) ≠ u ∧
        (∀ e ∈ M, (c : V) ≠ e.1 ∧ (c : V) ≠ e.2) ∧ ¬ G.Adj c u)
    (hhu : h ≠ u) (hhB : h ∉ B)
    (hhM : ∀ e ∈ M, h ≠ e.1 ∧ h ≠ e.2)
    (huOdd : Odd (G.degree u)) (hEvenB : Even #B)
    (hpacket : ∀ e ∈ M, ∃ (C : (evenSubgraph G).ConnectedComponent)
      (a b c : evenVertices G), e = ((b : V),(c : V)) ∧
      C.supp = {a,b,c} ∧ (a : V) ∈ B) :
    ∃ E : Decomposition (starPuncture G u B),
      E.size ≤ (Fintype.card V + 1) / 2 ∧ 2 ≤ E.endpointCount h ∧
      0 < E.endpointCount u ∧ (∀ t ∈ B, 0 < E.endpointCount t) ∧
      (∀ e ∈ M, 2 ≤ E.endpointCount e.1) := by
  classical
  have haux : ∃ D : Decomposition (ordinaryMatePuncture (starPuncture G u B) (M ++ [])),
      D.size ≤ (Fintype.card V + 1) / 2 ∧ 2 ≤ D.endpointCount h := by
    exact bare_early_hub_auxiliary_endpoint h u x H B privates (M ++ []) F
      hxB hadj hleaves (by simpa only [List.append_nil] using hdis)
      (by simpa only [List.append_nil] using havoid)
      (by simpa only [List.append_nil] using hedges)
      (by simpa only [List.append_nil] using hcontacts) hB
      (by simpa only [List.append_nil] using hM) hprivateNonempty
      hprivateCentre hprivates hprivateContacts
      (by simpa only [List.append_nil] using hordinary) hhu hhB
      (by simpa only [List.append_nil] using hhM)
  obtain ⟨D,hs,hh⟩ := haux
  obtain ⟨E,hsize,hhE,huE,hpos,hrec,_⟩ := prepare_early_hub_star u h B M
    hadj hleaves huOdd hEvenB hdis havoid hedges hhM hpacket D hh
  exact ⟨E,hsize.symm ▸ hs,hhE,huE,hpos,hrec⟩

end Gallai.TwoException
