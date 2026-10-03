/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.EarlySingleSpokeBudget

@[expose] public section

/-! # Native endpoint reserves after sole-single early preparation -/
namespace Gallai.TwoException
open scoped Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
noncomputable local instance preparationStarAdj (u : V) (B : Finset V) :
    DecidableRel (starPuncture G u B).Adj := fun _ _ => Classical.propDecidable _
noncomputable local instance preparationAuxAdj (u x q : V) (B : Finset V)
    (O : List (V × V)) : DecidableRel
      (ordinaryMatePuncture ((starPuncture G u B).deleteEdges {s(x,q)}) O).Adj :=
  fun _ _ => Classical.propDecidable _

/-- Paying the spoke and ordinary mates preserves the protected budget,
creates the sole-single mate reserve, and leaves an odd centre positive. -/
theorem prepare_early_single_spoke
    (u x q h : V) (B : Finset V) (O : List (V × V))
    (hadj : ∀ t ∈ B, G.Adj u t) (hleaves : ∀ t ∈ B, Even (G.degree t))
    (huOdd : Odd (G.degree u)) (hEvenB : Even #B)
    (hxB : x ∉ B) (hxu : x ≠ u) (hqu : q ≠ u) (hqB : q ∉ B)
    (hxq : G.Adj x q) (hqEven : Even (G.degree q))
    (hdis : O.Pairwise (fun e f =>
      e.1 ≠ f.1 ∧ e.1 ≠ f.2 ∧ e.2 ≠ f.1 ∧ e.2 ≠ f.2))
    (havoid : ∀ e ∈ O,
      e.1 ≠ u ∧ e.2 ≠ u ∧ e.1 ∉ B ∧ e.2 ∉ B)
    (hedges : ∀ e ∈ O, G.Adj e.1 e.2 ∧
      Even (G.degree e.1) ∧ Even (G.degree e.2))
    (hxAvoid : ∀ e ∈ O, x ≠ e.1 ∧ x ≠ e.2)
    (hqAvoid : ∀ e ∈ O, q ≠ e.1 ∧ q ≠ e.2)
    (hhAvoid : ∀ e ∈ O, h ≠ e.1 ∧ h ≠ e.2)
    (hhx : x ≠ h) (hhq : q ≠ h)
    (hpacket : ∀ e ∈ O, ∃ (C : (evenSubgraph G).ConnectedComponent)
      (a b c : evenVertices G), e = ((b : V),(c : V)) ∧
      C.supp = {a,b,c} ∧ (a : V) ∈ B)
    (D : Decomposition (ordinaryMatePuncture
      ((starPuncture G u B).deleteEdges {s(x,q)}) (O ++ [])))
    (hxOdd : Odd ((ordinaryMatePuncture
      ((starPuncture G u B).deleteEdges {s(x,q)}) (O ++ [])).degree x))
    (hzero : eDegree (ordinaryMatePuncture
      ((starPuncture G u B).deleteEdges {s(x,q)}) (O ++ [])) q = 0)
    (hh : 2 ≤ D.endpointCount h) :
    ∃ E : Decomposition (starPuncture G u B), E.size = D.size ∧
      2 ≤ E.endpointCount h ∧ 2 ≤ E.endpointCount q ∧
      0 < E.endpointCount u ∧ (∀ t ∈ B, 0 < E.endpointCount t) ∧
      (∀ e ∈ O, 2 ≤ E.endpointCount e.1) := by
  classical
  have hr := restore_early_spoke_and_ordinary_prefix u x q B O []
    hadj hleaves huOdd hEvenB hxB hxu hqu hxq
    (by simpa using hdis) (by simpa using havoid)
    (by simpa using hedges) (by simpa using hxAvoid) hpacket
  obtain ⟨E, hs, hp, hrec, htransfer⟩ := hr D hxOdd hzero
  have hqh := early_single_prefix_recipient_surplus u x q B (O ++ [])
    hxu hqu hqB hxq hqEven (by simpa using hqAvoid) D E
    (htransfer q hqAvoid)
  have hhh := htransfer h hhAvoid
  simp only [hhx, hhq, ite_false, Nat.add_zero] at hhh
  have hcentre := ordinary_star_mates_centre_reserve u B [] hadj huOdd hEvenB
    (by simp) E
  exact ⟨E, hs, hhh.symm ▸ hh, hqh, hcentre, hp, hrec⟩

end Gallai.TwoException
