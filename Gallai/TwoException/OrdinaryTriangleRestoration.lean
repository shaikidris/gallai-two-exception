/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.OrdinaryPreparationProfile
public import Gallai.TwoException.OrdinaryPreparations

@[expose] public section

/-! # Restoration in the actual ordinary triangle puncture -/
namespace Gallai.TwoException
open scoped Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
noncomputable local instance trianglePunctureAdj (u b c : V) (B : Finset V) :
    DecidableRel ((starPuncture G u B).deleteEdges {s(b,c)}).Adj :=
  fun _ _ => Classical.propDecidable _

/-- T1 and regular T2 mate restoration, with all mate parity and
retained-neighbour positivity derived from the literal deleted edges. -/
theorem restore_ordinary_triangle_puncture_mate
    (u a b c : V) (B : Finset V)
    (hadj : ∀ t ∈ B, G.Adj u t)
    (hleaves : ∀ t ∈ B, Even (G.degree t))
    (haB : a ∈ B) (hab : a ≠ b) (hac : a ≠ c)
    (hbu : b ≠ u) (hcu : c ≠ u) (hbB : b ∉ B) (hcB : c ∉ B)
    (hbc : G.Adj b c) (hbEven : Even (G.degree b)) (hcEven : Even (G.degree c))
    (heven : ∀ t, G.Adj b t → Even (G.degree t) → t = a ∨ t = c)
    (D : Decomposition ((starPuncture G u B).deleteEdges {s(b,c)}))
    (hcentre : ¬ ((starPuncture G u B).deleteEdges {s(b,c)}).Adj b u ∨
      0 < D.endpointCount u) :
    ∃ E : Decomposition (((starPuncture G u B).deleteEdges {s(b,c)}) ⊔
      SimpleGraph.edge b c), E.size = D.size ∧ 2 ≤ E.endpointCount b ∧
      ∀ t, E.endpointCount t + (if c = t then 1 else 0) =
        D.endpointCount t + if b = t then 1 else 0 := by
  classical
  obtain ⟨hprofile, hbOdd, hcOdd⟩ := ordinary_triangle_puncture_profile
    u b c B hadj hleaves hbu hcu hbB hcB hbc hbEven hcEven
  have haOdd := contact_spoke_puncture_leaf_odd u b c a B haB
    (hadj a haB) (hleaves a haB) hab hac
  have hsub : ((starPuncture G u B).deleteEdges {s(b,c)}) ≤ G := by
    intro v w hvw
    exact hvw.1.1
  have hmissing : ¬ ((starPuncture G u B).deleteEdges {s(b,c)}).Adj b c := by
    simp
  exact restore_ordinary_triangle_mate_of_profile D u a b c hsub hbc.ne
    hmissing hbOdd hcOdd haOdd heven hprofile hcentre

end Gallai.TwoException
