/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.ContactPunctureWitness

@[expose] public section

/-! # Parity profile of a hub-contact mate puncture -/
namespace Gallai.TwoException
open scoped Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
noncomputable local instance mateProfileStarAdj (u : V) (B : Finset V) :
    DecidableRel (starPuncture G u B).Adj := fun _ _ => Classical.propDecidable _
noncomputable local instance mateProfileDeleteAdj (u p q : V) (B : Finset V) :
    DecidableRel ((starPuncture G u B).deleteEdges {s(p,q)}).Adj :=
  fun _ _ => Classical.propDecidable _

/-- The star flips its hub leaf, and the mate deletion flips both private
endpoints. No originally odd vertex becomes even. -/
theorem contact_mate_puncture_profile
    (u x p q : V) (B : Finset V) (hu : u ∉ B)
    (hadj : ∀ t ∈ B, G.Adj u t)
    (huOdd : Odd (G.degree u)) (hB : Even #B)
    (hleaves : ∀ t ∈ B, Even (G.degree t))
    (hxB : x ∈ B) (hxp : x ≠ p) (hxq : x ≠ q)
    (hpu : p ≠ u) (hqu : q ≠ u) (hpB : p ∉ B) (hqB : q ∉ B)
    (hpq : G.Adj p q) (hpEven : Even (G.degree p)) (hqEven : Even (G.degree q)) :
    (∀ t, Even (((starPuncture G u B).deleteEdges {s(p,q)}).degree t) →
      Even (G.degree t)) ∧
    Odd (((starPuncture G u B).deleteEdges {s(p,q)}).degree x) ∧
    Odd (((starPuncture G u B).deleteEdges {s(p,q)}).degree p) ∧
    Odd (((starPuncture G u B).deleteEdges {s(p,q)}).degree q) := by
  classical
  have hp := contact_spoke_puncture_profile u p q B hu hadj huOdd hB hleaves
    hpu hqu hpB hqB hpq hpEven hqEven
  refine ⟨hp.1, ?_, hp.2.1, hp.2.2⟩
  have hxOdd := contact_spoke_puncture_leaf_odd u p q x B hxB (hadj x hxB)
    (hleaves x hxB) hxp hxq
  exact hxOdd

end Gallai.TwoException
