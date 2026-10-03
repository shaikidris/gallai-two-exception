/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.ContactE2

@[expose] public section

/-! # Hub-prescribed mate-contact restoration -/
namespace Gallai.TwoException
open scoped Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {R : SimpleGraph V} [DecidableRel R.Adj]
noncomputable local instance E4StarAdj (u v : V) (S : Finset V) :
    DecidableRel (starPuncture R u (insert v S)).Adj :=
  fun _ _ => Classical.propDecidable _
noncomputable local instance E4DeleteAdj (u v p q : V) (S : Finset V) :
    DecidableRel ((starPuncture R u (insert v S)).deleteEdges {s(q,p)}).Adj :=
  fun _ _ => Classical.propDecidable _

/-- Restore E4 with the hub prescribed inward. No E-degree restriction
is imposed on that hub; only the other contact leaves have the private cap. -/
theorem restore_contact_E4
    (u v x p q h : V) (S : Finset V)
    (hu : u ∉ S) (hv : v ∉ S) (huv : u ≠ v)
    (huOdd : Odd (R.degree u)) (hodd : Odd #S) (huvAdj : R.Adj u v)
    (hadj : ∀ t ∈ S, R.Adj u t) (heven : ∀ t ∈ S, Even (R.degree t))
    (hx : x ∈ S) (hcap : ∀ w ∈ S, w ≠ x → eDegree R w ≤ 2)
    (hseparate : ∀ w ∈ S, ¬ R.Adj v w)
    (hqu : q ≠ u) (hqv : q ≠ v) (hqS : q ∉ S)
    (hpu : p ≠ u) (hpv : p ≠ v) (hpS : p ∉ S)
    (hqp : R.Adj q p) (hqEven : Even (R.degree q)) (hpEven : Even (R.degree p))
    (hpvAdj : ¬ R.Adj p v)
    (hpair : ∀ t, R.Adj p t → Even (R.degree t) → t = x ∨ t = q)
    (hvq : ¬ R.Adj v q) (huq : ¬ R.Adj u q)
    (hhu : h ≠ u) (hhv : h ≠ v) (hhq : h ≠ q) (hhp : h ≠ p) (hhS : h ∉ S)
    (D : Decomposition ((starPuncture R u (insert v S)).deleteEdges {s(q,p)}))
    (hretained : ∀ t, R.Adj u t → t ∉ S → t ≠ p →
      Odd (R.degree t) ∨ 0 < D.endpointCount t)
    (hvpositive : ∀ t, (starPuncture R u (insert v S)).Adj v t →
      0 < D.endpointCount t) :
    ∃ F : Decomposition R, F.size = D.size ∧ 1 ≤ F.endpointCount u ∧
      F.endpointCount v = D.endpointCount v + 1 ∧
      F.endpointCount h = D.endpointCount h := by
  exact restore_contact_E2 u v q x p h S hu hv huv huOdd hodd huvAdj
    hadj heven hx hcap hseparate hqu hqv hqS hpu hpv hpS
    hqp hqEven hpEven hpvAdj (fun t ht he => (hpair t ht he).symm)
    hvq huq hhu hhv hhq hhp hhS D hretained hvpositive

end Gallai.TwoException
