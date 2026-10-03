/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.ContactE2Reserved

@[expose] public section

/-! # Mate-contact restoration exposing the reserved endpoint -/
namespace Gallai.TwoException
open scoped Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {R : SimpleGraph V} [DecidableRel R.Adj]
noncomputable local instance reservedE4StarAdj (u v : V) (S : Finset V) :
    DecidableRel (starPuncture R u (insert v S)).Adj :=
  fun _ _ => Classical.propDecidable _
noncomputable local instance reservedE4DeleteAdj (u v p q : V) (S : Finset V) :
    DecidableRel ((starPuncture R u (insert v S)).deleteEdges {s(q,p)}).Adj :=
  fun _ _ => Classical.propDecidable _

/-- Restore the deleted mate edge and contact star, prescribing the hub inward
and increasing the reserved endpoint count by one. -/
theorem restore_contact_E4_reserved_endpoint
    (u v x p q : V) (S : Finset V)
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
    (D : Decomposition ((starPuncture R u (insert v S)).deleteEdges {s(q,p)}))
    (hretained : ∀ t, R.Adj u t → t ∉ S → t ≠ p →
      Odd (R.degree t) ∨ 0 < D.endpointCount t)
    (hvpositive : ∀ t, (starPuncture R u (insert v S)).Adj v t →
      0 < D.endpointCount t) :
    ∃ F : Decomposition R, F.size = D.size ∧ 1 ≤ F.endpointCount u ∧
      F.endpointCount v = D.endpointCount v + 1 := by
  exact restore_contact_E2_reserved_endpoint u v q x p S hu hv huv huOdd hodd huvAdj
    hadj heven hx hcap hseparate hqu hqv hqS hpu hpv hpS
    hqp hqEven hpEven hpvAdj (fun t ht he => (hpair t ht he).symm)
    hvq huq D hretained hvpositive

end Gallai.TwoException
