/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.ContactE2
public import Gallai.TwoException.ContactRetained

@[expose] public section

/-! # E2 restoration exposing the reserved endpoint -/
namespace Gallai.TwoException
open scoped Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {R : SimpleGraph V} [DecidableRel R.Adj]
noncomputable local instance reservedE2StarAdj (u v : V) (S : Finset V) :
    DecidableRel (starPuncture R u (insert v S)).Adj :=
  fun _ _ => Classical.propDecidable _
noncomputable local instance reservedE2DeleteAdj (u v x q : V) (S : Finset V) :
    DecidableRel ((starPuncture R u (insert v S)).deleteEdges {s(x,q)}).Adj :=
  fun _ _ => Classical.propDecidable _

/-- Restore E2 with a positive reserve at its retained petal contact, while
increasing the reserved endpoint instead of preserving a separate vertex. -/
theorem restore_contact_E2_reserved_endpoint
    (u v x p q : V) (S : Finset V)
    (hu : u ∉ S) (hv : v ∉ S) (huv : u ≠ v)
    (huOdd : Odd (R.degree u)) (hodd : Odd #S) (huvAdj : R.Adj u v)
    (hadj : ∀ t ∈ S, R.Adj u t) (heven : ∀ t ∈ S, Even (R.degree t))
    (hp : p ∈ S) (hcap : ∀ w ∈ S, w ≠ p → eDegree R w ≤ 2)
    (hseparate : ∀ w ∈ S, ¬ R.Adj v w)
    (hxu : x ≠ u) (hxv : x ≠ v) (hxS : x ∉ S)
    (hqu : q ≠ u) (hqv : q ≠ v) (hqS : q ∉ S)
    (hxq : R.Adj x q) (hxEven : Even (R.degree x)) (hqEven : Even (R.degree q))
    (hqvAdj : ¬ R.Adj q v)
    (hpair : ∀ t, R.Adj q t → Even (R.degree t) → t = x ∨ t = p)
    (hvx : ¬ R.Adj v x) (hux : ¬ R.Adj u x)
    (D : Decomposition ((starPuncture R u (insert v S)).deleteEdges {s(x,q)}))
    (hretained : ∀ t, R.Adj u t → t ∉ S → t ≠ q →
      Odd (R.degree t) ∨ 0 < D.endpointCount t)
    (hvpositive : ∀ t, (starPuncture R u (insert v S)).Adj v t →
      0 < D.endpointCount t) :
    ∃ F : Decomposition R, F.size = D.size ∧ 1 ≤ F.endpointCount u ∧
      F.endpointCount v = D.endpointCount v + 1 := by
  classical
  obtain ⟨E, hs, hEq, he⟩ := restore_double_petal_contact_spoke u v x p q S hp
    hadj heven hxu hxv hxS hqu hqv hqS hxq hxEven hqEven hu hv huv
    huOdd hodd huvAdj hqvAdj hpair D
  have hEretained : ∀ t, R.Adj u t → t ∉ S → t ≠ u →
      Odd (R.degree t) ∨ 0 < E.endpointCount t := by
    intro t ht htS _
    by_cases htq : t = q
    · subst t
      right
      omega
    · rcases hretained t ht htS htq with ho | hpD
      · exact Or.inl ho
      · right
        have htx : t ≠ x := fun e => hux (e ▸ ht)
        have hqt : q ≠ t := fun e => htq e.symm
        have hh := he t
        simp only [htx.symm, hqt, ite_false, Nat.add_zero] at hh
        rw [hh]
        exact hpD
  have hEp : ∀ t, (starPuncture R u (insert v S)).Adj v t →
      0 < E.endpointCount t := by
    intro t ht
    have htx : t ≠ x := fun e => hvx (e ▸ ht.1)
    have htq : t ≠ q := fun e => hqvAdj (e ▸ ht.1.symm)
    have hh := he t
    simp only [htx.symm, htq.symm, ite_false, Nat.add_zero] at hh
    rw [hh]
    exact hvpositive t ht
  obtain ⟨F, hfs, hfu, hfv, _⟩ := restore_contact_with_retained_positive
    u v u p S hu hv huv huOdd hodd huvAdj hadj heven hp hcap hseparate
    E hEretained (E.endpointCount_pos_of_odd_degree u
      (contact_puncture_center_odd u v S hu hv huv huOdd hodd huvAdj hadj)) hEp
  have hvkeep := he v
  simp only [hxv, hqv, ite_false, Nat.add_zero] at hvkeep
  refine ⟨F, hfs.trans hs, hfu, ?_⟩
  rw [hfv, hvkeep]

end Gallai.TwoException
