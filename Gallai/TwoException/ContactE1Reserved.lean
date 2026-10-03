/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.ContactE1

@[expose] public section

/-! # E1 restoration exposing the reserved endpoint -/
namespace Gallai.TwoException
open scoped Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {R : SimpleGraph V} [DecidableRel R.Adj]

noncomputable local instance reservedE1StarAdj (u v : V) (S : Finset V) :
    DecidableRel (starPuncture R u (insert v S)).Adj :=
  fun _ _ => Classical.propDecidable _
noncomputable local instance reservedE1DeleteAdj (u v x q : V) (S : Finset V) :
    DecidableRel ((starPuncture R u (insert v S)).deleteEdges {s(x,q)}).Adj :=
  fun _ _ => Classical.propDecidable _

/-- E1 increases the reserved endpoint's count without requiring a distinct
protected vertex. This is the interface when that endpoint is itself h. -/
theorem restore_contact_E1_reserved_endpoint
    (u v x p q b : V) (S : Finset V)
    (hu : u ∉ S) (hv : v ∉ S) (huv : u ≠ v)
    (huOdd : Odd (R.degree u)) (hodd : Odd #S) (huvAdj : R.Adj u v)
    (hadj : ∀ t ∈ S, R.Adj u t) (heven : ∀ t ∈ S, Even (R.degree t))
    (hp : p ∈ S) (hb : b ∈ S)
    (hcap : ∀ w ∈ S, w ≠ b → eDegree R w ≤ 2)
    (hseparate : ∀ w ∈ S, ¬ R.Adj v w)
    (hxu : x ≠ u) (hxv : x ≠ v) (hxS : x ∉ S)
    (hqu : ¬ R.Adj q u) (hqv : ¬ R.Adj q v) (hqne : q ≠ u) (hqvne : q ≠ v)
    (hxq : R.Adj x q) (hxEven : Even (R.degree x))
    (hpair : ∀ t, R.Adj q t → Even (R.degree t) → t = x ∨ t = p)
    (hvx : ¬ R.Adj v x) (hux : ¬ R.Adj u x)
    (D : Decomposition ((starPuncture R u (insert v S)).deleteEdges {s(x,q)}))
    (hretained : ∀ t, R.Adj u t → t ∉ S →
      Odd (R.degree t) ∨ 0 < D.endpointCount t)
    (hvpositive : ∀ t, (starPuncture R u (insert v S)).Adj v t →
      0 < D.endpointCount t) :
    ∃ F : Decomposition R, F.size = D.size ∧ 1 ≤ F.endpointCount u ∧
      F.endpointCount v = D.endpointCount v + 1 := by
  classical
  obtain ⟨E, hs, he⟩ := restore_single_petal_contact_spoke u v x p q S hp
    hadj heven hxu hxv hxS hqu hqv hqne hxq hxEven hpair D
  have hEp : ∀ t, (starPuncture R u (insert v S)).Adj v t →
      0 < E.endpointCount t := by
    intro t ht
    have htx : t ≠ x := fun e => hvx (e ▸ ht.1)
    have htq : t ≠ q := fun e => hqv (e ▸ ht.1.symm)
    have hh := he t
    simp only [htx.symm, htq.symm, ite_false, Nat.add_zero] at hh
    rw [hh]
    exact hvpositive t ht
  have hEretained : ∀ t, R.Adj u t → t ∉ S → t ≠ u →
      Odd (R.degree t) ∨ 0 < E.endpointCount t := by
    intro t ht htS _
    rcases hretained t ht htS with ho | hpD
    · exact Or.inl ho
    · right
      have htx : t ≠ x := fun e => hux (e ▸ ht)
      have htq : t ≠ q := fun e => hqu (e ▸ ht.symm)
      have hh := he t
      simp only [htx.symm, htq.symm, ite_false, Nat.add_zero] at hh
      rw [hh]
      exact hpD
  obtain ⟨F, hfs, hfu, hfv, _⟩ := restore_contact_with_retained_positive
    u v u b S hu hv huv huOdd hodd huvAdj hadj heven hb hcap hseparate
    E hEretained (E.endpointCount_pos_of_odd_degree u
      (contact_puncture_center_odd u v S hu hv huv huOdd hodd huvAdj hadj)) hEp
  have hvkeep := he v
  simp only [hxv, hqvne, ite_false, Nat.add_zero] at hvkeep
  refine ⟨F, hfs.trans hs, hfu, ?_⟩
  rw [hfv, hvkeep]

end Gallai.TwoException
