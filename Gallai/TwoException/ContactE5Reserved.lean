/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.ContactE5

@[expose] public section

/-! # Ordered E5 restoration exposing the reserved endpoint -/
namespace Gallai.TwoException
open scoped Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {R : SimpleGraph V} [DecidableRel R.Adj]
noncomputable local instance reservedE5StarAdj (u v : V) (S : Finset V) :
    DecidableRel (starPuncture R u (insert v S)).Adj := fun _ _ => Classical.propDecidable _
noncomputable local instance reservedE5SpokeAdj (u v x s : V) (S : Finset V) :
    DecidableRel ((starPuncture R u (insert v S)).deleteEdges {s(x,s)}).Adj :=
  fun _ _ => Classical.propDecidable _
noncomputable local instance reservedE5MateAdj (u v x s p q : V) (S : Finset V) :
    DecidableRel (((starPuncture R u (insert v S)).deleteEdges {s(x,s)}).deleteEdges
      {s(q,p)}).Adj := fun _ _ => Classical.propDecidable _

/-- Restore the mate, separate spoke, contact star and reserved edge in order.
The reserved endpoint gains one occurrence at unchanged path count. -/
theorem restore_contact_E5_reserved_endpoint
    (u v x s p q r : V) (S : Finset V)
    (hu : u ∉ S) (hv : v ∉ S) (huv : u ≠ v)
    (huOdd : Odd (R.degree u)) (hodd : Odd #S) (huvAdj : R.Adj u v)
    (hadj : ∀ t ∈ S, R.Adj u t) (heven : ∀ t ∈ S, Even (R.degree t))
    (hr : r ∈ S) (hcap : ∀ w ∈ S, w ≠ r → eDegree R w ≤ 2)
    (hseparate : ∀ w ∈ S, ¬ R.Adj v w)
    (hxu : x ≠ u) (hxv : x ≠ v) (hxS : x ∉ S) (hsu : s ≠ u)
    (hxs : R.Adj x s) (hxEven : Even (R.degree x)) (hsEven : Even (R.degree s))
    (hpvAdj : ¬ R.Adj p v)
    (hpairP : ∀ t, R.Adj p t → Even (R.degree t) → t = x ∨ t = q)
    (hpu : p ≠ u) (hpv : p ≠ v) (hpS : p ∉ S) (hpx : p ≠ x) (hps : p ≠ s)
    (hqu : q ≠ u) (hqv : q ≠ v) (hqS : q ∉ S) (hqx : q ≠ x) (hqs : q ≠ s)
    (hqp : R.Adj q p) (hpEven : Even (R.degree p)) (hqEven : Even (R.degree q))
    (hsuAdj : ¬ R.Adj s u) (hsvAdj : ¬ R.Adj s v)
    (hpairS : ∀ t, R.Adj s t → Even (R.degree t) → t = x ∨ t = r)
    (hvx : ¬ R.Adj v x) (hvq : ¬ R.Adj v q)
    (hux : ¬ R.Adj u x) (huq : ¬ R.Adj u q)
    (D : Decomposition (((starPuncture R u (insert v S)).deleteEdges {s(x,s)}).deleteEdges
      {s(q,p)}))
    (hretained : ∀ t, R.Adj u t → t ∉ S → t ≠ p →
      Odd (R.degree t) ∨ 0 < D.endpointCount t)
    (hvpositive : ∀ t, (starPuncture R u (insert v S)).Adj v t →
      0 < D.endpointCount t) :
    ∃ F : Decomposition R, F.size = D.size ∧ 1 ≤ F.endpointCount u ∧
      F.endpointCount v = D.endpointCount v + 1 := by
  classical
  obtain ⟨E, hs1, hEp, he1⟩ := restore_contact_E5_mate u v x s p q S hu hv huv
    huOdd hodd huvAdj hadj heven hxu hxv hxS hsu hxs hxEven hsEven
    hpvAdj hpairP hpu hpv hpS hpx hps hqu hqv hqS hqx hqs hqp hpEven hqEven D
  obtain ⟨K, hs2, he2⟩ := restore_single_petal_contact_spoke u v x r s S hr
    hadj heven hxu hxv hxS hsuAdj hsvAdj hsu hxs hxEven hpairS E
  have hKp : 0 < K.endpointCount p := by
    have hv := he2 p
    simp only [hpx.symm, hps.symm, ite_false, Nat.add_zero] at hv
    omega
  have hKv : ∀ t, (starPuncture R u (insert v S)).Adj v t →
      0 < K.endpointCount t := by
    intro t ht
    have htx : t ≠ x := fun e => hvx (e ▸ ht.1)
    have hts : t ≠ s := fun e => hsvAdj (e ▸ ht.1.symm)
    have htp : t ≠ p := fun e => hpvAdj (e ▸ ht.1.symm)
    have htq : t ≠ q := fun e => hvq (e ▸ ht.1)
    have ha := he1 t
    have hb := he2 t
    simp only [htx.symm, hts.symm, htp.symm, htq.symm, ite_false,
      Nat.add_zero] at ha hb
    rw [hb, ha]
    exact hvpositive t ht
  have hKretained : ∀ t, R.Adj u t → t ∉ S → t ≠ p →
      Odd (R.degree t) ∨ 0 < K.endpointCount t := by
    intro t ht htS htp
    rcases hretained t ht htS htp with ho | hpD
    · exact Or.inl ho
    · right
      have htx : t ≠ x := fun e => hux (e ▸ ht)
      have htq : t ≠ q := fun e => huq (e ▸ ht)
      have hts : t ≠ s := fun e => hsuAdj (e ▸ ht.symm)
      have ha := he1 t
      have hb := he2 t
      simp only [htx.symm, hts.symm, htp.symm, htq.symm, ite_false,
        Nat.add_zero] at ha hb
      rw [hb, ha]
      exact hpD
  obtain ⟨F, hfs, hfu, hfv, _⟩ := restore_contact_with_retained_positive
    u v p r S hu hv huv huOdd hodd huvAdj hadj heven hr hcap
    hseparate K hKretained hKp hKv
  have hsv : s ≠ v := by
    intro e
    exact hvx (e ▸ hxs.symm)
  have hv1 := he1 v
  have hv2 := he2 v
  simp only [hqv, hpv, hxv, hsv, ite_false, Nat.add_zero] at hv1 hv2
  refine ⟨F, hfs.trans (hs2.trans hs1), hfu, ?_⟩
  rw [hfv, hv2, hv1]

end Gallai.TwoException
