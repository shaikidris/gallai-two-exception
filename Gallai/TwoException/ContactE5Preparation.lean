/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.ContactMate

@[expose] public section

/-! # Separate-spoke parity for E5 mate preparation -/
namespace Gallai.TwoException
open scoped Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {R : SimpleGraph V} [DecidableRel R.Adj]
noncomputable local instance E5StarAdj (u v : V) (S : Finset V) :
    DecidableRel (starPuncture R u (insert v S)).Adj :=
  fun _ _ => Classical.propDecidable _
noncomputable local instance E5SpokeAdj (u v x s : V) (S : Finset V) :
    DecidableRel ((starPuncture R u (insert v S)).deleteEdges {s(x,s)}).Adj :=
  fun _ _ => Classical.propDecidable _

/-- The separate deleted spoke makes the hub odd before E5 restores the
mate. The centre stays odd, and other original odd neighbours keep degree. -/
theorem contact_E5_mate_neighbors_odd
    (u v x s p q : V) (S : Finset V)
    (hu : u ∉ S) (hv : v ∉ S) (huv : u ≠ v)
    (huOdd : Odd (R.degree u)) (hodd : Odd #S) (huvAdj : R.Adj u v)
    (hadj : ∀ t ∈ S, R.Adj u t) (heven : ∀ t ∈ S, Even (R.degree t))
    (hxu : x ≠ u) (hxv : x ≠ v) (hxS : x ∉ S) (hsu : s ≠ u)
    (hxs : R.Adj x s) (hxEven : Even (R.degree x)) (hsEven : Even (R.degree s))
    (hpv : ¬ R.Adj p v)
    (hpair : ∀ t, R.Adj p t → Even (R.degree t) → t = x ∨ t = q) :
    ∀ t, ((starPuncture R u (insert v S)).deleteEdges {s(x,s)}).Adj p t →
      t ≠ q → Odd (((starPuncture R u (insert v S)).deleteEdges {s(x,s)}).degree t) := by
  classical
  let J := starPuncture R u (insert v S)
  have hedge : J.Adj x s := by
    refine ⟨hxs, ?_⟩
    rw [star_sup_adj_off_center u (insert v S) x s hxu]
    simp [hsu]
  intro t ht htq
  have htR : R.Adj p t := ht.1.1
  by_cases htu : t = u
  · subst t
    have hd := degree_delete_edge_of_ne J x s u hxu.symm hsu.symm
    have ho := contact_puncture_center_odd u v S hu hv huv huOdd hodd huvAdj hadj
    simp only [← SimpleGraph.ncard_neighborSet] at hd ho ⊢
    rwa [hd]
  by_cases htEven : Even (R.degree t)
  · have htx : t = x := (hpair t htR htEven).resolve_right htq
    subst t
    have hd := degree_delete_edge_add_one J x s hedge
    have hxdeg := starPuncture_degree_other (G := R) u (insert v S) x hxu
      (by simp [hxv, hxS])
    dsimp only [J] at hd
    simp only [← SimpleGraph.ncard_neighborSet] at hd hxdeg hxEven ⊢
    rw [Nat.even_iff] at hxEven
    rw [Nat.odd_iff]
    omega
  · have htv : t ≠ v := fun e => hpv (e ▸ htR)
    have htS : t ∉ S := fun ht => htEven (heven t ht)
    have htx : t ≠ x := fun e => htEven (e ▸ hxEven)
    have hts : t ≠ s := fun e => htEven (e ▸ hsEven)
    have hd := degree_delete_edge_of_ne J x s t htx hts
    have hj := starPuncture_degree_other (G := R) u (insert v S) t htu
      (by simp [htv, htS])
    have ho := Nat.not_even_iff_odd.mp htEven
    simp only [← SimpleGraph.ncard_neighborSet] at hd hj ho ⊢
    rw [hd, hj]
    exact ho

noncomputable local instance E5MateAdj (u v x s p q : V) (S : Finset V) :
    DecidableRel (((starPuncture R u (insert v S)).deleteEdges {s(x,s)}).deleteEdges
      {s(q,p)}).Adj := fun _ _ => Classical.propDecidable _

/-- E5 restores its mate while the separate spoke and reserved edge remain
absent. The retained contact receives two endpoints. -/
theorem restore_contact_E5_mate
    (u v x s p q : V) (S : Finset V)
    (hu : u ∉ S) (hv : v ∉ S) (huv : u ≠ v)
    (huOdd : Odd (R.degree u)) (hodd : Odd #S) (huvAdj : R.Adj u v)
    (hadj : ∀ t ∈ S, R.Adj u t) (heven : ∀ t ∈ S, Even (R.degree t))
    (hxu : x ≠ u) (hxv : x ≠ v) (hxS : x ∉ S) (hsu : s ≠ u)
    (hxs : R.Adj x s) (hxEven : Even (R.degree x)) (hsEven : Even (R.degree s))
    (hpvAdj : ¬ R.Adj p v)
    (hpair : ∀ t, R.Adj p t → Even (R.degree t) → t = x ∨ t = q)
    (hpu : p ≠ u) (hpv : p ≠ v) (hpS : p ∉ S) (hpx : p ≠ x) (hps : p ≠ s)
    (hqu : q ≠ u) (hqv : q ≠ v) (hqS : q ∉ S) (hqx : q ≠ x) (hqs : q ≠ s)
    (hqp : R.Adj q p) (hpEven : Even (R.degree p)) (hqEven : Even (R.degree q))
    (D : Decomposition (((starPuncture R u (insert v S)).deleteEdges {s(x,s)}).deleteEdges
      {s(q,p)})) :
    ∃ E : Decomposition ((starPuncture R u (insert v S)).deleteEdges {s(x,s)}),
      E.size = D.size ∧ 2 ≤ E.endpointCount p ∧ ∀ t,
        E.endpointCount t + (if q = t then 1 else 0) =
          D.endpointCount t + if p = t then 1 else 0 := by
  classical
  let J := starPuncture R u (insert v S)
  let K := J.deleteEdges {s(x,s)}
  have hedgeJ : J.Adj q p := by
    refine ⟨hqp, ?_⟩
    rw [star_sup_adj_off_center u (insert v S) q p hqu]
    simp [hpu]
  have hedge : K.Adj q p := by
    simpa [K, SimpleGraph.deleteEdges_adj, hqx, hqs] using hedgeJ
  have hdegree : ∀ t, t ≠ u → t ≠ v → t ∉ S → t ≠ x → t ≠ s →
      K.degree t = R.degree t := by
    intro t htu htv htS htx hts
    have hd := degree_delete_edge_of_ne J x s t htx hts
    have hj := starPuncture_degree_other (G := R) u (insert v S) t htu
      (by simp [htv, htS])
    dsimp only [K, J] at hd ⊢
    simp only [← SimpleGraph.ncard_neighborSet] at hd hj ⊢
    exact hd.trans hj
  have hqE : Even (K.degree q) := by
    rw [hdegree q hqu hqv hqS hqx hqs]
    exact hqEven
  have hpO : Odd ((K.deleteEdges {s(q,p)}).degree p) := by
    have hd := degree_delete_edge_add_one_other K q p hedge
    have hpdeg := hdegree p hpu hpv hpS hpx hps
    dsimp only [K, J] at hd hpdeg ⊢
    simp only [← SimpleGraph.ncard_neighborSet] at hd hpdeg hpEven ⊢
    rw [Nat.even_iff] at hpEven
    rw [Nat.odd_iff]
    omega
  obtain ⟨E, hs, he⟩ := restore_contact_spoke q p hedge hqE
    (contact_E5_mate_neighbors_odd u v x s p q S hu hv huv huOdd hodd
      huvAdj hadj heven hxu hxv hxS hsu hxs hxEven hsEven hpvAdj hpair) D
  refine ⟨E, hs, ?_, he⟩
  have hpos := D.endpointCount_pos_of_odd_degree p hpO
  have hv := he p
  simp only [hqp.ne, ite_false, ite_true, Nat.add_zero] at hv
  omega

end Gallai.TwoException
