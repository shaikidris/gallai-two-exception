/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.ContactSpoke

@[expose] public section

/-! # Double-petal contact restoration -/
namespace Gallai.TwoException
open scoped Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {R : SimpleGraph V} [DecidableRel R.Adj]
noncomputable local instance E2StarAdj (u v : V) (S : Finset V) :
    DecidableRel (starPuncture R u (insert v S)).Adj :=
  fun _ _ => Classical.propDecidable _
noncomputable local instance E2DeleteAdj (u v x q : V) (S : Finset V) :
    DecidableRel ((starPuncture R u (insert v S)).deleteEdges {s(x,q)}).Adj :=
  fun _ _ => Classical.propDecidable _

/-- The retained double-petal contact is supplied by spoke restoration;
all other contact positivity follows from the actual puncture parity. -/
theorem restore_contact_E2
    (u v x p q h : V) (S : Finset V)
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
    (hhu : h ≠ u) (hhv : h ≠ v) (hhx : h ≠ x) (hhq : h ≠ q) (hhS : h ∉ S)
    (D : Decomposition ((starPuncture R u (insert v S)).deleteEdges {s(x,q)}))
    (hretained : ∀ t, R.Adj u t → t ∉ S → t ≠ q →
      Odd (R.degree t) ∨ 0 < D.endpointCount t)
    (hvpositive : ∀ t, (starPuncture R u (insert v S)).Adj v t →
      0 < D.endpointCount t) :
    ∃ F : Decomposition R, F.size = D.size ∧ 1 ≤ F.endpointCount u ∧
      F.endpointCount v = D.endpointCount v + 1 ∧
      F.endpointCount h = D.endpointCount h := by
  classical
  let J := starPuncture R u (insert v S)
  have huI : u ∉ insert v S := by simp [huv, hu]
  have hsub : J ≤ R := fun _ _ ha => ha.1
  obtain ⟨E, hs, hEq, he⟩ := restore_double_petal_contact_spoke u v x p q S hp
    hadj heven hxu hxv hxS hqu hqv hqS hxq hxEven hqEven hu hv huv
    huOdd hodd huvAdj hqvAdj hpair D
  have hmissing : ∀ w ∈ S, ¬ J.Adj u w := fun w hw =>
    starPuncture_missing R u (insert v S) huI w (Finset.mem_insert_of_mem hw)
  have hreserved : ¬ J.Adj u v :=
    starPuncture_missing R u (insert v S) huI v (Finset.mem_insert_self _ _)
  have hpositive : ∀ t, J.Adj u t ∨ t ∈ S → 0 < E.endpointCount t := by
    intro t ht
    by_cases htq : t = q
    · subst t
      omega
    by_cases htS : t ∈ S
    · apply E.endpointCount_pos_of_odd_degree
      have hd := starPuncture_degree_leaf (G := R) u (insert v S) t
        (Finset.mem_insert_of_mem htS) (hadj t htS)
      have hE := heven t htS
      simp only [← SimpleGraph.ncard_neighborSet] at hd hE ⊢
      rw [Nat.even_iff] at hE
      rw [Nat.odd_iff]
      omega
    · have ha := ht.resolve_right htS
      have htR := hsub ha
      have htu : t ≠ u := htR.ne.symm
      have htv : t ≠ v := fun e => hreserved (e ▸ ha)
      have hd := starPuncture_degree_other (G := R) u (insert v S) t htu
        (by simp [htv, htS])
      rcases hretained t htR htS htq with ho | hpD
      · apply E.endpointCount_pos_of_odd_degree
        simp only [← SimpleGraph.ncard_neighborSet] at hd ho ⊢
        rwa [hd]
      · have htx : t ≠ x := fun e => hux (e ▸ htR)
        have hqt : q ≠ t := fun e => htq e.symm
        have hh := he t
        simp only [htx.symm, hqt, ite_false, Nat.add_zero] at hh
        rw [hh]
        exact hpD
  have hEp : ∀ t, J.Adj v t → 0 < E.endpointCount t := by
    intro t ht
    have htx : t ≠ x := fun e => hvx (e ▸ ht.1)
    have htq : t ≠ q := fun e => hqvAdj (e ▸ ht.1.symm)
    have hh := he t
    simp only [htx.symm, htq.symm, ite_false, Nat.add_zero] at hh
    rw [hh]
    exact hvpositive t ht
  have hoddpositive : ∀ w ∈ S, w ≠ p → ∀ t,
      J.Adj w t → Odd (R.degree t) → 0 < E.endpointCount t := by
    intro w hw _ t ha ho
    have htu : t ≠ u := fun e => hmissing w hw (e ▸ ha.symm)
    have htv : t ≠ v := fun e => hseparate w hw (e ▸ (hsub ha).symm)
    have htS : t ∉ S := by
      intro ht
      have hE := heven t ht
      rw [Nat.even_iff] at hE
      rw [Nat.odd_iff] at ho
      omega
    apply E.endpointCount_pos_of_odd_degree
    have hd := starPuncture_degree_other (G := R) u (insert v S) t htu
      (by simp [htv, htS])
    simp only [← SimpleGraph.ncard_neighborSet] at hd ho ⊢
    rwa [hd]
  obtain ⟨F, hfs, hfu, hfv, hkeep⟩ :=
    restore_odd_contact_sequence_of_original_even_cap R E u v p S hsub hu hv huv
      hreserved hmissing (fun w hw ha => hseparate w hw (hsub ha)) hpositive hEp
      (E.endpointCount_pos_of_odd_degree u
        (contact_puncture_center_odd u v S hu hv huv huOdd hodd huvAdj hadj))
      hodd hp heven hcap hoddpositive
  have hvkeep := he v
  simp only [hxv, hqv, ite_false, Nat.add_zero] at hvkeep
  have hhkeep := he h
  simp only [hhx.symm, hhq.symm, ite_false, Nat.add_zero] at hhkeep
  have hr : (J ⊔ S.sup (SimpleGraph.edge u)) ⊔ SimpleGraph.edge v u = R := by
    have hr := starPuncture_restore R u (insert v S) (by
      intro t ht
      rcases Finset.mem_insert.mp ht with rfl | ht
      · exact huvAdj
      · exact hadj t ht)
    simpa only [J, Finset.sup_insert, SimpleGraph.edge_comm v u,
      sup_assoc, sup_left_comm, sup_comm] using hr
  have hout : ∃ F : Decomposition ((J ⊔ S.sup (SimpleGraph.edge u)) ⊔
      SimpleGraph.edge v u), F.size = D.size ∧ 1 ≤ F.endpointCount u ∧
      F.endpointCount v = D.endpointCount v + 1 ∧
      F.endpointCount h = D.endpointCount h := by
    refine ⟨F, hfs.trans hs, hfu, ?_, ?_⟩
    · rw [hfv, hvkeep]
    · exact (hkeep h hhu hhv hhS).trans hhkeep
  rwa [hr] at hout

end Gallai.TwoException
