/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.ContactHalfStar
public import Gallai.TwoException.ContactRetained

@[expose] public section

/-! # The full-contact E3 puncture -/

namespace Gallai.TwoException

open scoped Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {R : SimpleGraph V} [DecidableRel R.Adj]

noncomputable local instance E3PunctureAdj (u v : V) (S : Finset V) :
    DecidableRel (starPuncture R u (insert v S)).Adj :=
  fun _ _ => Classical.propDecidable _

/-- E3 deletes the odd contact star and the separate reserved edge. Its
centre and every contact or retained centre neighbour are odd in the actual
puncture, supplying the half-star positivity without an endpoint assumption.
-/
theorem contact_E3_puncture_odd
    (u v : V) (S : Finset V) (hu : u ∉ S) (hv : v ∉ S) (huv : u ≠ v)
    (huOdd : Odd (R.degree u)) (hodd : Odd #S) (huvAdj : R.Adj u v)
    (hadj : ∀ t ∈ S, R.Adj u t)
    (heven : ∀ t ∈ S, Even (R.degree t))
    (hretained : ∀ t, R.Adj u t → t ∉ S → Odd (R.degree t)) :
    Odd ((starPuncture R u (insert v S)).degree u) ∧
      ∀ t, (starPuncture R u (insert v S)).Adj u t ∨ t ∈ S →
        Odd ((starPuncture R u (insert v S)).degree t) := by
  classical
  have huI : u ∉ insert v S := by simp [huv, hu]
  have hIadj : ∀ t ∈ insert v S, R.Adj u t := by
    intro t ht
    rcases Finset.mem_insert.mp ht with rfl | ht
    · exact huvAdj
    · exact hadj t ht
  constructor
  · have hd := starPuncture_degree_center (G := R) u (insert v S) huI
      (fun t ht => (R.mem_neighborFinset u t).mpr (hIadj t ht))
    have hc : #(insert v S) = #S + 1 := Finset.card_insert_of_notMem hv
    rw [hc] at hd
    rw [Nat.odd_iff] at huOdd hodd ⊢
    omega
  · intro t ht
    by_cases htS : t ∈ S
    · have hd := starPuncture_degree_leaf (G := R) u (insert v S) t
        (Finset.mem_insert_of_mem htS) (hadj t htS)
      have he := heven t htS
      rw [Nat.even_iff] at he
      rw [Nat.odd_iff]
      omega
    · have htAdj := ht.resolve_right htS
      have htR : R.Adj u t := htAdj.1
      have htu : t ≠ u := htR.ne.symm
      have htv : t ≠ v := by
        intro he
        subst t
        exact starPuncture_missing R u (insert v S) huI v
          (Finset.mem_insert_self _ _) htAdj
      have hd := starPuncture_degree_other (G := R) u (insert v S) t htu
        (by simp [htv, htS])
      rw [hd]
      exact hretained t htR htS

/-- E3's parity preparation supplies all centre and contact positivity. -/
theorem contact_E3_puncture_positive
    (u v : V) (S : Finset V) (hu : u ∉ S) (hv : v ∉ S) (huv : u ≠ v)
    (huOdd : Odd (R.degree u)) (hodd : Odd #S) (huvAdj : R.Adj u v)
    (hadj : ∀ t ∈ S, R.Adj u t)
    (heven : ∀ t ∈ S, Even (R.degree t))
    (hretained : ∀ t, R.Adj u t → t ∉ S → Odd (R.degree t))
    (D : Decomposition (starPuncture R u (insert v S))) :
    0 < D.endpointCount u ∧ ∀ t,
      (starPuncture R u (insert v S)).Adj u t ∨ t ∈ S →
      0 < D.endpointCount t := by
  obtain ⟨huJ, hleaf⟩ := contact_E3_puncture_odd u v S hu hv huv
    huOdd hodd huvAdj hadj heven hretained
  exact ⟨D.endpointCount_pos_of_odd_degree u huJ,
    fun t ht => D.endpointCount_pos_of_odd_degree t (hleaf t ht)⟩

/-- Restore E3's actual contact-star/reserved-edge puncture. All contact
positivity is derived; the reserved-neighbour reserve is the stated locality
guard from the contact lemma. The prescribed hub has no E-degree bound. -/
theorem restore_contact_E3
    (u v b : V) (S : Finset V) (hu : u ∉ S) (hv : v ∉ S) (huv : u ≠ v)
    (huOdd : Odd (R.degree u)) (hodd : Odd #S) (huvAdj : R.Adj u v)
    (hadj : ∀ t ∈ S, R.Adj u t)
    (heven : ∀ t ∈ S, Even (R.degree t))
    (hretained : ∀ t, R.Adj u t → t ∉ S → Odd (R.degree t))
    (hb : b ∈ S) (hcap : ∀ w ∈ S, w ≠ b → eDegree R w ≤ 2)
    (hseparate : ∀ w ∈ S, ¬ R.Adj v w)
    (D : Decomposition (starPuncture R u (insert v S)))
    (hvpositive : ∀ t, (starPuncture R u (insert v S)).Adj v t →
      0 < D.endpointCount t) :
    ∃ F : Decomposition R, F.size = D.size ∧ 1 ≤ F.endpointCount u ∧
      F.endpointCount v = D.endpointCount v + 1 ∧
      ∀ t, t ≠ u → t ≠ v → t ∉ S → F.endpointCount t = D.endpointCount t := by
  classical
  let J := starPuncture R u (insert v S)
  have huI : u ∉ insert v S := by simp [huv, hu]
  have hsub : J ≤ R := fun _ _ hadj => hadj.1
  obtain ⟨hDu, hpositive⟩ := contact_E3_puncture_positive u v S hu hv huv
    huOdd hodd huvAdj hadj heven hretained D
  have hmissing : ∀ w ∈ S, ¬ J.Adj u w := by
    intro w hw
    exact starPuncture_missing R u (insert v S) huI w (Finset.mem_insert_of_mem hw)
  have hreserved : ¬ J.Adj u v :=
    starPuncture_missing R u (insert v S) huI v (Finset.mem_insert_self _ _)
  have hoddpositive : ∀ w ∈ S, w ≠ b → ∀ t,
      J.Adj w t → Odd (R.degree t) → 0 < D.endpointCount t := by
    intro w hw hwb t hwt htOdd
    have htu : t ≠ u := by
      intro he
      exact hmissing w hw (he ▸ hwt.symm)
    have htv : t ≠ v := by
      intro he
      exact hseparate w hw (he ▸ (hsub hwt).symm)
    have htS : t ∉ S := by
      intro ht
      have hE := heven t ht
      rw [Nat.even_iff] at hE
      rw [Nat.odd_iff] at htOdd
      omega
    apply D.endpointCount_pos_of_odd_degree
    rw [starPuncture_degree_other (G := R) u (insert v S) t htu
      (by simp [htv, htS])]
    exact htOdd
  obtain ⟨F, hsize, hFu, hFv, hpreserve⟩ :=
    restore_odd_contact_sequence_of_original_even_cap R D u v b S hsub hu hv huv
      hreserved hmissing (fun w hw hadj => hseparate w hw (hsub hadj))
      hpositive hvpositive hDu hodd hb heven hcap hoddpositive
  have hrestore : (J ⊔ S.sup (SimpleGraph.edge u)) ⊔ SimpleGraph.edge v u = R := by
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
      ∀ t, t ≠ u → t ≠ v → t ∉ S → F.endpointCount t = D.endpointCount t :=
    ⟨F, hsize, hFu, hFv, hpreserve⟩
  rwa [hrestore] at hout

/-- E3's endgame interface admits supplied reserves at originally even
retained neighbours as well as parity-derived positivity. -/
theorem restore_contact_E3_with_retained_reserves
    (u v b : V) (S : Finset V) (hu : u ∉ S) (hv : v ∉ S) (huv : u ≠ v)
    (huOdd : Odd (R.degree u)) (hodd : Odd #S) (huvAdj : R.Adj u v)
    (hadj : ∀ t ∈ S, R.Adj u t) (heven : ∀ t ∈ S, Even (R.degree t))
    (hb : b ∈ S) (hcap : ∀ w ∈ S, w ≠ b → eDegree R w ≤ 2)
    (hseparate : ∀ w ∈ S, ¬ R.Adj v w)
    (D : Decomposition (starPuncture R u (insert v S)))
    (hretained : ∀ t, R.Adj u t → t ∉ S →
      Odd (R.degree t) ∨ 0 < D.endpointCount t)
    (hvpositive : ∀ t, (starPuncture R u (insert v S)).Adj v t →
      0 < D.endpointCount t) :
    ∃ F : Decomposition R, F.size = D.size ∧ 1 ≤ F.endpointCount u ∧
      F.endpointCount v = D.endpointCount v + 1 ∧
      ∀ t, t ≠ u → t ≠ v → t ∉ S → F.endpointCount t = D.endpointCount t := by
  exact restore_contact_with_retained_positive u v u b S hu hv huv huOdd hodd
    huvAdj hadj heven hb hcap hseparate D
    (fun t ht htS _ => hretained t ht htS)
    (D.endpointCount_pos_of_odd_degree u
      (contact_puncture_center_odd u v S hu hv huv huOdd hodd huvAdj hadj)) hvpositive

/-- Concrete E3 contact set: the hub contact plus an even number of private
contacts. Prescribing the hub derives its exemption from the private cap. -/
theorem restore_contact_E3_hub_even_privates
    (u v x : V) (P : Finset V) (hu : u ∉ P) (hv : v ∉ P) (hx : x ∉ P)
    (hux : u ≠ x) (hvx : v ≠ x) (huv : u ≠ v)
    (huOdd : Odd (R.degree u)) (hP : Even #P)
    (huvAdj : R.Adj u v) (huxAdj : R.Adj u x)
    (hadj : ∀ t ∈ P, R.Adj u t)
    (hxEven : Even (R.degree x)) (heven : ∀ t ∈ P, Even (R.degree t))
    (hretained : ∀ t, R.Adj u t → t ≠ x → t ∉ P → Odd (R.degree t))
    (hcap : ∀ w ∈ P, eDegree R w ≤ 2)
    (hvxAdj : ¬ R.Adj v x) (hseparate : ∀ w ∈ P, ¬ R.Adj v w)
    (D : Decomposition (starPuncture R u (insert v (insert x P))))
    (hvpositive : ∀ t, (starPuncture R u (insert v (insert x P))).Adj v t →
      0 < D.endpointCount t) :
    ∃ F : Decomposition R, F.size = D.size ∧ 1 ≤ F.endpointCount u ∧
      F.endpointCount v = D.endpointCount v + 1 ∧
      ∀ t, t ≠ u → t ≠ v → t ∉ insert x P →
        F.endpointCount t = D.endpointCount t := by
  classical
  have hodd : Odd #(insert x P) := by
    rw [Finset.card_insert_of_notMem hx]
    rw [Nat.even_iff] at hP
    rw [Nat.odd_iff]
    omega
  apply restore_contact_E3 u v x (insert x P)
    (by simp [hux, hu]) (by simp [hvx, hv]) huv huOdd hodd huvAdj
    (fun t ht => ?_) (fun t ht => ?_) (fun t ht htS => ?_)
    (Finset.mem_insert_self _ _) (fun w hw hwx => ?_)
    (fun w hw => ?_) D hvpositive
  · rcases Finset.mem_insert.mp ht with rfl | ht
    · exact huxAdj
    · exact hadj t ht
  · rcases Finset.mem_insert.mp ht with rfl | ht
    · exact hxEven
    · exact heven t ht
  · exact hretained t ht (fun he => htS (Finset.mem_insert.mpr (Or.inl he)))
      (fun hp => htS (Finset.mem_insert_of_mem hp))
  · exact hcap w ((Finset.mem_insert.mp hw).resolve_left hwx)
  · rcases Finset.mem_insert.mp hw with rfl | hw
    · exact hvxAdj
    · exact hseparate w hw

end Gallai.TwoException
