/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.ContactSpoke

@[expose] public section

/-! # Contact restoration with an exposed retained contact -/
namespace Gallai.TwoException
open scoped Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {R : SimpleGraph V} [DecidableRel R.Adj]
noncomputable local instance retainedStarAdj (u v : V) (S : Finset V) :
    DecidableRel (starPuncture R u (insert v S)).Adj :=
  fun _ _ => Classical.propDecidable _

/-- A retained contact may be even, provided the preparation has exposed
it. All other positivity is derived from the literal star puncture. -/
theorem restore_contact_with_retained_positive
    (u v p b : V) (S : Finset V) (hu : u ∉ S) (hv : v ∉ S) (huv : u ≠ v)
    (huOdd : Odd (R.degree u)) (hodd : Odd #S) (huvAdj : R.Adj u v)
    (hadj : ∀ t ∈ S, R.Adj u t) (heven : ∀ t ∈ S, Even (R.degree t))
    (hb : b ∈ S) (hcap : ∀ w ∈ S, w ≠ b → eDegree R w ≤ 2)
    (hseparate : ∀ w ∈ S, ¬ R.Adj v w)
    (D : Decomposition (starPuncture R u (insert v S)))
    (hretained : ∀ t, R.Adj u t → t ∉ S → t ≠ p →
      Odd (R.degree t) ∨ 0 < D.endpointCount t)
    (hp : 0 < D.endpointCount p)
    (hvpositive : ∀ t, (starPuncture R u (insert v S)).Adj v t →
      0 < D.endpointCount t) :
    ∃ F : Decomposition R, F.size = D.size ∧ 1 ≤ F.endpointCount u ∧
      F.endpointCount v = D.endpointCount v + 1 ∧
      ∀ t, t ≠ u → t ≠ v → t ∉ S → F.endpointCount t = D.endpointCount t := by
  classical
  let J := starPuncture R u (insert v S)
  have huI : u ∉ insert v S := by simp [huv, hu]
  have hsub : J ≤ R := fun _ _ ha => ha.1
  have hmissing : ∀ w ∈ S, ¬ J.Adj u w := fun w hw =>
    starPuncture_missing R u (insert v S) huI w (Finset.mem_insert_of_mem hw)
  have hreserved : ¬ J.Adj u v :=
    starPuncture_missing R u (insert v S) huI v (Finset.mem_insert_self _ _)
  have hpositive : ∀ t, J.Adj u t ∨ t ∈ S → 0 < D.endpointCount t := by
    intro t ht
    by_cases htp : t = p
    · subst t
      exact hp
    by_cases htS : t ∈ S
    · apply D.endpointCount_pos_of_odd_degree
      have hd := starPuncture_degree_leaf (G := R) u (insert v S) t
        (Finset.mem_insert_of_mem htS) (hadj t htS)
      have he := heven t htS
      simp only [← SimpleGraph.ncard_neighborSet] at hd he ⊢
      rw [Nat.even_iff] at he
      rw [Nat.odd_iff]
      omega
    · have ha := ht.resolve_right htS
      have htR := hsub ha
      have htu : t ≠ u := htR.ne.symm
      have htv : t ≠ v := fun e => hreserved (e ▸ ha)
      have hd := starPuncture_degree_other (G := R) u (insert v S) t htu
        (by simp [htv, htS])
      rcases hretained t htR htS htp with ho | htpos
      · apply D.endpointCount_pos_of_odd_degree
        simp only [← SimpleGraph.ncard_neighborSet] at hd ho ⊢
        rwa [hd]
      · exact htpos
  have hoddpositive : ∀ w ∈ S, w ≠ b → ∀ t,
      J.Adj w t → Odd (R.degree t) → 0 < D.endpointCount t := by
    intro w hw _ t ha ho
    have htu : t ≠ u := fun e => hmissing w hw (e ▸ ha.symm)
    have htv : t ≠ v := fun e => hseparate w hw (e ▸ (hsub ha).symm)
    have htS : t ∉ S := by
      intro ht
      have he := heven t ht
      rw [Nat.even_iff] at he
      rw [Nat.odd_iff] at ho
      omega
    apply D.endpointCount_pos_of_odd_degree
    have hd := starPuncture_degree_other (G := R) u (insert v S) t htu
      (by simp [htv, htS])
    simp only [← SimpleGraph.ncard_neighborSet] at hd ho ⊢
    rwa [hd]
  obtain ⟨F, hs, hfu, hfv, hkeep⟩ :=
    restore_odd_contact_sequence_of_original_even_cap R D u v b S hsub hu hv huv
      hreserved hmissing (fun w hw ha => hseparate w hw (hsub ha)) hpositive hvpositive
      (D.endpointCount_pos_of_odd_degree u
        (contact_puncture_center_odd u v S hu hv huv huOdd hodd huvAdj hadj))
      hodd hb heven hcap hoddpositive
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
      ∀ t, t ≠ u → t ≠ v → t ∉ S → F.endpointCount t = D.endpointCount t :=
    ⟨F, hs, hfu, hfv, hkeep⟩
  rwa [hr] at hout

end Gallai.TwoException
