/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.ContactSpoke

@[expose] public section

/-! # Retained-contact mate preparation -/
namespace Gallai.TwoException
open scoped Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {R : SimpleGraph V} [DecidableRel R.Adj]
noncomputable local instance mateStarAdj (u v : V) (S : Finset V) :
    DecidableRel (starPuncture R u (insert v S)).Adj :=
  fun _ _ => Classical.propDecidable _
noncomputable local instance mateDeleteAdj (u v p q : V) (S : Finset V) :
    DecidableRel ((starPuncture R u (insert v S)).deleteEdges {s(q,p)}).Adj :=
  fun _ _ => Classical.propDecidable _

/-- E4 deletes the hub contact while retaining up. Thus the hub and
centre are odd in the star puncture, supplying all nonmate neighbours
needed to restore the mate edge towards p. -/
theorem contact_mate_retained_neighbors_odd
    (u v x p q : V) (S : Finset V)
    (hu : u ∉ S) (hv : v ∉ S) (huv : u ≠ v)
    (huOdd : Odd (R.degree u)) (hodd : Odd #S) (huvAdj : R.Adj u v)
    (hadj : ∀ t ∈ S, R.Adj u t) (heven : ∀ t ∈ S, Even (R.degree t))
    (hx : x ∈ S) (hpv : ¬ R.Adj p v)
    (hpair : ∀ t, R.Adj p t → Even (R.degree t) → t = x ∨ t = q) :
    ∀ t, (starPuncture R u (insert v S)).Adj p t → t ≠ q →
      Odd ((starPuncture R u (insert v S)).degree t) := by
  classical
  intro t ht htq
  by_cases htu : t = u
  · subst t
    exact contact_puncture_center_odd u v S hu hv huv huOdd hodd huvAdj hadj
  have htR : R.Adj p t := ht.1
  by_cases htEven : Even (R.degree t)
  · have htx : t = x := (hpair t htR htEven).resolve_right htq
    subst t
    have hd := starPuncture_degree_leaf (G := R) u (insert v S) x
      (Finset.mem_insert_of_mem hx) (hadj x hx)
    have he := heven x hx
    simp only [← SimpleGraph.ncard_neighborSet] at hd he ⊢
    rw [Nat.even_iff] at he
    rw [Nat.odd_iff]
    omega
  · have htv : t ≠ v := fun he => hpv (he ▸ htR)
    have htS : t ∉ S := fun ht => htEven (heven t ht)
    have hd := starPuncture_degree_other (G := R) u (insert v S) t htu
      (by simp [htv, htS])
    have ho := Nat.not_even_iff_odd.mp htEven
    simp only [← SimpleGraph.ncard_neighborSet] at hd ho ⊢
    rwa [hd]

/-- The E4 mate preparation supplies two endpoints at the retained contact,
without consuming an endpoint at the star centre or the reserved vertex. -/
theorem restore_contact_mate
    (u v x p q : V) (S : Finset V)
    (hu : u ∉ S) (hv : v ∉ S) (huv : u ≠ v)
    (huOdd : Odd (R.degree u)) (hodd : Odd #S) (huvAdj : R.Adj u v)
    (hadj : ∀ t ∈ S, R.Adj u t) (heven : ∀ t ∈ S, Even (R.degree t))
    (hx : x ∈ S) (hpvAdj : ¬ R.Adj p v)
    (hpair : ∀ t, R.Adj p t → Even (R.degree t) → t = x ∨ t = q)
    (hpu : p ≠ u) (hpv : p ≠ v) (hpS : p ∉ S)
    (hqu : q ≠ u) (hqv : q ≠ v) (hqS : q ∉ S)
    (hqp : R.Adj q p) (hpEven : Even (R.degree p)) (hqEven : Even (R.degree q))
    (D : Decomposition ((starPuncture R u (insert v S)).deleteEdges {s(q,p)})) :
    ∃ E : Decomposition (starPuncture R u (insert v S)),
      E.size = D.size ∧ 2 ≤ E.endpointCount p ∧ ∀ t,
        E.endpointCount t + (if q = t then 1 else 0) =
          D.endpointCount t + if p = t then 1 else 0 := by
  classical
  have hedge : (starPuncture R u (insert v S)).Adj q p := by
    refine ⟨hqp, ?_⟩
    rw [star_sup_adj_off_center u (insert v S) q p hqu]
    simp [hpu]
  have hqdeg := starPuncture_degree_other (G := R) u (insert v S) q hqu
    (by simp [hqv, hqS])
  have hpdeg := starPuncture_degree_other (G := R) u (insert v S) p hpu
    (by simp [hpv, hpS])
  have hqE : Even ((starPuncture R u (insert v S)).degree q) := by
    simp only [← SimpleGraph.ncard_neighborSet] at hqdeg hqEven ⊢
    rwa [hqdeg]
  have hpO : Odd (((starPuncture R u (insert v S)).deleteEdges {s(q,p)}).degree p) := by
    have hd := degree_delete_edge_add_one_other
      (starPuncture R u (insert v S)) q p hedge
    simp only [← SimpleGraph.ncard_neighborSet] at hd hpdeg hpEven ⊢
    rw [Nat.even_iff] at hpEven
    rw [Nat.odd_iff]
    omega
  obtain ⟨E, hs, he⟩ := restore_contact_spoke q p hedge hqE
    (contact_mate_retained_neighbors_odd u v x p q S hu hv huv huOdd hodd
      huvAdj hadj heven hx hpvAdj hpair) D
  refine ⟨E, hs, ?_, he⟩
  have hpos := D.endpointCount_pos_of_odd_degree p hpO
  have hv := he p
  simp only [hqp.ne, ite_false, ite_true, Nat.add_zero] at hv
  omega

end Gallai.TwoException
