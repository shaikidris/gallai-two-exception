/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.ContactHalfStar
public import Gallai.Structure.EdgeDeletion

@[expose] public section

/-! # Spoke preparation restoration for contact rows -/

namespace Gallai.TwoException

open scoped Finset

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {R : SimpleGraph V} [DecidableRel R.Adj]

noncomputable local instance contactSpokeDeleteAdj (x q : V) :
    DecidableRel (R.deleteEdges {s(x, q)}).Adj := fun _ _ => Classical.propDecidable _

/-- Restore a deleted spoke outward at its private endpoint. The even hub
becomes odd after deletion, and all retained private neighbours are odd,
so addibility is forced without an endpoint-selection assumption. -/
theorem restore_contact_spoke
    (x q : V) (hxq : R.Adj x q) (hxEven : Even (R.degree x))
    (hother : ∀ t, R.Adj q t → t ≠ x → Odd (R.degree t))
    (D : Decomposition (R.deleteEdges {s(x, q)})) :
    ∃ E : Decomposition R, E.size = D.size ∧
      ∀ t, E.endpointCount t + (if x = t then 1 else 0) =
        D.endpointCount t + if q = t then 1 else 0 := by
  classical
  have hxOdd : Odd ((R.deleteEdges {s(x, q)}).degree x) := by
    have hd := degree_delete_edge_add_one R x q hxq
    simp only [← SimpleGraph.ncard_neighborSet] at hd hxEven ⊢
    rw [Nat.even_iff] at hxEven
    rw [Nat.odd_iff]
    omega
  have hpos : ∀ t, (R.deleteEdges {s(x, q)}).Adj q t → 0 < D.endpointCount t := by
    intro t ht
    have htx : t ≠ x := by
      intro he
      subst t
      simpa [SimpleGraph.deleteEdges_adj] using ht
    have htq : t ≠ q := ht.1.ne.symm
    apply D.endpointCount_pos_of_odd_degree
    have hd := degree_delete_edge_of_ne R x q t htx htq
    have ho := hother t ht.1 htx
    simp only [← SimpleGraph.ncard_neighborSet] at hd ho ⊢
    rw [hd]
    exact ho
  have hzero : #{t ∈ (R.deleteEdges {s(x, q)}).neighborFinset q |
      D.endpointCount t = 0} = 0 := by
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro t ht
    obtain ⟨htN, htZero⟩ := Finset.mem_filter.mp ht
    have hp := hpos t (((R.deleteEdges {s(x, q)}).mem_neighborFinset q t).mp htN)
    omega
  obtain ⟨E, hs, hv⟩ := D.single_edge_addibility q x hxq.ne.symm
    (by simp [SimpleGraph.deleteEdges_adj])
    (by rw [hzero]; exact D.endpointCount_pos_of_odd_degree x hxOdd)
  have hout : ∃ E : Decomposition (R.deleteEdges {s(x, q)} ⊔ SimpleGraph.edge q x),
      E.size = D.size ∧ ∀ t, E.endpointCount t + (if x = t then 1 else 0) =
        D.endpointCount t + if q = t then 1 else 0 := ⟨E, hs, hv⟩
  rw [SimpleGraph.edge_comm q x, delete_edge_sup_edge R x q hxq] at hout
  exact hout

noncomputable local instance contactSpokeStarAdj (u v : V) (S : Finset V) :
    DecidableRel (starPuncture R u (insert v S)).Adj :=
  fun _ _ => Classical.propDecidable _

/-- Endpoint positivity, rather than odd parity, suffices for the final
spoke payment. This permits a restored even mate to protect the recipient. -/
theorem restore_contact_spoke_of_positive_neighbors
    (x q : V) (hxq : R.Adj x q)
    (D : Decomposition (R.deleteEdges {s(x, q)}))
    (hx : 0 < D.endpointCount x)
    (hpos : ∀ t, (R.deleteEdges {s(x, q)}).Adj q t →
      0 < D.endpointCount t) :
    ∃ E : Decomposition R, E.size = D.size ∧
      ∀ t, E.endpointCount t + (if x = t then 1 else 0) =
        D.endpointCount t + if q = t then 1 else 0 := by
  classical
  have hzero : #{t ∈ (R.deleteEdges {s(x, q)}).neighborFinset q |
      D.endpointCount t = 0} = 0 := by
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro t ht
    obtain ⟨htN, htZero⟩ := Finset.mem_filter.mp ht
    have hp := hpos t (((R.deleteEdges {s(x, q)}).mem_neighborFinset q t).mp htN)
    omega
  obtain ⟨E, hs, hv⟩ := D.single_edge_addibility q x hxq.ne.symm
    (by simp [SimpleGraph.deleteEdges_adj]) (by rw [hzero]; exact hx)
  have hout : ∃ E : Decomposition (R.deleteEdges {s(x, q)} ⊔ SimpleGraph.edge q x),
      E.size = D.size ∧ ∀ t, E.endpointCount t + (if x = t then 1 else 0) =
        D.endpointCount t + if q = t then 1 else 0 := ⟨E, hs, hv⟩
  rw [SimpleGraph.edge_comm q x, delete_edge_sup_edge R x q hxq] at hout
  exact hout

/-- In delayed payment the only originally even neighbours of the private
recipient are its hub and mate. The hub edge is still absent; the restored
mate is exposed. Any new even neighbour is the exposed contact centre. -/
theorem restore_delayed_contact_spoke
    (x q p u : V) (hxq : R.Adj x q)
    (hpair : ∀ t, R.Adj q t → Even (R.degree t) → t = x ∨ t = p)
    (hprofile : ∀ t, Even ((R.deleteEdges {s(x, q)}).degree t) →
      Even (R.degree t) ∨ t = u)
    (D : Decomposition (R.deleteEdges {s(x, q)}))
    (hx : 0 < D.endpointCount x) (hp : 2 ≤ D.endpointCount p)
    (hu : 0 < D.endpointCount u) :
    ∃ E : Decomposition R, E.size = D.size ∧
      ∀ t, E.endpointCount t + (if x = t then 1 else 0) =
        D.endpointCount t + if q = t then 1 else 0 := by
  apply restore_contact_spoke_of_positive_neighbors x q hxq D hx
  intro t ht
  by_contra hn
  have hz : D.endpointCount t = 0 := by omega
  have he : Even ((R.deleteEdges {s(x, q)}).degree t) := by
    rw [Nat.even_iff]
    have hm := D.endpointCount_mod_two t
    rw [hz] at hm
    omega
  rcases hprofile t he with he | rfl
  · rcases hpair t ht.1 he with rfl | rfl
    · omega
    · omega
  · omega

/-- In the actual contact puncture, the contacted mate is odd; all other
retained private neighbours apart from the hub were originally odd and keep
their degree. This supplies the spoke lemma's parity guard for E1. -/
theorem contact_single_petal_retained_neighbors_odd
    (u v x p q : V) (S : Finset V) (hp : p ∈ S)
    (hadj : ∀ t ∈ S, R.Adj u t) (heven : ∀ t ∈ S, Even (R.degree t))
    (hqu : ¬ R.Adj q u) (hqv : ¬ R.Adj q v)
    (hpair : ∀ t, R.Adj q t → Even (R.degree t) → t = x ∨ t = p) :
    ∀ t, (starPuncture R u (insert v S)).Adj q t → t ≠ x →
      Odd ((starPuncture R u (insert v S)).degree t) := by
  classical
  intro t ht htx
  have htR : R.Adj q t := ht.1
  by_cases htEven : Even (R.degree t)
  · have htp : t = p := (hpair t htR htEven).resolve_left htx
    subst t
    have hd := starPuncture_degree_leaf (G := R) u (insert v S) p
      (Finset.mem_insert_of_mem hp) (hadj p hp)
    have he := heven p hp
    simp only [← SimpleGraph.ncard_neighborSet] at hd he ⊢
    rw [Nat.even_iff] at he
    rw [Nat.odd_iff]
    omega
  · have htu : t ≠ u := fun he => hqu (he ▸ htR)
    have htv : t ≠ v := fun he => hqv (he ▸ htR)
    have htS : t ∉ S := fun ht => htEven (heven t ht)
    have hd := starPuncture_degree_other (G := R) u (insert v S) t htu
      (by simp [htv, htS])
    have ho := Nat.not_even_iff_odd.mp htEven
    simp only [← SimpleGraph.ncard_neighborSet] at hd ho ⊢
    rw [hd]
    exact ho

/-- E1's preparatory spoke restoration on the literal contact puncture.
The hub keeps its original even degree before the spoke is removed. -/
theorem restore_single_petal_contact_spoke
    (u v x p q : V) (S : Finset V) (hp : p ∈ S)
    (hadj : ∀ t ∈ S, R.Adj u t) (heven : ∀ t ∈ S, Even (R.degree t))
    (hxu : x ≠ u) (hxv : x ≠ v) (hxS : x ∉ S)
    (hqu : ¬ R.Adj q u) (hqv : ¬ R.Adj q v) (hqne : q ≠ u)
    (hxq : R.Adj x q) (hxEven : Even (R.degree x))
    (hpair : ∀ t, R.Adj q t → Even (R.degree t) → t = x ∨ t = p)
    (D : Decomposition ((starPuncture R u (insert v S)).deleteEdges {s(x, q)})) :
    ∃ E : Decomposition (starPuncture R u (insert v S)),
      E.size = D.size ∧ ∀ t,
        E.endpointCount t + (if x = t then 1 else 0) =
          D.endpointCount t + if q = t then 1 else 0 := by
  classical
  have hspoke : (starPuncture R u (insert v S)).Adj x q := by
    refine ⟨hxq, ?_⟩
    rw [star_sup_adj_off_center u (insert v S) x q hxu]
    simp [hqne]
  have hd := starPuncture_degree_other (G := R) u (insert v S) x hxu
    (by simp [hxv, hxS])
  have he : Even ((starPuncture R u (insert v S)).degree x) := by
    simp only [← SimpleGraph.ncard_neighborSet] at hd hxEven ⊢
    rw [hd]
    exact hxEven
  exact restore_contact_spoke x q hspoke he
    (contact_single_petal_retained_neighbors_odd u v x p q S hp hadj heven
      hqu hqv hpair) D

/-- In E2 the contact centre remains adjacent to the unselected mate.
Its odd parity replaces E1's nonadjacency guard. -/
theorem contact_double_petal_retained_neighbors_odd
    (u v x p q : V) (S : Finset V) (hp : p ∈ S)
    (hadj : ∀ t ∈ S, R.Adj u t) (heven : ∀ t ∈ S, Even (R.degree t))
    (huOdd : Odd ((starPuncture R u (insert v S)).degree u))
    (hqv : ¬ R.Adj q v)
    (hpair : ∀ t, R.Adj q t → Even (R.degree t) → t = x ∨ t = p) :
    ∀ t, (starPuncture R u (insert v S)).Adj q t → t ≠ x →
      Odd ((starPuncture R u (insert v S)).degree t) := by
  classical
  intro t ht htx
  by_cases htu : t = u
  · subst t
    exact huOdd
  have htR : R.Adj q t := ht.1
  by_cases htEven : Even (R.degree t)
  · have htp : t = p := (hpair t htR htEven).resolve_left htx
    subst t
    have hd := starPuncture_degree_leaf (G := R) u (insert v S) p
      (Finset.mem_insert_of_mem hp) (hadj p hp)
    have he := heven p hp
    simp only [← SimpleGraph.ncard_neighborSet] at hd he ⊢
    rw [Nat.even_iff] at he
    rw [Nat.odd_iff]
    omega
  · have htv : t ≠ v := fun he => hqv (he ▸ htR)
    have htS : t ∉ S := fun ht => htEven (heven t ht)
    have hd := starPuncture_degree_other (G := R) u (insert v S) t htu
      (by simp [htv, htS])
    have ho := Nat.not_even_iff_odd.mp htEven
    simp only [← SimpleGraph.ncard_neighborSet] at hd ho ⊢
    rw [hd]
    exact ho

/-- Deleting an odd contact star and its separate reserved edge removes
an even number of edges at an originally odd centre. -/
theorem contact_puncture_center_odd
    (u v : V) (S : Finset V) (hu : u ∉ S) (hv : v ∉ S) (huv : u ≠ v)
    (huOdd : Odd (R.degree u)) (hodd : Odd #S) (huvAdj : R.Adj u v)
    (hadj : ∀ t ∈ S, R.Adj u t) :
    Odd ((starPuncture R u (insert v S)).degree u) := by
  classical
  have huI : u ∉ insert v S := by simp [huv, hu]
  have hIadj : ∀ t ∈ insert v S, R.Adj u t := by
    intro t ht
    rcases Finset.mem_insert.mp ht with rfl | ht
    · exact huvAdj
    · exact hadj t ht
  have hd := starPuncture_degree_center (G := R) u (insert v S) huI
    (fun t ht => (R.mem_neighborFinset u t).mpr (hIadj t ht))
  rw [Finset.card_insert_of_notMem hv] at hd
  simp only [← SimpleGraph.ncard_neighborSet] at hd huOdd ⊢
  rw [Nat.odd_iff] at huOdd hodd ⊢
  omega

/-- E2's spoke restoration makes the retained contact positive with two
endpoints, rather than requiring it to be odd after restoration. -/
theorem restore_double_petal_contact_spoke
    (u v x p q : V) (S : Finset V) (hp : p ∈ S)
    (hadj : ∀ t ∈ S, R.Adj u t) (heven : ∀ t ∈ S, Even (R.degree t))
    (hxu : x ≠ u) (hxv : x ≠ v) (hxS : x ∉ S)
    (hqu : q ≠ u) (hqv : q ≠ v) (hqS : q ∉ S)
    (hxq : R.Adj x q) (hxEven : Even (R.degree x)) (hqEven : Even (R.degree q))
    (hu : u ∉ S) (hv : v ∉ S) (huv : u ≠ v)
    (huOdd : Odd (R.degree u)) (hodd : Odd #S) (huvAdj : R.Adj u v)
    (hqvAdj : ¬ R.Adj q v)
    (hpair : ∀ t, R.Adj q t → Even (R.degree t) → t = x ∨ t = p)
    (D : Decomposition ((starPuncture R u (insert v S)).deleteEdges {s(x,q)})) :
    ∃ E : Decomposition (starPuncture R u (insert v S)),
      E.size = D.size ∧ 2 ≤ E.endpointCount q ∧ ∀ t,
        E.endpointCount t + (if x = t then 1 else 0) =
          D.endpointCount t + if q = t then 1 else 0 := by
  classical
  have hspoke : (starPuncture R u (insert v S)).Adj x q := by
    refine ⟨hxq, ?_⟩
    rw [star_sup_adj_off_center u (insert v S) x q hxu]
    simp [hqu]
  have hxdeg := starPuncture_degree_other (G := R) u (insert v S) x hxu
    (by simp [hxv, hxS])
  have hqdeg := starPuncture_degree_other (G := R) u (insert v S) q hqu
    (by simp [hqv, hqS])
  have hxE : Even ((starPuncture R u (insert v S)).degree x) := by
    simp only [← SimpleGraph.ncard_neighborSet] at hxdeg hxEven ⊢
    rwa [hxdeg]
  have hqO : Odd (((starPuncture R u (insert v S)).deleteEdges {s(x,q)}).degree q) := by
    have hd := degree_delete_edge_add_one_other
      (starPuncture R u (insert v S)) x q hspoke
    simp only [← SimpleGraph.ncard_neighborSet] at hd hqdeg hqEven ⊢
    rw [Nat.even_iff] at hqEven
    rw [Nat.odd_iff]
    omega
  obtain ⟨E, hs, he⟩ := restore_contact_spoke x q hspoke hxE
    (contact_double_petal_retained_neighbors_odd u v x p q S hp hadj heven
      (contact_puncture_center_odd u v S hu hv huv huOdd hodd huvAdj hadj)
      hqvAdj hpair) D
  refine ⟨E, hs, ?_, he⟩
  have hpD := D.endpointCount_pos_of_odd_degree q hqO
  have hv := he q
  simp only [hxq.ne, ite_false, ite_true, Nat.add_zero] at hv
  omega

/-- The first private edge in delayed payment is restored before either
the odd hub or the odd mate is paid. Thus every current neighbour of its
recipient is exposed, and one endpoint at the centre is enough. -/
theorem restore_delayed_first_private
    (J : SimpleGraph V) [DecidableRel J.Adj]
    (u p x q : V) (hup : R.Adj u p) (hsub : J ≤ R)
    (hmissing : ¬ J.Adj p u)
    (hkeep : ∀ t, Even (J.degree t) → Even (R.degree t))
    (hpair : ∀ t, R.Adj p t → Even (R.degree t) → t = x ∨ t = q)
    (hxOdd : Odd (J.degree x)) (hqOdd : Odd (J.degree q))
    (hpOdd : Odd (J.degree p)) (D : Decomposition J)
    (hu : 0 < D.endpointCount u) :
    ∃ E : Decomposition (J ⊔ SimpleGraph.edge p u), E.size = D.size ∧
      2 ≤ E.endpointCount p ∧ ∀ t,
        E.endpointCount t + (if u = t then 1 else 0) =
          D.endpointCount t + if p = t then 1 else 0 := by
  classical
  have hpos : ∀ t, J.Adj p t → 0 < D.endpointCount t := by
    intro t ht
    by_contra hn
    have hz : D.endpointCount t = 0 := by omega
    have he : Even (J.degree t) := by
      rw [Nat.even_iff]
      have hm := D.endpointCount_mod_two t
      rw [hz] at hm
      omega
    rcases hpair t (hsub ht) (hkeep t he) with rfl | rfl
    · exact (Nat.not_even_iff_odd.mpr hxOdd) he
    · exact (Nat.not_even_iff_odd.mpr hqOdd) he
  have hzero : #{t ∈ J.neighborFinset p | D.endpointCount t = 0} = 0 := by
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro t ht
    obtain ⟨htN,htZero⟩ := Finset.mem_filter.mp ht
    have htPos := hpos t ((J.mem_neighborFinset p t).mp htN)
    omega
  obtain ⟨E,hs,hv⟩ := D.single_edge_addibility p u hup.ne.symm hmissing
    (by rw [hzero]; exact hu)
  refine ⟨E,hs,?_,hv⟩
  have hpPos := D.endpointCount_pos_of_odd_degree p hpOdd
  have hp := hv p
  simp only [hup.ne,ite_false,ite_true,Nat.add_zero] at hp
  omega

end Gallai.TwoException
