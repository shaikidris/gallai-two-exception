/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.OrdinaryMatePuncture
public import Gallai.TwoException.ContactSpoke

@[expose] public section

/-! # Private mate restoration while the hub spoke remains unpaid -/
namespace Gallai.TwoException
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {R J : SimpleGraph V} [DecidableRel R.Adj] [DecidableRel J.Adj]
noncomputable local instance delayedMateAdj (M : List (V × V)) :
    DecidableRel (ordinaryMatePuncture J M).Adj :=
  fun _ _ => Classical.propDecidable _

/-- A pending private mate can be restored towards its recipient. Its
only original even neighbours are its donor and the still-odd hub, so every
retained neighbour is odd in the actual tail graph. -/
theorem restore_delayed_private_mate_head
    (x p q : V) (M : List (V × V))
    (hdis : ((p,q) :: M).Pairwise (fun e f =>
      e.1 ≠ f.1 ∧ e.1 ≠ f.2 ∧ e.2 ≠ f.1 ∧ e.2 ≠ f.2))
    (hedges : ∀ e ∈ (p,q) :: M,
      J.Adj e.1 e.2 ∧ Even (J.degree e.1) ∧ Even (J.degree e.2))
    (hxavoid : ∀ e ∈ M, x ≠ e.1 ∧ x ≠ e.2)
    (hsub : J ≤ R)
    (hprofile : ∀ t, Even (J.degree t) → Even (R.degree t))
    (hxOdd : Odd (J.degree x))
    (hpair : ∀ t, R.Adj q t → Even (R.degree t) → t = x ∨ t = p)
    (D : Decomposition (ordinaryMatePuncture J ((p,q) :: M))) :
    ∃ E : Decomposition (ordinaryMatePuncture J M),
      E.size = D.size ∧ 2 ≤ E.endpointCount q ∧
      ∀ t, E.endpointCount t + (if p = t then 1 else 0) =
        D.endpointCount t + if q = t then 1 else 0 := by
  classical
  obtain ⟨hhead,htail⟩ := List.pairwise_cons.mp hdis
  have hpavoid : ∀ e ∈ M, p ≠ e.1 ∧ p ≠ e.2 :=
    fun e he => ⟨(hhead e he).1,(hhead e he).2.1⟩
  have hqavoid : ∀ e ∈ M, q ≠ e.1 ∧ q ≠ e.2 :=
    fun e he => (hhead e he).2.2
  obtain ⟨hpq,hpEven,hqEven⟩ := hedges (p,q) (List.mem_cons_self ..)
  have hpqT : (ordinaryMatePuncture J M).Adj p q :=
    (ordinaryMatePuncture_adj_of_avoids M p q hpavoid).mpr hpq
  have hpEvenT : Even ((ordinaryMatePuncture J M).degree p) := by
    rw [ordinaryMatePuncture_degree_of_avoids M p hpavoid]
    exact hpEven
  have hqEvenT : Even ((ordinaryMatePuncture J M).degree q) := by
    rw [ordinaryMatePuncture_degree_of_avoids M q hqavoid]
    exact hqEven
  have hxOddT : Odd ((ordinaryMatePuncture J M).degree x) := by
    rw [ordinaryMatePuncture_degree_of_avoids M x hxavoid]
    exact hxOdd
  have hother : ∀ t, (ordinaryMatePuncture J M).Adj q t → t ≠ p →
      Odd ((ordinaryMatePuncture J M).degree t) := by
    intro t hat htp
    rcases Nat.even_or_odd ((ordinaryMatePuncture J M).degree t) with he | ho
    · have htJ := ordinaryMatePuncture_even_preserved M htail
        (fun e he => hedges e (List.mem_cons_of_mem (p,q) he)) t he
      have htR := hprofile t htJ
      have hatR := hsub (ordinaryMatePuncture_le M hat)
      rcases hpair t hatR htR with rfl | heq
      · exact False.elim (Nat.not_even_iff_odd.mpr hxOddT he)
      · exact False.elim (htp heq)
    · exact ho
  have hqOddD : Odd ((ordinaryMatePuncture J ((p,q) :: M)).degree q) := by
    have hd := degree_delete_edge_add_one_other (ordinaryMatePuncture J M) p q hpqT
    simp only [← SimpleGraph.ncard_neighborSet] at hd hqEvenT ⊢
    rw [Nat.even_iff] at hqEvenT
    change Odd ((((ordinaryMatePuncture J M).deleteEdges {s(p,q)}).neighborSet q).ncard)
    rw [Nat.odd_iff]
    omega
  obtain ⟨E,hs,hvec⟩ := restore_contact_spoke p q hpqT hpEvenT hother D
  refine ⟨E,hs,?_,hvec⟩
  have hp := D.endpointCount_pos_of_odd_degree q hqOddD
  have hv := hvec q
  simp only [hpq.ne,ite_false,ite_true,Nat.add_zero] at hv
  change 2 ≤ E.endpointCount q
  rw [hv]
  exact Nat.succ_le_succ hp

/-- Restore the entire disjoint private-mate family before paying the
hub spoke. Every vertex outside the family retains its endpoint count. -/
theorem restore_delayed_private_mate_family
    (x : V) (M : List (V × V)) (hsub : J ≤ R)
    (hprofile : ∀ t, Even (J.degree t) → Even (R.degree t))
    (hxOdd : Odd (J.degree x)) :
    M.Pairwise (fun e f =>
      e.1 ≠ f.1 ∧ e.1 ≠ f.2 ∧ e.2 ≠ f.1 ∧ e.2 ≠ f.2) →
    (∀ e ∈ M, J.Adj e.1 e.2 ∧ Even (J.degree e.1) ∧ Even (J.degree e.2)) →
    (∀ e ∈ M, x ≠ e.1 ∧ x ≠ e.2) →
    (∀ e ∈ M, ∀ t, R.Adj e.2 t → Even (R.degree t) → t = x ∨ t = e.1) →
    ∀ D : Decomposition (ordinaryMatePuncture J M),
      ∃ E : Decomposition J, E.size = D.size ∧
        (∀ e ∈ M, 2 ≤ E.endpointCount e.2) ∧
        ∀ t, (∀ e ∈ M, t ≠ e.1 ∧ t ≠ e.2) →
          E.endpointCount t = D.endpointCount t := by
  classical
  induction M with
  | nil =>
    intro _ _ _ _ D
    exact ⟨D,rfl,by simp,fun _ _ => rfl⟩
  | cons e M ih =>
    intro hdis hedges hxavoid hpair D
    obtain ⟨hhead,htail⟩ := List.pairwise_cons.mp hdis
    have hxTail : ∀ f ∈ M, x ≠ f.1 ∧ x ≠ f.2 :=
      fun f hf => hxavoid f (List.mem_cons_of_mem e hf)
    obtain ⟨E1,hs1,hrec1,hvec⟩ := restore_delayed_private_mate_head x e.1 e.2 M
      hdis hedges hxTail hsub hprofile hxOdd (hpair e (List.mem_cons_self ..)) D
    obtain ⟨E2,hs2,hrec2,hkeep2⟩ := ih htail
      (fun f hf => hedges f (List.mem_cons_of_mem e hf)) hxTail
      (fun f hf => hpair f (List.mem_cons_of_mem e hf)) E1
    refine ⟨E2,hs2.trans hs1,?_,?_⟩
    · intro f hf
      rcases List.mem_cons.mp hf with heq | hf
      · subst f
        have heAvoid : ∀ f ∈ M, e.2 ≠ f.1 ∧ e.2 ≠ f.2 :=
          fun f hf => (hhead f hf).2.2
        rw [hkeep2 e.2 heAvoid]
        exact hrec1
      · exact hrec2 f hf
    · intro t ht
      have htTail : ∀ f ∈ M, t ≠ f.1 ∧ t ≠ f.2 :=
        fun f hf => ht f (List.mem_cons_of_mem e hf)
      rw [hkeep2 t htTail]
      obtain ⟨htp,htq⟩ := ht e (List.mem_cons_self ..)
      have hv := hvec t
      simpa only [Ne.symm htp,Ne.symm htq,ite_false,Nat.add_zero] using hv

noncomputable local instance delayedFinalDeleteAdj (x q : V) :
    DecidableRel (R.deleteEdges {s(x,q)}).Adj :=
  fun _ _ => Classical.propDecidable _

/-- Complete the delayed return from the private-mate puncture to the
original graph. Only the final spoke spends an endpoint at the hub. -/
theorem restore_delayed_mates_and_final_spoke
    (x q p u : V) (M : List (V × V)) (hxq : R.Adj x q)
    (hprofile : ∀ t, Even ((R.deleteEdges {s(x,q)}).degree t) → Even (R.degree t))
    (hxOdd : Odd ((R.deleteEdges {s(x,q)}).degree x))
    (hdis : M.Pairwise (fun e f =>
      e.1 ≠ f.1 ∧ e.1 ≠ f.2 ∧ e.2 ≠ f.1 ∧ e.2 ≠ f.2))
    (hedges : ∀ e ∈ M, (R.deleteEdges {s(x,q)}).Adj e.1 e.2 ∧
      Even ((R.deleteEdges {s(x,q)}).degree e.1) ∧
      Even ((R.deleteEdges {s(x,q)}).degree e.2))
    (hxavoid : ∀ e ∈ M, x ≠ e.1 ∧ x ≠ e.2)
    (hpavoid : ∀ e ∈ M, p ≠ e.1 ∧ p ≠ e.2)
    (huavoid : ∀ e ∈ M, u ≠ e.1 ∧ u ≠ e.2)
    (hmates : ∀ e ∈ M, ∀ t, R.Adj e.2 t → Even (R.degree t) → t = x ∨ t = e.1)
    (hpair : ∀ t, R.Adj q t → Even (R.degree t) → t = x ∨ t = p)
    (D : Decomposition (ordinaryMatePuncture (R.deleteEdges {s(x,q)}) M))
    (hp : 2 ≤ D.endpointCount p) (hu : 0 < D.endpointCount u) :
    ∃ E : Decomposition R, E.size = D.size ∧
      ∀ t, t ≠ x → t ≠ q → (∀ e ∈ M, t ≠ e.1 ∧ t ≠ e.2) →
        E.endpointCount t = D.endpointCount t := by
  classical
  obtain ⟨E1,hs1,_,hkeep⟩ := restore_delayed_private_mate_family
    (R := R) (J := R.deleteEdges {s(x,q)}) x M (fun _ _ ha => ha.1)
    hprofile hxOdd hdis hedges hxavoid hmates D
  have hp1 : 2 ≤ E1.endpointCount p := by rwa [hkeep p hpavoid]
  have hu1 : 0 < E1.endpointCount u := by rwa [hkeep u huavoid]
  have hx1 := E1.endpointCount_pos_of_odd_degree x hxOdd
  obtain ⟨E2,hs2,hvec⟩ := restore_delayed_contact_spoke x q p u hxq hpair
    (fun t ht => Or.inl (hprofile t ht)) E1 hx1 hp1 hu1
  refine ⟨E2,hs2.trans hs1,?_⟩
  intro t htx htq htM
  have hv := hvec t
  simp only [Ne.symm htx,Ne.symm htq,ite_false,Nat.add_zero] at hv
  exact hv.trans (hkeep t htM)

end Gallai.TwoException
