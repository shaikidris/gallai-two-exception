/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.Inputs.HalfStar
public import Gallai.Inputs.OddHubReserve
public import Gallai.TwoException.StarSurplus
public import Gallai.TwoException.ContactHalfStar

@[expose] public section

/-! # Full star restoration from the ordinary packet gain -/
namespace Gallai.TwoException
open scoped Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
noncomputable local instance packetGainAdj (u : V) (A : Finset V) :
    DecidableRel (G ⊔ A.sup (SimpleGraph.edge u)).Adj := fun _ _ => Classical.propDecidable _

/-- A positive centre or odd star size supplies the rounding reserve.
Strict packet gain then excludes one-surplus failure after prescribing
the distinguished hub spoke. -/
theorem restore_star_of_packet_gain
    (D : Decomposition G) (u x : V) (L : Finset V)
    (hxL : x ∉ L) (hu : u ∉ insert x L)
    (hmissing : ∀ t ∈ insert x L, ¬ G.Adj u t)
    (hpositive : ∀ t, G.Adj u t ∨ t ∈ insert x L → 0 < D.endpointCount t)
    (hDu : 0 < D.endpointCount u ∨ Odd (insert x L).card)
    (hpassing : ∀ A : Finset V, A ⊆ insert x L → x ∈ A →
      ∀ E : Decomposition (G ⊔ A.sup (SimpleGraph.edge u)),
      (∀ t, E.endpointCount t + (if t ∈ A then 1 else 0) =
        D.endpointCount t + if u = t then #A else 0) →
      ∀ t ∈ insert x L \ A, passingNeighborCount E t ≤ 2)
    (hgain : ∀ A : Finset V, A ⊆ insert x L → x ∈ A →
      ∀ E : Decomposition (G ⊔ A.sup (SimpleGraph.edge u)),
      (∀ t, E.endpointCount t + (if t ∈ A then 1 else 0) =
        D.endpointCount t + if u = t then #A else 0) →
      (∀ t ∈ insert x L \ A, passingNeighborCount E t = 2) →
      #(L \ A) + 1 ≤ #(L ∩ A) + D.endpointCount u) :
    ∃ F : Decomposition (G ⊔ (insert x L).sup (SimpleGraph.edge u)),
      F.size = D.size ∧ ∀ t, t ≠ u → t ∉ insert x L →
        F.endpointCount t = D.endpointCount t := by
  classical
  obtain ⟨A,hAB,hxA,hhalf,E,hED,hvec⟩ :=
    D.prescribed_half_star_addibility u (insert x L) hu hmissing hpositive x (by simp)
  have huA : u ∉ A := fun ha => hu (hAB ha)
  have hEu : E.endpointCount u = D.endpointCount u + #A := by
    simpa only [huA,if_false,if_true,Nat.add_zero] using hvec u
  have hpart := Finset.card_sdiff_add_card_eq_card hAB
  have hreserve : #(insert x L \ A) + 1 ≤ E.endpointCount u := by
    rcases hDu with hDu | hodd
    · omega
    · rw [Nat.odd_iff] at hodd
      omega
  have hnoU : u ∉ insert x L \ A := fun ht => hu (Finset.mem_sdiff.mp ht).1
  have hmiss : ∀ t ∈ insert x L \ A, ¬ (G ⊔ A.sup (SimpleGraph.edge u)).Adj u t := by
    intro t ht ha
    rcases ha with ha | ha
    · exact hmissing t (Finset.mem_sdiff.mp ht).1 ha
    · exact (Finset.mem_sdiff.mp ht).2 ((star_sup_adj_center u A huA t).mp ha)
  have hrestore : ∃ F : Decomposition ((G ⊔ A.sup (SimpleGraph.edge u)) ⊔
      (insert x L \ A).sup (SimpleGraph.edge u)), F.size = E.size ∧
      ∀ t, F.endpointCount t + (if u = t then #(insert x L \ A) else 0) =
        E.endpointCount t + if t ∈ insert x L \ A then 1 else 0 := by
    by_contra hf
    obtain ⟨he,htight⟩ := star_surplus_failure_profile E u (insert x L \ A)
      hnoU hmiss (hpassing A hAB hxA E hvec) hreserve hf
    have hg := hgain A hAB hxA E hvec htight
    have hA : A = insert x (L ∩ A) := by
      ext t
      simp only [Finset.mem_insert,Finset.mem_inter]
      constructor
      · intro ht
        rcases Finset.mem_insert.mp (hAB ht) with he | hl
        · exact Or.inl he
        · exact Or.inr ⟨hl,ht⟩
      · rintro (rfl | ⟨_,ht⟩)
        · exact hxA
        · exact ht
    have hxI : x ∉ L ∩ A := fun ht => hxL (Finset.mem_inter.mp ht).1
    have hcount : #A = #(L ∩ A) + 1 :=
      (congrArg Finset.card hA).trans (Finset.card_insert_of_notMem hxI)
    have hdiff : insert x L \ A = L \ A := by
      ext t
      simp only [Finset.mem_sdiff,Finset.mem_insert]
      constructor
      · rintro ⟨he | hl,hn⟩
        · exact False.elim (hn (he ▸ hxA))
        · exact ⟨hl,hn⟩
      · rintro ⟨hl,hn⟩; exact ⟨Or.inr hl,hn⟩
    rw [hdiff] at he
    omega
  obtain ⟨F,hFE,hend⟩ := hrestore
  have hgraph : (G ⊔ A.sup (SimpleGraph.edge u)) ⊔
      (insert x L \ A).sup (SimpleGraph.edge u) =
      G ⊔ (insert x L).sup (SimpleGraph.edge u) := by
    rw [sup_assoc,← Finset.sup_union,Finset.union_sdiff_of_subset hAB]
  have hout : ∃ F : Decomposition ((G ⊔ A.sup (SimpleGraph.edge u)) ⊔
      (insert x L \ A).sup (SimpleGraph.edge u)), F.size = D.size ∧
      ∀ t, t ≠ u → t ∉ insert x L → F.endpointCount t = D.endpointCount t := by
    refine ⟨F,hFE.trans hED,?_⟩
    intro t htu htB
    have htA : t ∉ A := fun ht => htB (hAB ht)
    have htR : t ∉ insert x L \ A := fun ht => htB (Finset.mem_sdiff.mp ht).1
    have hv := hvec t
    have hf := hend t
    simp only [htA,htR,htu.symm,if_false,Nat.add_zero] at hv hf
    exact hf.trans hv
  rwa [hgraph] at hout

/-- An odd residual star has one unit of reserve even after the first
outward payment has spent the centre's only endpoint. Failure therefore
forces every pending leaf to have two passing neighbours and forces the
exact endpoint/cardinality equality used by delayed-payment counting. -/
theorem odd_star_restoration_or_tight_profile
    (D : Decomposition G) (u b : V) (S : Finset V)
    (hu : u ∉ S) (hb : b ∈ S) (hodd : Odd #S)
    (hmissing : ∀ t ∈ S, ¬ G.Adj u t)
    (hpositive : ∀ t, G.Adj u t ∨ t ∈ S → 0 < D.endpointCount t)
    (hpassing : ∀ A : Finset V, A ⊆ S → b ∈ A →
      ∀ E : Decomposition (G ⊔ A.sup (SimpleGraph.edge u)),
      (∀ t, E.endpointCount t + (if t ∈ A then 1 else 0) =
        D.endpointCount t + if u = t then #A else 0) →
      ∀ t ∈ S \ A, passingNeighborCount E t ≤ 2) :
    (∃ F : Decomposition (G ⊔ S.sup (SimpleGraph.edge u)),
      F.size = D.size ∧ 0 < F.endpointCount u ∧ ∀ t, t ≠ u → t ∉ S →
        F.endpointCount t = D.endpointCount t) ∨
    (∃ A : Finset V, A ⊆ S ∧ b ∈ A ∧ #S ≤ 2 * #A ∧
      ∃ E : Decomposition (G ⊔ A.sup (SimpleGraph.edge u)),
        E.size = D.size ∧
        (∀ t, E.endpointCount t + (if t ∈ A then 1 else 0) =
          D.endpointCount t + if u = t then #A else 0) ∧
        D.endpointCount u + #A = #(S \ A) + 1 ∧
        ∀ t ∈ S \ A, passingNeighborCount E t = 2) := by
  classical
  obtain ⟨A,hAS,hbA,hhalf,E,hs,hvec⟩ :=
    D.prescribed_half_star_addibility u S hu hmissing hpositive b hb
  have huA : u ∉ A := fun ht => hu (hAS ht)
  have hEu : E.endpointCount u = D.endpointCount u + #A := by
    simpa only [huA,if_false,if_true,Nat.add_zero] using hvec u
  have hpart := Finset.card_sdiff_add_card_eq_card hAS
  have hreserve : #(S \ A) + 1 ≤ E.endpointCount u := by
    rw [Nat.odd_iff] at hodd
    omega
  have huR : u ∉ S \ A := fun ht => hu (Finset.mem_sdiff.mp ht).1
  have hmiss : ∀ t ∈ S \ A, ¬ (G ⊔ A.sup (SimpleGraph.edge u)).Adj u t := by
    intro t ht ha
    rcases ha with ha | ha
    · exact hmissing t (Finset.mem_sdiff.mp ht).1 ha
    · exact (Finset.mem_sdiff.mp ht).2 ((star_sup_adj_center u A huA t).mp ha)
  by_cases hr : ∃ F : Decomposition ((G ⊔ A.sup (SimpleGraph.edge u)) ⊔
      (S \ A).sup (SimpleGraph.edge u)), F.size = E.size ∧
      ∀ t, F.endpointCount t + (if u = t then #(S \ A) else 0) =
        E.endpointCount t + if t ∈ S \ A then 1 else 0
  · obtain ⟨F,hfs,hfv⟩ := hr
    have hg : (G ⊔ A.sup (SimpleGraph.edge u)) ⊔
        (S \ A).sup (SimpleGraph.edge u) = G ⊔ S.sup (SimpleGraph.edge u) := by
      rw [sup_assoc,← Finset.sup_union,Finset.union_sdiff_of_subset hAS]
    left
    rw [← hg]
    refine ⟨F,hfs.trans hs,?_,?_⟩
    · have hfu := hfv u
      simp only [huR,ite_true,ite_false,Nat.add_zero] at hfu
      omega
    intro t htu htS
    have htA : t ∉ A := fun ht => htS (hAS ht)
    have htR : t ∉ S \ A := fun ht => htS (Finset.mem_sdiff.mp ht).1
    have he := hvec t
    have hf := hfv t
    simp only [htA,htR,htu.symm,if_false,Nat.add_zero] at he hf
    exact hf.trans he
  · obtain ⟨he,htight⟩ := star_surplus_failure_profile E u (S \ A)
      huR hmiss (hpassing A hAS hbA E hvec) hreserve hr
    right
    exact ⟨A,hAS,hbA,hhalf,E,hs,hvec,by omega,htight⟩

/-- Private leaves cannot remain pending in a tight failure. Their forced
selection and the ordinary packet gain rule out delayed failure while
retaining a positive centre reserve for the final spoke payment. -/
theorem restore_delayed_odd_star_of_packet_gain
    (D : Decomposition G) (u b : V) (K L : Finset V) (N epsilon : ℕ)
    (hdisjoint : Disjoint K L) (hu : u ∉ K ∪ L) (hb : b ∈ K ∪ L)
    (hodd : Odd #(K ∪ L)) (hstrict : epsilon + 1 < #K + N)
    (hmissing : ∀ t ∈ K ∪ L, ¬ G.Adj u t)
    (hpositive : ∀ t, G.Adj u t ∨ t ∈ K ∪ L → 0 < D.endpointCount t)
    (hpassing : ∀ A : Finset V, A ⊆ K ∪ L → b ∈ A →
      ∀ E : Decomposition (G ⊔ A.sup (SimpleGraph.edge u)),
      (∀ t, E.endpointCount t + (if t ∈ A then 1 else 0) =
        D.endpointCount t + if u = t then #A else 0) →
      ∀ t ∈ (K ∪ L) \ A, passingNeighborCount E t ≤ 2)
    (hprivate : ∀ A : Finset V, A ⊆ K ∪ L → b ∈ A →
      ∀ E : Decomposition (G ⊔ A.sup (SimpleGraph.edge u)),
      (∀ t, E.endpointCount t + (if t ∈ A then 1 else 0) =
        D.endpointCount t + if u = t then #A else 0) →
      ∀ t ∈ K \ A, passingNeighborCount E t ≤ 1)
    (hgain : ∀ A : Finset V, A ⊆ K ∪ L → b ∈ A →
      ∀ E : Decomposition (G ⊔ A.sup (SimpleGraph.edge u)),
      (∀ t, E.endpointCount t + (if t ∈ A then 1 else 0) =
        D.endpointCount t + if u = t then #A else 0) →
      (∀ t ∈ (K ∪ L) \ A, passingNeighborCount E t = 2) →
      #(L \ A) + N ≤ #(L ∩ A) + epsilon) :
    ∃ F : Decomposition (G ⊔ (K ∪ L).sup (SimpleGraph.edge u)),
      F.size = D.size ∧ 0 < F.endpointCount u ∧
      ∀ t, t ≠ u → t ∉ K ∪ L → F.endpointCount t = D.endpointCount t := by
  classical
  rcases odd_star_restoration_or_tight_profile D u b (K ∪ L) hu hb hodd
      hmissing hpositive hpassing with hs | ⟨A,hA,hbA,_,E,_,hvec,htight,hzero⟩
  · exact hs
  · have hK : K ⊆ A := by
      intro t ht
      by_contra hn
      have hp := hprivate A hA hbA E hvec t (Finset.mem_sdiff.mpr ⟨ht,hn⟩)
      have hz := hzero t (Finset.mem_sdiff.mpr ⟨Finset.mem_union_left L ht,hn⟩)
      omega
    have hc := delayed_packet_failure_count K L A (D.endpointCount u) N epsilon
      hdisjoint hA hK htight (hgain A hA hbA E hvec hzero)
    omega

end Gallai.TwoException
