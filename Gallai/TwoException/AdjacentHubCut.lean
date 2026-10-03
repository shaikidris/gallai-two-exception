/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.AdjacentCut

@[expose] public section

/-! # The even/even hub-cut branch in Xie's Claim 1

This module isolates the first remaining hub-separator case of Xie's proof of
Theorem 1.4.  Unlike the ordinary-separator branch, both pieces retain the
exceptional hub `x`; the `x`-side is handled by adjacent minimality and the
opposite side by the one-exception endpoint theorem.  The final `y` output
uses the checked split-plus-double-merge consumer.

The odd/odd fresh-leaf branches are deliberately not folded into this file.
-/

namespace Gallai.TwoException

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- At a one-vertex union, even total degree at the shared hub and even degree
on one piece force even degree on the other piece.  This is the local parity
calculation used implicitly in Xie's even/even hub-cut subcase. -/
theorem hub_cut_even_right_of_total_even
    {A B : SimpleGraph V} [DecidableRel A.Adj] [DecidableRel B.Adj]
    (x : V)
    (hmeet : ∀ w, (∃ a, A.Adj w a) → (∃ b, B.Adj w b) → w = x)
    (hx : Even ((A ⊔ B).degree x)) (hxA : Even (A.degree x)) :
    Even (B.degree x) := by
  have hdis : Disjoint (A.neighborFinset x) (B.neighborFinset x) := by
    apply Finset.disjoint_left.mpr
    intro w ha hb
    have ha' := (A.mem_neighborFinset x w).mp ha
    have hb' := (B.mem_neighborFinset x w).mp hb
    exact ha'.ne (hmeet w ⟨x, ha'.symm⟩ ⟨x, hb'.symm⟩).symm
  have hxdeg : (A ⊔ B).degree x = A.degree x + B.degree x := by
    rw [← SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.neighborFinset_sup,
      Finset.card_union_of_disjoint hdis]
    rfl
  rw [hxdeg] at hx
  exact (Nat.even_add.mp hx).mp hxA

/-- At the same one-vertex union, an odd local degree on one piece forces an
odd local degree on the other whenever the total hub degree is even.  This is
the parity invariant for Xie's fresh-leaf hub-cut subcase. -/
theorem hub_cut_odd_right_of_total_even
    {A B : SimpleGraph V} [DecidableRel A.Adj] [DecidableRel B.Adj]
    (x : V)
    (hmeet : ∀ w, (∃ a, A.Adj w a) → (∃ b, B.Adj w b) → w = x)
    (hx : Even ((A ⊔ B).degree x)) (hxA : Odd (A.degree x)) :
    Odd (B.degree x) := by
  have hdis : Disjoint (A.neighborFinset x) (B.neighborFinset x) := by
    apply Finset.disjoint_left.mpr
    intro w ha hb
    have ha' := (A.mem_neighborFinset x w).mp ha
    have hb' := (B.mem_neighborFinset x w).mp hb
    exact ha'.ne (hmeet w ⟨x, ha'.symm⟩ ⟨x, hb'.symm⟩).symm
  have hxdeg : (A ⊔ B).degree x = A.degree x + B.degree x := by
    rw [← SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.neighborFinset_sup,
      Finset.card_union_of_disjoint hdis]
    rfl
  rw [Nat.even_iff, hxdeg] at hx
  rw [Nat.odd_iff] at hxA ⊢
  omega

/-- A disconnected deletion of an adjacent exceptional hub supplies the
literal source partition for the hub-cut cases.  The side containing the
other hub is selected by reachability in `G - x`; the opposite side carries a
vertex distinct from `x`, so both induced pieces are connected and nontrivial.
-/
theorem adjacent_hub_cut_partition_of_disconnected
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (x y : V) (hconn : G.Connected) (hxy : x ≠ y)
    (hdisc : ¬ (G.induce {v | v ≠ x}).Connected) :
    ∃ S T : Set V, ∃ _ : DecidablePred (· ∈ S), ∃ _ : DecidablePred (· ∈ T),
      y ∈ S ∧ x ∈ S ∧ x ∈ T ∧ (∃ b ∈ T, b ≠ x) ∧
      S ∪ T = Set.univ ∧ S ∩ T = {x} ∧
      (G.induce S).spanningCoe ⊔ (G.induce T).spanningCoe = G ∧
      (G.induce S).Connected ∧ (G.induce T).Connected := by
  classical
  obtain ⟨b, hb⟩ := exists_not_reachable_of_not_connected
    (G.induce {v | v ≠ x}) ⟨y, hxy.symm⟩ hdisc
  obtain ⟨S, T, hcover, hinter, hyS, hbT, hgraph, hconnS, hconnT⟩ :=
    cut_vertex_pieces G hconn x y b.val hxy.symm b.property hb
  letI : DecidablePred (· ∈ S) := Classical.decPred _
  letI : DecidablePred (· ∈ T) := Classical.decPred _
  have hxST : x ∈ S ∩ T := by
    rw [hinter]
    simp
  exact ⟨S, T, inferInstance, inferInstance, hyS, hxST.1, hxST.2,
    ⟨b, hbT, b.property⟩, hcover, hinter, hgraph, hconnS, hconnT⟩

/-- The oriented adjacent-hub cut partition additionally retains the source
choice that the `y`-side has connected core after `x` is removed.  This is the
form consumed by the singleton opposite-piece branch. -/
theorem adjacent_hub_cut_partition_with_selected_core_of_disconnected
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (x y : V) (hconn : G.Connected) (hxy : x ≠ y)
    (hdisc : ¬ (G.induce {v | v ≠ x}).Connected) :
    ∃ S T : Set V, ∃ _ : DecidablePred (· ∈ S), ∃ _ : DecidablePred (· ∈ T),
      y ∈ S ∧ x ∈ S ∧ x ∈ T ∧ (∃ b ∈ T, b ≠ x) ∧
      S ∪ T = Set.univ ∧ S ∩ T = {x} ∧
      (G.induce S).spanningCoe ⊔ (G.induce T).spanningCoe = G ∧
      (G.induce S).Connected ∧ (G.induce T).Connected ∧
      (G.induce {v | v ∈ S ∧ v ≠ x}).Connected := by
  classical
  obtain ⟨b, hb⟩ := exists_not_reachable_of_not_connected
    (G.induce {v | v ≠ x}) ⟨y, hxy.symm⟩ hdisc
  obtain ⟨S, T, hcover, hinter, hyS, hbT, hgraph, hconnS, hconnT, hcore⟩ :=
    cut_vertex_pieces_with_selected_core G hconn x y b.val hxy.symm b.property hb
  letI : DecidablePred (· ∈ S) := Classical.decPred _
  letI : DecidablePred (· ∈ T) := Classical.decPred _
  have hxST : x ∈ S ∩ T := by
    rw [hinter]
    simp
  exact ⟨S, T, inferInstance, inferInstance, hyS, hxST.1, hxST.2,
    ⟨b, hbT, b.property⟩, hcover, hinter, hgraph, hconnS, hconnT, hcore⟩

/-- The literal even/even hub-cut reconstruction from Xie's Claim 1.  The
two cut pieces meet only at the adjacent exceptional hub `x`; `y` lies on the
left, while `b` certifies that the right piece is nontrivial.  The local
evenness assumptions are exactly the source's Subcase 2.1. -/
theorem adjacent_hub_even_even_cut_not_edge_minimal
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (S T : Set V) [DecidablePred (· ∈ S)] [DecidablePred (· ∈ T)]
    (x y b : V) (M : AdjacentEdgeMinimalCounterexample G x y)
    (hcover : S ∪ T = Set.univ) (hinter : S ∩ T = {x})
    (hxS : x ∈ S) (hyS : y ∈ S) (hxT : x ∈ T) (hbT : b ∈ T)
    (hxy : x ≠ y) (hbx : b ≠ x)
    (hgraph : (G.induce S).spanningCoe ⊔ (G.induce T).spanningCoe = G)
    (hconnS : (G.induce S).Connected) (hconnT : (G.induce T).Connected)
    (hxEvenS : Even ((G.induce S).spanningCoe.degree x)) : False := by
  let A : SimpleGraph V := (G.induce S).spanningCoe
  let B : SimpleGraph V := (G.induce T).spanningCoe
  letI : DecidableRel (A ⊔ B).Adj := SimpleGraph.Sup.adjDecidable V A B
  have hAB : A ⊔ B = G := by
    simpa only [A, B] using hgraph
  have hA : A.support ⊆ S := by
    intro v hv
    rw [SimpleGraph.support_spanningCoe] at hv
    obtain ⟨w, hw, rfl⟩ := hv
    exact w.property
  have hB : B.support ⊆ T := by
    intro v hv
    rw [SimpleGraph.support_spanningCoe] at hv
    obtain ⟨w, hw, rfl⟩ := hv
    exact w.property
  have hmeetG : ∀ w, w ∈ S → w ∈ T → w = x := by
    intro w hwS hwT
    have hw : w ∈ S ∩ T := ⟨hwS, hwT⟩
    simpa only [hinter, Set.mem_singleton_iff] using hw
  have hmeet : ∀ w, (∃ a, A.Adj w a) → (∃ b, B.Adj w b) → w = x := by
    intro w hAw hBw
    rcases hAw with ⟨a, ha⟩
    rcases hBw with ⟨b, hb⟩
    exact hmeetG w (hA ⟨a, ha⟩) (hB ⟨b, hb⟩)
  have hyT : y ∉ T := by
    intro hyT
    exact hxy.symm (hmeetG y hyS hyT)
  have hyBiso : ∀ w, ¬ B.Adj y w := by
    intro w hyw
    exact hyT (hB ⟨w, hyw⟩)
  have hconnA : (A.induce S).Connected := by
    simpa only [A, SimpleGraph.induce_spanningCoe] using hconnS
  have hconnB : (B.induce T).Connected := by
    simpa only [B, SimpleGraph.induce_spanningCoe] using hconnT
  have hHAB : AdjacentInstance (A ⊔ B) x y :=
    AdjacentInstance.congr x y hAB.symm M.counterexample.1
  have hxEvenB : Even (B.degree x) :=
    hub_cut_even_right_of_total_even x hmeet hHAB.2.2.2.1
      (by simpa only [A] using hxEvenS)
  have hxyA : A.Adj x y := by
    exact (spanning_induce_adj_iff G S x y).mpr
      ⟨M.counterexample.1.2.2.1, hxS, hyS⟩
  have hleft : AdjacentInstance (A.induce S) ⟨x, hxS⟩ ⟨y, hyS⟩ := by
    exact adjacentInstance_induced_left_hub_of_union S x y hHAB hA hxS hyS hconnA
      (by simpa only [A] using hxEvenS) hyBiso hxyA hHAB.2.2.2.1 hmeet
  have hsmall0 : (G.induce S).edgeFinset.card < G.edgeFinset.card :=
    cut_piece_edge_count_lt (G := G) S T x M.counterexample.1.1 hxT hmeetG
      hgraph ⟨b, hbT, hbx⟩
  have hleftG : AdjacentInstance (G.induce S) ⟨x, hxS⟩ ⟨y, hyS⟩ := by
    simpa only [A, SimpleGraph.induce_spanningCoe] using hleft
  have hleftOutG := M.of_edge_smaller S (G.induce S) ⟨x, hxS⟩ ⟨y, hyS⟩
    hsmall0 hleftG
  have hAS : A.induce S = G.induce S := by
    simp only [A, SimpleGraph.induce_spanningCoe]
  have hleftOut : AdjacentConclusion (A.induce S) ⟨x, hxS⟩ ⟨y, hyS⟩ :=
    AdjacentConclusion.congr _ _ hAS.symm hleftOutG
  obtain ⟨Dx0, hDx0size, hxDx0⟩ := hleftOut.1
  obtain ⟨Dy0, hDy0size, hyDy0⟩ := hleftOut.2
  obtain ⟨Dx, hDxsize, hDxends⟩ := adjacent_lift_cut_piece S hA Dx0
  obtain ⟨Dy, hDysize, hDyends⟩ := adjacent_lift_cut_piece S hA Dy0
  have hxDx : 2 ≤ Dx.endpointCount x := by
    rw [hDxends ⟨x, hxS⟩]
    exact hxDx0
  have hyDy : 2 ≤ Dy.endpointCount y := by
    rw [hDyends ⟨y, hyS⟩]
    exact hyDy0
  have hntT : Nontrivial T := ⟨⟨x, hxT⟩, ⟨b, hbT⟩,
    fun h => hbx (congrArg Subtype.val h).symm⟩
  have hxposT : 0 < (B.induce T).degree ⟨x, hxT⟩ :=
    hconnB.preconnected.degree_pos_of_nontrivial ⟨x, hxT⟩
  obtain ⟨R0, hR0size, hxR0⟩ :=
    one_exception_endpoint_induced_right_of_absent_other_hub T x y hHAB hB hxT hyT
      hconnB hxposT (by
        rw [SimpleGraph.degree_induce_of_support_subset hB]
        exact hxEvenB) hHAB.2.2.2.1 hmeet
  obtain ⟨R, hRsize, hRends⟩ := adjacent_lift_cut_piece T hB R0
  have hxR : 2 ≤ R.endpointCount x := by
    rw [hRends ⟨x, hxT⟩]
    exact hxR0
  have hntS : Nontrivial S := ⟨⟨x, hxS⟩, ⟨y, hyS⟩,
    fun h => hxy (congrArg Subtype.val h)⟩
  have hxposA : 0 < (A.induce S).degree ⟨x, hxS⟩ :=
    hconnA.preconnected.degree_pos_of_nontrivial ⟨x, hxS⟩
  have hxpos : 0 < A.degree x := by
    rw [SimpleGraph.degree_induce_of_support_subset hA] at hxposA
    exact hxposA
  have hcard := card_cover_single_inter S T x hcover hinter
  have hbudget := ceiling_one_vertex_budget (Fintype.card S) (Fintype.card T)
    (Fintype.card V) hcard
  apply M.counterexample.2
  apply AdjacentConclusion.congr x y hAB
  exact xie_adjacent_hub_even_glue_after_exposure_double Dx Dy R x y hxy
    hxDx hyDy hxR hxpos (by simpa only [A] using hxEvenS)
    (adjacent_right_separator_incident T x b hB hxT hbT hbx hconnB)
    hmeet (by
      rw [hDxsize, hRsize]
      have hDx : Dx0.size ≤ (Fintype.card S + 1) / 2 := by simpa using hDx0size
      have hR : R0.size ≤ (Fintype.card T + 1) / 2 := by simpa using hR0size
      omega)
    (by
      rw [hDysize, hRsize]
      have hDy : Dy0.size ≤ (Fintype.card S + 1) / 2 := by simpa using hDy0size
      have hR : R0.size ≤ (Fintype.card T + 1) / 2 := by simpa using hR0size
      omega)

end Gallai.TwoException
