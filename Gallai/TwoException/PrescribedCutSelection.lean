/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.PrescribedLeafCut
public import Gallai.TwoException.PrescribedPendant

@[expose] public section

/-! # Selection of actual prescribed-vertex cut branches -/

namespace Gallai.TwoException
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- An actual two-vertex cut side is a leaf edge. Separation and side
connectivity derive every leaf-cut guard, including the connected core. -/
theorem prescribed_two_vertex_cut_side
    (S T : Set V) [DecidablePred (· ∈ S)] [DecidablePred (· ∈ T)]
    (h x : V) (hconn : G.Connected) (hhne : h ≠ x)
    (hhEven : Even (G.degree h)) (hxEven : Even (G.degree x))
    (hhx : ¬ G.Adj h x) (hhT : h ∈ T)
    (hcover : S ∪ T = Set.univ) (hinter : S ∩ T = {h})
    (hgraph : (G.induce S).spanningCoe ⊔ (G.induce T).spanningCoe = G)
    (hconnT : (G.induce T).Connected)
    (hcoreS : (G.induce {a | a ∈ S ∧ a ≠ h}).Connected)
    (hcardT : Fintype.card T = 2)
    (hcap : ∀ a, Even (G.degree a) → a ≠ h → a ≠ x → eDegree G a ≤ 3)
    (hind : ∀ (J : SimpleGraph V) [DecidableRel J.Adj],
      J.edgeFinset.card < G.edgeFinset.card → J.Connected →
      ∀ a b : V, a ≠ b → 0 < J.degree a → Even (J.degree a) →
      Even (J.degree b) →
      (∀ t, Even (J.degree t) → t ≠ a → t ≠ b → eDegree J t ≤ 3) →
      BareConclusion J a) : BareConclusion G h := by
  classical
  have hpair : ∃ w, w ≠ h ∧ T = {h, w} := by
    obtain ⟨a, b, hab, ht⟩ := Set.ncard_eq_two.mp
      (show T.ncard = 2 by rwa [← Set.fintypeCard_eq_ncard])
    have hm : h = a ∨ h = b := by simpa only [ht, Set.mem_insert_iff,
      Set.mem_singleton_iff] using hhT
    rcases hm with rfl | rfl
    · exact ⟨b, hab.symm, ht⟩
    · exact ⟨a, hab, by simpa only [Set.pair_comm] using ht⟩
  obtain ⟨w, hwh, ht⟩ := hpair
  have hwT : w ∈ T := by simp [ht]
  have hwS : w ∉ S := by
    intro hs
    have hm : w ∈ S ∩ T := ⟨hs, hwT⟩
    exact hwh (by simpa only [hinter, Set.mem_singleton_iff] using hm)
  have hsep (a b : V) (hab : G.Adj a b) :
      (a ∈ S ∧ b ∈ S) ∨ (a ∈ T ∧ b ∈ T) := by
    rw [← hgraph, SimpleGraph.sup_adj] at hab
    rcases hab with hs | ht'
    · exact Or.inl ((spanning_induce_adj_iff G S a b).mp hs).2
    · exact Or.inr ((spanning_induce_adj_iff G T a b).mp ht').2
  let : Nontrivial T := ⟨⟨h, hhT⟩, ⟨w, hwT⟩,
    fun he => hwh (congrArg Subtype.val he).symm⟩
  obtain ⟨a, ha⟩ := hconnT.preconnected.exists_adj_of_nontrivial ⟨h, hhT⟩
  have haw : a.val = w := by
    have hm : a.val = h ∨ a.val = w := by simpa [ht] using a.property
    exact hm.resolve_left (fun he => ha.ne (Subtype.ext he.symm))
  have hhw : G.Adj h w := by simpa only [haw] using (show G.Adj h a.val from ha)
  have hwleaf (a : V) (ha : G.Adj w a) : a = h := by
    have hm : a ∈ T := (hsep w a ha).resolve_left (fun hs => hwS hs.1) |>.2
    have ham : a = h ∨ a = w := by simpa [ht] using hm
    exact ham.resolve_right (fun he => ha.ne he.symm)
  have hwd : G.degree w = 1 := by
    rw [SimpleGraph.degree_eq_one_iff_existsUnique_adj]
    exact ⟨h, hhw.symm, fun a ha => hwleaf a ha⟩
  have hcoreEq : {a : V | a ∈ S ∧ a ≠ h} = {a | a ≠ h ∧ a ≠ w} := by
    ext a
    constructor
    · rintro ⟨haS, hah⟩
      exact ⟨hah, fun he => hwS (he ▸ haS)⟩
    · rintro ⟨hah, haw'⟩
      have hm : a ∈ S ∪ T := by rw [hcover]; trivial
      have haT : a ∉ T := by simp [ht, hah, haw']
      exact ⟨hm.resolve_right haT, hah⟩
  apply prescribed_leaf_cut_reducible G h x w hconn hhne hhEven hxEven hhx
    (by rwa [← hcoreEq]) hhw (by simp [hwd]) hwleaf hcap hind

/-- A selected nontrivial core side exhausts all even-order cut branches.
Local even degrees use even-side gluing. Local odd degrees use the
fresh-pendant argument, except for the literal two-vertex leaf side. -/
theorem prescribed_selected_core_cut
    (S T : Set V) [DecidablePred (· ∈ S)] [DecidablePred (· ∈ T)]
    (h x : V) (hconn : G.Connected) (hhne : h ≠ x)
    (hhEven : Even (G.degree h)) (hxEven : Even (G.degree x))
    (hhx : ¬ G.Adj h x) (hn : Even (Fintype.card V))
    (hhS : h ∈ S) (hhT : h ∈ T)
    (hcover : S ∪ T = Set.univ) (hinter : S ∩ T = {h})
    (hgraph : (G.induce S).spanningCoe ⊔ (G.induce T).spanningCoe = G)
    (hconnS : (G.induce S).Connected) (hconnT : (G.induce T).Connected)
    (hcoreS : (G.induce {a | a ∈ S ∧ a ≠ h}).Connected)
    (hsizeS : 3 ≤ Fintype.card S) (hsizeT : 2 ≤ Fintype.card T)
    (hcap : ∀ a, Even (G.degree a) → a ≠ h → a ≠ x → eDegree G a ≤ 3)
    (hvertex : ∀ (W : Type u) [Fintype W] [DecidableEq W]
      (J : SimpleGraph W) [DecidableRel J.Adj],
      Fintype.card W < Fintype.card V → J.Connected →
      ∀ a b : W, a ≠ b → 0 < J.degree a → Even (J.degree a) →
      Even (J.degree b) →
      (∀ a', Even (J.degree a') → a' ≠ a → a' ≠ b → eDegree J a' ≤ 3) →
      BareConclusion J a)
    (hedge : ∀ (J : SimpleGraph V) [DecidableRel J.Adj],
      J.edgeFinset.card < G.edgeFinset.card → J.Connected →
      ∀ a b : V, a ≠ b → 0 < J.degree a → Even (J.degree a) →
      Even (J.degree b) →
      (∀ a', Even (J.degree a') → a' ≠ a → a' ≠ b → eDegree J a' ≤ 3) →
      BareConclusion J a) : BareConclusion G h := by
  classical
  let A := (G.induce S).spanningCoe
  let B := (G.induce T).spanningCoe
  let : DecidableRel A.Adj := fun _ _ => Classical.propDecidable _
  let : DecidableRel B.Adj := fun _ _ => Classical.propDecidable _
  have hg : A ⊔ B = G := hgraph
  have hA : A.support ⊆ S := by
    rintro a ⟨b, hab⟩
    exact ((spanning_induce_adj_iff G S a b).mp hab).2.1
  have hB : B.support ⊆ T := by
    rintro a ⟨b, hab⟩
    exact ((spanning_induce_adj_iff G T a b).mp hab).2.1
  have hcA : (A.induce S).Connected := by
    change (((G.induce S).spanningCoe).induce S).Connected
    rwa [SimpleGraph.induce_spanningCoe]
  have hcB : (B.induce T).Connected := by
    change (((G.induce T).spanningCoe).induce T).Connected
    rwa [SimpleGraph.induce_spanningCoe]
  have hhE := even_degree_congr h hg.symm hhEven
  have hxE := even_degree_congr x hg.symm hxEven
  have hcap' : ∀ a, Even ((A ⊔ B).degree a) → a ≠ h → a ≠ x →
      eDegree (A ⊔ B) a ≤ 3 := by
    simpa only [eDegree, evenNeighbors, SimpleGraph.degree,
      SimpleGraph.neighborFinset, ← Set.ncard_eq_toFinset_card', hg] using hcap
  have hincA : ∃ a, A.Adj h a := by
    let : Nontrivial S := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
    obtain ⟨a, ha⟩ := hcA.preconnected.exists_adj_of_nontrivial ⟨h, hhS⟩
    exact ⟨a.val, ha⟩
  have hincB : ∃ b, B.Adj h b := by
    let : Nontrivial T := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
    obtain ⟨b, hb⟩ := hcB.preconnected.exists_adj_of_nontrivial ⟨h, hhT⟩
    exact ⟨b.val, hb⟩
  have hmeet (a : V) (ha : ∃ b, A.Adj a b) (hb : ∃ b, B.Adj a b) : a = h := by
    have hm : a ∈ S ∩ T := ⟨hA ha, hB hb⟩
    simpa only [hinter, Set.mem_singleton_iff] using hm
  by_cases he : Even (A.degree h)
  · have heB := even_right_of_even_one_vertex_union A B h hhE he hmeet
    exact bareConclusion_congr h hg (prescribed_actual_even_cut A B S T h x hhS
      hhT hhne hcover hinter hA hB hcA hcB hhE hxE he heB hincA hincB hcap' hvertex)
  · have hoA := Nat.not_even_iff_odd.mp he
    have hdis : Disjoint (A.neighborFinset h) (B.neighborFinset h) := by
      apply Finset.disjoint_left.mpr
      intro a ha hb
      have ha' := (SimpleGraph.mem_neighborFinset A h a).mp ha
      have hb' := (SimpleGraph.mem_neighborFinset B h a).mp hb
      exact ha'.ne (hmeet a ⟨h, ha'.symm⟩ ⟨h, hb'.symm⟩).symm
    have hdeg : (A ⊔ B).degree h = A.degree h + B.degree h := by
      rw [← SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.neighborFinset_sup,
        Finset.card_union_of_disjoint hdis]
      rfl
    have hoB : Odd (B.degree h) := by
      rw [hdeg] at hhE
      rcases hhE with ⟨a, ha⟩
      rcases hoA with ⟨b, hb⟩
      apply Nat.not_even_iff_odd.mp
      rintro ⟨c, hc⟩
      omega
    have hcard := card_cover_single_inter S T h hcover hinter
    by_cases hsOdd : Odd (Fintype.card S)
    · by_cases htFour : 4 ≤ Fintype.card T
      · exact bareConclusion_congr h hg (prescribed_actual_odd_cut A B S T h x hhS
          hhT hhne hcover hinter hA hB hcA hcB hoA hoB hhE hxE hsOdd htFour hcap' hvertex)
      · have htTwo : Fintype.card T = 2 := by
          rcases hn with ⟨a, ha⟩
          rcases hsOdd with ⟨b, hb⟩
          omega
        exact prescribed_two_vertex_cut_side G S T h x hconn hhne hhEven hxEven hhx
          hhT hcover hinter hgraph hconnT hcoreS htTwo hcap hedge
    · have hsEven := Nat.not_odd_iff_even.mp hsOdd
      have htOdd : Odd (Fintype.card T) := by
        apply Nat.not_even_iff_odd.mp
        rintro ⟨c, hc⟩
        rcases hn with ⟨a, ha⟩
        rcases hsEven with ⟨b, hb⟩
        omega
      have hsFour : 4 ≤ Fintype.card S := by
        rcases hsEven with ⟨a, ha⟩
        omega
      have hout := prescribed_actual_odd_cut B A T S h x hhT hhS hhne
        (by simpa only [Set.union_comm] using hcover)
        (by simpa only [Set.inter_comm] using hinter) hB hA hcB hcA hoB hoA
        (by simpa only [SimpleGraph.degree, SimpleGraph.neighborFinset,
          ← Set.ncard_eq_toFinset_card', sup_comm] using hhE)
        (by simpa only [SimpleGraph.degree, SimpleGraph.neighborFinset,
          ← Set.ncard_eq_toFinset_card', sup_comm] using hxE)
        htOdd hsFour (by simpa only [SimpleGraph.degree, SimpleGraph.neighborFinset,
          ← Set.ncard_eq_toFinset_card', sup_comm] using hcap') hvertex
      exact bareConclusion_congr h (by simpa only [sup_comm] using hg) hout

/-- An arbitrary even-order cut at the prescribed hub supplies a selected
nontrivial core unless the hub has E-degree zero, which is the checked bare
case. The cut decomposition and every side-size guard are constructed here. -/
theorem prescribed_even_order_cut_reducible (h x : V)
    (hconn : G.Connected) (hhne : h ≠ x) (hhpos : 0 < G.degree h)
    (hhEven : Even (G.degree h)) (hxEven : Even (G.degree x))
    (hhx : ¬ G.Adj h x) (hn : Even (Fintype.card V))
    (hdisc : ¬ (G.induce {a | a ≠ h}).Connected)
    (hcap : ∀ a, Even (G.degree a) → a ≠ h → a ≠ x → eDegree G a ≤ 3)
    (hvertex : ∀ (W : Type u) [Fintype W] [DecidableEq W]
      (J : SimpleGraph W) [DecidableRel J.Adj],
      Fintype.card W < Fintype.card V → J.Connected →
      ∀ a b : W, a ≠ b → 0 < J.degree a → Even (J.degree a) →
      Even (J.degree b) →
      (∀ a', Even (J.degree a') → a' ≠ a → a' ≠ b → eDegree J a' ≤ 3) →
      BareConclusion J a)
    (hedge : ∀ (J : SimpleGraph V) [DecidableRel J.Adj],
      J.edgeFinset.card < G.edgeFinset.card → J.Connected →
      ∀ a b : V, a ≠ b → 0 < J.degree a → Even (J.degree a) →
      Even (J.degree b) →
      (∀ a', Even (J.degree a') → a' ≠ a → a' ≠ b → eDegree J a' ≤ 3) →
      BareConclusion J a) : BareConclusion G h := by
  classical
  by_cases hz : eDegree G h = 0
  · exact bare_endpoint h x ⟨hconn, hhne, hhpos, hhEven, hxEven, hz, hcap⟩
  obtain ⟨v, hv⟩ := Finset.card_pos.mp (show 0 < eDegree G h by omega)
  obtain ⟨hhv, hvEven⟩ := (mem_evenNeighbors h v).mp hv
  have hvh : v ≠ h := hhv.ne.symm
  have hvdeg : 2 ≤ G.degree v := by
    have hp := hhv.degree_pos_right
    rcases hvEven with ⟨a, ha⟩
    omega
  have hhNv : h ∈ G.neighborFinset v := (SimpleGraph.mem_neighborFinset G v h).mpr hhv.symm
  have herase : 0 < ((G.neighborFinset v).erase h).card := by
    rw [Finset.card_erase_of_mem hhNv, SimpleGraph.card_neighborFinset_eq_degree]
    omega
  obtain ⟨b, hb⟩ := Finset.card_pos.mp herase
  obtain ⟨hbh, hbN⟩ := Finset.mem_erase.mp hb
  have hvb : G.Adj v b := (SimpleGraph.mem_neighborFinset G v b).mp hbN
  have hbv : b ≠ v := hvb.ne.symm
  obtain ⟨c, hnc⟩ := exists_not_reachable_of_not_connected
    (G.induce {a | a ≠ h}) ⟨v, hvh⟩ hdisc
  obtain ⟨S, T, hcover, hinter, hvS, hcT, hgraph, hconnS, hconnT, hcoreS⟩ :=
    cut_vertex_pieces_with_selected_core G hconn h v c.val hvh c.property hnc
  have hhST : h ∈ S ∩ T := by rw [hinter]; simp
  have hhS := hhST.1
  have hhT := hhST.2
  have hvT : v ∉ T := by
    intro hvt
    have hm : v ∈ S ∩ T := ⟨hvS, hvt⟩
    exact hvh (by simpa only [hinter, Set.mem_singleton_iff] using hm)
  have hbS : b ∈ S := by
    have hp := hvb
    rw [← hgraph, SimpleGraph.sup_adj] at hp
    rcases hp with hs | ht
    · exact ((spanning_induce_adj_iff G S v b).mp hs).2.2
    · exact (hvT ((spanning_induce_adj_iff G T v b).mp ht).2.1).elim
  have hsfin : ({h, v, b} : Finset V) ⊆ S.toFinset := by
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl <;> simp [hhS, hvS, hbS]
  have htfin : ({h, c.val} : Finset V) ⊆ T.toFinset := by
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl <;> simp [hhT, hcT]
  have hsizeS : 3 ≤ Fintype.card S := by
    have hp := Finset.card_le_card hsfin
    simpa [hvh, hbh, hbv, Ne.symm hvh, Ne.symm hbh, Ne.symm hbv] using hp
  have hsizeT : 2 ≤ Fintype.card T := by
    have hp := Finset.card_le_card htfin
    simpa [c.property, Ne.symm c.property] using hp
  exact prescribed_selected_core_cut G S T h x hconn hhne hhEven hxEven hhx hn
    hhS hhT hcover hinter hgraph hconnS hconnT hcoreS hsizeS hsizeT hcap hvertex hedge

end Gallai.TwoException
