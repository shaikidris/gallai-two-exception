/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.DelayedAuxiliaryProfile

@[expose] public section

/-! # The double-spoke early-payment auxiliary -/
namespace Gallai.TwoException
open scoped Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
noncomputable local instance (u x q : V) (B : Finset V) :
    DecidableRel ((starPuncture G u B).deleteEdges {s(x,q)}).Adj :=
  fun _ _ => Classical.propDecidable _

noncomputable local instance (u x q : V) (B : Finset V) (M : List (V × V)) :
    DecidableRel (ordinaryMatePuncture
      ((starPuncture G u B).deleteEdges {s(x,q)}) M).Adj :=
  fun _ _ => Classical.propDecidable _

/-- Deleting both contacts of a double spoke petal and its hub spoke
leaves the spoke recipient even with E-degree zero. Only the star centre
can be a newly even vertex. -/
theorem early_double_spoke_profile
    (u x p q : V) (B : Finset V)
    (hadj : ∀ t ∈ B, G.Adj u t) (hleaves : ∀ t ∈ B, Even (G.degree t))
    (hpB : p ∈ B) (hqB : q ∈ B) (hxB : x ∉ B)
    (hxu : x ≠ u) (hpx : p ≠ x) (hpq : p ≠ q)
    (hxq : G.Adj x q) (hxEven : Even (G.degree x))
    (hpair : ∀ t, G.Adj q t → Even (G.degree t) → t = x ∨ t = p) :
    let J := (starPuncture G u B).deleteEdges {s(x,q)}
    (∀ t, Even (J.degree t) → Even (G.degree t) ∨ t = u) ∧
      Odd (J.degree x) ∧ Odd (J.degree p) ∧
      Even (J.degree q) ∧ eDegree J q = 0 := by
  classical
  let Q := starPuncture G u B
  let J := Q.deleteEdges {s(x,q)}
  letI : DecidableRel Q.Adj := fun _ _ => Classical.propDecidable _
  letI : DecidableRel J.Adj := fun _ _ => Classical.propDecidable _
  change (∀ t, Even (J.degree t) → Even (G.degree t) ∨ t = u) ∧
    Odd (J.degree x) ∧ Odd (J.degree p) ∧ Even (J.degree q) ∧ eDegree J q = 0
  have huB : u ∉ B := fun ht => G.irrefl (hadj u ht)
  have hqu : q ≠ u := (hadj q hqB).ne.symm
  have hxqQ : Q.Adj x q := by
    refine ⟨hxq,?_⟩
    intro ha
    exact hqu ((star_sup_adj_off_center u B x q hxu).mp ha).2
  have hxOdd : Odd (J.degree x) := by
    have hs := starPuncture_degree_other (G := G) u B x hxu hxB
    have hd := degree_delete_edge_add_one Q x q hxqQ
    simp only [← SimpleGraph.ncard_neighborSet] at hs hd hxEven ⊢
    change (J.neighborSet x).ncard + 1 = (Q.neighborSet x).ncard at hd
    rw [hs] at hd
    rw [Nat.even_iff] at hxEven
    rw [Nat.odd_iff]
    omega
  have hpOdd : Odd (J.degree p) :=
    contact_spoke_puncture_leaf_odd u x q p B hpB (hadj p hpB)
      (hleaves p hpB) hpx hpq
  have hqEven : Even (J.degree q) := by
    have hs := starPuncture_degree_leaf (G := G) u B q hqB (hadj q hqB)
    have hd := degree_delete_edge_add_one_other Q x q hxqQ
    have he := hleaves q hqB
    simp only [← SimpleGraph.ncard_neighborSet] at hs hd he ⊢
    change (Q.neighborSet q).ncard + 1 = (G.neighborSet q).ncard at hs
    change (J.neighborSet q).ncard + 1 = (Q.neighborSet q).ncard at hd
    rw [Nat.even_iff] at he ⊢
    omega
  have hprofile : ∀ t, Even (J.degree t) → Even (G.degree t) ∨ t = u := by
    intro t ht
    by_cases htu : t = u
    · exact Or.inr htu
    left
    by_cases htx : t = x
    · exact False.elim ((Nat.not_even_iff_odd.mpr hxOdd) (htx ▸ ht))
    by_cases htq : t = q
    · exact htq ▸ hleaves q hqB
    by_cases htB : t ∈ B
    · have ho := contact_spoke_puncture_leaf_odd u x q t B htB (hadj t htB)
        (hleaves t htB) htx htq
      exact False.elim ((Nat.not_even_iff_odd.mpr ho) ht)
    · have hs := starPuncture_degree_other (G := G) u B t htu htB
      have hd := degree_delete_edge_of_ne Q x q t htx htq
      simp only [← SimpleGraph.ncard_neighborSet] at hs hd ht ⊢
      change (J.neighborSet t).ncard = (Q.neighborSet t).ncard at hd
      rw [hd,hs] at ht
      exact ht
  refine ⟨hprofile,hxOdd,hpOdd,hqEven,?_⟩
  change #(evenNeighbors J q) = 0
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro t ht
  obtain ⟨hqt,htEven⟩ := (mem_evenNeighbors (G := J) q t).mp ht
  rcases hprofile t htEven with htOriginal | htu
  · rcases hpair t hqt.1.1 htOriginal with htx | htp
    · exact (Nat.not_even_iff_odd.mpr hxOdd) (htx ▸ htEven)
    · exact (Nat.not_even_iff_odd.mpr hpOdd) (htp ▸ htEven)
  · subst t
    exact starPuncture_missing G u B huB q hqB hqt.1.symm

/-- Disjoint ordinary and neutral mate preparations preserve the actual
double-spoke witness and introduce no additional even vertex. -/
theorem early_double_spoke_mates_profile
    (u x p q : V) (B : Finset V) (M : List (V × V))
    (hadj : ∀ t ∈ B, G.Adj u t) (hleaves : ∀ t ∈ B, Even (G.degree t))
    (hpB : p ∈ B) (hqB : q ∈ B) (hxB : x ∉ B)
    (hxu : x ≠ u) (hpx : p ≠ x) (hpq : p ≠ q)
    (hxq : G.Adj x q) (hxEven : Even (G.degree x))
    (hpair : ∀ t, G.Adj q t → Even (G.degree t) → t = x ∨ t = p)
    (hdis : M.Pairwise (fun e f =>
      e.1 ≠ f.1 ∧ e.1 ≠ f.2 ∧ e.2 ≠ f.1 ∧ e.2 ≠ f.2))
    (havoid : ∀ e ∈ M,
      e.1 ≠ u ∧ e.2 ≠ u ∧ e.1 ∉ B ∧ e.2 ∉ B ∧
      e.1 ≠ x ∧ e.2 ≠ x ∧ e.1 ≠ q ∧ e.2 ≠ q)
    (hedges : ∀ e ∈ M, G.Adj e.1 e.2 ∧
      Even (G.degree e.1) ∧ Even (G.degree e.2)) :
    let J := ordinaryMatePuncture ((starPuncture G u B).deleteEdges {s(x,q)}) M
    (∀ t, Even (J.degree t) → Even (G.degree t) ∨ t = u) ∧
      Odd (J.degree x) ∧ Odd (J.degree p) ∧
      Even (J.degree q) ∧ eDegree J q = 0 := by
  classical
  let Q := starPuncture G u B
  let K := Q.deleteEdges {s(x,q)}
  let J := ordinaryMatePuncture K M
  letI : DecidableRel Q.Adj := fun _ _ => Classical.propDecidable _
  letI : DecidableRel K.Adj := fun _ _ => Classical.propDecidable _
  letI : DecidableRel J.Adj := fun _ _ => Classical.propDecidable _
  change (∀ t, Even (J.degree t) → Even (G.degree t) ∨ t = u) ∧
    Odd (J.degree x) ∧ Odd (J.degree p) ∧ Even (J.degree q) ∧ eDegree J q = 0
  have hp := early_double_spoke_profile u x p q B hadj hleaves hpB hqB hxB
    hxu hpx hpq hxq hxEven hpair
  have hdeg : ∀ t, t ≠ u → t ∉ B → t ≠ x → t ≠ q →
      K.degree t = G.degree t := by
    intro t htu htB htx htq
    have hs := starPuncture_degree_other (G := G) u B t htu htB
    have hd := degree_delete_edge_of_ne Q x q t htx htq
    simp only [← SimpleGraph.ncard_neighborSet] at hs hd ⊢
    exact hd.trans hs
  have hm : ∀ e ∈ M, K.Adj e.1 e.2 ∧
      Even (K.degree e.1) ∧ Even (K.degree e.2) := by
    intro e he
    obtain ⟨heu,hevu,heB,hevB,hex,hevx,heq,hevq⟩ := havoid e he
    obtain ⟨ha,hpe,hqe⟩ := hedges e he
    have hQ : Q.Adj e.1 e.2 := by
      exact ⟨ha,fun ht => hevu ((star_sup_adj_off_center u B e.1 e.2 heu).mp ht).2⟩
    refine ⟨?_,?_,?_⟩
    · change Q.Adj e.1 e.2 ∧ _
      refine ⟨hQ,?_⟩
      simp
      rintro (he | he)
      · exact False.elim (hex (congrArg Prod.fst he))
      · exact False.elim (heq (congrArg Prod.fst he))
    · rw [hdeg e.1 heu heB hex heq]
      exact hpe
    · rw [hdeg e.2 hevu hevB hevx hevq]
      exact hqe
  have hkeep : ∀ t, Even (J.degree t) → Even (K.degree t) :=
    ordinaryMatePuncture_even_preserved (G := K) M hdis hm
  have hdx := ordinaryMatePuncture_degree_of_avoids (G := K) M x
    (fun e he => ⟨(havoid e he).2.2.2.2.1.symm,(havoid e he).2.2.2.2.2.1.symm⟩)
  have hdp := ordinaryMatePuncture_degree_of_avoids (G := K) M p (by
    intro e he
    exact ⟨fun ht => (havoid e he).2.2.1 (ht ▸ hpB),
      fun ht => (havoid e he).2.2.2.1 (ht ▸ hpB)⟩)
  have hdq := ordinaryMatePuncture_degree_of_avoids (G := K) M q
    (fun e he => ⟨(havoid e he).2.2.2.2.2.2.1.symm,
      (havoid e he).2.2.2.2.2.2.2.symm⟩)
  obtain ⟨hprofile,hxOdd,hpOdd,hqEven,hqzero⟩ := hp
  refine ⟨fun t ht => hprofile t (hkeep t ht),?_,?_,?_,?_⟩
  · simp only [← SimpleGraph.ncard_neighborSet] at hdx hxOdd ⊢
    rwa [hdx]
  · simp only [← SimpleGraph.ncard_neighborSet] at hdp hpOdd ⊢
    rwa [hdp]
  · simp only [← SimpleGraph.ncard_neighborSet] at hdq hqEven ⊢
    rwa [hdq]
  · have hmono := eDegree_le_of_subgraph_of_even_preservation
      (ordinaryMatePuncture_le (G := K) M) hkeep q
    change eDegree J q ≤ eDegree K q at hmono
    change eDegree K q = 0 at hqzero
    omega

/-- Every even mate endpoint is odd in the spoke auxiliary when the
disjoint mate family avoids the star leaves and the spoke endpoints. -/
theorem early_spoke_mates_endpoints_odd
    (u x q : V) (B : Finset V) (M : List (V × V))
    (hdis : M.Pairwise (fun e f =>
      e.1 ≠ f.1 ∧ e.1 ≠ f.2 ∧ e.2 ≠ f.1 ∧ e.2 ≠ f.2))
    (havoid : ∀ e ∈ M,
      e.1 ≠ u ∧ e.2 ≠ u ∧ e.1 ∉ B ∧ e.2 ∉ B ∧
      e.1 ≠ x ∧ e.2 ≠ x ∧ e.1 ≠ q ∧ e.2 ≠ q)
    (hedges : ∀ e ∈ M, G.Adj e.1 e.2 ∧
      Even (G.degree e.1) ∧ Even (G.degree e.2)) :
    let J := ordinaryMatePuncture ((starPuncture G u B).deleteEdges {s(x,q)}) M
    ∀ e ∈ M, Odd (J.degree e.1) ∧ Odd (J.degree e.2) := by
  classical
  let Q := starPuncture G u B
  let K := Q.deleteEdges {s(x,q)}
  letI : DecidableRel Q.Adj := fun _ _ => Classical.propDecidable _
  letI : DecidableRel K.Adj := fun _ _ => Classical.propDecidable _
  have hdeg : ∀ t, t ≠ u → t ∉ B → t ≠ x → t ≠ q →
      K.degree t = G.degree t := by
    intro t htu htB htx htq
    have hs := starPuncture_degree_other (G := G) u B t htu htB
    have hd := degree_delete_edge_of_ne Q x q t htx htq
    simp only [← SimpleGraph.ncard_neighborSet] at hs hd ⊢
    exact hd.trans hs
  have hm : ∀ e ∈ M, K.Adj e.1 e.2 ∧
      Even (K.degree e.1) ∧ Even (K.degree e.2) := by
    intro e he
    obtain ⟨heu,hevu,heB,hevB,hex,hevx,heq,hevq⟩ := havoid e he
    obtain ⟨ha,hpe,hqe⟩ := hedges e he
    have hQ : Q.Adj e.1 e.2 :=
      ⟨ha,fun ht => hevu ((star_sup_adj_off_center u B e.1 e.2 heu).mp ht).2⟩
    refine ⟨?_,?_,?_⟩
    · change Q.Adj e.1 e.2 ∧ _
      refine ⟨hQ,?_⟩
      simp
      rintro (he | he)
      · exact False.elim (hex (congrArg Prod.fst he))
      · exact False.elim (heq (congrArg Prod.fst he))
    · rw [hdeg e.1 heu heB hex heq]
      exact hpe
    · rw [hdeg e.2 hevu hevB hevx hevq]
      exact hqe
  exact ordinaryMatePuncture_endpoints_odd (G := K) M hdis hm

/-- Complete even-contact coverage gives the actual double-spoke mate
auxiliary its global subcubic cap. The only possible even neighbour of
the newly even centre is the protected bare vertex. -/
theorem bare_early_double_spoke_mates_cap
    (h x : V) (H : BareMinimalCounterexample G h x)
    (u p q : V) (B : Finset V) (M : List (V × V))
    (hadj : ∀ t ∈ B, G.Adj u t) (hleaves : ∀ t ∈ B, Even (G.degree t))
    (hpB : p ∈ B) (hqB : q ∈ B) (hxB : x ∉ B)
    (hxu : x ≠ u) (hpx : p ≠ x) (hpq : p ≠ q)
    (hxq : G.Adj x q)
    (hpair : ∀ t, G.Adj q t → Even (G.degree t) → t = x ∨ t = p)
    (hdis : M.Pairwise (fun e f =>
      e.1 ≠ f.1 ∧ e.1 ≠ f.2 ∧ e.2 ≠ f.1 ∧ e.2 ≠ f.2))
    (havoid : ∀ e ∈ M,
      e.1 ≠ u ∧ e.2 ≠ u ∧ e.1 ∉ B ∧ e.2 ∉ B ∧
      e.1 ≠ x ∧ e.2 ≠ x ∧ e.1 ≠ q ∧ e.2 ≠ q)
    (hedges : ∀ e ∈ M, G.Adj e.1 e.2 ∧
      Even (G.degree e.1) ∧ Even (G.degree e.2))
    (hcontacts : ∀ t, G.Adj u t → Even (G.degree t) →
      t ∈ B ∨ (∃ e ∈ M, t = e.1 ∨ t = e.2) ∨ t = x ∨ t = h) :
    let J := ordinaryMatePuncture ((starPuncture G u B).deleteEdges {s(x,q)}) M
    (∀ t, Even (J.degree t) → eDegree J t ≤ 3) ∧ eDegree J u ≤ 1 := by
  classical
  let K := (starPuncture G u B).deleteEdges {s(x,q)}
  let J := ordinaryMatePuncture K M
  letI : DecidableRel K.Adj := fun _ _ => Classical.propDecidable _
  letI : DecidableRel J.Adj := fun _ _ => Classical.propDecidable _
  change (∀ t, Even (J.degree t) → eDegree J t ≤ 3) ∧ eDegree J u ≤ 1
  rcases H.counterexample.1 with ⟨_,_,_,_,hxEven,hhzero,hcap⟩
  obtain ⟨hprofile,hxOdd,_,_,_⟩ := early_double_spoke_mates_profile
    u x p q B M hadj hleaves hpB hqB hxB hxu hpx hpq hxq hxEven hpair
    hdis havoid hedges
  have hmOdd := early_spoke_mates_endpoints_odd u x q B M hdis havoid hedges
  change Odd (J.degree x) at hxOdd
  have hsub : J ≤ G := fun _ _ ha =>
    ((ordinaryMatePuncture_le (G := K) M) ha).1.1
  have huB : u ∉ B := fun ht => G.irrefl (hadj u ht)
  have hcentre : ∀ t, J.Adj u t → Even (J.degree t) → t = h := by
    intro t hut ht
    rcases hprofile t ht with htOriginal | htu
    · rcases hcontacts t (hsub hut) htOriginal with htB | hmate | htx | hth
      · exact False.elim (starPuncture_missing G u B huB t htB
          ((ordinaryMatePuncture_le (G := K) M) hut).1)
      · obtain ⟨e,he,hte⟩ := hmate
        obtain ⟨h1,h2⟩ := hmOdd e he
        rcases hte with hte | hte
        · exact False.elim ((Nat.not_even_iff_odd.mpr h1) (hte ▸ ht))
        · exact False.elim ((Nat.not_even_iff_odd.mpr h2) (hte ▸ ht))
      · exact False.elim ((Nat.not_even_iff_odd.mpr hxOdd) (htx ▸ ht))
      · exact hth
    · subst t
      exact False.elim (J.irrefl hut)
  have hc : ∀ t, Even (G.degree t) → t ≠ x → eDegree G t ≤ 3 := by
    intro t ht htx
    by_cases hth : t = h
    · subst t
      omega
    · exact hcap t ht hth htx
  refine ⟨puncture_cap_of_one_new_even_center h x u hsub hprofile hxOdd hhzero hc hcentre,?_⟩
  change #(evenNeighbors J u) ≤ 1
  apply (Finset.card_le_card (show evenNeighbors J u ⊆ {h} from ?_)).trans_eq
    (Finset.card_singleton h)
  intro t ht
  obtain ⟨hut,htEven⟩ := (mem_evenNeighbors (G := J) u t).mp ht
  exact Finset.mem_singleton.mpr (hcentre t hut htEven)

end Gallai.TwoException
