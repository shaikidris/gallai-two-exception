/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.EarlyPrefixRestoration

@[expose] public section

/-! # Actual recipient reserve in single-spoke early payment -/
namespace Gallai.TwoException
open scoped Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
noncomputable local instance singleSpokeStarAdj (u : V) (B : Finset V) :
    DecidableRel (starPuncture G u B).Adj := fun _ _ => Classical.propDecidable _
noncomputable local instance singleSpokeDeletedAdj (u x q : V) (B : Finset V) :
    DecidableRel ((starPuncture G u B).deleteEdges {s(x,q)}).Adj :=
  fun _ _ => Classical.propDecidable _
noncomputable local instance singleSpokeMatesAdj (u x q : V) (B : Finset V)
    (O : List (V × V)) : DecidableRel
      (ordinaryMatePuncture ((starPuncture G u B).deleteEdges {s(x,q)}) O).Adj :=
  fun _ _ => Classical.propDecidable _

/-- The unselected private mate loses only its hub spoke and is odd
before restoration; ordinary packet mates avoid it. -/
theorem early_single_spoke_recipient_odd
    (u x q : V) (B : Finset V) (O : List (V × V))
    (hxu : x ≠ u) (hqu : q ≠ u) (hqB : q ∉ B)
    (hxq : G.Adj x q) (hqEven : Even (G.degree q))
    (havoid : ∀ e ∈ O, q ≠ e.1 ∧ q ≠ e.2) :
    Odd ((ordinaryMatePuncture
      ((starPuncture G u B).deleteEdges {s(x,q)}) O).degree q) := by
  classical
  let K := (starPuncture G u B).deleteEdges {s(x,q)}
  letI : DecidableRel K.Adj := fun _ _ => Classical.propDecidable _
  have hxqS : (starPuncture G u B).Adj x q := by
    refine ⟨hxq,?_⟩
    intro ht
    exact hqu ((star_sup_adj_off_center u B x q hxu).mp ht).2
  have hs := starPuncture_degree_other (G := G) u B q hqu hqB
  have hd := degree_delete_edge_add_one_other (starPuncture G u B) x q hxqS
  have hm := ordinaryMatePuncture_degree_of_avoids (G := K) O q havoid
  simp only [← SimpleGraph.ncard_neighborSet] at hs hd hm hqEven ⊢
  rw [hm]
  change (K.neighborSet q).ncard + 1 =
    ((starPuncture G u B).neighborSet q).ncard at hd
  rw [hs] at hd
  rw [Nat.even_iff] at hqEven
  rw [Nat.odd_iff]
  omega

/-- The exact early-prefix endpoint transfer supplies the two-endpoint
reserve at the sole-single mate, without a favourable endpoint assumption. -/
theorem early_single_prefix_recipient_surplus
    (u x q : V) (B : Finset V) (O : List (V × V))
    (hxu : x ≠ u) (hqu : q ≠ u) (hqB : q ∉ B)
    (hxq : G.Adj x q) (hqEven : Even (G.degree q))
    (havoid : ∀ e ∈ O, q ≠ e.1 ∧ q ≠ e.2)
    (D : Decomposition (ordinaryMatePuncture
      ((starPuncture G u B).deleteEdges {s(x,q)}) O))
    (E : Decomposition (starPuncture G u B))
    (htransfer : E.endpointCount q + (if x = q then 1 else 0) =
      D.endpointCount q + if q = q then 1 else 0) :
    2 ≤ E.endpointCount q := by
  have hp := D.endpointCount_pos_of_odd_degree q
    (early_single_spoke_recipient_odd u x q B O hxu hqu hqB hxq hqEven havoid)
  simp only [hxq.ne, ite_false, ite_true, Nat.add_zero] at htransfer
  omega

/-- Deleting the contact star, one even-even spoke and ordinary even-even
mates introduces no new even vertex other than the star centre. -/
theorem early_single_spoke_even_profile
    (u x q : V) (B : Finset V) (O : List (V × V))
    (hleaves : ∀ t ∈ B, Even (G.degree t))
    (hxEven : Even (G.degree x)) (hqEven : Even (G.degree q))
    (hmEven : ∀ e ∈ O, Even (G.degree e.1) ∧ Even (G.degree e.2)) :
    ∀ t, Even ((ordinaryMatePuncture
      ((starPuncture G u B).deleteEdges {s(x,q)}) O).degree t) →
      Even (G.degree t) ∨ t = u := by
  classical
  intro t ht
  by_cases he : Even (G.degree t)
  · exact Or.inl he
  by_cases htu : t = u
  · exact Or.inr htu
  have htB : t ∉ B := fun hm => he (hleaves t hm)
  have htx : t ≠ x := fun h => he (h ▸ hxEven)
  have htq : t ≠ q := fun h => he (h ▸ hqEven)
  let K := (starPuncture G u B).deleteEdges {s(x,q)}
  letI : DecidableRel K.Adj := fun _ _ => Classical.propDecidable _
  have hs := starPuncture_degree_other (G := G) u B t htu htB
  have hd := degree_delete_edge_of_ne (starPuncture G u B) x q t htx htq
  have hm := ordinaryMatePuncture_degree_of_avoids (G := K) O t (by
    intro e hem
    exact ⟨fun h => he (h ▸ (hmEven e hem).1),
      fun h => he (h ▸ (hmEven e hem).2)⟩)
  simp only [← SimpleGraph.ncard_neighborSet] at hs hd hm ht he
  exact False.elim (he (by rwa [hm,hd,hs] at ht))

/-- In the single-spoke auxiliary, both original even neighbours of the
recipient are odd and the centre is not adjacent to it. Its E-degree is
therefore zero, independently of the auxiliary decomposition. -/
theorem early_single_spoke_recipient_eDegree_zero
    (u x p q : V) (B : Finset V) (O : List (V × V))
    (hadj : ∀ t ∈ B, G.Adj u t) (hleaves : ∀ t ∈ B, Even (G.degree t))
    (hpB : p ∈ B) (hqB : q ∉ B) (hxB : x ∉ B)
    (hxu : x ≠ u) (hqu : q ≠ u) (hpq : p ≠ q)
    (hxq : G.Adj x q) (hxEven : Even (G.degree x)) (hqEven : Even (G.degree q))
    (hquMissing : ¬ G.Adj q u)
    (hpair : ∀ t, G.Adj q t → Even (G.degree t) → t = x ∨ t = p)
    (havoid : ∀ e ∈ O, e.1 ∉ B ∧ e.2 ∉ B ∧
      x ≠ e.1 ∧ x ≠ e.2 ∧ q ≠ e.1 ∧ q ≠ e.2)
    (hmEven : ∀ e ∈ O, Even (G.degree e.1) ∧ Even (G.degree e.2)) :
    eDegree (ordinaryMatePuncture
      ((starPuncture G u B).deleteEdges {s(x,q)}) O) q = 0 := by
  classical
  let J := ordinaryMatePuncture ((starPuncture G u B).deleteEdges {s(x,q)}) O
  letI : DecidableRel J.Adj := fun _ _ => Classical.propDecidable _
  have hprofile := early_single_spoke_even_profile u x q B O hleaves hxEven hqEven hmEven
  have hxOdd : Odd (J.degree x) := by
    have ho := early_single_spoke_recipient_odd u q x B O hqu hxu hxB
      hxq.symm hxEven (fun e he => ⟨(havoid e he).2.2.1,(havoid e he).2.2.2.1⟩)
    have he : s(q,x) = s(x,q) := Sym2.eq_swap
    simp only [← SimpleGraph.ncard_neighborSet] at ho ⊢
    rw [he] at ho
    exact ho
  have hpOdd : Odd (J.degree p) := early_spoke_mates_leaf_odd u x q p B O hpB
    (hadj p hpB) (hleaves p hpB) (fun he => hxB (he ▸ hpB)) hpq
    (fun e he => ⟨(havoid e he).1,(havoid e he).2.1⟩)
  change #(evenNeighbors J q) = 0
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro t ht
  obtain ⟨hqt,htEven⟩ := (mem_evenNeighbors (G := J) q t).mp ht
  have hqtG : G.Adj q t := ((ordinaryMatePuncture_le O) hqt).1.1
  rcases hprofile t htEven with he | rfl
  · rcases hpair t hqtG he with rfl | rfl
    · exact (Nat.not_even_iff_odd.mpr hxOdd) htEven
    · exact (Nat.not_even_iff_odd.mpr hpOdd) htEven
  · exact hquMissing hqtG

/-- Complete subcubic even-degree cap and centre witness for the actual
single-spoke auxiliary. Retained even contacts can only be the protected
vertex after all ordinary mate endpoints have been made odd. -/
theorem bare_early_single_spoke_mates_cap
    (h x : V) (H : BareMinimalCounterexample G h x)
    (u q : V) (B : Finset V) (O : List (V × V))
    (hadj : ∀ t ∈ B, G.Adj u t) (hleaves : ∀ t ∈ B, Even (G.degree t))
    (hxB : x ∉ B) (hqB : q ∉ B) (hxu : x ≠ u) (hqu : q ≠ u)
    (hxq : G.Adj x q) (hqEven : Even (G.degree q))
    (hdis : O.Pairwise (fun e f =>
      e.1 ≠ f.1 ∧ e.1 ≠ f.2 ∧ e.2 ≠ f.1 ∧ e.2 ≠ f.2))
    (havoid : ∀ e ∈ O, e.1 ≠ u ∧ e.2 ≠ u ∧ e.1 ∉ B ∧ e.2 ∉ B ∧
      e.1 ≠ x ∧ e.2 ≠ x ∧ e.1 ≠ q ∧ e.2 ≠ q)
    (hedges : ∀ e ∈ O, G.Adj e.1 e.2 ∧
      Even (G.degree e.1) ∧ Even (G.degree e.2))
    (hcontacts : ∀ t, G.Adj u t → Even (G.degree t) →
      t ∈ B ∨ (∃ e ∈ O, t = e.1 ∨ t = e.2) ∨ t = x ∨ t = h) :
    let J := ordinaryMatePuncture ((starPuncture G u B).deleteEdges {s(x,q)}) O
    (∀ t, Even (J.degree t) → eDegree J t ≤ 3) ∧ eDegree J u ≤ 1 ∧
      Odd (J.degree x) := by
  classical
  let K := (starPuncture G u B).deleteEdges {s(x,q)}
  let J := ordinaryMatePuncture K O
  letI : DecidableRel K.Adj := fun _ _ => Classical.propDecidable _
  letI : DecidableRel J.Adj := fun _ _ => Classical.propDecidable _
  change (∀ t, Even (J.degree t) → eDegree J t ≤ 3) ∧ eDegree J u ≤ 1 ∧
    Odd (J.degree x)
  rcases H.counterexample.1 with ⟨_,_,_,_,hxEven,hhzero,hcap⟩
  have hprofile := early_single_spoke_even_profile u x q B O hleaves hxEven hqEven
    (fun e he => (hedges e he).2)
  have hxOdd : Odd (J.degree x) := by
    have ho := early_single_spoke_recipient_odd u q x B O hqu hxu hxB hxq.symm
      hxEven (fun e he => ⟨(havoid e he).2.2.2.2.1.symm,
        (havoid e he).2.2.2.2.2.1.symm⟩)
    have he : s(q,x) = s(x,q) := Sym2.eq_swap
    simp only [← SimpleGraph.ncard_neighborSet] at ho ⊢
    rw [he] at ho
    exact ho
  have hmOdd := early_spoke_mates_endpoints_odd u x q B O hdis havoid hedges
  have hsub : J ≤ G := fun _ _ ha => ((ordinaryMatePuncture_le (G := K) O) ha).1.1
  have huB : u ∉ B := fun ht => G.irrefl (hadj u ht)
  have hcentre : ∀ t, J.Adj u t → Even (J.degree t) → t = h := by
    intro t hut ht
    rcases hprofile t ht with he | rfl
    · rcases hcontacts t (hsub hut) he with htB | ⟨e,hem,hte⟩ | htx | hth
      · exact False.elim (starPuncture_missing G u B huB t htB
          ((ordinaryMatePuncture_le (G := K) O) hut).1)
      · obtain ⟨h1,h2⟩ := hmOdd e hem
        rcases hte with hte | hte
        · exact False.elim ((Nat.not_even_iff_odd.mpr h1) (hte ▸ ht))
        · exact False.elim ((Nat.not_even_iff_odd.mpr h2) (hte ▸ ht))
      · exact False.elim ((Nat.not_even_iff_odd.mpr hxOdd) (htx ▸ ht))
      · exact hth
    · exact False.elim (J.irrefl hut)
  have hc : ∀ t, Even (G.degree t) → t ≠ x → eDegree G t ≤ 3 := by
    intro t ht htx
    by_cases hth : t = h
    · subst t
      omega
    · exact hcap t ht hth htx
  refine ⟨puncture_cap_of_one_new_even_center h x u hsub hprofile hxOdd hhzero hc hcentre,
    ?_,hxOdd⟩
  change #(evenNeighbors J u) ≤ 1
  apply (Finset.card_le_card (show evenNeighbors J u ⊆ {h} from ?_)).trans_eq
    (Finset.card_singleton h)
  intro t ht
  obtain ⟨hut,htEven⟩ := (mem_evenNeighbors (G := J) u t).mp ht
  exact Finset.mem_singleton.mpr (hcentre t hut htEven)

end Gallai.TwoException
