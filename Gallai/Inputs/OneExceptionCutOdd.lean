/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.Inputs.FloorOrSET
public import Gallai.Inputs.HangingESET
public import Gallai.Structure.OneExceptionPieces
public import Gallai.Structure.CutVertexPieces
public import Gallai.Operations.SingleMerge

@[expose] public section

/-! # Odd/odd designated cuts via floor-or-SET

Two floor-budget pieces need no join. Otherwise a SET piece supplies three
endpoints at the odd separator, so one join leaves the required two endpoints.
This avoids a pendant comparison and does not use a recursive premise.
-/

namespace Gallai

universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

/-- An odd designated vertex in a cap-three connected graph has either a
floor decomposition or a ceiling decomposition with at least three endpoints. -/
theorem odd_vertex_floor_or_three (G : SimpleGraph V) [DecidableRel G.Adj]
    (hconn : G.Connected) (hcap : ∀ v, Even (G.degree v) → eDegree G v ≤ 3)
    (x : V) (hx : Odd (G.degree x)) :
    ∃ D : Decomposition G, D.size ≤ (Fintype.card V + 1) / 2 ∧
      (D.size ≤ Fintype.card V / 2 ∨ 3 ≤ D.endpointCount x) := by
  rcases floor_or_set G hconn hcap with ⟨D, hd⟩ | hs
  · exact ⟨D, by omega, Or.inl hd⟩
  · obtain ⟨D, hd, he⟩ := hs.endpoint_reserve x
    exact ⟨D, hd, Or.inr (D.three_le_endpointCount_of_odd_degree x hx he)⟩

/-- An odd/odd split at the designated even vertex satisfies the ceiling bound
with two exposed endpoints. No smaller-graph induction hypothesis is required. -/
theorem one_exception_cut_odd (A B : SimpleGraph V)
    [DecidableRel A.Adj] [DecidableRel B.Adj]
    (S T : Set V) [DecidablePred (· ∈ S)] [DecidablePred (· ∈ T)] (x : V)
    (hxS : x ∈ S) (hxT : x ∈ T)
    (hcover : S ∪ T = Set.univ) (hinter : S ∩ T = {x})
    (hA : A.support ⊆ S) (hB : B.support ⊆ T)
    (hconn : (A ⊔ B).Connected)
    (hxA : Odd (A.degree x)) (hxB : Odd (B.degree x))
    (hxEven : Even ((A ⊔ B).degree x))
    (hcap : ∀ v, Even ((A ⊔ B).degree v) → v ≠ x → eDegree (A ⊔ B) v ≤ 3) :
    ∃ D : Decomposition (A ⊔ B),
      D.size ≤ (Fintype.card V + 1) / 2 ∧ 2 ≤ D.endpointCount x := by
  classical
  have hj (v : V) (hs : v ∈ S) (ht : v ∈ T) : v = x := by
    have h : v ∈ S ∩ T := ⟨hs, ht⟩
    simpa only [hinter, Set.mem_singleton_iff] using h
  have hm : ∀ w, (∃ a, A.Adj w a) → (∃ b, B.Adj w b) → w = x :=
    fun w ha hb => hj w (hA ha) (hB hb)
  have hAm (a b : V) (h : A.Adj a b) : a ∈ S := hA ⟨b, h⟩
  have hBm (a b : V) (h : B.Adj a b) : a ∈ T := hB ⟨b, h⟩
  have hcB := connected_right_of_one_vertex_separation A B T x hconn hxT hBm
    (fun a b hab ha => hj a (hAm a b hab) ha)
  have hcBA : (B ⊔ A).Connected := by simpa only [sup_comm] using hconn
  have hcA := connected_right_of_one_vertex_separation B A S x hcBA hxS hAm
    (fun a b hab ha => hj a ha (hBm a b hab))
  have capB := one_exception_cap_induced_right A B T x x hB hxEven hm hcap
  have capA := one_exception_cap_induced_right B A S x x hA
    (by simpa only [SimpleGraph.degree, SimpleGraph.neighborFinset,
      ← Set.ncard_eq_toFinset_card', sup_comm] using hxEven)
    (fun w hb ha => hm w ha hb)
    (by simpa only [SimpleGraph.degree, SimpleGraph.neighborFinset,
      ← Set.ncard_eq_toFinset_card', sup_comm] using hcap)
  have allA (v : S) (hv : Even ((A.induce S).degree v)) :
      eDegree (A.induce S) v ≤ 3 := by
    apply capA v hv
    intro heq
    rw [SimpleGraph.degree_induce_of_support_subset hA, heq] at hv
    exact (Nat.not_even_iff_odd.mpr hxA) hv
  have allB (v : T) (hv : Even ((B.induce T).degree v)) :
      eDegree (B.induce T) v ≤ 3 := by
    apply capB v hv
    intro heq
    rw [SimpleGraph.degree_induce_of_support_subset hB, heq] at hv
    exact (Nat.not_even_iff_odd.mpr hxB) hv
  obtain ⟨D0, hD0, hd0⟩ := odd_vertex_floor_or_three (A.induce S) hcA allA ⟨x, hxS⟩
    (by rwa [SimpleGraph.degree_induce_of_support_subset hA])
  obtain ⟨E0, hE0, he0⟩ := odd_vertex_floor_or_three (B.induce T) hcB allB ⟨x, hxT⟩
    (by rwa [SimpleGraph.degree_induce_of_support_subset hB])
  have lift {H : SimpleGraph V} (U : Set V) [DecidablePred (· ∈ U)]
      (hu : H.support ⊆ U) (hx : x ∈ U) (P : Decomposition (H.induce U)) :
      ∃ Q : Decomposition H, Q.size = P.size ∧
        Q.endpointCount x = P.endpointCount ⟨x, hx⟩ := by
    have hg : (H.induce U).map (Function.Embedding.subtype _) = H :=
      (H.spanningCoe_induce_eq_self U).mpr hu
    have hout : ∃ Q : Decomposition ((H.induce U).map (Function.Embedding.subtype _)),
        Q.size = P.size ∧ Q.endpointCount x = P.endpointCount ⟨x, hx⟩ :=
      ⟨P.map (Function.Embedding.subtype _), rfl,
        P.map_endpointCount (Function.Embedding.subtype _) ⟨x, hx⟩⟩
    rwa [hg] at hout
  obtain ⟨D, hsD, heD⟩ := lift S hA hxS D0
  obtain ⟨E, hsE, heE⟩ := lift T hB hxT E0
  have hdpos := D.endpointCount_pos_of_odd_degree x hxA
  have hepos := E.endpointCount_pos_of_odd_degree x hxB
  have hn := card_cover_single_inter S T x hcover hinter
  by_cases hf : D.size ≤ Fintype.card S / 2 ∧ E.size ≤ Fintype.card T / 2
  · have hdis : Disjoint A.edgeSet B.edgeSet := by
      apply Set.disjoint_left.mpr
      intro e
      induction e using Sym2.inductionOn with
      | hf a b =>
        intro ha hb
        have ha' : A.Adj a b := ha
        have hb' : B.Adj a b := hb
        exact ha'.ne ((hm a ⟨b, ha'⟩ ⟨b, hb'⟩).trans
          (hm b ⟨a, ha'.symm⟩ ⟨a, hb'.symm⟩).symm)
    obtain ⟨F, hs, he⟩ := D.union_disjoint_endpoints E hdis
    exact ⟨F, by omega, by rw [he x]; omega⟩
  · have hr : 3 ≤ D.endpointCount x ∨ 3 ≤ E.endpointCount x := by
      rcases hd0 with hd | hd <;> rcases he0 with he | he
      · omega
      · exact Or.inr (by omega)
      · exact Or.inl (by omega)
      · exact Or.inl (by omega)
    obtain ⟨F, hs, he⟩ := D.single_merge_endpoints E x hdpos hepos hm
    have hbgt := ceiling_one_vertex_budget (Fintype.card S) (Fintype.card T)
      (Fintype.card V) hn
    refine ⟨F, by omega, ?_⟩
    have h : F.endpointCount x + 2 = D.endpointCount x + E.endpointCount x := by
      simpa using he x
    omega

end Gallai
