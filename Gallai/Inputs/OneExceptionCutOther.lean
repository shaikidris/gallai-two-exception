/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.Structure.OneExceptionPieces
public import Gallai.Structure.CutVertexPieces
public import Gallai.Inputs.HangingESET
public import Gallai.Inputs.FloorOrSET
public import Gallai.Operations.SingleMerge
public import Gallai.Operations.AttachedMerge

@[expose] public section

/-! # The non-designated even-separator induction case

The induction hypothesis is quantified over genuinely smaller finite graphs.
This module consumes it on both actual pieces; it does not assume a gluing
certificate or either required endpoint reserve.
-/

namespace Gallai

universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
variable (A B : SimpleGraph V) [DecidableRel A.Adj] [DecidableRel B.Adj]

omit [Fintype V] in
private theorem lift_piece {H : SimpleGraph V} (S : Set V)
    (hs : H.support ⊆ S) (D : Decomposition (H.induce S)) :
    ∃ E : Decomposition H, E.size = D.size ∧
      ∀ w : S, E.endpointCount w.val = D.endpointCount w := by
  have hg : (H.induce S).map (Function.Embedding.subtype _) = H :=
    (H.spanningCoe_induce_eq_self S).mpr hs
  have hout : ∃ E : Decomposition ((H.induce S).map (Function.Embedding.subtype _)),
      E.size = D.size ∧ ∀ w : S, E.endpointCount w.val = D.endpointCount w :=
    ⟨D.map (Function.Embedding.subtype _), rfl,
      fun w => D.map_endpointCount (Function.Embedding.subtype _) w⟩
  rwa [hg] at hout

/-- A minimum counterexample cannot split at an even vertex other than its
designated exception. Both split-degree parities are handled; the smaller
one-exception theorem is used only at strict edge decreases. -/
theorem one_exception_cut_other_false (S T : Set V)
    [DecidablePred (· ∈ S)] [DecidablePred (· ∈ T)] (z x : V)
    (hzS : z ∈ S) (hzT : z ∈ T) (hxT : x ∈ T) (hxS : x ∉ S)
    (hother : ∃ a ∈ S, a ≠ z)
    (hcover : S ∪ T = Set.univ) (hinter : S ∩ T = {z})
    (hA : A.support ⊆ S) (hB : B.support ⊆ T)
    (hconn : (A ⊔ B).Connected)
    (hxEven : Even ((A ⊔ B).degree x)) (hzEven : Even ((A ⊔ B).degree z))
    (hcap : ∀ v, Even ((A ⊔ B).degree v) → v ≠ x → eDegree (A ⊔ B) v ≤ 3)
    (hnot : ¬ ∃ D : Decomposition (A ⊔ B),
      D.size ≤ (Fintype.card V + 1) / 2 ∧ 2 ≤ D.endpointCount x)
    (hmin : ∀ (W : Type u) [Fintype W] [DecidableEq W]
      (J : SimpleGraph W) [DecidableRel J.Adj],
      J.edgeFinset.card < (A ⊔ B).edgeFinset.card → J.Connected →
      ∀ y : W, 0 < J.degree y → Even (J.degree y) →
        (∀ v, Even (J.degree v) → v ≠ y → eDegree J v ≤ 3) →
        ∃ D : Decomposition J, D.size ≤ (Fintype.card W + 1) / 2 ∧
          2 ≤ D.endpointCount y) : False := by
  classical
  have hxz : x ≠ z := fun h => hxS (h ▸ hzS)
  have hj (v : V) (hs : v ∈ S) (ht : v ∈ T) : v = z := by
    have h : v ∈ S ∩ T := ⟨hs, ht⟩
    simpa only [hinter, Set.mem_singleton_iff] using h
  have hm : ∀ w, (∃ a, A.Adj w a) → (∃ b, B.Adj w b) → w = z :=
    fun w ha hb => hj w (hA ha) (hB hb)
  have hAm (a b : V) (h : A.Adj a b) : a ∈ S := hA ⟨b, h⟩
  have hBm (a b : V) (h : B.Adj a b) : a ∈ T := hB ⟨b, h⟩
  have hcB := connected_right_of_one_vertex_separation A B T z hconn hzT hBm
    (fun a b hab ha => hj a (hAm a b hab) ha)
  have hcBA : (B ⊔ A).Connected := by simpa only [sup_comm] using hconn
  have hcA := connected_right_of_one_vertex_separation B A S z hcBA hzS hAm
    (fun a b hab ha => hj a ha (hBm a b hab))
  obtain ⟨wa, hwa⟩ := joint_neighbor_of_one_vertex_separation B A S z hcBA hzS hAm
    (fun a b hab ha => hj a ha (hBm a b hab)) hother
  obtain ⟨wb, hwb⟩ := joint_neighbor_of_one_vertex_separation A B T z hconn hzT hBm
    (fun a b hab ha => hj a (hAm a b hab) ha) ⟨x, hxT, hxz⟩
  have hltB := right_edge_count_lt_of_one_vertex_separation A B T z hBm
    (fun a b hab ha => hj a (hAm a b hab) ha) ⟨z, wa, hwa⟩
  have hltA : (A.induce S).edgeFinset.card < (A ⊔ B).edgeFinset.card := by
    have h := right_edge_count_lt_of_one_vertex_separation B A S z hAm
      (fun a b hab ha => hj a ha (hBm a b hab)) ⟨z, wb, hwb⟩
    simpa only [SimpleGraph.edgeFinset, ← Set.ncard_eq_toFinset_card', sup_comm] using h
  have capB := one_exception_cap_induced_right A B T z x hB hzEven hm hcap
  have capA0 := one_exception_cap_right B A z x
    (by simpa only [SimpleGraph.degree, SimpleGraph.neighborFinset,
      ← Set.ncard_eq_toFinset_card', sup_comm] using hzEven)
    (fun w hb ha => hm w ha hb)
    (by simpa only [SimpleGraph.degree, SimpleGraph.neighborFinset,
      ← Set.ncard_eq_toFinset_card', sup_comm] using hcap)
  have capA (v : S) (hv : Even ((A.induce S).degree v)) :
      eDegree (A.induce S) v ≤ 3 := by
    rw [eDegree_induce_of_support_subset A S hA v]
    apply capA0 v.val ?_ (fun h => hxS (h ▸ v.property))
    rwa [SimpleGraph.degree_induce_of_support_subset hA v] at hv
  have hxdeg : (B.induce T).degree ⟨x, hxT⟩ = (A ⊔ B).degree x := by
    rw [SimpleGraph.degree_induce_of_support_subset hB]
    exact (degree_union_of_left_isolated A B x (fun w hw => hxS (hA ⟨w, hw⟩))).symm
  have : Nontrivial T := ⟨⟨⟨x, hxT⟩, ⟨z, hzT⟩, fun h => hxz (congrArg Subtype.val h)⟩⟩
  obtain ⟨E0, hE0, hxE0⟩ := hmin T (B.induce T) hltB hcB ⟨x, hxT⟩
    (hcB.preconnected.degree_pos_of_nontrivial _) (by rwa [hxdeg])
    (fun v hv hvx => capB v hv (fun h => hvx (Subtype.ext h)))
  obtain ⟨E, hEsize, hEends⟩ := lift_piece T hB E0
  have hE : E.size ≤ (Fintype.card T + 1) / 2 := by omega
  have hxE : 2 ≤ E.endpointCount x := by rw [hEends ⟨x, hxT⟩]; exact hxE0
  have hn := card_cover_single_inter S T z hcover hinter
  have hbgt := ceiling_one_vertex_budget (Fintype.card S) (Fintype.card T)
    (Fintype.card V) hn
  have finish (D : Decomposition A) (hD : D.size ≤ (Fintype.card S + 1) / 2)
      (F : Decomposition (A ⊔ B)) (hs : F.size + 1 = D.size + E.size)
      (he : ∀ w, F.endpointCount w + 2 * (if z = w then 1 else 0) =
        D.endpointCount w + E.endpointCount w) : False := by
    apply hnot
    refine ⟨F, by omega, ?_⟩
    have h := he x
    simp only [Ne.symm hxz, if_false, mul_zero, Nat.add_zero] at h
    omega
  by_cases hzA : Even (A.degree z)
  · have hzpos : 0 < (A.induce S).degree ⟨z, hzS⟩ := by
      rw [SimpleGraph.degree_induce_of_support_subset hA]
      exact hwa.degree_pos_left
    obtain ⟨D0, hD0, hzD0⟩ := hmin S (A.induce S) hltA hcA ⟨z, hzS⟩ hzpos
      (by rwa [SimpleGraph.degree_induce_of_support_subset hA]) (fun v hv _ => capA v hv)
    obtain ⟨D, hDsize, hDends⟩ := lift_piece S hA D0
    have hzD : 2 ≤ D.endpointCount z := by rw [hDends ⟨z, hzS⟩]; exact hzD0
    obtain ⟨F, hs, he⟩ := D.glue_at_exposed_vertex E z hzD ⟨wb, hwb⟩ hm
    exact finish D (by omega) F hs he
  · have hzAo : Odd (A.degree z) := Nat.not_even_iff_odd.mp hzA
    have hdis : Disjoint (A.neighborFinset z) (B.neighborFinset z) := by
      apply Finset.disjoint_left.mpr
      intro w ha hb
      have ha' := (A.mem_neighborFinset z w).mp ha
      have hb' := (B.mem_neighborFinset z w).mp hb
      exact ha'.ne (hm w ⟨z, ha'.symm⟩ ⟨z, hb'.symm⟩).symm
    have hdeg : (A ⊔ B).degree z = A.degree z + B.degree z := by
      rw [← SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.neighborFinset_sup,
        Finset.card_union_of_disjoint hdis]
      rfl
    have hzBo : Odd (B.degree z) := by
      rw [Nat.even_iff, hdeg] at hzEven
      rw [Nat.odd_iff] at hzAo ⊢
      omega
    have hleft : HasPathBudget (A.induce S) ((Fintype.card S + 1) / 2) := by
      rcases floor_or_set (A.induce S) hcA capA with ⟨D, hd⟩ | hset
      · exact ⟨D, by omega⟩
      · obtain ⟨D, hd, _⟩ := hset.endpoint_reserve ⟨z, hzS⟩
        exact ⟨D, hd⟩
    obtain ⟨D0, hD0⟩ := hleft
    obtain ⟨D, hDsize, _⟩ := lift_piece S hA D0
    obtain ⟨F, hs, he⟩ := D.single_merge_endpoints E z
      (D.endpointCount_pos_of_odd_degree z hzAo)
      (E.endpointCount_pos_of_odd_degree z hzBo) hm
    exact finish D (by omega) F hs he

end Gallai
