/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.Structure.OneExceptionPieces
public import Gallai.Structure.CutVertexPieces
public import Gallai.Inputs.HangingESET
public import Gallai.Operations.SingleMerge

@[expose] public section

/-! # The designated-separator even/even induction case

Both pieces expose the separator twice by strict induction. Joining one pair
of terminal carriers saves one path and leaves two endpoints at the separator.
-/

namespace Gallai

universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

/-- Restore the endpoint conclusion across an even/even split at its designated
vertex. The decompositions are obtained by strict smaller-edge induction,
not supplied as certificates. -/
theorem one_exception_cut_even (A B : SimpleGraph V)
    [DecidableRel A.Adj] [DecidableRel B.Adj]
    (S T : Set V) [DecidablePred (· ∈ S)] [DecidablePred (· ∈ T)] (x : V)
    (hxS : x ∈ S) (hxT : x ∈ T)
    (hotherS : ∃ a ∈ S, a ≠ x) (hotherT : ∃ b ∈ T, b ≠ x)
    (hcover : S ∪ T = Set.univ) (hinter : S ∩ T = {x})
    (hA : A.support ⊆ S) (hB : B.support ⊆ T)
    (hconn : (A ⊔ B).Connected)
    (hxA : Even (A.degree x)) (hxB : Even (B.degree x))
    (hxEven : Even ((A ⊔ B).degree x))
    (hcap : ∀ v, Even ((A ⊔ B).degree v) → v ≠ x → eDegree (A ⊔ B) v ≤ 3)
    (hmin : ∀ (W : Type u) [Fintype W] [DecidableEq W]
      (J : SimpleGraph W) [DecidableRel J.Adj],
      J.edgeFinset.card < (A ⊔ B).edgeFinset.card → J.Connected →
      ∀ y : W, 0 < J.degree y → Even (J.degree y) →
        (∀ v, Even (J.degree v) → v ≠ y → eDegree J v ≤ 3) →
        ∃ D : Decomposition J, D.size ≤ (Fintype.card W + 1) / 2 ∧
          2 ≤ D.endpointCount y) :
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
  obtain ⟨wa, hwa⟩ := joint_neighbor_of_one_vertex_separation B A S x hcBA hxS hAm
    (fun a b hab ha => hj a ha (hBm a b hab)) hotherS
  obtain ⟨wb, hwb⟩ := joint_neighbor_of_one_vertex_separation A B T x hconn hxT hBm
    (fun a b hab ha => hj a (hAm a b hab) ha) hotherT
  have hltB := right_edge_count_lt_of_one_vertex_separation A B T x hBm
    (fun a b hab ha => hj a (hAm a b hab) ha) ⟨x, wa, hwa⟩
  have hltA : (A.induce S).edgeFinset.card < (A ⊔ B).edgeFinset.card := by
    have h := right_edge_count_lt_of_one_vertex_separation B A S x hAm
      (fun a b hab ha => hj a ha (hBm a b hab)) ⟨x, wb, hwb⟩
    simpa only [SimpleGraph.edgeFinset, ← Set.ncard_eq_toFinset_card', sup_comm] using h
  have capB := one_exception_cap_induced_right A B T x x hB hxEven hm hcap
  have capA := one_exception_cap_induced_right B A S x x hA
    (by simpa only [SimpleGraph.degree, SimpleGraph.neighborFinset,
      ← Set.ncard_eq_toFinset_card', sup_comm] using hxEven)
    (fun w hb ha => hm w ha hb)
    (by simpa only [SimpleGraph.degree, SimpleGraph.neighborFinset,
      ← Set.ncard_eq_toFinset_card', sup_comm] using hcap)
  obtain ⟨D0, hD0, hxD0⟩ := hmin S (A.induce S) hltA hcA ⟨x, hxS⟩
    (by rw [SimpleGraph.degree_induce_of_support_subset hA]; exact hwa.degree_pos_left)
    (by rwa [SimpleGraph.degree_induce_of_support_subset hA])
    (fun v hv hvx => capA v hv (fun h => hvx (Subtype.ext h)))
  obtain ⟨E0, hE0, hxE0⟩ := hmin T (B.induce T) hltB hcB ⟨x, hxT⟩
    (by rw [SimpleGraph.degree_induce_of_support_subset hB]; exact hwb.degree_pos_left)
    (by rwa [SimpleGraph.degree_induce_of_support_subset hB])
    (fun v hv hvx => capB v hv (fun h => hvx (Subtype.ext h)))
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
  have hd : 2 ≤ D.endpointCount x := by omega
  have he : 2 ≤ E.endpointCount x := by omega
  obtain ⟨F, hs, hv⟩ := D.single_merge_endpoints E x (by omega) (by omega) hm
  have hn := card_cover_single_inter S T x hcover hinter
  have hbgt := ceiling_one_vertex_budget (Fintype.card S) (Fintype.card T)
    (Fintype.card V) hn
  refine ⟨F, by omega, ?_⟩
  have h : F.endpointCount x + 2 = D.endpointCount x + E.endpointCount x := by
    simpa using hv x
  omega

end Gallai
