/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.Inputs.ESETAssembly
public import Gallai.Operations.DoubleMerge
public import Gallai.Structure.OneVertexUnion
public import Mathlib.Data.Set.Card

@[expose] public section

/-! # Reconstruction from a smaller floor-or-SET alternative

These are induction-step consumers, not the global floor-or-SET theorem.
All budgets count actual piece vertices rather than ambient isolates.
-/

namespace Gallai

universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

/-- Covering vertex subsets with a singleton overlap have the required order identity. -/
theorem card_cover_single_inter (S T : Set V) [DecidablePred (· ∈ S)]
    [DecidablePred (· ∈ T)] (z : V) (hc : S ∪ T = Set.univ)
    (hi : S ∩ T = {z}) :
    Fintype.card V + 1 = Fintype.card S + Fintype.card T := by
  have hf : S.toFinset ∩ T.toFinset = {z} := by
    ext v
    have hv := Set.ext_iff.mp hi v
    simpa using hv
  have hu : S.toFinset ∪ T.toFinset = Finset.univ := by
    ext v
    have hv := Set.ext_iff.mp hc v
    simpa using hv
  have h := card_union_of_single_inter S.toFinset T.toFinset z hf
  simpa only [hu, Finset.card_univ, Set.toFinset_card] using h

variable (A B : SimpleGraph V) [DecidableRel A.Adj] [DecidableRel B.Adj]

/-- A hanging ESET and a smaller floor-or-SET outcome reconstruct a floor budget.
The nonempty right joint supplies the carrier needed in the floor branch. -/
theorem hanging_eset_floor_of_alternative (S T : Set V)
    [DecidablePred (· ∈ S)] [DecidablePred (· ∈ T)]
    (z : V) (hzS : z ∈ S) (hzT : z ∈ T)
    (hc : S ∪ T = Set.univ) (hi : S ∩ T = {z})
    (hA : A.support ⊆ S) (hB : B.support ⊆ T)
    (he : IsESETAt (A.induce S) ⟨z, hzS⟩)
    (hp : ∃ t, B.Adj z t)
    (hr : HasPathBudget (B.induce T) (Fintype.card T / 2) ∨ IsSET (B.induce T)) :
    HasPathBudget (A ⊔ B) (Fintype.card V / 2) := by
  classical
  have ha : (A.induce S).map (Function.Embedding.subtype _) = A :=
    (A.spanningCoe_induce_eq_self S).mpr hA
  have hb : (B.induce T).map (Function.Embedding.subtype _) = B :=
    (B.spanningCoe_induce_eq_self T).mpr hB
  have hj : ∀ w, w ∈ S → w ∈ T → w = z := by
    intro w hs ht
    have hw : w ∈ S ∩ T := ⟨hs, ht⟩
    simpa only [hi, Set.mem_singleton_iff] using hw
  have hn := card_cover_single_inter S T z hc hi
  rcases hr with ⟨D, hD⟩ | hs
  · have hd : ∃ E : Decomposition B, E.size ≤ Fintype.card T / 2 := by
      have hm : ∃ E : Decomposition ((B.induce T).map
          (Function.Embedding.subtype _)), E.size ≤ Fintype.card T / 2 :=
        ⟨D.map (Function.Embedding.subtype _), hD⟩
      rw [hb] at hm
      exact hm
    obtain ⟨E, hE⟩ := hd
    obtain ⟨F, hF⟩ := he.absorb_hanging (Function.Embedding.subtype _) E hp (by
      intro w hw hrange
      obtain ⟨v, rfl⟩ := hrange
      exact hj v v.property (hB hw))
    have hout : HasPathBudget ((A.induce S).map (Function.Embedding.subtype _) ⊔ B)
        (Fintype.card V / 2) := ⟨F, hF.trans (by
      have := ceiling_floor_one_vertex_budget (Fintype.card S) (Fintype.card T)
        (Fintype.card V) hn
      omega)⟩
    simpa only [ha] using hout
  · have left : ∃ D : Decomposition A, D.size ≤ (Fintype.card S + 1) / 2 ∧
        2 ≤ D.endpointCount z := by
      obtain ⟨D, hD, hz⟩ := he.endpoint_reserve
      have hm : ∃ E : Decomposition ((A.induce S).map
          (Function.Embedding.subtype _)), E.size ≤ (Fintype.card S + 1) / 2 ∧
            2 ≤ E.endpointCount z :=
        ⟨D.map (Function.Embedding.subtype _), hD, by
          change 2 ≤ (D.map (Function.Embedding.subtype _)).endpointCount
            ((Function.Embedding.subtype _) ⟨z, hzS⟩)
          rw [Decomposition.map_endpointCount]
          exact hz⟩
      rw [ha] at hm
      exact hm
    have right : ∃ D : Decomposition B, D.size ≤ (Fintype.card T + 1) / 2 ∧
        2 ≤ D.endpointCount z := by
      obtain ⟨D, hD, hz⟩ := hs.endpoint_reserve ⟨z, hzT⟩
      have hm : ∃ E : Decomposition ((B.induce T).map
          (Function.Embedding.subtype _)), E.size ≤ (Fintype.card T + 1) / 2 ∧
            2 ≤ E.endpointCount z :=
        ⟨D.map (Function.Embedding.subtype _), hD, by
          change 2 ≤ (D.map (Function.Embedding.subtype _)).endpointCount
            ((Function.Embedding.subtype _) ⟨z, hzT⟩)
          rw [Decomposition.map_endpointCount]
          exact hz⟩
      rw [hb] at hm
      exact hm
    obtain ⟨D, hD, hzD⟩ := left
    obtain ⟨E, hE, hzE⟩ := right
    obtain ⟨F, hF⟩ := D.double_merge E z hzD hzE (by
      intro w hwA hwB
      exact hj w (hA hwA) (hB hwB))
    refine ⟨F, ?_⟩
    have := two_ceilings_one_vertex_budget (Fintype.card S) (Fintype.card T)
      (Fintype.card V) hn
    omega

end Gallai
