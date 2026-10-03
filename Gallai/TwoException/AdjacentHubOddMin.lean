/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.AdjacentHubOddBudget

@[expose] public section

/-! # Native cut-piece budget for Xie's odd/odd hub-cut branch -/

namespace Gallai.TwoException

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- Xie's fresh-leaf auxiliary is built on the connected induced cut piece,
not on its ambient spanning graph (which has isolated vertices off the cut
side).  If the opposite cut piece has at least two edges, the native pendant
auxiliary is strictly edge-smaller than the original graph. -/
theorem pendantExtension_induce_edgeFinset_lt_of_cut_piece
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (S T : Set V) [DecidablePred (· ∈ S)] [DecidablePred (· ∈ T)]
    [iS : Fintype ↥S] [iT : Fintype ↥T]
    (h : V) (hhS : h ∈ S)
    (hgraph : (G.induce S).spanningCoe ⊔ (G.induce T).spanningCoe = G)
    (hSsupport : ((G.induce S).spanningCoe).support ⊆ S)
    (hTsupport : ((G.induce T).spanningCoe).support ⊆ T)
    (hinter : S ∩ T = {h})
    (hTcount : 2 ≤ (G.induce T).edgeFinset.card) :
    (pendantExtension (G.induce S) ⟨h, hhS⟩).edgeFinset.card <
      G.edgeFinset.card := by
  classical
  let A : SimpleGraph V := (G.induce S).spanningCoe
  let B : SimpleGraph V := (G.induce T).spanningCoe
  have hdis : Disjoint A B :=
    disjoint_of_support_inter_singleton A B S T h
      (by simpa only [A] using hSsupport) (by simpa only [B] using hTsupport) hinter
  have hAB : A ⊔ B = G := by
    simpa only [A, B] using hgraph
  have hAc : A.edgeFinset.card = (G.induce S).edgeFinset.card := by
    set_option maxHeartbeats 800000 in
      exact @SimpleGraph.card_edgeFinset_map (Subtype S) iS V inferInstance inferInstance
        (Function.Embedding.subtype S) (G.induce S) _
  have hBc : B.edgeFinset.card = (G.induce T).edgeFinset.card := by
    set_option maxHeartbeats 800000 in
      exact @SimpleGraph.card_edgeFinset_map (Subtype T) iT V inferInstance inferInstance
        (Function.Embedding.subtype T) (G.induce T) _
  rw [pendantExtension_edgeFinset_card]
  rw [← hBc] at hTcount
  rw [← hAc]
  calc
    A.edgeFinset.card + 1 < (A ⊔ B).edgeFinset.card := by
      rw [SimpleGraph.edgeFinset_sup, Finset.card_union_of_disjoint
        (SimpleGraph.disjoint_edgeFinset.mpr hdis)]
      omega
    _ = G.edgeFinset.card := by
      simp only [SimpleGraph.edgeFinset, ← Set.ncard_eq_toFinset_card', hAB]

end Gallai.TwoException
