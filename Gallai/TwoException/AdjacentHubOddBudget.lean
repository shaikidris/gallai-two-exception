/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.AdjacentHubOddInvariants

@[expose] public section

/-! # Edge budgets for Xie's odd/odd hub-cut pendant auxiliaries -/

namespace Gallai.TwoException

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- Attaching a fresh pendant edge increases the finite edge count by exactly
one.  This is the arithmetic payment used only in Xie's non-singleton
hub-cut branch. -/
theorem pendantExtension_edgeFinset_card
    (G : SimpleGraph V) [DecidableRel G.Adj] (h : V) :
    (pendantExtension G h).edgeFinset.card = G.edgeFinset.card + 1 := by
  unfold pendantExtension
  rw [SimpleGraph.card_edgeFinset_sup_edge]
  · rw [SimpleGraph.card_edgeFinset_map]
  · simp [SimpleGraph.map_adj]
  · exact Sum.inl_ne_inr

/-- In the non-singleton branch, two edge-disjoint opposite-piece edges pay
for the one fresh pendant edge. -/
theorem pendantExtension_edgeFinset_lt_union_of_two_edges
    (A B : SimpleGraph V) [DecidableRel A.Adj] [DecidableRel B.Adj]
    (h : V) (hdis : Disjoint A B) (hA : 2 ≤ A.edgeFinset.card) :
    (pendantExtension B h).edgeFinset.card < (A ⊔ B).edgeFinset.card := by
  rw [pendantExtension_edgeFinset_card, SimpleGraph.edgeFinset_sup,
    Finset.card_union_of_disjoint]
  · omega
  · exact SimpleGraph.disjoint_edgeFinset.mpr hdis

/-- Two graph pieces supported on vertex sets meeting only at `h` cannot share
an edge: a shared edge would force a forbidden loop at `h`. -/
theorem disjoint_of_support_inter_singleton
    (A B : SimpleGraph V) (S T : Set V) (h : V)
    (hA : A.support ⊆ S) (hB : B.support ⊆ T)
    (hinter : S ∩ T = {h}) : Disjoint A B := by
  rw [SimpleGraph.disjoint_left]
  intro a b habA habB
  have ha : a ∈ S ∩ T := ⟨hA ⟨b, habA⟩, hB ⟨b, habB⟩⟩
  have hb : b ∈ S ∩ T := ⟨hA ⟨a, habA.symm⟩, hB ⟨a, habB.symm⟩⟩
  have eqa : a = h := by simpa only [hinter, Set.mem_singleton_iff] using ha
  have eqb : b = h := by simpa only [hinter, Set.mem_singleton_iff] using hb
  subst a
  subst b
  exact A.irrefl habA

/-- The strict pendant decrease in the non-singleton source branch, stated
directly from the literal one-vertex cut-piece support data. -/
theorem pendantExtension_edgeFinset_lt_union_of_cut_piece
    (A B : SimpleGraph V) [DecidableRel A.Adj] [DecidableRel B.Adj]
    (S T : Set V) (h : V) (hA : A.support ⊆ S) (hB : B.support ⊆ T)
    (hinter : S ∩ T = {h}) (hAcount : 2 ≤ A.edgeFinset.card) :
    (pendantExtension B h).edgeFinset.card < (A ⊔ B).edgeFinset.card := by
  exact pendantExtension_edgeFinset_lt_union_of_two_edges A B h
    (disjoint_of_support_inter_singleton A B S T h hA hB hinter) hAcount

/-- The exact cross-type minimality invocation in Xie's non-singleton odd/odd
hub-cut branch.  The source-specific work left to its consumer is only to
produce the literal cut-piece support data, the two-edge opposite piece, and
the native adjacent pendant instance. -/
theorem adjacent_pendant_conclusion_of_cut_budget
    (A B : SimpleGraph V) [DecidableRel A.Adj] [DecidableRel B.Adj]
    (h y : V) [DecidableRel (pendantExtension A h).Adj] (S T : Set V)
    (M : AdjacentEdgeMinimalCounterexample (A ⊔ B) h y)
    (hA : A.support ⊆ S) (hB : B.support ⊆ T)
    (hinter : S ∩ T = {h}) (hBcount : 2 ≤ B.edgeFinset.card)
    (hpendant : AdjacentInstance (pendantExtension A h) (.inl h) (.inl y)) :
    AdjacentConclusion (pendantExtension A h) (.inl h) (.inl y) := by
  have hsmallBA : (pendantExtension A h).edgeFinset.card <
      (B ⊔ A).edgeFinset.card :=
    pendantExtension_edgeFinset_lt_union_of_cut_piece B A T S h hB hA
      (by simpa only [Set.inter_comm] using hinter) hBcount
  have hsmall : (pendantExtension A h).edgeFinset.card <
      (A ⊔ B).edgeFinset.card := by
    simpa only [SimpleGraph.edgeFinset, ← Set.ncard_eq_toFinset_card', sup_comm] using hsmallBA
  let finPSup : Fintype (pendantExtension A h).edgeSet :=
    (SimpleGraph.map (Function.Embedding.inl : V ↪ V ⊕ Unit) A).fintypeEdgeSetSup
      (SimpleGraph.edge (.inl h : V ⊕ Unit) (.inr ()))
  let finUSup : Fintype (A ⊔ B).edgeSet := A.fintypeEdgeSetSup B
  apply M.2 (V ⊕ Unit) (pendantExtension A h) (.inl h) (.inl y) ?_ hpendant
  calc
    _ = @Fintype.card (pendantExtension A h).edgeSet
        (pendantExtension A h).fintypeEdgeSet :=
      @SimpleGraph.edgeFinset_card _ (pendantExtension A h)
        (pendantExtension A h).fintypeEdgeSet
    _ = @Fintype.card (pendantExtension A h).edgeSet finPSup :=
      @Fintype.card_congr _ _ (pendantExtension A h).fintypeEdgeSet finPSup (Equiv.refl _)
    _ = (@SimpleGraph.edgeFinset _ (pendantExtension A h) finPSup).card :=
      (@SimpleGraph.edgeFinset_card _ (pendantExtension A h) finPSup).symm
    _ < (@SimpleGraph.edgeFinset _ (A ⊔ B) finUSup).card := by
      simpa only [finPSup, finUSup] using hsmall
    _ = @Fintype.card (A ⊔ B).edgeSet finUSup :=
      @SimpleGraph.edgeFinset_card _ (A ⊔ B) finUSup
    _ = @Fintype.card (A ⊔ B).edgeSet (A ⊔ B).fintypeEdgeSet :=
      @Fintype.card_congr _ _ finUSup (A ⊔ B).fintypeEdgeSet (Equiv.refl _)
    _ = _ := (@SimpleGraph.edgeFinset_card _ (A ⊔ B)
      (A ⊔ B).fintypeEdgeSet).symm

end Gallai.TwoException
