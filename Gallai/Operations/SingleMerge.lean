/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.Operations.AbsorbPath
public import Gallai.Operations.Union
public import Gallai.Foundations.HubProfiles

@[expose] public section

/-! # Endpoint-preserving gluing across a single vertex

Joining one exposed carrier from each side saves one path and consumes exactly
two endpoints at the joint. This is the odd split-degree case in the
one-exception theorem's cut-vertex induction.
-/

namespace Gallai.Decomposition

variable {V : Type*} [DecidableEq V] {G H : SimpleGraph V}

/-- Positive endpoint count supplies an actual terminal carrier. -/
theorem exists_terminal_of_pos (D : Decomposition G) (v : V)
    (hv : 0 < D.endpointCount v) :
    ∃ i : Fin D.size, (D.path i).start = v ∨ (D.path i).finish = v := by
  have hc : 0 < (D.terminalCarriers v).card := by
    simpa only [D.card_terminalCarriers] using hv
  obtain ⟨i, hi⟩ := Finset.card_pos.mp hc
  exact ⟨i, (Finset.mem_filter.mp hi).2⟩

/-- One join across a single-vertex intersection saves exactly one path and
preserves every off-joint endpoint multiplicity. Both input carriers are
nonempty; single-edge carriers require no special convention. -/
theorem single_merge_endpoints (D : Decomposition G) (E : Decomposition H) (v : V)
    (hD : 0 < D.endpointCount v) (hE : 0 < E.endpointCount v)
    (hmeet : ∀ w, (∃ a, G.Adj w a) → (∃ b, H.Adj w b) → w = v) :
    ∃ F : Decomposition (G ⊔ H), F.size + 1 = D.size + E.size ∧
      ∀ w, F.endpointCount w + 2 * (if v = w then 1 else 0) =
        D.endpointCount w + E.endpointCount w := by
  classical
  obtain ⟨i, hi⟩ := E.exists_terminal_of_pos v hE
  let E' := E.orientToward v
  let Q := (E'.path i).reverse
  have hq : Q.start = v := E.orientToward_terminal v i hi
  let J := G ⊔ Q.walk.toSubgraph.spanningCoe
  let R := H.deleteEdges {e | e ∈ (E'.path i).walk.edges}
  have hd : Disjoint G.edgeSet H.edgeSet := by
    apply Set.disjoint_left.mpr
    intro e
    induction e using Sym2.inductionOn with
    | hf a b =>
      intro hg hh
      have ha : G.Adj a b := hg
      have hb : H.Adj a b := hh
      exact ha.ne ((hmeet a ⟨b, ha⟩ ⟨b, hb⟩).trans
        (hmeet b ⟨a, ha.symm⟩ ⟨a, hb.symm⟩).symm)
  have hJ (e : Sym2 V) : e ∈ J.edgeSet ↔ e ∈ G.edgeSet ∨ e ∈ Q.walk.edges := by
    simp only [J, SimpleGraph.edgeSet_sup, Set.mem_union,
      SimpleGraph.Subgraph.edgeSet_spanningCoe, SimpleGraph.Walk.mem_edges_toSubgraph]
  let Q' := Q.transfer J (fun e he => (hJ e).mpr (Or.inr he))
  obtain ⟨B, hsB, heB⟩ := D.absorb_path Q' le_sup_left
    (by simpa only [Q', NonemptyPath.transfer, hq] using hD)
    (by
      intro j w hw hq'
      have hwQ : w ∈ Q.walk.support := by simpa [Q'] using hq'
      obtain ⟨a, _, ha⟩ := SimpleGraph.adj_of_mem_walk_support
        (D.path j).walk (D.path j).nonempty hw
      obtain ⟨b, _, hb⟩ := SimpleGraph.adj_of_mem_walk_support Q.walk Q.nonempty hwQ
      exact (hmeet w ⟨a, ha⟩ ⟨b, hb⟩).trans hq.symm)
    (by intro e; simpa [Q'] using hJ e)
    (by
      intro e he hg
      have heQ : e ∈ Q.walk.edges := by simpa [Q'] using he
      exact Set.disjoint_left.mp hd hg (Q.walk.edges_subset_edgeSet heQ))
  have hJR : Disjoint J.edgeSet R.edgeSet := by
    apply Set.disjoint_left.mpr
    intro e hj hr
    have hr' : e ∈ H.edgeSet ∧ e ∉ (E'.path i).walk.edges := by
      simpa [R, SimpleGraph.edgeSet_deleteEdges] using hr
    rcases (hJ e).mp hj with hg | hq'
    · exact Set.disjoint_left.mp hd hg hr'.1
    · exact hr'.2 (by simpa [Q] using hq')
  obtain ⟨F, hsF, heF⟩ := B.union_disjoint_endpoints (E'.eraseCarrier i) hJR
  have hgraph : J ⊔ R = G ⊔ H := by
    apply SimpleGraph.edgeSet_injective
    ext e
    simp only [SimpleGraph.edgeSet_sup, Set.mem_union]
    rw [hJ]
    have hr : e ∈ R.edgeSet ↔ e ∈ H.edgeSet ∧ e ∉ Q.walk.edges := by
      simp [R, SimpleGraph.edgeSet_deleteEdges, Q]
    rw [hr]
    have hp := Q.walk.edges_subset_edgeSet (e := e)
    tauto
  have hs : F.size + 1 = D.size + E.size := by
    have hsR : (E'.eraseCarrier i).size = E.size - 1 := E'.eraseCarrier_size i
    have hi' := i.isLt
    omega
  have he (w : V) : F.endpointCount w + 2 * (if v = w then 1 else 0) =
      D.endpointCount w + E.endpointCount w := by
    have hb := heB w
    have hr := E'.eraseCarrier_endpointCount i w
    have hf := heF w
    have hend : (E'.path i).finish = v := hq
    simp only [Q', NonemptyPath.transfer, Q, NonemptyPath.reverse, hend] at hb
    simp only [hend] at hr
    have heE : E'.endpointCount w = E.endpointCount w :=
      E.orientToward_endpointCount v w
    omega
  have hout : ∃ F : Decomposition (J ⊔ R), F.size + 1 = D.size + E.size ∧
      ∀ w, F.endpointCount w + 2 * (if v = w then 1 else 0) =
        D.endpointCount w + E.endpointCount w := ⟨F, hs, he⟩
  rw [hgraph] at hout
  exact hout

end Gallai.Decomposition
