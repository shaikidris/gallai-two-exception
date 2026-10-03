/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.Operations.AbsorbPath
public import Gallai.Operations.Union

@[expose] public section

/-! # Full-family gluing at a twice-exposed separator

An arbitrary carrier on the second side can be cut at the separator and
absorbed on the first side. The remaining second-side carriers are then
restored unchanged. This includes terminal cuts and single-edge carriers.
-/

namespace Gallai.Decomposition

variable {V : Type*} [DecidableEq V] {G H : SimpleGraph V}

/-- Absorb any carrier through a twice-exposed separator, retaining the rest
of both families. Exactly one path and two separator endpoints are saved. -/
theorem absorb_carrier_union_endpoints (D : Decomposition G) (E : Decomposition H)
    (v : V) (i : Fin E.size) (hv : v ∈ (E.path i).walk.support)
    (hreserve : 2 ≤ D.endpointCount v)
    (hmeet : ∀ w, (∃ a, G.Adj w a) → (∃ b, H.Adj w b) → w = v) :
    ∃ F : Decomposition (G ⊔ H), F.size + 1 = D.size + E.size ∧
      ∀ w, F.endpointCount w + 2 * (if v = w then 1 else 0) =
        D.endpointCount w + E.endpointCount w := by
  classical
  let P := E.path i
  let J := G ⊔ P.walk.toSubgraph.spanningCoe
  let R := H.deleteEdges {e | e ∈ P.walk.edges}
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
  have hJ (e : Sym2 V) : e ∈ J.edgeSet ↔ e ∈ G.edgeSet ∨ e ∈ P.walk.edges := by
    simp only [J, SimpleGraph.edgeSet_sup, Set.mem_union,
      SimpleGraph.Subgraph.edgeSet_spanningCoe, SimpleGraph.Walk.mem_edges_toSubgraph]
  let P' := P.transfer J (fun e he => (hJ e).mpr (Or.inr he))
  obtain ⟨B, hsB, heB⟩ := D.absorb_attached_path_endpoints P' v
    (by simpa [P'] using hv) hreserve le_sup_left
    (by intro e; simpa [P'] using hJ e)
    (by
      intro e he hg
      have heP : e ∈ P.walk.edges := by simpa [P'] using he
      exact Set.disjoint_left.mp hd hg (P.walk.edges_subset_edgeSet heP))
    (by
      intro w hw hn a ha
      have hwP : w ∈ P.walk.support := by simpa [P'] using hw
      obtain ⟨b, _, hb⟩ := SimpleGraph.adj_of_mem_walk_support P.walk P.nonempty hwP
      exact hn (hmeet w ⟨a, ha⟩ ⟨b, hb⟩))
  have hJR : Disjoint J.edgeSet R.edgeSet := by
    apply Set.disjoint_left.mpr
    intro e hj hr
    have hr' : e ∈ H.edgeSet ∧ e ∉ P.walk.edges := by
      simpa [R, SimpleGraph.edgeSet_deleteEdges] using hr
    rcases (hJ e).mp hj with hg | hp
    · exact Set.disjoint_left.mp hd hg hr'.1
    · exact hr'.2 hp
  obtain ⟨F, hsF, heF⟩ := B.union_disjoint_endpoints (E.eraseCarrier i) hJR
  have hgraph : J ⊔ R = G ⊔ H := by
    apply SimpleGraph.edgeSet_injective
    ext e
    simp only [SimpleGraph.edgeSet_sup, Set.mem_union]
    rw [hJ]
    have hr : e ∈ R.edgeSet ↔ e ∈ H.edgeSet ∧ e ∉ P.walk.edges := by
      simp [R, SimpleGraph.edgeSet_deleteEdges]
    rw [hr]
    have hp := P.walk.edges_subset_edgeSet (e := e)
    tauto
  have hs : F.size + 1 = D.size + E.size := by
    have hsR := E.eraseCarrier_size i
    have hi := i.isLt
    omega
  have he (w : V) : F.endpointCount w + 2 * (if v = w then 1 else 0) =
      D.endpointCount w + E.endpointCount w := by
    have hb : B.endpointCount w + 2 * (if v = w then 1 else 0) =
        D.endpointCount w + (if (E.path i).start = w then 1 else 0) +
          (if (E.path i).finish = w then 1 else 0) := heB w
    have hr := E.eraseCarrier_endpointCount i w
    have hf := heF w
    omega
  have hout : ∃ F : Decomposition (J ⊔ R), F.size + 1 = D.size + E.size ∧
      ∀ w, F.endpointCount w + 2 * (if v = w then 1 else 0) =
        D.endpointCount w + E.endpointCount w := ⟨F, hs, he⟩
  rw [hgraph] at hout
  exact hout

/-- Select the second-side carrier from an actual incident edge. No endpoint
supply is needed on that side: the separator may be internal to every carrier. -/
theorem glue_at_exposed_vertex (D : Decomposition G) (E : Decomposition H)
    (v : V) (hreserve : 2 ≤ D.endpointCount v)
    (hincident : ∃ w, H.Adj v w)
    (hmeet : ∀ w, (∃ a, G.Adj w a) → (∃ b, H.Adj w b) → w = v) :
    ∃ F : Decomposition (G ⊔ H), F.size + 1 = D.size + E.size ∧
      ∀ w, F.endpointCount w + 2 * (if v = w then 1 else 0) =
        D.endpointCount w + E.endpointCount w := by
  obtain ⟨w, hw⟩ := hincident
  obtain ⟨i, hi, _⟩ := E.covers s(v, w) hw
  exact D.absorb_carrier_union_endpoints E v i
    ((E.path i).walk.fst_mem_support_of_mem_edges hi) hreserve hmeet

end Gallai.Decomposition
