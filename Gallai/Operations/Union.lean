/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.Operations.EraseCarrier
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Fintype.BigOperators

@[expose] public section

/-! # Exact union of edge-disjoint decomposition families -/

namespace Gallai.Decomposition

universe u
variable {V : Type u} {G H : SimpleGraph V}

private def unionFamily (D : Decomposition G) (E : Decomposition H) :
    Fin D.size ⊕ Fin E.size → NonemptyPath (G ⊔ H)
  | Sum.inl i => (D.path i).transfer _ (fun _ he =>
      SimpleGraph.edgeSet_mono le_sup_left ((D.path i).walk.edges_subset_edgeSet he))
  | Sum.inr i => (E.path i).transfer _ (fun _ he =>
      SimpleGraph.edgeSet_mono le_sup_right ((E.path i).walk.edges_subset_edgeSet he))

/-- Edge-disjoint families have additive path counts and endpoint multiplicities. -/
theorem union_disjoint_endpoints [DecidableEq V] (D : Decomposition G) (E : Decomposition H)
    (hdis : Disjoint G.edgeSet H.edgeSet) :
    ∃ F : Decomposition (G ⊔ H), F.size = D.size + E.size ∧
      ∀ w, F.endpointCount w = D.endpointCount w + E.endpointCount w := by
  classical
  have hcover : ∀ e ∈ (G ⊔ H).edgeSet, ∃! j, e ∈ (unionFamily D E j).walk.edges := by
    intro e he
    rw [SimpleGraph.edgeSet_sup] at he
    rcases he with hg | hh
    · obtain ⟨i, hi, hu⟩ := D.covers e hg
      refine ⟨Sum.inl i, by simpa [unionFamily] using hi, ?_⟩
      intro j hj
      cases j with
      | inl j => exact congrArg Sum.inl (hu j (by simpa [unionFamily] using hj))
      | inr j =>
        have he' : e ∈ (E.path j).walk.edges := by simpa [unionFamily] using hj
        exact (Set.disjoint_left.mp hdis hg ((E.path j).walk.edges_subset_edgeSet he')).elim
    · obtain ⟨i, hi, hu⟩ := E.covers e hh
      refine ⟨Sum.inr i, by simpa [unionFamily] using hi, ?_⟩
      intro j hj
      cases j with
      | inr j => exact congrArg Sum.inr (hu j (by simpa [unionFamily] using hj))
      | inl j =>
        have he' : e ∈ (D.path j).walk.edges := by simpa [unionFamily] using hj
        exact (Set.disjoint_left.mp hdis ((D.path j).walk.edges_subset_edgeSet he') hh).elim
  refine ⟨ofFamily (unionFamily D E) hcover, by simp, ?_⟩
  intro w
  rw [ofFamily_endpointCount, Fintype.sum_sum_type]
  rfl

/-- Edge-disjoint decompositions combine with exactly additive path count. -/
theorem union_disjoint (D : Decomposition G) (E : Decomposition H)
    (hdis : Disjoint G.edgeSet H.edgeSet) :
    ∃ F : Decomposition (G ⊔ H), F.size = D.size + E.size := by
  classical
  obtain ⟨F, hs, _⟩ := D.union_disjoint_endpoints E hdis
  exact ⟨F, hs⟩

/-- Replace one remainder carrier by a decomposition of it together with an
edge-disjoint attached graph. Untouched carriers are retained exactly once. -/
theorem replace_carrier_union {K : SimpleGraph V} (D : Decomposition G)
    (i : Fin D.size) (E : Decomposition H)
    (hedges : ∀ e, e ∈ H.edgeSet ↔ e ∈ K.edgeSet ∨ e ∈ (D.path i).walk.edges)
    (hdis : Disjoint K.edgeSet G.edgeSet) :
    ∃ F : Decomposition (K ⊔ G), F.size = E.size + D.size - 1 := by
  classical
  let R := G.deleteEdges {e | e ∈ (D.path i).walk.edges}
  have hdr : Disjoint H.edgeSet R.edgeSet := by
    apply Set.disjoint_left.mpr
    intro e he hr
    have hr' : e ∈ G.edgeSet ∧ e ∉ (D.path i).walk.edges := by
      simpa [R, SimpleGraph.edgeSet_deleteEdges] using hr
    rcases (hedges e).mp he with hk | hp
    · exact Set.disjoint_left.mp hdis hk hr'.1
    · exact hr'.2 hp
  obtain ⟨F, hs⟩ := E.union_disjoint (D.eraseCarrier i) hdr
  have hgraph : H ⊔ R = K ⊔ G := by
    apply SimpleGraph.edgeSet_injective
    ext e
    simp only [SimpleGraph.edgeSet_sup, Set.mem_union]
    rw [hedges]
    have hr : e ∈ R.edgeSet ↔ e ∈ G.edgeSet ∧ e ∉ (D.path i).walk.edges := by
      simp [R, SimpleGraph.edgeSet_deleteEdges]
    rw [hr]
    have hp : e ∈ (D.path i).walk.edges → e ∈ G.edgeSet :=
      fun he => (D.path i).walk.edges_subset_edgeSet he
    tauto
  have hs' : F.size = E.size + D.size - 1 := by
    rw [eraseCarrier_size] at hs
    have hi := i.isLt
    omega
  have castSize {L M : SimpleGraph V} (h : L = M) (B : Decomposition L) :
      (h ▸ B).size = B.size := by subst M; rfl
  exact ⟨hgraph ▸ F, (castSize hgraph F).trans hs'⟩

/-- Replace a carrier by an exact endpoint-preserving reconstruction of that
carrier together with an edge-disjoint attached graph.  Unlike the count-only
consumer above, this interface retains every endpoint multiplicity of the
original decomposition. -/
theorem replace_carrier_union_endpoints [DecidableEq V] {K : SimpleGraph V} (D : Decomposition G)
    (i : Fin D.size) (E : Decomposition H)
    (hedges : ∀ e, e ∈ H.edgeSet ↔ e ∈ K.edgeSet ∨ e ∈ (D.path i).walk.edges)
    (hdis : Disjoint K.edgeSet G.edgeSet)
    (hend : ∀ w, E.endpointCount w =
      (if (D.path i).start = w then 1 else 0) +
        (if (D.path i).finish = w then 1 else 0)) :
    ∃ F : Decomposition (K ⊔ G), F.size = E.size + D.size - 1 ∧
      ∀ w, F.endpointCount w = D.endpointCount w := by
  classical
  let R := G.deleteEdges {e | e ∈ (D.path i).walk.edges}
  have hdr : Disjoint H.edgeSet R.edgeSet := by
    apply Set.disjoint_left.mpr
    intro e he hr
    have hr' : e ∈ G.edgeSet ∧ e ∉ (D.path i).walk.edges := by
      simpa [R, SimpleGraph.edgeSet_deleteEdges] using hr
    rcases (hedges e).mp he with hk | hp
    · exact Set.disjoint_left.mp hdis hk hr'.1
    · exact hr'.2 hp
  obtain ⟨F, hs, hends⟩ := E.union_disjoint_endpoints (D.eraseCarrier i) hdr
  have hgraph : H ⊔ R = K ⊔ G := by
    apply SimpleGraph.edgeSet_injective
    ext e
    simp only [SimpleGraph.edgeSet_sup, Set.mem_union]
    rw [hedges]
    have hr : e ∈ R.edgeSet ↔ e ∈ G.edgeSet ∧ e ∉ (D.path i).walk.edges := by
      simp [R, SimpleGraph.edgeSet_deleteEdges]
    rw [hr]
    have hp : e ∈ (D.path i).walk.edges → e ∈ G.edgeSet :=
      fun he => (D.path i).walk.edges_subset_edgeSet he
    tauto
  have hs' : F.size = E.size + D.size - 1 := by
    rw [eraseCarrier_size] at hs
    have hi := i.isLt
    omega
  have castSize {L M : SimpleGraph V} (h : L = M) (P : Decomposition L) :
      (h ▸ P).size = P.size := by subst M; rfl
  have castEnds {L M : SimpleGraph V} (h : L = M) (P : Decomposition L) (w : V) :
      (h ▸ P).endpointCount w = P.endpointCount w := by subst M; rfl
  refine ⟨hgraph ▸ F, (castSize hgraph F).trans hs', ?_⟩
  intro w
  rw [castEnds hgraph F w, hends]
  have herase := D.eraseCarrier_endpointCount i w
  rw [hend w]
  omega

/-- The one-vertex form of endpoint-preserving carrier replacement.  It is
the useful form when an attached configuration is known to preserve just a
designated endpoint reserve rather than the whole endpoint vector. -/
theorem replace_carrier_union_endpoint [DecidableEq V] {K : SimpleGraph V}
    (D : Decomposition G) (i : Fin D.size) (E : Decomposition H)
    (hedges : ∀ e, e ∈ H.edgeSet ↔ e ∈ K.edgeSet ∨ e ∈ (D.path i).walk.edges)
    (hdis : Disjoint K.edgeSet G.edgeSet) (w : V)
    (hend : E.endpointCount w =
      (if (D.path i).start = w then 1 else 0) +
        (if (D.path i).finish = w then 1 else 0)) :
    ∃ F : Decomposition (K ⊔ G), F.size = E.size + D.size - 1 ∧
      F.endpointCount w = D.endpointCount w := by
  classical
  let R := G.deleteEdges {e | e ∈ (D.path i).walk.edges}
  have hdr : Disjoint H.edgeSet R.edgeSet := by
    apply Set.disjoint_left.mpr
    intro e he hr
    have hr' : e ∈ G.edgeSet ∧ e ∉ (D.path i).walk.edges := by
      simpa [R, SimpleGraph.edgeSet_deleteEdges] using hr
    rcases (hedges e).mp he with hk | hp
    · exact Set.disjoint_left.mp hdis hk hr'.1
    · exact hr'.2 hp
  obtain ⟨F, hs, hends⟩ := E.union_disjoint_endpoints (D.eraseCarrier i) hdr
  have hgraph : H ⊔ R = K ⊔ G := by
    apply SimpleGraph.edgeSet_injective
    ext e
    simp only [SimpleGraph.edgeSet_sup, Set.mem_union]
    rw [hedges]
    have hr : e ∈ R.edgeSet ↔ e ∈ G.edgeSet ∧ e ∉ (D.path i).walk.edges := by
      simp [R, SimpleGraph.edgeSet_deleteEdges]
    rw [hr]
    have hp : e ∈ (D.path i).walk.edges → e ∈ G.edgeSet :=
      fun he => (D.path i).walk.edges_subset_edgeSet he
    tauto
  have hs' : F.size = E.size + D.size - 1 := by
    rw [eraseCarrier_size] at hs
    have hi := i.isLt
    omega
  have castSize {L M : SimpleGraph V} (h : L = M) (P : Decomposition L) :
      (h ▸ P).size = P.size := by subst M; rfl
  have castEnd {L M : SimpleGraph V} (h : L = M) (P : Decomposition L) :
      (h ▸ P).endpointCount w = P.endpointCount w := by subst M; rfl
  refine ⟨hgraph ▸ F, (castSize hgraph F).trans hs', ?_⟩
  rw [castEnd hgraph F, hends, hend]
  have herase := D.eraseCarrier_endpointCount i w
  omega

end Gallai.Decomposition
