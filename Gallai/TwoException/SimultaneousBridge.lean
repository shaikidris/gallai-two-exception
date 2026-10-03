/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.BridgePartition
public import Gallai.Inputs.FloorOrSET
public import Gallai.Inputs.SETReserve
public import Gallai.Operations.AddEdge
public import Gallai.Operations.InsertEdge
public import Gallai.Operations.SingleMerge
public import Gallai.Operations.Union

@[expose] public section

/-! # The floor--floor bridge assembly

This is the constructive terminal branch for the deleted-bridge case.  Once
the two puncture components have floor-budget decompositions, their
edge-disjoint union followed by the bridge as a singleton path exposes both
bridge ends with one additional carrier.
-/

namespace Gallai.TwoException

universe u

variable {V : Type u} [DecidableEq V]
variable {J K : SimpleGraph V}

/-- Each actual connected component of a graph inherits its ambient
even-degree cap, so the floor-or-SET theorem applies directly to its subtype
graph. -/
theorem floor_or_set_component [Fintype V] [DecidableRel J.Adj]
    (C : J.ConnectedComponent)
    (hcap : ∀ v, Even (J.degree v) → eDegree J v ≤ 3) :
    HasPathBudget (J.induce C.supp) (Fintype.card C.supp / 2) ∨
      IsSET (J.induce C.supp) := by
  classical
  apply floor_or_set (J.induce C.supp) C.connected_toSimpleGraph
  have hclosed : ∀ v ∈ C.supp, J.neighborSet v ⊆ C.supp := by
    intro v hv w hw
    exact C.mem_supp_of_adj_mem_supp hv hw
  exact even_degree_cap_induce_of_closed J C.supp hclosed 3 hcap

/-- Deleting an edge joining two even designated vertices introduces no new
even vertices, and the subcubic E-degree cap therefore survives. -/
theorem delete_even_edge_cap [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]
    (h x : V) (hedge : G.Adj h x)
    (hh : Even (G.degree h)) (hx : Even (G.degree x))
    (hcap : ∀ v, Even (G.degree v) → v ≠ h → v ≠ x → eDegree G v ≤ 3) :
    ∀ v, Even ((G.deleteEdges {s(h, x)}).degree v) →
      eDegree (G.deleteEdges {s(h, x)}) v ≤ 3 := by
  let P := G.deleteEdges {s(h, x)}
  have hdh : P.degree h + 1 = G.degree h := by
    simpa [P] using degree_delete_edge_add_one G h x hedge
  have hdx : P.degree x + 1 = G.degree x := by
    have hd := degree_delete_edge_add_one G x h hedge.symm
    have hs : s(x, h) = s(h, x) := Sym2.eq_swap
    rw [hs] at hd
    simpa [P] using hd
  have hoff (v : V) (hvh : v ≠ h) (hvx : v ≠ x) : P.degree v = G.degree v := by
    simpa [P] using degree_delete_edge_of_ne G h x v hvh hvx
  have hparity (v : V) : Even (P.degree v) →
      Even (G.degree v) ∧ v ≠ h ∧ v ≠ x := by
    intro hv
    by_cases hvh : v = h
    · subst v
      have ho : Odd (P.degree h) := by
        rcases hh with ⟨q, hq⟩
        exact ⟨q - 1, by omega⟩
      exact False.elim ((Nat.not_even_iff_odd.mpr ho) hv)
    by_cases hvx : v = x
    · subst v
      have ho : Odd (P.degree x) := by
        rcases hx with ⟨q, hq⟩
        exact ⟨q - 1, by omega⟩
      exact False.elim ((Nat.not_even_iff_odd.mpr ho) hv)
    rw [hoff v hvh hvx] at hv
    exact ⟨hv, hvh, hvx⟩
  intro v hv
  obtain ⟨hvG, hvh, hvx⟩ := hparity v hv
  apply (Finset.card_le_card (s := evenNeighbors P v) (t := evenNeighbors G v) ?_).trans
    (hcap v hvG hvh hvx)
  intro w hw
  obtain ⟨ha, he⟩ := (mem_evenNeighbors v w).mp hw
  have hle : G.Adj v w := by
    exact (SimpleGraph.deleteEdges_adj.mp ha).1
  exact (mem_evenNeighbors v w).mpr ⟨hle, (hparity w he).1⟩

/-- The two literal puncture components of a deleted bridge have disjoint
edge sets and cover the whole puncture.  This is the ambient graph interface
for mapping their subtype decompositions. -/
theorem bridge_component_graph_partition [Fintype V] {G : SimpleGraph V}
    [DecidableRel G.Adj] (h x : V) (hconn : G.Connected) (hne : h ≠ x)
    (hbridge : G.IsBridge s(h, x)) :
    let P := G.deleteEdges {s(h, x)}
    let Ch := P.connectedComponentMk h
    let Cx := P.connectedComponentMk x
    Disjoint ((P.induce Ch.supp).spanningCoe).edgeSet
        ((P.induce Cx.supp).spanningCoe).edgeSet ∧
      (P.induce Ch.supp).spanningCoe ⊔ (P.induce Cx.supp).spanningCoe = P ∧
      x ∉ Ch.supp ∧ h ∉ Cx.supp := by
  classical
  dsimp only
  let P := G.deleteEdges {s(h, x)}
  let Ch := P.connectedComponentMk h
  let Cx := P.connectedComponentMk x
  have hxCh : x ∉ Ch.supp := by
    rw [← bridgeSide_eq_component_supp (G := G) h x]
    exact not_mem_bridgeSide_other h x hbridge
  have hChh : h ∈ Ch.supp := by
    simp [Ch]
  have hChCx : Ch ≠ Cx := by
    intro hEq
    apply hxCh
    rw [hEq]
    simp [Cx]
  have hdis : Disjoint ((P.induce Ch.supp).spanningCoe).edgeSet
      ((P.induce Cx.supp).spanningCoe).edgeSet := by
    apply Set.disjoint_left.mpr
    intro e
    induction e using Sym2.inductionOn with
    | hf a b =>
      intro ha hb
      exact Set.disjoint_left.mp
        (P.pairwise_disjoint_supp_connectedComponent hChCx)
        ((Ch.adj_spanningCoe_toSimpleGraph).mp ha).1
        ((Cx.adj_spanningCoe_toSimpleGraph).mp hb).1
  have hmemCh {v : V} (hv : P.Reachable h v) : v ∈ Ch.supp := by
    simp only [Ch, SimpleGraph.ConnectedComponent.mem_supp_iff,
      SimpleGraph.ConnectedComponent.eq]
    exact hv.symm
  have hmemCx {v : V} (hv : P.Reachable x v) : v ∈ Cx.supp := by
    simp only [Cx, SimpleGraph.ConnectedComponent.mem_supp_iff,
      SimpleGraph.ConnectedComponent.eq]
    exact hv.symm
  have hgraph : (P.induce Ch.supp).spanningCoe ⊔
      (P.induce Cx.supp).spanningCoe = P := by
    apply le_antisymm
    · exact sup_le (P.spanningCoe_induce_le Ch.supp)
        (P.spanningCoe_induce_le Cx.supp)
    · intro a b hab
      rcases puncture_reachable_from_h_or_x (G := G) hconn h x a hne with ha | ha
      · exact Or.inl ((Ch.adj_spanningCoe_toSimpleGraph).mpr ⟨hmemCh ha, hab⟩)
      · exact Or.inr ((Cx.adj_spanningCoe_toSimpleGraph).mpr ⟨hmemCx ha, hab⟩)
  have hhCx : h ∉ Cx.supp := by
    intro hh
    exact Set.disjoint_left.mp
      (P.pairwise_disjoint_supp_connectedComponent hChCx) hChh hh
  exact ⟨hdis, hgraph, hxCh, hhCx⟩

/-- A decomposition of a literal component subtype maps to its ambient induced
component graph without changing its carrier count or endpoint multiplicities
at vertices of that component. -/
theorem map_component_decomposition [Fintype V] [DecidableRel J.Adj]
    (C : J.ConnectedComponent) (D : Decomposition (J.induce C.supp)) :
    ∃ E : Decomposition ((J.induce C.supp).spanningCoe),
      E.size = D.size ∧
      ∀ v (hv : v ∈ C.supp), E.endpointCount v = D.endpointCount ⟨v, hv⟩ := by
  classical
  refine ⟨D.map (Function.Embedding.subtype _), rfl, ?_⟩
  intro v hv
  change (D.map (Function.Embedding.subtype _)).endpointCount v =
    D.endpointCount ⟨v, hv⟩
  exact D.map_endpointCount (Function.Embedding.subtype _) ⟨v, hv⟩

/-- Every carrier mapped from a component subtype avoids each ambient vertex
outside that component support. -/
theorem map_component_path_avoids [Fintype V] [DecidableRel J.Adj]
    (C : J.ConnectedComponent) (D : Decomposition (J.induce C.supp))
    (w : V) (hw : w ∉ C.supp) :
    ∀ i : Fin D.size, w ∉ ((D.map (Function.Embedding.subtype _)).path i).walk.support := by
  intro i hi
  simp only [Decomposition.map, NonemptyPath.map_support] at hi
  obtain ⟨v, hv, hEq⟩ := List.mem_map.mp hi
  change v.val = w at hEq
  exact hw (hEq ▸ v.property)

/-- Adding the absent bridge edge to one ambient component graph remains
edge-disjoint from the opposite component graph. -/
theorem bridge_component_add_edge_disjoint [Fintype V] [DecidableRel J.Adj]
    (h x : V) (hne : h ≠ x) (Ch Cx : J.ConnectedComponent)
    (hdis : Disjoint ((J.induce Ch.supp).spanningCoe).edgeSet
      ((J.induce Cx.supp).spanningCoe).edgeSet)
    (hmissing : ¬ J.Adj h x) :
    Disjoint (((J.induce Ch.supp).spanningCoe ⊔ SimpleGraph.edge x h).edgeSet)
      ((J.induce Cx.supp).spanningCoe).edgeSet := by
  let A := (J.induce Ch.supp).spanningCoe
  let B := (J.induce Cx.supp).spanningCoe
  have hBle : B ≤ J := J.spanningCoe_induce_le Cx.supp
  have hBmissing : ¬ B.Adj x h := by
    intro ha
    exact hmissing (hBle ha).symm
  have hEdgeDis : Disjoint (SimpleGraph.edge x h).edgeSet B.edgeSet := by
    apply Set.disjoint_left.mpr
    intro e he hb
    rw [SimpleGraph.edgeSet_edge_of_ne hne.symm] at he
    have heq : e = s(x, h) := Set.mem_singleton_iff.mp he
    subst e
    apply hBmissing
    rw [← SimpleGraph.mem_edgeSet]
    exact hb
  change Disjoint (A ⊔ SimpleGraph.edge x h).edgeSet B.edgeSet
  apply Set.disjoint_left.mpr
  intro e he hb
  rw [SimpleGraph.edgeSet_sup] at he
  rcases he with he | he
  · exact Set.disjoint_left.mp (by simpa [A, B] using hdis) he hb
  · exact Set.disjoint_left.mp hEdgeDis he hb

/-- If two distinct connected-component supports cover the ambient vertices,
their subtype cardinalities add to the ambient cardinality. -/
theorem card_sum_of_component_cover [Fintype V] [DecidableRel J.Adj]
    (Ch Cx : J.ConnectedComponent) (hne : Ch ≠ Cx)
    (hcover : ∀ v : V, v ∈ Ch.supp ∨ v ∈ Cx.supp) :
    Fintype.card Ch.supp + Fintype.card Cx.supp = Fintype.card V := by
  classical
  have hdis : Disjoint Ch.supp Cx.supp :=
    J.pairwise_disjoint_supp_connectedComponent hne
  let f : V → Ch.supp ⊕ Cx.supp := fun v =>
    if hv : v ∈ Ch.supp then Sum.inl ⟨v, hv⟩ else
      Sum.inr ⟨v, (hcover v).resolve_left hv⟩
  let g : Ch.supp ⊕ Cx.supp → V := fun z => match z with
    | Sum.inl v => v
    | Sum.inr v => v
  have hgf : Function.LeftInverse g f := by
    intro v
    by_cases hv : J.connectedComponentMk v = Ch
    · have hm : v ∈ Ch.supp := (SimpleGraph.ConnectedComponent.mem_supp_iff Ch v).mpr hv
      simp [f, g, hm, hv]
    · have hm : v ∉ Ch.supp := fun hm => hv ((SimpleGraph.ConnectedComponent.mem_supp_iff Ch v).mp hm)
      simp [f, g, hm, hv]
  have hfg : Function.RightInverse g f := by
    intro z
    rcases z with v | v
    · have hv : (v.val : V) ∈ Ch.supp := v.property
      have hcomponent : J.connectedComponentMk v.val = Ch :=
        (SimpleGraph.ConnectedComponent.mem_supp_iff Ch v.val).mp hv
      change f v.val = Sum.inl v
      simp [f, hcomponent]
    · have hv : v.val ∉ Ch.supp := fun hv =>
        Set.disjoint_left.mp hdis hv v.property
      have hcomponent : J.connectedComponentMk v.val ≠ Ch := by
        intro heq
        apply hv
        have hself : v.val ∈ (J.connectedComponentMk v.val).supp := by simp
        simpa [heq] using hself
      change f v.val = Sum.inr v
      simp [f, hcomponent]
  have hcard : Fintype.card V = Fintype.card (Ch.supp ⊕ Cx.supp) :=
    Fintype.card_congr (Equiv.ofBijective f ⟨hgf.injective, hfg.surjective⟩)
  rw [Fintype.card_sum] at hcard
  omega

/-- The endpoint of an even deleted edge has odd degree in its literal
puncture component.  This is the endpoint-supply input for every bridge
floor/SET branch. -/
theorem odd_degree_delete_edge_component [Fintype V] {G : SimpleGraph V}
    [DecidableRel G.Adj] (h x : V) (hedge : G.Adj h x)
    (hh : Even (G.degree h)) :
    let P := G.deleteEdges {s(h, x)}
    Odd ((P.induce (P.connectedComponentMk h).supp).degree ⟨h, by simp⟩) := by
  dsimp only
  let P := G.deleteEdges {s(h, x)}
  have hoddP : Odd (P.degree h) := by
    have hd : P.degree h + 1 = G.degree h := by
      simpa [P] using degree_delete_edge_add_one G h x hedge
    rcases hh with ⟨q, hq⟩
    exact ⟨q - 1, by omega⟩
  have hclosed : P.neighborSet h ⊆ (P.connectedComponentMk h).supp :=
    fun _ hw => (P.connectedComponentMk h).mem_supp_of_adj_mem_supp (by simp) hw
  rw [SimpleGraph.degree_induce_of_neighborSet_subset hclosed]
  exact hoddP

/-- Two edge-disjoint floor-side decompositions with a positive endpoint at
their respective bridge ends combine with the bridge singleton. -/
theorem bridge_floor_floor_assembly (h x : V) (hne : h ≠ x)
    (hdis : Disjoint J.edgeSet K.edgeSet)
    (hmissing : ¬ (J ⊔ K).Adj h x)
    (D : Decomposition J) (E : Decomposition K)
    (hD : 0 < D.endpointCount h) (hE : 0 < E.endpointCount x) :
    ∃ F : Decomposition ((J ⊔ K) ⊔ SimpleGraph.edge h x),
      F.size = D.size + E.size + 1 ∧
        2 ≤ F.endpointCount h ∧ 2 ≤ F.endpointCount x := by
  classical
  obtain ⟨U, hsizeU, hendsU⟩ := D.union_disjoint_endpoints E hdis
  let F := U.insertEdge h x hne hmissing
  have hsizeF : F.size = D.size + E.size + 1 := by
    rw [show F = U.insertEdge h x hne hmissing by rfl,
      Decomposition.insertEdge_size, hsizeU]
  have hFh : 2 ≤ F.endpointCount h := by
    rw [show F = U.insertEdge h x hne hmissing by rfl,
      Decomposition.insertEdge_endpointCount, hendsU h]
    simp
    omega
  have hFx : 2 ≤ F.endpointCount x := by
    rw [show F = U.insertEdge h x hne hmissing by rfl,
      Decomposition.insertEdge_endpointCount, hendsU x]
    simp [hne]
    omega
  exact ⟨F, hsizeF, hFh, hFx⟩

/-- The floor--floor bridge construction with literal component graphs.  This
consumes mapped subtype budgets, the exact component partition and local odd
degree endpoint supply; only global component-cardinality arithmetic remains
for its eventual use in the public bridge theorem. -/
theorem bridge_floor_floor_of_component_budgets [Fintype V]
    [DecidableRel J.Adj] (h x : V) (hne : h ≠ x)
    (Ch Cx : J.ConnectedComponent)
    (hdis : Disjoint ((J.induce Ch.supp).spanningCoe).edgeSet
      ((J.induce Cx.supp).spanningCoe).edgeSet)
    (hgraph : (J.induce Ch.supp).spanningCoe ⊔
      (J.induce Cx.supp).spanningCoe = J)
    (hmissing : ¬ J.Adj h x)
    (hmem : h ∈ Ch.supp) (xmem : x ∈ Cx.supp)
    (hodd : Odd ((J.induce Ch.supp).degree ⟨h, hmem⟩))
    (xodd : Odd ((J.induce Cx.supp).degree ⟨x, xmem⟩))
    (hD : HasPathBudget (J.induce Ch.supp) (Fintype.card Ch.supp / 2))
    (hE : HasPathBudget (J.induce Cx.supp) (Fintype.card Cx.supp / 2)) :
    ∃ F : Decomposition (J ⊔ SimpleGraph.edge h x),
      F.size ≤ Fintype.card Ch.supp / 2 + Fintype.card Cx.supp / 2 + 1 ∧
        2 ≤ F.endpointCount h ∧ 2 ≤ F.endpointCount x := by
  obtain ⟨D, hDsize⟩ := hD
  obtain ⟨E, hEsize⟩ := hE
  obtain ⟨D', hDmap, hDends⟩ := map_component_decomposition Ch D
  obtain ⟨E', hEmap, hEends⟩ := map_component_decomposition Cx E
  have hDpos : 0 < D'.endpointCount h := by
    rw [hDends h hmem]
    exact D.endpointCount_pos_of_odd_degree ⟨h, hmem⟩ hodd
  have hEpos : 0 < E'.endpointCount x := by
    rw [hEends x xmem]
    exact E.endpointCount_pos_of_odd_degree ⟨x, xmem⟩ xodd
  obtain ⟨F, hFsize, hFh, hFx⟩ :=
    bridge_floor_floor_assembly h x hne hdis (by simpa [hgraph] using hmissing)
      D' E' hDpos hEpos
  have hFbudget : F.size ≤ Fintype.card Ch.supp / 2 +
      Fintype.card Cx.supp / 2 + 1 := by
    rw [hFsize, hDmap, hEmap]
    omega
  have hout : ∃ F : Decomposition
      (((J.induce Ch.supp).spanningCoe ⊔ (J.induce Cx.supp).spanningCoe) ⊔
        SimpleGraph.edge h x),
      F.size ≤ Fintype.card Ch.supp / 2 + Fintype.card Cx.supp / 2 + 1 ∧
        2 ≤ F.endpointCount h ∧ 2 ≤ F.endpointCount x :=
    ⟨F, hFbudget, hFh, hFx⟩
  rwa [hgraph] at hout

/-- A side with three endpoint occurrences at `h` can carry the bridge to an
edge-disjoint opposite side without another path.  The carrier selected at
`h` is required to avoid `x`, as it does for distinct bridge components. -/
theorem bridge_reserve_extension (h x : V) (hne : h ≠ x)
    (D : Decomposition J) (E : Decomposition K)
    (hreserve : 3 ≤ D.endpointCount h) (hE : 0 < E.endpointCount x)
    (havoid : ∀ i : Fin D.size, x ∉ (D.path i).walk.support)
    (hmissing : ¬ J.Adj x h)
    (hdis : Disjoint (J ⊔ SimpleGraph.edge x h).edgeSet K.edgeSet) :
    ∃ F : Decomposition ((J ⊔ SimpleGraph.edge x h) ⊔ K),
      F.size = D.size + E.size ∧
        2 ≤ F.endpointCount h ∧ 2 ≤ F.endpointCount x := by
  classical
  obtain ⟨i, hi⟩ := D.exists_terminal_of_pos h (by omega)
  obtain ⟨D', hsD', heD'⟩ :=
    D.exists_add_of_avoiding_endpoint i x h hi (havoid i) hmissing
  obtain ⟨F, hsF, heF⟩ := D'.union_disjoint_endpoints E hdis
  have hsizeF : F.size = D.size + E.size := by
    rw [hsF, hsD']
  have hDh : D'.endpointCount h + 1 = D.endpointCount h := by
    have hh := heD' h
    simpa [Ne.symm hne] using hh
  have hDx : D'.endpointCount x = D.endpointCount x + 1 := by
    have hx := heD' x
    simpa [hne] using hx
  have hFh : 2 ≤ F.endpointCount h := by
    rw [heF h]
    omega
  have hFx : 2 ≤ F.endpointCount x := by
    rw [heF x, hDx]
    omega
  exact ⟨F, hsizeF, hFh, hFx⟩

/-- A literal SET component supplies the bridge reserve directly.  Its mapped
decomposition retains three endpoint occurrences at the puncture-odd hub,
and the bridge is placed on an avoiding terminal carrier without adding a
path. -/
theorem bridge_set_reserve_of_component [Fintype V] [DecidableRel J.Adj]
    (h x : V) (hne : h ≠ x) (Ch Cx : J.ConnectedComponent)
    (hdis : Disjoint ((J.induce Ch.supp).spanningCoe).edgeSet
      ((J.induce Cx.supp).spanningCoe).edgeSet)
    (hgraph : (J.induce Ch.supp).spanningCoe ⊔
      (J.induce Cx.supp).spanningCoe = J)
    (hmissing : ¬ J.Adj h x)
    (hmem : h ∈ Ch.supp) (xmem : x ∈ Cx.supp) (hxnot : x ∉ Ch.supp)
    (hodd : Odd ((J.induce Ch.supp).degree ⟨h, hmem⟩))
    (hset : IsSET (J.induce Ch.supp))
    (E : Decomposition (J.induce Cx.supp))
    (hEpos : 0 < E.endpointCount ⟨x, xmem⟩) :
    ∃ F : Decomposition (J ⊔ SimpleGraph.edge h x),
      F.size ≤ (Fintype.card Ch.supp + 1) / 2 + E.size ∧
        2 ≤ F.endpointCount h ∧ 2 ≤ F.endpointCount x := by
  obtain ⟨D, hDsize, hDtwo⟩ := hset.endpoint_reserve ⟨h, hmem⟩
  let D' := D.map (Function.Embedding.subtype _)
  let E' := E.map (Function.Embedding.subtype _)
  have hDthree0 : 3 ≤ D.endpointCount ⟨h, hmem⟩ :=
    D.three_le_endpointCount_of_odd_degree ⟨h, hmem⟩ hodd hDtwo
  have hDends : (D.map (Function.Embedding.subtype _)).endpointCount h =
      D.endpointCount ⟨h, hmem⟩ := by
    exact D.map_endpointCount (Function.Embedding.subtype _) ⟨h, hmem⟩
  have hDthree : 3 ≤ D'.endpointCount h := by
    change 3 ≤ (D.map (Function.Embedding.subtype _)).endpointCount h
    rw [hDends]
    exact hDthree0
  have hEends : (E.map (Function.Embedding.subtype _)).endpointCount x =
      E.endpointCount ⟨x, xmem⟩ := by
    exact E.map_endpointCount (Function.Embedding.subtype _) ⟨x, xmem⟩
  have hEpos' : 0 < E'.endpointCount x := by
    change 0 < (E.map (Function.Embedding.subtype _)).endpointCount x
    rw [hEends]
    exact hEpos
  have havoid : ∀ i : Fin D'.size, x ∉ (D'.path i).walk.support := by
    change ∀ i : Fin D.size, x ∉ ((D.map (Function.Embedding.subtype _)).path i).walk.support
    exact map_component_path_avoids Ch D x hxnot
  have hmissing' : ¬ ((J.induce Ch.supp).spanningCoe).Adj x h := by
    intro ha
    exact hmissing ((J.spanningCoe_induce_le Ch.supp ha).symm)
  have hdis' : Disjoint (((J.induce Ch.supp).spanningCoe ⊔
      SimpleGraph.edge x h).edgeSet) ((J.induce Cx.supp).spanningCoe).edgeSet :=
    bridge_component_add_edge_disjoint h x hne Ch Cx hdis hmissing
  obtain ⟨F, hFsize, hFh, hFx⟩ :=
    bridge_reserve_extension h x hne D' E' hDthree hEpos' havoid hmissing' hdis'
  have hFbudget : F.size ≤ (Fintype.card Ch.supp + 1) / 2 + E.size := by
    rw [hFsize]
    change D.size + E.size ≤ (Fintype.card Ch.supp + 1) / 2 + E.size
    omega
  have hout : ∃ F : Decomposition
      (((J.induce Ch.supp).spanningCoe ⊔ SimpleGraph.edge x h) ⊔
        (J.induce Cx.supp).spanningCoe),
      F.size ≤ (Fintype.card Ch.supp + 1) / 2 + E.size ∧
        2 ≤ F.endpointCount h ∧ 2 ≤ F.endpointCount x :=
    ⟨F, hFbudget, hFh, hFx⟩
  have hfinal : (((J.induce Ch.supp).spanningCoe ⊔ SimpleGraph.edge x h) ⊔
      (J.induce Cx.supp).spanningCoe) = J ⊔ SimpleGraph.edge h x := by
    calc
      _ = ((J.induce Ch.supp).spanningCoe ⊔
          (J.induce Cx.supp).spanningCoe) ⊔ SimpleGraph.edge x h := by ac_rfl
      _ = J ⊔ SimpleGraph.edge h x := by rw [hgraph, SimpleGraph.edge_comm]
  rwa [hfinal] at hout

/-- Simultaneous endpoint exposure when the edge joining the two exceptional
vertices is a bridge.  The puncture has precisely the two endpoint components;
the floor-or-SET alternative on each component is assembled by a singleton
bridge in the floor--floor case and by a reserved SET terminal otherwise. -/
theorem simultaneous_of_bridge [Fintype V] {G : SimpleGraph V}
    [DecidableRel G.Adj] (hconn : G.Connected) (h x : V) (hne : h ≠ x)
    (hedge : G.Adj h x) (hbridge : G.IsBridge s(h, x))
    (hh : Even (G.degree h)) (hx : Even (G.degree x))
    (hcap : ∀ v, Even (G.degree v) → v ≠ h → v ≠ x → eDegree G v ≤ 3) :
    ∃ D : Decomposition G, D.size ≤ Fintype.card V / 2 + 1 ∧
      2 ≤ D.endpointCount h ∧ 2 ≤ D.endpointCount x := by
  classical
  let P := G.deleteEdges {s(h, x)}
  let Ch := P.connectedComponentMk h
  let Cx := P.connectedComponentMk x
  obtain ⟨hdis, hgraph, hxnot, hnotCx⟩ := by
    simpa only [P, Ch, Cx] using bridge_component_graph_partition h x hconn hne hbridge
  have hmem : h ∈ Ch.supp := by simp [Ch]
  have xmem : x ∈ Cx.supp := by simp [Cx]
  have hcompne : Ch ≠ Cx := by
    intro heq
    have hxnot' : x ∉ Ch.supp := by simpa [P, Ch] using hxnot
    exact hxnot' (by rw [heq]; exact xmem)
  have hcover (v : V) : v ∈ Ch.supp ∨ v ∈ Cx.supp := by
    rcases puncture_reachable_from_h_or_x hconn h x v hne with hv | hv
    · left
      change P.connectedComponentMk v = Ch
      simpa [Ch] using hv.symm
    · right
      change P.connectedComponentMk v = Cx
      simpa [Cx] using hv.symm
  have hcard : Fintype.card Ch.supp + Fintype.card Cx.supp = Fintype.card V :=
    card_sum_of_component_cover Ch Cx hcompne hcover
  have hPcap : ∀ v, Even (P.degree v) → eDegree P v ≤ 3 := by
    simpa only [P] using delete_even_edge_cap h x hedge hh hx hcap
  have hCh := floor_or_set_component Ch hPcap
  have hCx := floor_or_set_component Cx hPcap
  have hoddh : Odd ((P.induce Ch.supp).degree ⟨h, hmem⟩) := by
    simpa only [P, Ch] using odd_degree_delete_edge_component h x hedge hh
  have hoddx : Odd ((P.induce Cx.supp).degree ⟨x, xmem⟩) := by
    have hoddP : Odd (P.degree x) := by
      have hd : P.degree x + 1 = G.degree x := by
        have hd' := degree_delete_edge_add_one G x h hedge.symm
        have hs : s(x, h) = s(h, x) := Sym2.eq_swap
        rw [hs] at hd'
        simpa [P] using hd'
      rcases hx with ⟨q, hq⟩
      exact ⟨q - 1, by omega⟩
    have hclosed : P.neighborSet x ⊆ Cx.supp :=
      fun _ hw => Cx.mem_supp_of_adj_mem_supp (by simp [Cx]) hw
    rw [SimpleGraph.degree_induce_of_neighborSet_subset hclosed]
    exact hoddP
  have hmissing : ¬ P.Adj h x := by
    simp [P, SimpleGraph.deleteEdges_adj]
  have hrestore : P ⊔ SimpleGraph.edge h x = G := by
    simpa [P] using delete_edge_sup_edge G h x hedge
  rcases hCh with hCh | hCh <;> rcases hCx with hCx | hCx
  · obtain ⟨D, hDsize, hDh, hDx⟩ :=
      bridge_floor_floor_of_component_budgets h x hne Ch Cx hdis hgraph hmissing
        hmem xmem hoddh hoddx hCh hCx
    have hbudget : D.size ≤ Fintype.card V / 2 + 1 := by omega
    have hout : ∃ D : Decomposition (P ⊔ SimpleGraph.edge h x),
        D.size ≤ Fintype.card V / 2 + 1 ∧
          2 ≤ D.endpointCount h ∧ 2 ≤ D.endpointCount x :=
      ⟨D, hbudget, hDh, hDx⟩
    rwa [hrestore] at hout
  · obtain ⟨E, hEsize⟩ := hCh
    have hEpos : 0 < E.endpointCount ⟨h, hmem⟩ :=
      E.endpointCount_pos_of_odd_degree ⟨h, hmem⟩ hoddh
    obtain ⟨D, hDsize, hDx, hDh⟩ :=
      bridge_set_reserve_of_component x h hne.symm Cx Ch hdis.symm
        (by rw [sup_comm]; exact hgraph) (fun ha => hmissing ha.symm)
        xmem hmem hnotCx hoddx hCx E hEpos
    have hoddcard : Odd (Fintype.card Cx.supp) := hCx.odd_order
    have hbudget : D.size ≤ Fintype.card V / 2 + 1 := by omega
    have hrestore' : P ⊔ SimpleGraph.edge x h = G := by
      rw [SimpleGraph.edge_comm]
      exact hrestore
    have hout : ∃ D : Decomposition (P ⊔ SimpleGraph.edge x h),
        D.size ≤ Fintype.card V / 2 + 1 ∧
          2 ≤ D.endpointCount h ∧ 2 ≤ D.endpointCount x :=
      ⟨D, hbudget, hDh, hDx⟩
    rwa [hrestore'] at hout
  · obtain ⟨E, hEsize⟩ := hCx
    have hEpos : 0 < E.endpointCount ⟨x, xmem⟩ :=
      E.endpointCount_pos_of_odd_degree ⟨x, xmem⟩ hoddx
    obtain ⟨D, hDsize, hDh, hDx⟩ :=
      bridge_set_reserve_of_component h x hne Ch Cx hdis hgraph hmissing hmem xmem hxnot
        hoddh hCh E hEpos
    have hoddcard : Odd (Fintype.card Ch.supp) := hCh.odd_order
    have hbudget : D.size ≤ Fintype.card V / 2 + 1 := by omega
    have hout : ∃ D : Decomposition (P ⊔ SimpleGraph.edge h x),
        D.size ≤ Fintype.card V / 2 + 1 ∧
          2 ≤ D.endpointCount h ∧ 2 ≤ D.endpointCount x :=
      ⟨D, hbudget, hDh, hDx⟩
    rwa [hrestore] at hout
  · obtain ⟨E, hEsize, hEtwo⟩ := hCx.endpoint_reserve ⟨x, xmem⟩
    have hEpos : 0 < E.endpointCount ⟨x, xmem⟩ := by omega
    obtain ⟨D, hDsize, hDh, hDx⟩ :=
      bridge_set_reserve_of_component h x hne Ch Cx hdis hgraph hmissing hmem xmem hxnot
        hoddh hCh E hEpos
    have hoddCh : Odd (Fintype.card Ch.supp) := hCh.odd_order
    have hoddCx : Odd (Fintype.card Cx.supp) := hCx.odd_order
    have hbudget : D.size ≤ Fintype.card V / 2 + 1 := by omega
    have hout : ∃ D : Decomposition (P ⊔ SimpleGraph.edge h x),
        D.size ≤ Fintype.card V / 2 + 1 ∧
          2 ≤ D.endpointCount h ∧ 2 ≤ D.endpointCount x :=
      ⟨D, hbudget, hDh, hDx⟩
    rwa [hrestore] at hout

end Gallai.TwoException
