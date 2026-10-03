/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.Inputs.SETReserve
public import Gallai.Inputs.TwoEdgeAttach
public import Gallai.Operations.DecompositionMap
public import Gallai.Operations.AbsorbPath
public import Gallai.Operations.Union

@[expose] public section

/-! # Endpoint reserve at the new vertex of an extended SET graph -/

namespace Gallai

universe u v
variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
variable {W : Type v} [Fintype W] [DecidableEq W]

/-- Explicit graph-image adjacency decision for addibility. -/
noncomputable local instance esetImageAdj (f : V ↪ W) :
    DecidableRel (G.map f).Adj := fun _ _ => Classical.propDecidable _

/-- Attach the connection vertex to one odd and one even vertex of a SET graph.
The construction keeps the SET decomposition's budget; no endpoint witness is assumed. -/
theorem IsSET.extension_endpoint_reserve (h : IsSET G) (f : V ↪ W) (z : W)
    (hz : z ∉ Set.range f) (x y : V) (hx : Odd (G.degree x)) (hy : Even (G.degree y)) :
    ∃ E : Decomposition ((G.map f ⊔ SimpleGraph.edge z (f x)) ⊔
      SimpleGraph.edge z (f y)), E.size ≤ (Fintype.card V + 1) / 2 ∧
      2 ≤ E.endpointCount z := by
  classical
  have hxy : x ≠ y := by
    rintro rfl
    exact Nat.not_even_iff_odd.mpr hx hy
  have hza : z ≠ f x := fun he => hz ⟨x, he.symm⟩
  have hzb : z ≠ f y := fun he => hz ⟨y, he.symm⟩
  have hiso (w : W) : ¬ (G.map f).Adj z w := by
    intro he
    obtain ⟨a, b, _, ha, _⟩ := (SimpleGraph.map_adj f G z w).mp he
    exact hz ⟨a, ha⟩
  obtain ⟨D, hD, hDy⟩ := h.endpoint_reserve y
  have hDx := D.endpointCount_pos_of_odd_degree x hx
  have hRx : 0 < (D.map f).endpointCount (f x) := by simpa using hDx
  have hRy : 2 ≤ (D.map f).endpointCount (f y) := by simpa using hDy
  obtain ⟨E, hs, he⟩ := (D.map f).attach_two_edges z (f x) (f y)
    hza hzb (fun he => hxy (f.injective he)) hiso hRx hRy
  refine ⟨E, ?_, ?_⟩
  · simpa only [Decomposition.map_size] using hs.le.trans (by simpa using hD)
  · omega

/-- The extended graph satisfies the ceiling budget on its whole finite vertex type. -/
theorem IsSET.extension_ceiling_reserve (h : IsSET G) (f : V ↪ W) (z : W)
    (hz : z ∉ Set.range f) (x y : V) (hx : Odd (G.degree x)) (hy : Even (G.degree y)) :
    ∃ E : Decomposition ((G.map f ⊔ SimpleGraph.edge z (f x)) ⊔
      SimpleGraph.edge z (f y)), E.size ≤ (Fintype.card W + 1) / 2 ∧
      2 ≤ E.endpointCount z := by
  obtain ⟨E, hs, he⟩ := h.extension_endpoint_reserve f z hz x y hx hy
  have hc := Fintype.card_le_of_injective f f.injective
  exact ⟨E, by omega, he⟩

omit [Fintype W] in
/-- BS Lemma 11 for a SET graph embedded in a larger ambient graph.
The attached path meets the whole embedded vertex set only at the connection. -/
theorem IsSET.absorb_embedded_path (h : IsSET G) (f : V ↪ W) (u : V)
    {H : SimpleGraph W} {a b : W} (p : H.Walk a b) (hp : p.IsPath)
    (hu : f u ∈ p.support) (hle : G.map f ≤ H)
    (hedges : ∀ e, e ∈ H.edgeSet ↔ e ∈ (G.map f).edgeSet ∨ e ∈ p.edges)
    (hmeet : ∀ w ∈ p.support, w ∈ Set.range f → w = f u) :
    ∃ E : Decomposition H, E.size ≤ (Fintype.card V + 1) / 2 := by
  obtain ⟨D, hD, huD⟩ := h.endpoint_reserve u
  obtain ⟨E, hs⟩ := (D.map f).absorb_walk_of_vertex_intersection p hp (f u) hu
    (by simpa using huD) hle hedges (by
      intro w hw hadj
      obtain ⟨z, hz⟩ := hadj
      obtain ⟨r, s, _, hr, _⟩ := (SimpleGraph.map_adj f G w z).mp hz
      exact hmeet w hw ⟨r, hr⟩)
  exact ⟨E, hs.le.trans hD⟩

/-- BS Lemma 11 for an extended SET, with its fresh connection vertex.
The bound is already the ceiling for the smaller underlying SET graph. -/
theorem IsSET.absorb_extension_path (h : IsSET G) (f : V ↪ W) (z : W)
    (hz : z ∉ Set.range f) (x y : V) (hx : Odd (G.degree x)) (hy : Even (G.degree y))
    {H : SimpleGraph W} {a b : W} (p : H.Walk a b) (hp : p.IsPath)
    (hu : z ∈ p.support)
    (hle : ((G.map f ⊔ SimpleGraph.edge z (f x)) ⊔ SimpleGraph.edge z (f y)) ≤ H)
    (hedges : ∀ e, e ∈ H.edgeSet ↔
      e ∈ ((G.map f ⊔ SimpleGraph.edge z (f x)) ⊔ SimpleGraph.edge z (f y)).edgeSet ∨
        e ∈ p.edges)
    (hmeet : ∀ w ∈ p.support, w ∈ Set.range f → w = z) :
    ∃ E : Decomposition H, E.size ≤ (Fintype.card V + 1) / 2 := by
  obtain ⟨D, hD, huD⟩ := h.extension_endpoint_reserve f z hz x y hx hy
  obtain ⟨E, hs⟩ := D.absorb_walk_of_vertex_intersection p hp z hu huD hle hedges (by
    intro w hw hadj
    obtain ⟨t, ht⟩ := hadj
    rcases ht with (hg | hx') | hy'
    · obtain ⟨r, s, _, hr, _⟩ := (SimpleGraph.map_adj f G w t).mp hg
      exact hmeet w hw ⟨r, hr⟩
    · simp only [SimpleGraph.edge_adj] at hx'
      rcases hx'.1 with h | h
      · exact h.1
      · exact hmeet w hw ⟨x, h.1.symm⟩
    · simp only [SimpleGraph.edge_adj] at hy'
      rcases hy'.1 with h | h
      · exact h.1
      · exact hmeet w hw ⟨y, h.1.symm⟩)
  exact ⟨E, hs.le.trans hD⟩

omit [Fintype W] in
/-- Hanging SET absorption saves one path from any remainder decomposition.
Positive degree at the joint is explicit, ensuring an actual carrier exists. -/
theorem IsSET.absorb_hanging (h : IsSET G) (f : V ↪ W) (u : V)
    {J : SimpleGraph W} (D : Decomposition J)
    (hpos : ∃ z, J.Adj (f u) z)
    (hmeet : ∀ w, (∃ z, J.Adj w z) → w ∈ Set.range f → w = f u) :
    ∃ E : Decomposition (G.map f ⊔ J),
      E.size ≤ (Fintype.card V + 1) / 2 + D.size - 1 := by
  classical
  obtain ⟨z, hz⟩ := hpos
  obtain ⟨i, hi, _⟩ := D.covers s(f u, z) hz
  let P := D.path i
  let K := G.map f ⊔ P.walk.toSubgraph.spanningCoe
  have heK (e : Sym2 W) : e ∈ K.edgeSet ↔ e ∈ (G.map f).edgeSet ∨ e ∈ P.walk.edges := by
    simp only [K, SimpleGraph.edgeSet_sup, Set.mem_union,
      SimpleGraph.Subgraph.edgeSet_spanningCoe, SimpleGraph.Walk.mem_edges_toSubgraph]
  let Q := P.transfer K (fun e he => (heK e).mpr (Or.inr he))
  obtain ⟨A, hA⟩ := h.absorb_embedded_path f u Q.walk Q.isPath
    (by simpa [Q] using P.walk.fst_mem_support_of_mem_edges hi)
    le_sup_left (by simpa [Q] using heK) (by
      intro w hw hr
      have hw' : w ∈ P.walk.support := by simpa [Q] using hw
      obtain ⟨t, _, ht⟩ := SimpleGraph.adj_of_mem_walk_support P.walk P.nonempty hw'
      exact hmeet w ⟨t, ht⟩ hr)
  have hdis : Disjoint (G.map f).edgeSet J.edgeSet := by
    apply Set.disjoint_left.mpr
    intro e
    induction e using Sym2.inductionOn with
    | hf a b =>
      intro hg hj
      have hab : J.Adj a b := hj
      obtain ⟨r, s, _, hr, hs⟩ := (SimpleGraph.map_adj f G a b).mp hg
      have ha := hmeet a ⟨b, hab⟩ ⟨r, hr⟩
      have hb := hmeet b ⟨a, hab.symm⟩ ⟨s, hs⟩
      exact hab.ne (ha.trans hb.symm)
  obtain ⟨E, hs⟩ := D.replace_carrier_union i A heK hdis
  exact ⟨E, by omega⟩

/-- Hanging extended-SET absorption, with its fresh connection vertex.
The resulting bound retains the underlying SET ceiling and saves one carrier. -/
theorem IsSET.absorb_extension_hanging (h : IsSET G) (f : V ↪ W) (z : W)
    (hz : z ∉ Set.range f) (x y : V) (hx : Odd (G.degree x)) (hy : Even (G.degree y))
    {J : SimpleGraph W} (D : Decomposition J) (hpos : ∃ t, J.Adj z t)
    (hmeet : ∀ w, (∃ t, J.Adj w t) → w ∈ Set.range f → w = z) :
    ∃ E : Decomposition (((G.map f ⊔ SimpleGraph.edge z (f x)) ⊔
        SimpleGraph.edge z (f y)) ⊔ J),
      E.size ≤ (Fintype.card V + 1) / 2 + D.size - 1 := by
  classical
  let B := (G.map f ⊔ SimpleGraph.edge z (f x)) ⊔ SimpleGraph.edge z (f y)
  obtain ⟨t, ht⟩ := hpos
  obtain ⟨i, hi, _⟩ := D.covers s(z, t) ht
  let P := D.path i
  let K := B ⊔ P.walk.toSubgraph.spanningCoe
  have heK (e : Sym2 W) : e ∈ K.edgeSet ↔ e ∈ B.edgeSet ∨ e ∈ P.walk.edges := by
    simp only [K, SimpleGraph.edgeSet_sup, Set.mem_union,
      SimpleGraph.Subgraph.edgeSet_spanningCoe, SimpleGraph.Walk.mem_edges_toSubgraph]
  let Q := P.transfer K (fun e he => (heK e).mpr (Or.inr he))
  obtain ⟨A, hA⟩ := h.absorb_extension_path f z hz x y hx hy Q.walk Q.isPath
    (by simpa [Q] using P.walk.fst_mem_support_of_mem_edges hi)
    le_sup_left (by simpa only [Q, NonemptyPath.transfer_edges] using heK) (by
      intro w hw hr
      have hw' : w ∈ P.walk.support := by simpa [Q] using hw
      obtain ⟨t, _, ht⟩ := SimpleGraph.adj_of_mem_walk_support P.walk P.nonempty hw'
      exact hmeet w ⟨t, ht⟩ hr)
  have hactive (w t : W) (hw : B.Adj w t) : w = z ∨ w ∈ Set.range f := by
    rcases hw with (hg | he) | he
    · obtain ⟨r, s, _, hr, _⟩ := (SimpleGraph.map_adj f G w t).mp hg
      exact Or.inr ⟨r, hr⟩
    · simp only [SimpleGraph.edge_adj] at he
      rcases he.1 with he | he
      · exact Or.inl he.1
      · exact Or.inr ⟨x, he.1.symm⟩
    · simp only [SimpleGraph.edge_adj] at he
      rcases he.1 with he | he
      · exact Or.inl he.1
      · exact Or.inr ⟨y, he.1.symm⟩
  have hdis : Disjoint B.edgeSet J.edgeSet := by
    apply Set.disjoint_left.mpr
    intro e
    induction e using Sym2.inductionOn with
    | hf a b =>
      intro hg hj
      have hab : J.Adj a b := hj
      have hBab : B.Adj a b := hg
      have ha : a = z := (hactive a b hBab).elim id (hmeet a ⟨b, hab⟩)
      have hb : b = z := (hactive b a hBab.symm).elim id (hmeet b ⟨a, hab.symm⟩)
      exact hab.ne (ha.trans hb.symm)
  obtain ⟨E, hs⟩ := D.replace_carrier_union i A heK hdis
  exact ⟨E, by omega⟩

end Gallai
