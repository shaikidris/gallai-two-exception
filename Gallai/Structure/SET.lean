/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.Structure.EvenSubgraphInduce
public import Gallai.Structure.OrderParity

@[expose] public section

/-! # Single even triangle graphs

The literal Botler--Sambinelli definition: the induced even graph is a triangle,
and every odd vertex has at least two even neighbours. No path budget is assumed.
-/

namespace Gallai

open scoped Finset

universe u v
variable {V : Type u} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Single even triangle graph, expressed without choosing triangle labels. -/
structure IsSET : Prop where
  /-- The even vertex set has exactly three vertices. -/
  card_even : #{v : V | Even (G.degree v)} = 3
  /-- Every two distinct even vertices are adjacent. -/
  even_clique : ∀ a b, Even (G.degree a) → Even (G.degree b) → a ≠ b → G.Adj a b
  /-- Every odd vertex has at least two even neighbours. -/
  odd_neighbors : ∀ v, Odd (G.degree v) → 2 ≤ eDegree G v

variable {G}

/-- Every SET graph has odd order by the handshaking identity. -/
theorem IsSET.odd_order (h : IsSET G) : Odd (Fintype.card V) :=
  odd_order_of_three_even_vertices G h.card_even

variable [DecidableEq V]

/-- An even SET vertex is adjacent to exactly the other two even vertices. -/
theorem IsSET.evenNeighbors_eq_erase (h : IsSET G) (u : V) (hu : Even (G.degree u)) :
    evenNeighbors G u = (Finset.univ.filter fun v => Even (G.degree v)).erase u := by
  ext v
  simp only [mem_evenNeighbors, Finset.mem_erase, Finset.mem_filter, Finset.mem_univ,
    true_and]
  constructor
  · rintro ⟨ha, he⟩
    exact ⟨ha.ne.symm, he⟩
  · rintro ⟨hne, he⟩
    exact ⟨h.even_clique u v hu he hne.symm, he⟩

/-- The E-degree of every even SET vertex is exactly two. -/
theorem IsSET.eDegree_even (h : IsSET G) (u : V) (hu : Even (G.degree u)) :
    eDegree G u = 2 := by
  unfold eDegree
  rw [h.evenNeighbors_eq_erase u hu, Finset.card_erase_of_mem (by simp [hu]), h.card_even]

omit [DecidableEq V] in
/-- Every vertex has at most three even neighbours. -/
theorem IsSET.eDegree_le_three (h : IsSET G) (u : V) : eDegree G u ≤ 3 := by
  have hs : evenNeighbors G u ⊆ Finset.univ.filter fun v => Even (G.degree v) := by
    intro v hv
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ v, ((mem_evenNeighbors u v).mp hv).2⟩
  exact (Finset.card_le_card hs).trans_eq h.card_even

/-- The designated even-neighbour star always has two or three spokes. -/
theorem IsSET.eDegree_two_or_three (h : IsSET G) (u : V) :
    eDegree G u = 2 ∨ eDegree G u = 3 := by
  have hupper := h.eDegree_le_three u
  by_cases he : Even (G.degree u)
  · exact Or.inl (h.eDegree_even u he)
  · have hlower := h.odd_neighbors u (Nat.not_even_iff_odd.mp he)
    omega

/-- No vertex of a SET graph is isolated or a leaf. -/
theorem IsSET.two_le_degree (h : IsSET G) (u : V) : 2 ≤ G.degree u := by
  have hl := eDegree_le_degree (G := G) u
  rcases h.eDegree_two_or_three u with he | he <;> omega

/-- Two odd vertices in a SET graph have a common even neighbour.  The
three-even-vertex condition is doing the work: otherwise their two required
even-neighbour sets would be disjoint subsets of a three-element set. -/
theorem IsSET.exists_common_even_neighbor_of_odd (h : IsSET G) (u v : V)
    (hu : Odd (G.degree u)) (hv : Odd (G.degree v)) :
    ∃ w, G.Adj u w ∧ G.Adj v w ∧ Even (G.degree w) := by
  classical
  by_contra hcommon
  have hdisjoint : Disjoint (evenNeighbors G u) (evenNeighbors G v) := by
    rw [Finset.disjoint_left]
    intro w hwu hwv
    apply hcommon
    obtain ⟨huw, hwe⟩ := (mem_evenNeighbors (G := G) u w).mp hwu
    obtain ⟨hvw, _⟩ := (mem_evenNeighbors (G := G) v w).mp hwv
    exact ⟨w, huw, hvw, hwe⟩
  let E := Finset.univ.filter fun w => Even (G.degree w)
  have hsubu : evenNeighbors G u ⊆ E := by
    intro w hw
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ w,
      ((mem_evenNeighbors (G := G) u w).mp hw).2⟩
  have hsubv : evenNeighbors G v ⊆ E := by
    intro w hw
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ w,
      ((mem_evenNeighbors (G := G) v w).mp hw).2⟩
  have hunion : evenNeighbors G u ∪ evenNeighbors G v ⊆ E :=
    Finset.union_subset hsubu hsubv
  have hcard : (evenNeighbors G u ∪ evenNeighbors G v).card ≤ 3 := by
    calc
      (evenNeighbors G u ∪ evenNeighbors G v).card ≤ E.card :=
        Finset.card_le_card hunion
      _ = 3 := h.card_even
  rw [Finset.card_union_of_disjoint hdisjoint] at hcard
  have hu2 := h.odd_neighbors u hu
  have hv2 := h.odd_neighbors v hv
  change 2 ≤ (evenNeighbors G u).card at hu2
  change 2 ≤ (evenNeighbors G v).card at hv2
  omega

/-- A three-spoke even-neighbour star can only be centred at an odd vertex. -/
theorem IsSET.odd_of_eDegree_three (h : IsSET G) (u : V) (hu : eDegree G u = 3) :
    Odd (G.degree u) := by
  apply Nat.not_even_iff_odd.mp
  intro he
  have hd := h.eDegree_even u he
  omega

/-- An odd vertex of a SET graph has at least two even neighbours.  In
particular, an odd vertex with no even neighbour excludes the SET
alternative. -/
theorem IsSET.not_odd_of_eDegree_zero (h : IsSET G) (u : V)
    (hu : Odd (G.degree u)) (hzero : eDegree G u = 0) : False := by
  have htwo := h.odd_neighbors u hu
  omega

/-- An even vertex of a SET graph has exactly two even neighbours, so an
even vertex with zero E-degree excludes the SET alternative. -/
theorem IsSET.not_even_of_eDegree_zero (h : IsSET G) (u : V)
    (hu : Even (G.degree u)) (hzero : eDegree G u = 0) : False := by
  have htwo := h.eDegree_even u hu
  omega

/-- The preceding obstruction is component-local.  A connected component is
neighbour-closed, so its induced graph preserves both the degree parity and
the E-degree of each retained vertex. -/
theorem component_not_set_of_even_eDegree_zero
    (C : G.ConnectedComponent) [DecidablePred (· ∈ C.supp)]
    (v : V) (hv : v ∈ C.supp) (heven : Even (G.degree v))
    (hzero : eDegree G v = 0) :
    ¬ IsSET (G.induce C.supp) := by
  intro hset
  have hclosed : ∀ u ∈ C.supp, G.neighborSet u ⊆ C.supp := by
    intro u hu w huw
    exact C.mem_supp_of_adj_mem_supp hu huw
  have hevenC : Even ((G.induce C.supp).degree ⟨v, hv⟩) := by
    rw [SimpleGraph.degree_induce_of_neighborSet_subset (hclosed v hv)]
    exact heven
  have hzeroC : eDegree (G.induce C.supp) ⟨v, hv⟩ = 0 := by
    rw [eDegree_induce_of_closed G C.supp hclosed]
    exact hzero
  exact hset.not_even_of_eDegree_zero ⟨v, hv⟩ hevenC hzeroC

/-- The odd-parity counterpart of `component_not_set_of_even_eDegree_zero`.
An odd vertex with no even neighbour rules out SET just as an even vertex
with no even neighbour does; connected-component closure transports both
local facts to the induced component. -/
theorem component_not_set_of_odd_eDegree_zero
    (C : G.ConnectedComponent) [DecidablePred (· ∈ C.supp)]
    (v : V) (hv : v ∈ C.supp) (hodd : Odd (G.degree v))
    (hzero : eDegree G v = 0) :
    ¬ IsSET (G.induce C.supp) := by
  intro hset
  have hclosed : ∀ u ∈ C.supp, G.neighborSet u ⊆ C.supp := by
    intro u hu w huw
    exact C.mem_supp_of_adj_mem_supp hu huw
  have hoddC : Odd ((G.induce C.supp).degree ⟨v, hv⟩) := by
    rw [SimpleGraph.degree_induce_of_neighborSet_subset (hclosed v hv)]
    exact hodd
  have hzeroC : eDegree (G.induce C.supp) ⟨v, hv⟩ = 0 := by
    rw [eDegree_induce_of_closed G C.supp hclosed]
    exact hzero
  exact hset.not_odd_of_eDegree_zero ⟨v, hv⟩ hoddC hzeroC

/-! ## Isomorphism transport -/

namespace SimpleGraph.Iso

variable {W : Type v} {H : SimpleGraph W}
variable [Fintype W] [DecidableEq W] [DecidableRel H.Adj]

omit [DecidableEq V] [DecidableEq W] in
/-- A simple-graph isomorphism preserves vertex degrees. -/
theorem degree_eq (f : G ≃g H) (v : V) :
    G.degree v = H.degree (f v) := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree,
    ← SimpleGraph.card_neighborFinset_eq_degree]
  simpa [SimpleGraph.neighborFinset_def] using Fintype.card_congr (f.mapNeighborSet v)

/-- A simple-graph isomorphism transports the finite type of even neighbours
at a vertex. -/
noncomputable def evenNeighborEquiv (f : G ≃g H) (v : V) :
    evenNeighbors G v ≃ evenNeighbors H (f v) where
  toFun w := by
    refine ⟨f w, ?_⟩
    obtain ⟨hwAdj, hwEven⟩ := (mem_evenNeighbors (G := G) v w).mp w.property
    apply (mem_evenNeighbors (G := H) (f v) (f w)).mpr
    refine ⟨f.map_adj_iff.mpr hwAdj, ?_⟩
    simpa only [f.degree_eq] using hwEven
  invFun w := by
    refine ⟨f.symm w, ?_⟩
    obtain ⟨hwAdj, hwEven⟩ := (mem_evenNeighbors (G := H) (f v) w).mp w.property
    apply (mem_evenNeighbors (G := G) v (f.symm w)).mpr
    refine ⟨?_, ?_⟩
    · simpa using f.symm.map_adj_iff.mpr hwAdj
    · have hdegree : G.degree (f.symm w) = H.degree w := by
        calc
          G.degree (f.symm w) = H.degree (f (f.symm w)) :=
            SimpleGraph.Iso.degree_eq f (f.symm w)
          _ = H.degree w := by rw [f.apply_symm_apply]
      rw [hdegree]
      exact hwEven
  left_inv w := by
    apply Subtype.ext
    simp
  right_inv w := by
    apply Subtype.ext
    simp

omit [DecidableEq V] [DecidableEq W] in
/-- A simple-graph isomorphism preserves E-degrees. -/
theorem eDegree_eq (f : G ≃g H) (v : V) :
    eDegree G v = eDegree H (f v) := by
  unfold eDegree
  rw [← Fintype.card_coe (evenNeighbors G v),
    ← Fintype.card_coe (evenNeighbors H (f v))]
  exact Fintype.card_congr (SimpleGraph.Iso.evenNeighborEquiv f v)

omit [DecidableEq V] [DecidableEq W] in
/-- A simple-graph isomorphism preserves the number of even-degree vertices. -/
theorem card_even_eq (f : G ≃g H) :
    #{v : V | Even (G.degree v)} = #{w : W | Even (H.degree w)} := by
  classical
  apply Finset.card_bij (fun v _ => f v)
  · intro v hv
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
    have hd := SimpleGraph.Iso.degree_eq f v
    rw [← hd]
    exact hv
  · intro a _ b _ hab
    exact f.injective hab
  · intro w hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
    refine ⟨f.symm w, ?_, f.apply_symm_apply w⟩
    have hdegree : G.degree (f.symm w) = H.degree w := by
      calc
        G.degree (f.symm w) = H.degree (f (f.symm w)) :=
          SimpleGraph.Iso.degree_eq f (f.symm w)
        _ = H.degree w := by rw [f.apply_symm_apply]
    rw [hdegree]
    exact hw

omit [DecidableEq V] [DecidableEq W] in
/-- The SET predicate is invariant under simple-graph isomorphism. -/
theorem isSET_map (f : G ≃g H) (hset : IsSET G) : IsSET H where
  card_even := by
    rw [← SimpleGraph.Iso.card_even_eq f]
    exact hset.card_even
  even_clique := by
    intro a b ha hb hab
    have hda : G.degree (f.symm a) = H.degree a := by
      calc
        G.degree (f.symm a) = H.degree (f (f.symm a)) :=
          SimpleGraph.Iso.degree_eq f (f.symm a)
        _ = H.degree a := by rw [f.apply_symm_apply]
    have hdb : G.degree (f.symm b) = H.degree b := by
      calc
        G.degree (f.symm b) = H.degree (f (f.symm b)) :=
          SimpleGraph.Iso.degree_eq f (f.symm b)
        _ = H.degree b := by rw [f.apply_symm_apply]
    have ha' : Even (G.degree (f.symm a)) := by simpa [hda] using ha
    have hb' : Even (G.degree (f.symm b)) := by simpa [hdb] using hb
    have hab' : f.symm a ≠ f.symm b := fun e => hab (f.symm.injective e)
    have hAdj : G.Adj (f.symm a) (f.symm b) := hset.even_clique _ _ ha' hb' hab'
    simpa using f.map_adj_iff.mpr hAdj
  odd_neighbors := by
    intro w hw
    have hd : G.degree (f.symm w) = H.degree w := by
      calc
        G.degree (f.symm w) = H.degree (f (f.symm w)) :=
          SimpleGraph.Iso.degree_eq f (f.symm w)
        _ = H.degree w := by rw [f.apply_symm_apply]
    have hw' : Odd (G.degree (f.symm w)) := by rw [hd]; exact hw
    have hbound := hset.odd_neighbors (f.symm w) hw'
    rw [SimpleGraph.Iso.eDegree_eq f (f.symm w)] at hbound
    simpa using hbound

end SimpleGraph.Iso

end Gallai
