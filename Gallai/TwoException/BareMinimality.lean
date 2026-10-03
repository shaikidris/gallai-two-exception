/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.Foundations.Decomposition
public import Gallai.Foundations.Endpoints
public import Gallai.Inputs.OneException
public import Gallai.OddOrder
public import Gallai.Structure.EvenSubgraph

@[expose] public section

/-! # Lexicographic induction for the bare prescribed-vertex case

The paper's minimum-counterexample language ranges over graphs on differing
finite vertex types.  This module packages the corresponding induction: first
on the number of vertices, then on the number of edges at fixed order.  Later
bare-case reductions supply the predicate and the one-step proof.
-/

namespace Gallai.TwoException

universe u

/-- The literal hypothesis package for the first stage of the prescribed
endpoint theorem.  The designated vertex `h` is even, has positive ordinary
degree, and has no even neighbour; `x` is the sole permitted additional
E-degree exception. -/
def BareInstance {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h x : V) : Prop :=
  G.Connected ∧ h ≠ x ∧ 0 < G.degree h ∧ Even (G.degree h) ∧
    Even (G.degree x) ∧ eDegree G h = 0 ∧
    ∀ v, Even (G.degree v) → v ≠ h → v ≠ x → eDegree G v ≤ 3

/-- The exact endpoint conclusion required in the bare first stage. -/
def BareConclusion {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h : V) : Prop :=
  ∃ D : Decomposition G, D.size ≤ (Fintype.card V + 1) / 2 ∧
    2 ≤ D.endpointCount h

/-- Transport the bare endpoint conclusion across an explicit equality of
graphs.  Keeping this dependent transport named prevents cut consumers from
rewriting graph-indexed degree or endpoint expressions ad hoc. -/
theorem bareConclusion_congr {V : Type u} [Fintype V] [DecidableEq V]
    {G J : SimpleGraph V} [DecidableRel G.Adj] [DecidableRel J.Adj]
    (h : V) (e : G = J) : BareConclusion G h → BareConclusion J h := by
  subst J
  exact id

/-- A failure of the literal bare first-stage statement.  This is data for
the relative-minimality proof, not an assumed counterexample. -/
def BareCounterexample {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h x : V) : Prop :=
  BareInstance G h x ∧ ¬ BareConclusion G h

/-- The relative minimal-counterexample resource used by graph reductions in
the bare prescribed-endpoint argument.  It ranges over arbitrary finite vertex
types, because a deletion normally changes the type.  The strict order is
lexicographic in vertex count and then edge count at fixed order. -/
def BareMinimalCounterexample {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h x : V) : Prop :=
  BareCounterexample G h x ∧
  ∀ (W : Type u) [Fintype W] [DecidableEq W]
      (J : SimpleGraph W) [DecidableRel J.Adj] (u v : W),
    (Fintype.card W < Fintype.card V ∨
      (Fintype.card W = Fintype.card V ∧ J.edgeFinset.card < G.edgeFinset.card)) →
    BareInstance J u v → BareConclusion J u

/-- The underlying failure of a relative minimum counterexample. -/
theorem BareMinimalCounterexample.counterexample {V : Type u} [Fintype V]
    [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {h x : V}
    (H : BareMinimalCounterexample G h x) : BareCounterexample G h x := H.1

/-- Apply relative minimality to a vertex-smaller admissible bare instance. -/
theorem BareMinimalCounterexample.of_vertex_smaller {V : Type u} [Fintype V]
    [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {h x : V}
    (H : BareMinimalCounterexample G h x) (W : Type u) [Fintype W] [DecidableEq W]
    (J : SimpleGraph W) [DecidableRel J.Adj] (u v : W)
    (hsmall : Fintype.card W < Fintype.card V) (hJ : BareInstance J u v) :
    BareConclusion J u := H.2 W J u v (Or.inl hsmall) hJ

/-- Apply relative minimality to an edge-smaller admissible bare instance on
the same vertex order. -/
theorem BareMinimalCounterexample.of_edge_smaller {V : Type u} [Fintype V]
    [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {h x : V}
    (H : BareMinimalCounterexample G h x) (W : Type u) [Fintype W] [DecidableEq W]
    (J : SimpleGraph W) [DecidableRel J.Adj] (u v : W)
    (hcard : Fintype.card W = Fintype.card V)
    (hedge : J.edgeFinset.card < G.edgeFinset.card) (hJ : BareInstance J u v) :
    BareConclusion J u := H.2 W J u v (Or.inr ⟨hcard, hedge⟩) hJ

/-- Transport a complete bare-counterexample package across an explicit graph
equality.  `DecidableRel` is data rather than a proposition, so after graph
substitution the two instances are made definitionally identical using their
subsingleton property. -/
theorem bareCounterexample_congr {V : Type u} [Fintype V] [DecidableEq V]
    {G J : SimpleGraph V} [dG : DecidableRel G.Adj] [dJ : DecidableRel J.Adj]
    (h x : V) (e : G = J) : BareCounterexample G h x → BareCounterexample J h x := by
  subst J
  have hd : dG = dJ := Subsingleton.elim _ _
  cases hd
  intro H
  exact H

/-- Transport relative bare minimality across an explicit equality of graph
values.  The induction resource is graph-indexed through its edge order, so
the decidability instances are canonicalized after substitution rather than
rewritten implicitly by cut consumers. -/
theorem bareMinimalCounterexample_congr {V : Type u} [Fintype V] [DecidableEq V]
    {G J : SimpleGraph V} [dG : DecidableRel G.Adj] [dJ : DecidableRel J.Adj]
    (h x : V) (e : G = J) :
    BareMinimalCounterexample G h x → BareMinimalCounterexample J h x := by
  subst J
  have hd : dG = dJ := Subsingleton.elim _ _
  cases hd
  intro H
  exact H

/-- Transport an even-degree fact across an explicit graph equality, with the
same explicit canonicalization of graph-indexed decidability data. -/
theorem even_degree_congr {V : Type u} [Fintype V] [DecidableEq V]
    {G J : SimpleGraph V} [dG : DecidableRel G.Adj] [dJ : DecidableRel J.Adj]
    (v : V) (e : G = J) : Even (G.degree v) → Even (J.degree v) := by
  subst J
  have hd : dG = dJ := Subsingleton.elim _ _
  cases hd
  intro hv
  exact hv

/-- A bare prescribed vertex has no edge to the other designated even
vertex.  This is the precise reason the nonadjacent odd-order input is
available in the bare stage. -/
theorem BareInstance.not_adjacent {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {h x : V}
    (H : BareInstance G h x) : ¬ G.Adj h x := by
  intro hAdj
  have hmem : x ∈ evenNeighbors G h := (mem_evenNeighbors h x).mpr ⟨hAdj, H.2.2.2.2.1⟩
  have hzero := H.2.2.2.2.2.1
  change (evenNeighbors G h).card = 0 at hzero
  have hpos : 0 < (evenNeighbors G h).card := Finset.card_pos.mpr ⟨x, hmem⟩
  omega

/-- The inherited odd-order simultaneous theorem rules out a bare
counterexample of odd order. -/
theorem BareCounterexample.card_even {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {h x : V}
    (H : BareCounterexample G h x) : Even (Fintype.card V) := by
  apply Nat.not_odd_iff_even.mp
  intro hodd
  obtain ⟨m, hm⟩ := hodd
  obtain ⟨D, hsize, hh, hx⟩ := odd_order_two_exception_of_cap m hm H.1.1 h x
    H.1.2.1 H.1.not_adjacent H.1.2.2.2.1 H.1.2.2.2.2.1 H.1.2.2.2.2.2.2
  apply H.2
  refine ⟨D, ?_, hh⟩
  rw [hm]
  omega

/-- The second designated vertex is an actual exception in a bare
counterexample.  Otherwise the one-exception endpoint theorem applies at
the prescribed bare vertex `h` and directly contradicts the failure. -/
theorem BareCounterexample.exception_gt_three {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {h x : V}
    (H : BareCounterexample G h x) : 3 < eDegree G x := by
  by_contra hn
  have hxcap : eDegree G x ≤ 3 := Nat.le_of_not_gt hn
  have hcap : ∀ v, Even (G.degree v) → v ≠ h → eDegree G v ≤ 3 := by
    intro v hv hvh
    by_cases hvx : v = x
    · subst v
      exact hxcap
    · exact H.1.2.2.2.2.2.2 v hv hvh hvx
  obtain ⟨D, hsize, hh⟩ := one_exception_endpoint G h H.1.1 H.1.2.2.1
    H.1.2.2.2.1 hcap
  exact H.2 ⟨D, hsize, hh⟩

/-- Induction over finite simple graphs ordered lexicographically by vertex
cardinality and then edge cardinality.  The vertex-smaller hypothesis ranges
over arbitrary finite types; the edge-smaller hypothesis stays on the current
vertex type. -/
theorem lexicographic_finite_graph_induction
    (Q : ∀ {V : Type u} [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj], Prop)
    (step : ∀ (n : ℕ) (V : Type u) [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj],
      Fintype.card V = n →
      (∀ (m : ℕ), m < n → ∀ (W : Type u) [Fintype W] [DecidableEq W]
        (J : SimpleGraph W) [DecidableRel J.Adj], Fintype.card W = m → Q J) →
      (∀ (J : SimpleGraph V) [DecidableRel J.Adj],
        J.edgeFinset.card < G.edgeFinset.card → Q J) →
      Q G) :
    ∀ (V : Type u) [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj], Q G := by
  intro V _ _ G _
  have hall : ∀ n : ℕ, ∀ (W : Type u) [Fintype W] [DecidableEq W]
      (J : SimpleGraph W) [DecidableRel J.Adj], Fintype.card W = n → Q J := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n hn =>
      intro W _ _ J _ hW
      have hedge : ∀ e : ℕ, ∀ (K : SimpleGraph W) [DecidableRel K.Adj],
          K.edgeFinset.card = e → Q K := by
        intro e
        induction e using Nat.strong_induction_on with
        | h e ihe =>
          intro K _ hK
          apply step n W K hW
          · intro m hm U _ _ L _ hU
            exact hn m hm U L hU
          · intro L _ hL
            exact ihe L.edgeFinset.card (by omega) L rfl
      exact hedge J.edgeFinset.card J rfl
  exact hall (Fintype.card V) V G rfl

end Gallai.TwoException
