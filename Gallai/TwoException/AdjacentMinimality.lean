/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.Foundations.Decomposition
public import Gallai.Foundations.Endpoints
public import Gallai.Structure.EvenSubgraph
public import Gallai.Structure.EvenSubgraphInduce

@[expose] public section

/-!
# Minimality interface for Xie's adjacent-two-exception theorem

Xie Theorem 1.4 proves two *separate* endpoint conclusions: one decomposition
exposes the first adjacent exception, and possibly another exposes the second.
This file records that exact conclusion and the lexicographic
minimum-counterexample resource used by the source proof.  It is deliberately
independent of the later bare prescribed-endpoint theorem.

The first consumers are the two parity branches of the source's Claim 1
(an even vertex cannot be a cut vertex in a minimum counterexample).
-/

namespace Gallai.TwoException

universe u

/-- Xie's literal adjacent-two-exception hypothesis. -/
def AdjacentInstance {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x y : V) : Prop :=
  G.Connected ∧ x ≠ y ∧ G.Adj x y ∧
    Even (G.degree x) ∧ Even (G.degree y) ∧
    ∀ v, Even (G.degree v) → v ≠ x → v ≠ y → eDegree G v ≤ 3

/-- The exact two-output conclusion of Xie Theorem 1.4. -/
def AdjacentConclusion {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x y : V) : Prop :=
  (∃ D : Decomposition G, D.size ≤ (Fintype.card V + 1) / 2 ∧
      2 ≤ D.endpointCount x) ∧
  (∃ D : Decomposition G, D.size ≤ (Fintype.card V + 1) / 2 ∧
      2 ≤ D.endpointCount y)

/-- Swapping the named adjacent exceptions swaps the two independent source
conclusions. -/
theorem AdjacentInstance.swap {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {x y : V}
    (H : AdjacentInstance G x y) : AdjacentInstance G y x := by
  refine ⟨H.1, H.2.1.symm, H.2.2.1.symm, H.2.2.2.2.1, H.2.2.2.1, ?_⟩
  intro v hv hvy hvx
  exact H.2.2.2.2.2 v hv hvx hvy

/-- The adjacent endpoint conclusion is symmetric in its two named vertices. -/
theorem AdjacentConclusion.swap {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {x y : V}
    (H : AdjacentConclusion G x y) : AdjacentConclusion G y x :=
  ⟨H.2, H.1⟩

/-- Transport the two independent decomposition outputs across equality of the
ambient graph. This substitutes the graph before identifying its
adjacency-decision instances. -/
theorem AdjacentConclusion.congr {V : Type u} [Fintype V] [DecidableEq V]
    {G J : SimpleGraph V} [dG : DecidableRel G.Adj] [dJ : DecidableRel J.Adj]
    (x y : V) (e : G = J) : AdjacentConclusion G x y → AdjacentConclusion J x y := by
  subst J
  have hd : dG = dJ := Subsingleton.elim _ _
  cases hd
  intro H
  exact H

/-- Transport Xie's adjacent hypothesis across an explicit equality of graph
values.  Graph-indexed degree data depends on `DecidableRel`, so the two
instances are canonicalized after substitution instead of rewritten inside
cut consumers. -/
theorem AdjacentInstance.congr {V : Type u} [Fintype V] [DecidableEq V]
    {G J : SimpleGraph V} [dG : DecidableRel G.Adj] [dJ : DecidableRel J.Adj]
    (x y : V) (e : G = J) : AdjacentInstance G x y → AdjacentInstance J x y := by
  subst J
  have hd : dG = dJ := Subsingleton.elim _ _
  cases hd
  intro H
  exact H

/-- Transport an even-degree fact across a graph equality for the adjacent
development.  Keeping this dependency-sensitive step named avoids choosing
different adjacency-decision instances in degree calculations. -/
theorem adjacent_even_degree_congr {V : Type u} [Fintype V] [DecidableEq V]
    {G J : SimpleGraph V} [dG : DecidableRel G.Adj] [dJ : DecidableRel J.Adj]
    (v : V) (e : G = J) : Even (G.degree v) → Even (J.degree v) := by
  subst J
  have hd : dG = dJ := Subsingleton.elim _ _
  cases hd
  intro hv
  exact hv

/-- The adjacent hypothesis transports to an induced subtype when the graph
already has no support outside that subtype.  Connectivity is intentionally a
separate premise: the source's Claim 1 obtains it from the actual cut-piece
construction rather than from degree bookkeeping. -/
theorem adjacentInstance_induce_of_support_subset {V : Type u} [Fintype V]
    [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {x y : V}
    (H : AdjacentInstance G x y) (S : Set V) [DecidablePred (· ∈ S)]
    (hs : G.support ⊆ S) (hxS : x ∈ S) (hyS : y ∈ S)
    (hconn : (G.induce S).Connected) :
    AdjacentInstance (G.induce S) ⟨x, hxS⟩ ⟨y, hyS⟩ := by
  rcases H with ⟨_, hne, hxy, hxEven, hyEven, hcap⟩
  refine ⟨hconn, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun h => hne (Subtype.ext_iff.mp h)
  · exact hxy
  · rw [SimpleGraph.degree_induce_of_support_subset hs]
    exact hxEven
  · rw [SimpleGraph.degree_induce_of_support_subset hs]
    exact hyEven
  · intro v hv hvx hvy
    rw [eDegree_induce_of_support_subset G S hs v]
    apply hcap v.val ?_ (fun h => hvx (Subtype.ext h)) (fun h => hvy (Subtype.ext h))
    rwa [SimpleGraph.degree_induce_of_support_subset hs v] at hv

/-- Failure of the full two-output adjacent conclusion. -/
def AdjacentCounterexample {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x y : V) : Prop :=
  AdjacentInstance G x y ∧ ¬ AdjacentConclusion G x y

/-- A lexicographic minimum-counterexample resource used by the first cut
experiments.  It is useful for subtype reductions, but is deliberately kept
separate from Xie's source-faithful edge-minimal resource below: the published
proof also applies minimality after adjoining a fresh leaf. -/
def AdjacentMinimalCounterexample {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x y : V) : Prop :=
  AdjacentCounterexample G x y ∧
  ∀ (W : Type u) [Fintype W] [DecidableEq W]
      (J : SimpleGraph W) [DecidableRel J.Adj] (u v : W),
    (Fintype.card W < Fintype.card V ∨
      (Fintype.card W = Fintype.card V ∧ J.edgeFinset.card < G.edgeFinset.card)) →
    AdjacentInstance J u v → AdjacentConclusion J u v

/-- Extract the failed source theorem from the minimum-counterexample package. -/
theorem AdjacentMinimalCounterexample.counterexample {V : Type u} [Fintype V]
    [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {x y : V}
    (H : AdjacentMinimalCounterexample G x y) : AdjacentCounterexample G x y := H.1

/-- Transport the complete minimal-counterexample package across equality of
the ambient graph.  As for the conclusion transport, substitute first so the
graph-indexed adjacency-decision instances become definitionally identical. -/
theorem AdjacentMinimalCounterexample.congr {V : Type u} [Fintype V]
    [DecidableEq V] {G J : SimpleGraph V} [dG : DecidableRel G.Adj]
    [dJ : DecidableRel J.Adj] (x y : V) (e : G = J) :
    AdjacentMinimalCounterexample G x y → AdjacentMinimalCounterexample J x y := by
  subst J
  have hd : dG = dJ := Subsingleton.elim _ _
  cases hd
  intro H
  exact H

/-- Invoke adjacent minimality on a strictly smaller vertex type. -/
theorem AdjacentMinimalCounterexample.of_vertex_smaller {V : Type u} [Fintype V]
    [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {x y : V}
    (H : AdjacentMinimalCounterexample G x y) (W : Type u) [Fintype W] [DecidableEq W]
    (J : SimpleGraph W) [DecidableRel J.Adj] (u v : W)
    (hsmall : Fintype.card W < Fintype.card V) (hJ : AdjacentInstance J u v) :
    AdjacentConclusion J u v := H.2 W J u v (Or.inl hsmall) hJ

/-- Invoke adjacent minimality on an edge-smaller graph of the same order. -/
theorem AdjacentMinimalCounterexample.of_edge_smaller {V : Type u} [Fintype V]
    [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {x y : V}
    (H : AdjacentMinimalCounterexample G x y) (J : SimpleGraph V) [DecidableRel J.Adj]
    (u v : V) (hcard : Fintype.card V = Fintype.card V)
    (hedge : J.edgeFinset.card < G.edgeFinset.card) (hJ : AdjacentInstance J u v) :
    AdjacentConclusion J u v := H.2 V J u v (Or.inr ⟨hcard, hedge⟩) hJ

/-- Xie's actual minimum-counterexample resource: every recursive graph with
strictly fewer edges is admissible, even when it lives on a changed finite
vertex type.  This is the form needed for the source's fresh-leaf auxiliaries;
it is intentionally distinct from `AdjacentMinimalCounterexample`. -/
def AdjacentEdgeMinimalCounterexample {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x y : V) : Prop :=
  AdjacentCounterexample G x y ∧
  ∀ (W : Type u) [Fintype W] [DecidableEq W]
      (J : SimpleGraph W) [DecidableRel J.Adj] (u v : W),
    J.edgeFinset.card < G.edgeFinset.card →
    AdjacentInstance J u v → AdjacentConclusion J u v

/-- Extract the failed adjacent theorem from the source-faithful edge-minimal
resource. -/
theorem AdjacentEdgeMinimalCounterexample.counterexample {V : Type u} [Fintype V]
    [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {x y : V}
    (H : AdjacentEdgeMinimalCounterexample G x y) : AdjacentCounterexample G x y := H.1

/-- The source edge-minimal resource is symmetric in its two designated
adjacent exceptions.  Its two independent endpoint outputs are swapped, while
the strict edge comparison is unchanged. -/
theorem adjacentEdgeMinimalCounterexample_swap {V : Type u} [Fintype V]
    [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {x y : V}
    (H : AdjacentEdgeMinimalCounterexample G x y) :
    AdjacentEdgeMinimalCounterexample G y x := by
  refine ⟨?_, ?_⟩
  · refine ⟨H.1.1.swap, ?_⟩
    intro h
    exact H.1.2 h.swap
  · intro W _ _ J _ u v hsmall hJ
    exact (H.2 W J v u hsmall hJ.swap).swap

/-- Transport Xie's source-faithful edge-minimal package across equality of
the ambient graph.  Substitution canonicalizes the graph-indexed finite-edge
instances before the recursive edge comparison is consumed. -/
theorem AdjacentEdgeMinimalCounterexample.congr {V : Type u} [Fintype V]
    [DecidableEq V] {G J : SimpleGraph V} [dG : DecidableRel G.Adj]
    [dJ : DecidableRel J.Adj] (x y : V) (e : G = J) :
    AdjacentEdgeMinimalCounterexample G x y → AdjacentEdgeMinimalCounterexample J x y := by
  subst J
  have hd : dG = dJ := Subsingleton.elim _ _
  cases hd
  intro H
  exact H

/-- Invoke source-faithful adjacent minimality on any finite graph with fewer
edges, including a graph on a fresh-vertex extension type. -/
theorem AdjacentEdgeMinimalCounterexample.of_edge_smaller {V : Type u} [Fintype V]
    [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {x y : V}
    (H : AdjacentEdgeMinimalCounterexample G x y) (W : Type u) [Fintype W]
    [DecidableEq W] (J : SimpleGraph W) [DecidableRel J.Adj] (u v : W)
    (hedge : J.edgeFinset.card < G.edgeFinset.card) (hJ : AdjacentInstance J u v) :
    AdjacentConclusion J u v := H.2 W J u v hedge hJ

/-- Strong induction on edge count across arbitrary finite vertex types.  This
is the induction principle matching Xie's published edge-minimal proof. -/
theorem adjacent_edge_finite_graph_induction
    (Q : ∀ {V : Type u} [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj], Prop)
    (step : ∀ (n : ℕ) (V : Type u) [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj],
      G.edgeFinset.card = n →
      (∀ (W : Type u) [Fintype W] [DecidableEq W]
        (J : SimpleGraph W) [DecidableRel J.Adj],
        J.edgeFinset.card < n → Q J) →
      Q G) :
    ∀ (V : Type u) [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj], Q G := by
  intro V _ _ G _
  have hall : ∀ n : ℕ, ∀ (W : Type u) [Fintype W] [DecidableEq W]
      (J : SimpleGraph W) [DecidableRel J.Adj], J.edgeFinset.card = n → Q J := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro W _ _ J _ hJ
      apply step n W J hJ
      intro U _ _ K _ hK
      exact ih K.edgeFinset.card (by omega) U K rfl
  exact hall G.edgeFinset.card V G rfl

/-- Lexicographic induction on finite simple graphs, in the exact order used
by the published adjacent-theorem proof. -/
theorem adjacent_lexicographic_finite_graph_induction
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
