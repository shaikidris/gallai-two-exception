/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.Operations.Reversal
public import Gallai.Foundations.Endpoints
public import Mathlib.Combinatorics.SimpleGraph.Operations
public import Lean.Elab.Tactic.Omega

@[expose] public section

/-!
# Direct addition at an avoiding endpoint carrier

This is the terminating (length-one) branch of Fan's path-sequence proof.
The hypothesis is actual support avoidance, not merely distinct endpoints.
The general single-edge addibility lemma still requires the sequence argument.
-/

namespace Gallai

universe u

variable {V : Type u} {G : SimpleGraph V}

/-- Prepend an edge to a path that avoids its new initial vertex. -/
def NonemptyPath.prependFresh (P : NonemptyPath G) (a : V)
    (ha : a ∉ P.walk.support) : NonemptyPath (G ⊔ SimpleGraph.edge a P.start) where
  start := a
  finish := P.finish
  walk := .cons (Or.inr (by
    have hne : a ≠ P.start := fun h => ha (h ▸ P.walk.start_mem_support)
    change (SimpleGraph.edge a P.start).Adj a P.start
    rw [← SimpleGraph.mem_edgeSet, SimpleGraph.edgeSet_edge_of_ne hne]
    exact Set.mem_singleton _))
    (P.walk.transfer (G ⊔ SimpleGraph.edge a P.start) (fun _ he => by
      exact SimpleGraph.edgeSet_mono le_sup_left (P.walk.edges_subset_edgeSet he)))
  isPath := by
    apply SimpleGraph.Walk.IsPath.mk'
    simpa only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_transfer] using
      List.nodup_cons.mpr ⟨ha, P.isPath.support_nodup⟩
  nonempty := SimpleGraph.Walk.not_nil_cons

/-- Direct extension adds exactly its new edge to the carrier's edge list. -/
@[simp] theorem NonemptyPath.prependFresh_edges (P : NonemptyPath G) (a : V)
    (ha : a ∉ P.walk.support) :
    (P.prependFresh a ha).walk.edges = s(a, P.start) :: P.walk.edges := by
  simp only [prependFresh, SimpleGraph.Walk.edges_cons, SimpleGraph.Walk.edges_transfer]

namespace Decomposition

variable [DecidableEq V]

def addFamily (D : Decomposition G) (i : Fin D.size) (a : V)
    (ha : a ∉ (D.path i).walk.support) (j : Fin D.size) :
    NonemptyPath (G ⊔ SimpleGraph.edge a (D.path i).start) :=
  if j = i then (D.path i).prependFresh a ha else
    (D.path j).transfer _ (fun _ he => by
      exact SimpleGraph.edgeSet_mono le_sup_left ((D.path j).walk.edges_subset_edgeSet he))

omit [DecidableEq V] in
theorem addFamily_mem_edges (D : Decomposition G) (i j : Fin D.size) (a : V)
    (ha : a ∉ (D.path i).walk.support) (e : Sym2 V) :
    e ∈ (addFamily D i a ha j).walk.edges ↔
      e ∈ (D.path j).walk.edges ∨ (j = i ∧ e = s(a, (D.path i).start)) := by
  by_cases hji : j = i
  · subst j
    have hp : addFamily D i a ha i = (D.path i).prependFresh a ha := by
      unfold addFamily
      exact if_pos rfl
    rw [congrArg (fun P : NonemptyPath _ => P.walk.edges) hp]
    simp [or_comm]
  · have he : (addFamily D i a ha j).walk.edges = (D.path j).walk.edges := by
      unfold addFamily
      rw [if_neg hji]
      exact NonemptyPath.transfer_edges ..
    rw [he]
    simp [hji]

/-- Extend one avoiding initial carrier by a missing edge, preserving unique coverage. -/
def addAtStart (D : Decomposition G) (i : Fin D.size) (a : V)
    (ha : a ∉ (D.path i).walk.support) (hmissing : ¬ G.Adj a (D.path i).start) :
    Decomposition (G ⊔ SimpleGraph.edge a (D.path i).start) where
  size := D.size
  path := addFamily D i a ha
  covers := by
    have hne : a ≠ (D.path i).start :=
      fun h => ha (h ▸ (D.path i).walk.start_mem_support)
    have hab : s(a, (D.path i).start) ∉ G.edgeSet := hmissing
    intro e he
    rw [SimpleGraph.edgeSet_sup, SimpleGraph.edgeSet_edge_of_ne hne] at he
    rcases he with he | he
    · obtain ⟨j, hj, hu⟩ := D.covers e he
      refine ⟨j, (addFamily_mem_edges D i j a ha e).mpr (Or.inl hj), ?_⟩
      intro k hk
      rcases (addFamily_mem_edges D i k a ha e).mp hk with hk | ⟨_, heq⟩
      · exact hu k hk
      · exact False.elim (hab (heq ▸ he))
    · have heq : e = s(a, (D.path i).start) := he
      subst e
      refine ⟨i, (addFamily_mem_edges D i i a ha _).mpr (Or.inr ⟨rfl, rfl⟩), ?_⟩
      intro k hk
      rcases (addFamily_mem_edges D i k a ha _).mp hk with hk | ⟨hki, _⟩
      · exact False.elim (hab ((D.path k).walk.edges_subset_edgeSet hk))
      · exact hki

omit [DecidableEq V] in
/-- Direct extension changes no carrier count. -/
@[simp] theorem addAtStart_size (D : Decomposition G) (i : Fin D.size) (a : V)
    (ha : a ∉ (D.path i).walk.support) (hmissing : ¬ G.Adj a (D.path i).start) :
    (D.addAtStart i a ha hmissing).size = D.size := rfl

/-- The same output witness moves exactly one endpoint from the donor to the new vertex. -/
theorem addAtStart_endpointCount (D : Decomposition G) (i : Fin D.size) (a w : V)
    (ha : a ∉ (D.path i).walk.support) (hmissing : ¬ G.Adj a (D.path i).start) :
    (D.addAtStart i a ha hmissing).endpointCount w +
        (if (D.path i).start = w then 1 else 0) =
      D.endpointCount w + if a = w then 1 else 0 := by
  let ends {K : SimpleGraph V} (P : NonemptyPath K) :=
    (if P.start = w then 1 else 0) + (if P.finish = w then 1 else 0 : ℕ)
  have hsum :
      (∑ j : Fin D.size, (ends (addFamily D i a ha j) +
        if j = i then (if (D.path i).start = w then 1 else 0) else 0)) =
      ∑ j : Fin D.size, (ends (D.path j) +
        if j = i then (if a = w then 1 else 0) else 0) := by
    apply Finset.sum_congr rfl
    intro j _
    by_cases hji : j = i
    · subst j
      simp only [addFamily, ends, NonemptyPath.prependFresh, if_true]
      omega
    · simp [addFamily, hji, ends, NonemptyPath.transfer]
  simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true] at hsum
  exact hsum

/-- An avoiding carrier at either donor endpoint gives the exact direct-addition certificate. -/
theorem exists_add_of_avoiding_endpoint (D : Decomposition G) (i : Fin D.size) (a b : V)
    (hb : (D.path i).start = b ∨ (D.path i).finish = b)
    (ha : a ∉ (D.path i).walk.support) (hmissing : ¬ G.Adj a b) :
    ∃ E : Decomposition (G ⊔ SimpleGraph.edge a b), E.size = D.size ∧
      ∀ w, E.endpointCount w + (if b = w then 1 else 0) =
        D.endpointCount w + if a = w then 1 else 0 := by
  rcases hb with hb | hb
  · subst b
    exact ⟨D.addAtStart i a ha hmissing, rfl,
      fun w => D.addAtStart_endpointCount i a w ha hmissing⟩
  · subst b
    have hr : a ∉ (D.reverse.path i).walk.support := by
      simpa only [reverse, NonemptyPath.reverse, SimpleGraph.Walk.support_reverse,
        List.mem_reverse] using ha
    refine ⟨D.reverse.addAtStart i a hr hmissing, rfl, ?_⟩
    intro w
    have h := D.reverse.addAtStart_endpointCount i a w hr hmissing
    rw [reverse_endpointCount] at h
    convert h using 1
    rfl

end Decomposition

end Gallai
