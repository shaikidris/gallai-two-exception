/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.Foundations.EndpointBounds
public import Mathlib.Algebra.BigOperators.Ring.Finset

@[expose] public section

/-!
# Exact terminal and through-carrier counts

Endpoint parity alone does not classify the number of local runs. Unique
edge coverage and simplicity give the stronger degree identity: every
terminal carrier uses one spoke and every through carrier uses two.
-/

namespace Gallai

open scoped Finset

universe u

variable {V : Type u} {G : SimpleGraph V} [DecidableEq V]

/-- Each visit of a walk accounts for two incidences, except at its two ends. -/
theorem walk_incident_balance {a b : V} (P : G.Walk a b) (x : V) :
    P.edges.countP (fun e => x ∈ e) +
      (if a = x then 1 else 0) + (if b = x then 1 else 0) =
      2 * P.support.count x := by
  induction P with
  | @nil a =>
    by_cases h : a = x
    · subst a
      simp
    · simp [h]
  | @cons a b c hab P ih =>
    have habne := hab.ne
    by_cases ha : a = x <;> by_cases hb : b = x
    all_goals
      have ha' : x = a ↔ a = x := eq_comm
      have hb' : x = b ↔ b = x := eq_comm
      simp_all [SimpleGraph.Walk.edges_cons, SimpleGraph.Walk.support_cons,
        Sym2.mem_iff] <;> omega

/-- A simple nonempty path uses one incident edge at an end and two internally. -/
theorem NonemptyPath.incident_eq_endpoint_add_internal (P : NonemptyPath G) (x : V) :
    P.walk.edges.countP (fun e => x ∈ e) =
      ((if P.start = x then 1 else 0) + (if P.finish = x then 1 else 0)) +
      2 * (if x ∈ P.walk.support ∧ P.start ≠ x ∧ P.finish ≠ x then 1 else 0) := by
  have h := walk_incident_balance P.walk x
  have hne := P.start_ne_finish G
  by_cases hx : x ∈ P.walk.support
  · have hc := List.count_eq_one_of_mem P.isPath.support_nodup hx
    rw [hc] at h
    by_cases hs : P.start = x <;> by_cases ht : P.finish = x <;>
      simp_all
  · have hc := List.count_eq_zero_of_not_mem hx
    rw [hc] at h
    have hs : P.start ≠ x := fun heq => hx (heq ▸ P.walk.start_mem_support)
    have ht : P.finish ≠ x := fun heq => hx (heq ▸ P.walk.end_mem_support)
    simp only [hx, hs, ht, if_false, false_and] at h ⊢
    omega

/-- Number of decomposition paths containing a vertex internally. -/
def Decomposition.throughCount (D : Decomposition G) (x : V) : ℕ :=
  ∑ i : Fin D.size, if x ∈ (D.path i).walk.support ∧
    (D.path i).start ≠ x ∧ (D.path i).finish ≠ x then 1 else 0

/-- Actual indices of the carriers ending at a given vertex. -/
def Decomposition.terminalCarriers (D : Decomposition G) (x : V) : Finset (Fin D.size) :=
  Finset.univ.filter (fun i => (D.path i).start = x ∨ (D.path i).finish = x)

/-- Actual indices of the carriers passing internally through a given vertex. -/
def Decomposition.throughCarriers (D : Decomposition G) (x : V) : Finset (Fin D.size) :=
  Finset.univ.filter (fun i => x ∈ (D.path i).walk.support ∧
    (D.path i).start ≠ x ∧ (D.path i).finish ≠ x)

/-- Since a nonempty path has distinct ends, endpoint multiplicity counts carriers. -/
theorem Decomposition.card_terminalCarriers (D : Decomposition G) (x : V) :
    #(D.terminalCarriers x) = D.endpointCount x := by
  rw [terminalCarriers, Finset.card_filter]
  apply Finset.sum_congr rfl
  intro i _
  have hne := (D.path i).start_ne_finish G
  by_cases hs : (D.path i).start = x <;> by_cases ht : (D.path i).finish = x <;>
    simp_all

/-- The through count is the cardinality of the actual through-carrier index set. -/
theorem Decomposition.card_throughCarriers (D : Decomposition G) (x : V) :
    #(D.throughCarriers x) = D.throughCount x := by
  rw [throughCarriers, Finset.card_filter]
  rfl

/-- A carrier cannot both end at a vertex and pass internally through it. -/
theorem Decomposition.disjoint_terminal_through (D : Decomposition G) (x : V) :
    Disjoint (D.terminalCarriers x) (D.throughCarriers x) := by
  apply Finset.disjoint_left.mpr
  intro i hi hj
  simp only [terminalCarriers, throughCarriers, Finset.mem_filter,
    Finset.mem_univ, true_and] at hi hj
  exact hi.elim hj.2.1 hj.2.2

/-- The two index sets exhaust precisely the carriers containing the vertex. -/
theorem Decomposition.mem_support_iff_terminal_or_through (D : Decomposition G)
    (x : V) (i : Fin D.size) :
    x ∈ (D.path i).walk.support ↔
      i ∈ D.terminalCarriers x ∨ i ∈ D.throughCarriers x := by
  simp only [terminalCarriers, throughCarriers, Finset.mem_filter,
    Finset.mem_univ, true_and]
  constructor
  · intro hx
    by_cases hs : (D.path i).start = x
    · exact Or.inl (Or.inl hs)
    by_cases ht : (D.path i).finish = x
    · exact Or.inl (Or.inr ht)
    exact Or.inr ⟨hx, hs, ht⟩
  · rintro ((hs | ht) | hthrough)
    · exact hs ▸ (D.path i).walk.start_mem_support
    · exact ht ▸ (D.path i).walk.end_mem_support
    · exact hthrough.1

variable [Fintype V] [DecidableRel G.Adj]

/-- Terminal and through carriers account for every incident edge exactly once. -/
theorem Decomposition.degree_eq_endpoint_add_twice_through (D : Decomposition G) (x : V) :
    G.degree x = D.endpointCount x + 2 * D.throughCount x := by
  rw [D.degree_eq_sum_incident x]
  simp_rw [NonemptyPath.incident_eq_endpoint_add_internal]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  rfl

/-- A degree-four hub has exactly one of the three terminal/through profiles. -/
theorem Decomposition.degree_four_carrier_profiles (D : Decomposition G) (x : V)
    (hdegree : G.degree x = 4) :
    (D.endpointCount x = 0 ∧ D.throughCount x = 2) ∨
    (D.endpointCount x = 2 ∧ D.throughCount x = 1) ∨
    (D.endpointCount x = 4 ∧ D.throughCount x = 0) := by
  have h := D.degree_eq_endpoint_add_twice_through x
  omega

end Gallai
