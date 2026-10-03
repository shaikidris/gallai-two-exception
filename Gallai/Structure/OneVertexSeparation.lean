/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.Structure.OneVertexUnion
public import Gallai.Structure.EvenSubgraphInduce
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

@[expose] public section

/-! # Connectivity and strict induction size at a one-vertex separation

The remainder is restricted to its actual vertex set. Excursions in the left
piece can only return to that set at the joint, so they do not connect distinct
remainder components. No connectedness of either piece is assumed.
-/

namespace Gallai

universe u
variable {V : Type u} (G H : SimpleGraph V) (T : Set V) (u : V)

/-- A connected union forces the remainder to be connected on its own vertices
when the other piece meets that vertex set only at the joint. -/
theorem connected_right_of_one_vertex_separation
    (hconn : (G ⊔ H).Connected) (hu : u ∈ T)
    (hH : ∀ a b, H.Adj a b → a ∈ T)
    (hG : ∀ a b, G.Adj a b → a ∈ T → a = u) :
    (H.induce T).Connected := by
  have transport : ∀ {a b : V}, (G ⊔ H).Walk a b →
      (∀ ha : a ∈ T, (H.induce T).Reachable ⟨u, hu⟩ ⟨a, ha⟩) →
      ∀ hb : b ∈ T, (H.induce T).Reachable ⟨u, hu⟩ ⟨b, hb⟩ := by
    intro a b p
    induction p with
    | nil => exact fun ha => ha
    | @cons a b c hab p ih =>
      intro ha hc
      apply ih ?_ hc
      intro hb
      rcases hab with hg | hh
      · have he := hG b a hg.symm hb
        subst b
        exact SimpleGraph.Reachable.refl _
      · exact (ha (hH a b hh)).trans
          (show (H.induce T).Adj ⟨a, hH a b hh⟩ ⟨b, hb⟩ from hh).reachable
  have hr (v : T) : (H.induce T).Reachable ⟨u, hu⟩ v := by
    obtain ⟨p⟩ := hconn u v.val
    exact transport p (fun _ => SimpleGraph.Reachable.refl _) v.property
  let : Nonempty T := ⟨⟨u, hu⟩⟩
  exact ⟨fun a b => (hr a).symm.trans (hr b)⟩

/-- A nontrivial remainder has a genuine edge at the joint, as required by
hanging absorption; the premise is about vertices, not a chosen carrier. -/
theorem joint_neighbor_of_one_vertex_separation
    (hconn : (G ⊔ H).Connected) (hu : u ∈ T)
    (hH : ∀ a b, H.Adj a b → a ∈ T)
    (hG : ∀ a b, G.Adj a b → a ∈ T → a = u)
    (hother : ∃ v ∈ T, v ≠ u) : ∃ w, H.Adj u w := by
  have hc := connected_right_of_one_vertex_separation G H T u hconn hu hH hG
  obtain ⟨v, hv, hne⟩ := hother
  obtain ⟨p⟩ := hc ⟨u, hu⟩ ⟨v, hv⟩
  cases p with
  | nil => exact (hne rfl).elim
  | cons hadj _ => exact ⟨_, hadj⟩

variable [Fintype V] [DecidableEq V] [DecidablePred (· ∈ T)]
variable [DecidableRel G.Adj] [DecidableRel H.Adj]

/-- A nonempty left piece makes the actual remainder strictly smaller in edges.
This is the strict measure comparison needed by minimal-edge induction. -/
theorem right_edge_count_lt_of_one_vertex_separation
    (hH : ∀ a b, H.Adj a b → a ∈ T)
    (hG : ∀ a b, G.Adj a b → a ∈ T → a = u)
    (hleft : ∃ a b, G.Adj a b) :
    (H.induce T).edgeFinset.card < (G ⊔ H).edgeFinset.card := by
  have hs : H.support ⊆ T := by
    rintro v ⟨w, hw⟩
    exact hH v w hw
  rw [SimpleGraph.card_edgeFinset_induce_of_support_subset hs]
  apply Finset.card_lt_card
  apply SimpleGraph.edgeFinset_strict_mono
  refine lt_of_le_not_ge le_sup_right ?_
  intro hle
  obtain ⟨a, b, hab⟩ := hleft
  have hh : H.Adj a b := hle (Or.inl hab)
  have ha := hG a b hab (hH a b hh)
  have hb := hG b a hab.symm (hH b a hh.symm)
  exact hab.ne (ha.trans hb.symm)

/-- The actual smaller remainder satisfies all graph hypotheses for the next
minimal-edge induction call under the favourable joint parity. -/
theorem smaller_remainder_of_one_vertex_separation
    (hconn : (G ⊔ H).Connected) (hu : u ∈ T)
    (hH : ∀ a b, H.Adj a b → a ∈ T)
    (hG : ∀ a b, G.Adj a b → a ∈ T → a = u)
    (hleft : ∃ a b, G.Adj a b)
    (hparity : Even ((G ⊔ H).degree u) ∨ Odd (H.degree u)) (c : ℕ)
    (hcap : ∀ v, Even ((G ⊔ H).degree v) → eDegree (G ⊔ H) v ≤ c) :
    (H.induce T).Connected ∧
      (H.induce T).edgeFinset.card < (G ⊔ H).edgeFinset.card ∧
      ∀ v, Even ((H.induce T).degree v) → eDegree (H.induce T) v ≤ c := by
  refine ⟨connected_right_of_one_vertex_separation G H T u hconn hu hH hG,
    right_edge_count_lt_of_one_vertex_separation G H T u hH hG hleft, ?_⟩
  have hs : H.support ⊆ T := by
    rintro v ⟨w, hw⟩
    exact hH v w hw
  apply even_degree_cap_induce_of_support_subset H T hs c
  apply even_degree_cap_one_vertex_union G H u c ?_ hparity hcap
  intro w hwG hwH
  obtain ⟨a, ha⟩ := hwG
  obtain ⟨b, hb⟩ := hwH
  exact hG w a ha (hH w b hb)

end Gallai
