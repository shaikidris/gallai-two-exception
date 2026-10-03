/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.Inputs.Predecessor
public import Mathlib.Logic.Relation

@[expose] public section

/-!
# Finite reachability in the hub predecessor graph

An arc runs from an old carrier endpoint to its predecessor of the hub.
Unique spoke ownership makes the head map injective. A closed reachable set
without an avoiding carrier would have too few heads to support its endpoint
counts under Fan's strict inequality.
-/

namespace Gallai.Decomposition

open scoped Finset

universe u

variable {V : Type u} {G : SimpleGraph V} [DecidableEq V]

/-- One step along an actual oriented endpoint-to-predecessor incidence. -/
def HubStep (D : Decomposition G) (a v w : V) : Prop :=
  ∃ r : D.RunSlot a, D.runEndpoint a r = v ∧ D.runNeighbor a r = w

/-- Every step ends at a genuine neighbour of the hub. -/
theorem hubStep_adj (D : Decomposition G) (a v w : V) (h : D.HubStep a v w) :
    G.Adj a w := by
  obtain ⟨r, _, hw⟩ := h
  have hr := (D.path (D.runOwner a r)).walk.edges_subset_edgeSet (D.run_spoke_mem a r)
  exact hw ▸ hr

/-- Reachable vertices other than the root are hub neighbours. -/
theorem reachable_eq_root_or_adj (D : Decomposition G) (a b v : V)
    (h : Relation.ReflTransGen (D.HubStep a) b v) : v = b ∨ G.Adj a v := by
  rcases h.cases_tail with h | ⟨w, _, hw⟩
  · exact Or.inl h
  · exact Or.inr (D.hubStep_adj a w v hw)

/-- Endpoint incidences in a hub-avoiding vertex set count the runs rooted there,
provided all their carriers contain the hub. -/
theorem sum_endpoint_eq_run_filter (D : Decomposition G) (a : V) (S : Finset V)
    (ha : a ∉ S)
    (hall : ∀ v ∈ S, ∀ i : Fin D.size,
      ((D.path i).start = v ∨ (D.path i).finish = v) → a ∈ (D.path i).walk.support) :
    ∑ v ∈ S, D.endpointCount v =
      #{r : D.RunSlot a | D.runEndpoint a r ∈ S} := by
  classical
  calc
    ∑ v ∈ S, D.endpointCount v = ∑ v ∈ S, #{r : D.RunSlot a | D.runEndpoint a r = v} := by
      apply Finset.sum_congr rfl
      intro v hv
      have hva : v ≠ a := fun h => ha (h ▸ hv)
      simpa only [Fintype.card_subtype] using (D.card_runEndpoint_fiber a v hva (hall v hv)).symm
    _ = _ := Finset.sum_card_fiberwise_eq_card_filter Finset.univ S (D.runEndpoint a)

variable [Fintype V] [DecidableRel G.Adj]

/-- A closed set with no avoiding endpoint carrier pays the root multiplicity in passing neighbours. -/
theorem endpoint_le_passing_of_closed (D : Decomposition G) (a b : V) (S : Finset V)
    (hb : b ∈ S) (ha : a ∉ S) (hmissing : ¬ G.Adj a b)
    (hclosed : ∀ r : D.RunSlot a, D.runEndpoint a r ∈ S → D.runNeighbor a r ∈ S)
    (hshape : ∀ v ∈ S, v = b ∨ G.Adj a v)
    (hall : ∀ v ∈ S, ∀ i : Fin D.size,
      ((D.path i).start = v ∨ (D.path i).finish = v) → a ∈ (D.path i).walk.support) :
    D.endpointCount b ≤ #{v ∈ G.neighborFinset a | D.endpointCount v = 0} := by
  classical
  let R := Finset.univ.filter (fun r : D.RunSlot a => D.runEndpoint a r ∈ S)
  have hhead : #R ≤ #(S.erase b) := by
    apply Finset.card_le_card_of_injOn (D.runNeighbor a)
    · intro r hr
      apply Finset.mem_erase.mpr
      refine ⟨?_, hclosed r (Finset.mem_filter.mp hr).2⟩
      intro heq
      have hadj := (D.path (D.runOwner a r)).walk.edges_subset_edgeSet (D.run_spoke_mem a r)
      exact hmissing (heq ▸ hadj)
    · intro r _ s _ h
      exact D.runNeighbor_injective a h
  have hsum : (∑ v ∈ S, D.endpointCount v) ≤ #(S.erase b) := by
    rw [D.sum_endpoint_eq_run_filter a S ha hall]
    exact hhead
  have hpositive : #{v ∈ S.erase b | D.endpointCount v ≠ 0} ≤
      ∑ v ∈ S.erase b, D.endpointCount v := by
    rw [Finset.card_filter]
    apply Finset.sum_le_sum
    intro v _
    split_ifs with h <;> omega
  have hpartition := Finset.card_filter_add_card_filter_not
    (s := S.erase b) (fun v => D.endpointCount v = 0)
  change #{v ∈ S.erase b | D.endpointCount v = 0} +
    #{v ∈ S.erase b | D.endpointCount v ≠ 0} = #(S.erase b) at hpartition
  have herase := Finset.sum_erase_add (s := S) (f := D.endpointCount) hb
  have hzero : #{v ∈ S.erase b | D.endpointCount v = 0} ≤
      #{v ∈ G.neighborFinset a | D.endpointCount v = 0} := by
    apply Finset.card_le_card
    intro v hv
    obtain ⟨hv, hz⟩ := Finset.mem_filter.mp hv
    obtain ⟨hne, hvS⟩ := Finset.mem_erase.mp hv
    have hadj := (hshape v hvS).resolve_left hne
    exact Finset.mem_filter.mpr ⟨(G.mem_neighborFinset a v).mpr hadj, hz⟩
  omega

/-- Fan's strict inequality forces a finite predecessor chain to an actual avoiding endpoint carrier. -/
theorem exists_reachable_avoiding_endpoint (D : Decomposition G) (a b : V)
    (hab : a ≠ b) (hmissing : ¬ G.Adj a b)
    (hstrict : #{v ∈ G.neighborFinset a | D.endpointCount v = 0} < D.endpointCount b) :
    ∃ v, ∃ i : Fin D.size, Relation.ReflTransGen (D.HubStep a) b v ∧ v ≠ a ∧
      ((D.path i).start = v ∨ (D.path i).finish = v) ∧ a ∉ (D.path i).walk.support := by
  classical
  by_contra hnone
  let S := Finset.univ.filter (fun v => Relation.ReflTransGen (D.HubStep a) b v)
  have hb : b ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, .refl⟩
  have hshape : ∀ v ∈ S, v = b ∨ G.Adj a v := by
    intro v hv
    exact D.reachable_eq_root_or_adj a b v (Finset.mem_filter.mp hv).2
  have ha : a ∉ S := by
    intro h
    exact (hshape a h).elim hab (fun h => h.ne rfl)
  have hclosed : ∀ r : D.RunSlot a, D.runEndpoint a r ∈ S → D.runNeighbor a r ∈ S := by
    intro r hr
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, (Finset.mem_filter.mp hr).2.tail ⟨r, rfl, rfl⟩⟩
  have hall : ∀ v ∈ S, ∀ i : Fin D.size,
      ((D.path i).start = v ∨ (D.path i).finish = v) → a ∈ (D.path i).walk.support := by
    intro v hv i hi
    by_contra havoid
    exact hnone ⟨v, i, (Finset.mem_filter.mp hv).2,
      fun h => ha (h ▸ hv), hi, havoid⟩
  exact (D.endpoint_le_passing_of_closed a b S hb ha hmissing hclosed hshape hall).not_gt hstrict

end Gallai.Decomposition
