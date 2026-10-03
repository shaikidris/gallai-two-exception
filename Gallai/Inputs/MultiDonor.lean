/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.Inputs.SingleEdge

@[expose] public section

/-!
# Multi-donor inward addition

Fan's Lemma 3.3 follows from the closed-set predecessor count with several
missing-spoke roots. The aggregate endpoint supply, not any one donor's
individual supply, forces an avoiding carrier. Existing selected-run transport
then adds one of the missing edges with the exact endpoint balance.
-/

namespace Gallai.Decomposition

open scoped Finset

universe u

variable {V : Type u} {G : SimpleGraph V} [DecidableEq V]
  [Fintype V] [DecidableRel G.Adj]

/-- A closed set without an avoiding carrier charges every missing root's
endpoint multiplicity to passing neighbours of the hub. -/
theorem sum_endpoint_le_passing_of_closed (D : Decomposition G) (a : V)
    (B S : Finset V) (hBS : B ⊆ S) (ha : a ∉ S)
    (hmissing : ∀ b ∈ B, ¬ G.Adj a b)
    (hclosed : ∀ r : D.RunSlot a, D.runEndpoint a r ∈ S → D.runNeighbor a r ∈ S)
    (hshape : ∀ v ∈ S, v ∈ B ∨ G.Adj a v)
    (hall : ∀ v ∈ S, ∀ i : Fin D.size,
      ((D.path i).start = v ∨ (D.path i).finish = v) → a ∈ (D.path i).walk.support) :
    (∑ b ∈ B, D.endpointCount b) ≤
      #{v ∈ G.neighborFinset a | D.endpointCount v = 0} := by
  classical
  let R := Finset.univ.filter (fun r : D.RunSlot a => D.runEndpoint a r ∈ S)
  have hhead : #R ≤ #(S \ B) := by
    apply Finset.card_le_card_of_injOn (D.runNeighbor a)
    · intro r hr
      apply Finset.mem_sdiff.mpr
      refine ⟨hclosed r (Finset.mem_filter.mp hr).2, ?_⟩
      intro hb
      exact hmissing _ hb (D.hubStep_adj a _ _ ⟨r, rfl, rfl⟩)
    · intro r _ s _ h
      exact D.runNeighbor_injective a h
  have hsum : (∑ v ∈ S, D.endpointCount v) ≤ #(S \ B) := by
    rw [D.sum_endpoint_eq_run_filter a S ha hall]
    exact hhead
  have hpositive : #{v ∈ S \ B | D.endpointCount v ≠ 0} ≤
      ∑ v ∈ S \ B, D.endpointCount v := by
    rw [Finset.card_filter]
    apply Finset.sum_le_sum
    intro v _
    split_ifs <;> omega
  have hpartition := Finset.card_filter_add_card_filter_not
    (s := S \ B) (fun v => D.endpointCount v = 0)
  change #{v ∈ S \ B | D.endpointCount v = 0} +
    #{v ∈ S \ B | D.endpointCount v ≠ 0} = #(S \ B) at hpartition
  have hsplit := Finset.sum_sdiff hBS (f := D.endpointCount)
  have hzero : #{v ∈ S \ B | D.endpointCount v = 0} ≤
      #{v ∈ G.neighborFinset a | D.endpointCount v = 0} := by
    apply Finset.card_le_card
    intro v hv
    obtain ⟨hv, hz⟩ := Finset.mem_filter.mp hv
    obtain ⟨hvS, hvB⟩ := Finset.mem_sdiff.mp hv
    have hadj := (hshape v hvS).resolve_left hvB
    exact Finset.mem_filter.mpr ⟨(G.mem_neighborFinset a v).mpr hadj, hz⟩
  omega

/-- Aggregate strict supply forces an avoiding endpoint carrier reachable
from one of the missing-spoke roots. -/
theorem exists_multi_reachable_avoiding_endpoint (D : Decomposition G) (a : V)
    (B : Finset V) (haB : a ∉ B) (hmissing : ∀ b ∈ B, ¬ G.Adj a b)
    (hstrict : #{v ∈ G.neighborFinset a | D.endpointCount v = 0} <
      ∑ b ∈ B, D.endpointCount b) :
    ∃ b ∈ B, ∃ v, ∃ i : Fin D.size,
      Relation.ReflTransGen (D.HubStep a) b v ∧
      ((D.path i).start = v ∨ (D.path i).finish = v) ∧
      a ∉ (D.path i).walk.support := by
  classical
  by_contra hnone
  let S := Finset.univ.filter
    (fun v => ∃ b ∈ B, Relation.ReflTransGen (D.HubStep a) b v)
  have hBS : B ⊆ S := by
    intro b hb
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, b, hb, .refl⟩
  have hshape : ∀ v ∈ S, v ∈ B ∨ G.Adj a v := by
    intro v hv
    obtain ⟨b, hb, hreach⟩ := (Finset.mem_filter.mp hv).2
    rcases D.reachable_eq_root_or_adj a b v hreach with h | h
    · exact Or.inl (h ▸ hb)
    · exact Or.inr h
  have ha : a ∉ S := by
    intro h
    exact (hshape a h).elim haB (fun h => h.ne rfl)
  have hclosed : ∀ r : D.RunSlot a, D.runEndpoint a r ∈ S → D.runNeighbor a r ∈ S := by
    intro r hr
    obtain ⟨b, hb, hreach⟩ := (Finset.mem_filter.mp hr).2
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, b, hb, hreach.tail ⟨r, rfl, rfl⟩⟩
  have hall : ∀ v ∈ S, ∀ i : Fin D.size,
      ((D.path i).start = v ∨ (D.path i).finish = v) → a ∈ (D.path i).walk.support := by
    intro v hv i hi
    by_contra havoid
    obtain ⟨b, hb, hreach⟩ := (Finset.mem_filter.mp hv).2
    exact hnone ⟨b, hb, v, i, hreach, hi, havoid⟩
  exact (D.sum_endpoint_le_passing_of_closed a B S hBS ha hmissing
    hclosed hshape hall).not_gt hstrict

/-- Fan's multi-donor addition: an aggregate strict inequality selects one
missing spoke and adds it at the hub at unchanged size. -/
theorem multi_donor_addibility (D : Decomposition G) (a : V) (B : Finset V)
    (ha : a ∉ B) (hmissing : ∀ b ∈ B, ¬ G.Adj a b)
    (hstrict : #{v ∈ G.neighborFinset a | D.endpointCount v = 0} <
      ∑ b ∈ B, D.endpointCount b) :
    ∃ b ∈ B, ∃ E : Decomposition (G ⊔ SimpleGraph.edge a b),
      E.size = D.size ∧ ∀ v,
        E.endpointCount v + (if b = v then 1 else 0) =
          D.endpointCount v + if a = v then 1 else 0 := by
  obtain ⟨b, hb, v, i, hreach, hv, havoid⟩ :=
    D.exists_multi_reachable_avoiding_endpoint a B ha hmissing hstrict
  obtain ⟨R, _, hshape, hbalance⟩ := D.exists_selected_runs a b v (hmissing b hb) hreach
  obtain ⟨E, hsize, hend⟩ := D.exists_add_of_selected_runs a b v
    (fun h => ha (h.symm ▸ hb)) (hmissing b hb) R hshape
    (D.reachable_eq_root_or_adj a b v hreach) hbalance i hv havoid
  exact ⟨b, hb, E, hsize, hend⟩

end Gallai.Decomposition
