/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.Transport.RunSlots

@[expose] public section

/-!
# Endpoint and predecessor incidences at a hub

The existing run inventory distinguishes the two sides of a through carrier.
Its neighbour is the predecessor of the hub when approached from the endpoint
defined here. These incidences, not bare carrier indices, underlie Fan sequences.
-/

namespace Gallai.Decomposition

universe u

variable {V : Type u} {G : SimpleGraph V} [DecidableEq V]

/-- The non-hub endpoint on the side represented by a run. -/
def runEndpoint (D : Decomposition G) (a : V) : D.RunSlot a → V
  | .inl i => if (D.path i.val).start = a then (D.path i.val).finish else (D.path i.val).start
  | .inr (i, false) => (D.path i.val).start
  | .inr (i, true) => (D.path i.val).finish

/-- A run endpoint is a genuine endpoint of its one recorded carrier. -/
theorem runEndpoint_is_endpoint (D : Decomposition G) (a : V) (r : D.RunSlot a) :
    (D.path (D.runOwner a r)).start = D.runEndpoint a r ∨
      (D.path (D.runOwner a r)).finish = D.runEndpoint a r := by
  rcases r with i | ⟨i, b⟩
  · change (D.path i.val).start = (if (D.path i.val).start = a then
        (D.path i.val).finish else (D.path i.val).start) ∨
      (D.path i.val).finish = (if (D.path i.val).start = a then
        (D.path i.val).finish else (D.path i.val).start)
    by_cases hs : (D.path i.val).start = a
    · rw [if_pos hs]
      exact Or.inr rfl
    · rw [if_neg hs]
      exact Or.inl rfl
  · cases b <;> simp [runEndpoint, runOwner]

/-- The endpoint represented by a hub run is never the hub itself. -/
theorem runEndpoint_ne_hub (D : Decomposition G) (a : V) (r : D.RunSlot a) :
    D.runEndpoint a r ≠ a := by
  rcases r with i | ⟨i, b⟩
  · have hn := (D.path i.val).start_ne_finish G
    change (if (D.path i.val).start = a then (D.path i.val).finish
      else (D.path i.val).start) ≠ a
    split_ifs with hs
    · intro ht
      exact hn (hs.trans ht.symm)
    · exact hs
  · have h := (Finset.mem_filter.mp i.property).2
    cases b
    · exact h.2.1
    · exact h.2.2

/-- A run's owner contains the hub; this does not impose disjointness between carriers. -/
theorem runOwner_contains_hub (D : Decomposition G) (a : V) (r : D.RunSlot a) :
    a ∈ (D.path (D.runOwner a r)).walk.support :=
  (D.path (D.runOwner a r)).walk.fst_mem_support_of_mem_edges (D.run_spoke_mem a r)

/-- Different oriented runs have different predecessor neighbours. -/
theorem runNeighbor_injective (D : Decomposition G) (a : V) :
    Function.Injective (D.runNeighbor a) := by
  intro r s h
  apply (D.runSlotEquivNeighbor a).injective
  exact Subtype.ext h

/-- Carrier ownership and its chosen endpoint together identify the run. -/
theorem runOwner_endpoint_injective (D : Decomposition G) (a : V) :
    Function.Injective (fun r : D.RunSlot a => (D.runOwner a r, D.runEndpoint a r)) := by
  intro r s h
  have ho := congrArg Prod.fst h
  have he := congrArg Prod.snd h
  rcases r with i | ⟨i, b⟩ <;> rcases s with j | ⟨j, c⟩
  · exact congrArg Sum.inl (Subtype.ext ho)
  · have hj : j.val ∈ D.terminalCarriers a := by
      change i.val = j.val at ho
      rw [← ho]
      exact i.property
    exact False.elim ((Finset.disjoint_left.mp (D.disjoint_terminal_through a)) hj j.property)
  · have hi : i.val ∈ D.terminalCarriers a := by
      change i.val = j.val at ho
      rw [ho]
      exact j.property
    exact False.elim ((Finset.disjoint_left.mp (D.disjoint_terminal_through a)) hi i.property)
  · have hij : i = j := Subtype.ext ho
    subst j
    have hn := (D.path i.val).start_ne_finish G
    cases b <;> cases c
    · rfl
    · exact False.elim (hn he)
    · exact False.elim (hn he.symm)
    · rfl

/-- Every non-hub endpoint on a hub-containing carrier has its exact run. -/
theorem exists_run_of_endpoint (D : Decomposition G) (a v : V) (i : Fin D.size)
    (hva : v ≠ a) (hv : (D.path i).start = v ∨ (D.path i).finish = v)
    (ha : a ∈ (D.path i).walk.support) :
    ∃ r : D.RunSlot a, D.runOwner a r = i ∧ D.runEndpoint a r = v := by
  rcases (D.mem_support_iff_terminal_or_through a i).mp ha with ht | hp
  · let j : D.TerminalIndex a := ⟨i, ht⟩
    refine ⟨.inl j, rfl, ?_⟩
    have ht' := (Finset.mem_filter.mp ht).2
    change (if (D.path i).start = a then (D.path i).finish else (D.path i).start) = v
    split_ifs with hs
    · exact hv.resolve_left (fun h => hva (h.symm.trans hs))
    · have hf := ht'.resolve_left hs
      exact hv.resolve_right (fun h => hva (h.symm.trans hf))
  · let j : D.ThroughIndex a := ⟨i, hp⟩
    rcases hv with hv | hv
    · exact ⟨.inr (j, false), rfl, hv⟩
    · exact ⟨.inr (j, true), rfl, hv⟩

/-- At fixed endpoint, distinct runs have distinct carriers. -/
theorem runOwner_injective_on_endpoint (D : Decomposition G) (a v : V) :
    Function.Injective (fun r : {r : D.RunSlot a // D.runEndpoint a r = v} =>
      D.runOwner a r.val) := by
  intro r s h
  apply Subtype.ext
  exact D.runOwner_endpoint_injective a (Prod.ext h (r.property.trans s.property.symm))

/-- If all carriers ending at v contain the hub, their run fibre counts all endpoints at v. -/
theorem card_runEndpoint_fiber (D : Decomposition G) (a v : V) (hva : v ≠ a)
    (hall : ∀ i : Fin D.size, ((D.path i).start = v ∨ (D.path i).finish = v) →
      a ∈ (D.path i).walk.support) :
    Fintype.card {r : D.RunSlot a // D.runEndpoint a r = v} = D.endpointCount v := by
  let f : {r : D.RunSlot a // D.runEndpoint a r = v} → D.TerminalIndex v := fun r =>
    ⟨D.runOwner a r.val, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
      exact (D.runEndpoint_is_endpoint a r.val).imp
        (fun h => h.trans r.property) (fun h => h.trans r.property)⟩⟩
  have hi : Function.Injective f := by
    intro r s h
    exact D.runOwner_injective_on_endpoint a v (congrArg Subtype.val h)
  have hs : Function.Surjective f := by
    intro i
    have hv := (Finset.mem_filter.mp i.property).2
    obtain ⟨r, ho, he⟩ := D.exists_run_of_endpoint a v i.val hva hv (hall i.val hv)
    exact ⟨⟨r, he⟩, Subtype.ext ho⟩
  rw [Fintype.card_congr (Equiv.ofBijective f ⟨hi, hs⟩), Fintype.card_coe]
  exact D.card_terminalCarriers v

end Gallai.Decomposition
