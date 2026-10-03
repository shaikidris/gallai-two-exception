/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.Foundations.HubProfiles
public import Gallai.Operations.HubRelease
public import Gallai.Operations.Orient
public import Gallai.Operations.SpokeMembership
public import Mathlib.Data.Fintype.EquivFin

@[expose] public section

/-!
# Spokes with their actual decomposition owners

A spoke slot records a carrier index and a neighbour, together with actual
spoke membership. Unique edge coverage makes neighbour projection a bijection.
The attachment lemmas connect this ownership model to the local runs that
will consume a star-release identity.
-/

namespace Gallai.Decomposition

universe u

variable {V : Type u} {G : SimpleGraph V}

/-- A spoke together with the index of the carrier that actually contains it. -/
abbrev SpokeSlot (D : Decomposition G) (x : V) :=
  {slot : Fin D.size × V // G.Adj x slot.2 ∧ s(x, slot.2) ∈ (D.path slot.1).walk.edges}

/-- Forget the owner of a spoke, retaining its adjacent attachment vertex. -/
def slotNeighbor (D : Decomposition G) (x : V) (slot : D.SpokeSlot x) : G.neighborSet x :=
  ⟨slot.val.2, slot.property.1⟩

/-- Unique edge coverage forbids two different slots at the same neighbour. -/
theorem slotNeighbor_injective (D : Decomposition G) (x : V) :
    Function.Injective (D.slotNeighbor x) := by
  intro s t h
  have hv : s.val.2 = t.val.2 := congrArg Subtype.val h
  have ht : s(x, s.val.2) ∈ (D.path t.val.1).walk.edges := by
    rw [hv]
    exact t.property.2
  obtain ⟨i, _, hu⟩ := D.covers s(x, s.val.2) s.property.1
  apply Subtype.ext
  exact Prod.ext ((hu s.val.1 s.property.2).trans (hu t.val.1 ht).symm) hv

/-- Every hub neighbour has a slot, since its spoke has an owner. -/
theorem slotNeighbor_surjective (D : Decomposition G) (x : V) :
    Function.Surjective (D.slotNeighbor x) := by
  intro v
  obtain ⟨i, hi, _⟩ := D.covers s(x, v.val) v.property
  exact ⟨⟨⟨i, v.val⟩, v.property, hi⟩, rfl⟩

/-- Actual owned spokes and hub neighbours are equivalent, with no missing slots. -/
noncomputable def spokeSlotEquivNeighbor (D : Decomposition G) (x : V) :
    D.SpokeSlot x ≃ G.neighborSet x :=
  Equiv.ofBijective (D.slotNeighbor x)
    ⟨D.slotNeighbor_injective x, D.slotNeighbor_surjective x⟩

/-- Distinct carriers cannot use spokes with the same attachment vertex. -/
theorem spoke_attachments_ne (D : Decomposition G) (x : V)
    {i j : Fin D.size} (hne : i ≠ j) {a b : V}
    (ha : s(x, a) ∈ (D.path i).walk.edges)
    (hb : s(x, b) ∈ (D.path j).walk.edges) : a ≠ b := by
  intro hab
  have hb' : s(x, a) ∈ (D.path j).walk.edges := by
    rw [hab]
    exact hb
  obtain ⟨k, _, hu⟩ := D.covers s(x, a) ((D.path i).walk.edges_subset_edgeSet ha)
  exact hne ((hu i ha).trans (hu j hb').symm)

variable [DecidableEq V]

/-- Every spoke owner belongs to the actual terminal/through carrier inventory. -/
theorem slot_owner_terminal_or_through (D : Decomposition G) (x : V) (slot : D.SpokeSlot x) :
    slot.val.1 ∈ D.terminalCarriers x ∨ slot.val.1 ∈ D.throughCarriers x :=
  (D.mem_support_iff_terminal_or_through x slot.val.1).mp
    ((D.path slot.val.1).walk.fst_mem_support_of_mem_edges slot.property.2)

variable [Fintype V] [DecidableRel G.Adj]

/-- The number of actual owned spokes equals the ordinary degree of the hub. -/
theorem card_spokeSlots (D : Decomposition G) (x : V) :
    Fintype.card (D.SpokeSlot x) = G.degree x := by
  rw [Fintype.card_congr (D.spokeSlotEquivNeighbor x)]
  exact G.card_neighborSet_eq_degree x

/-- A degree-four hub has exactly four owned spoke slots. -/
theorem card_spokeSlots_of_degree_four (D : Decomposition G) (x : V)
    (hdegree : G.degree x = 4) : Fintype.card (D.SpokeSlot x) = 4 := by
  rw [D.card_spokeSlots x, hdegree]

end Gallai.Decomposition
