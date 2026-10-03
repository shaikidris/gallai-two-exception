/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.Transport.SpokeSlots
public import Mathlib.Logic.Equiv.Fin.Basic

@[expose] public section

/-!
# Terminal and through runs realize the owned-spoke slots

Each terminal carrier contributes one slot and each through carrier two.
The map below uses the actual terminal/released attachment vertices. Its
bijection to owned spokes is the missing realization step between carrier
counts and the four-neighbour labelling.
-/

namespace Gallai.Decomposition

universe u

variable {V : Type u} {G : SimpleGraph V} [DecidableEq V]

/-- Indices of actual terminal carriers at a vertex. -/
abbrev TerminalIndex (D : Decomposition G) (x : V) := ↥(D.terminalCarriers x)

/-- Indices of actual through carriers at a vertex. -/
abbrev ThroughIndex (D : Decomposition G) (x : V) := ↥(D.throughCarriers x)

/-- One slot per terminal run and two labelled sides per through run. -/
abbrev RunSlot (D : Decomposition G) (x : V) :=
  D.TerminalIndex x ⊕ (D.ThroughIndex x × Bool)

theorem terminal_hyp (D : Decomposition G) (x : V) (i : D.TerminalIndex x) :
    (D.path i.val).start = x ∨ (D.path i.val).finish = x :=
  (Finset.mem_filter.mp i.property).2

theorem through_hyp (D : Decomposition G) (x : V) (i : D.ThroughIndex x) :
    x ∈ (D.path i.val).walk.support ∧
      (D.path i.val).start ≠ x ∧ (D.path i.val).finish ≠ x :=
  (Finset.mem_filter.mp i.property).2

/-- The old carrier containing a given terminal/through run slot. -/
def runOwner (D : Decomposition G) (x : V) : D.RunSlot x → Fin D.size
  | .inl i => i.val
  | .inr (i, _) => i.val

/-- The actual attachment vertex of a terminal run or a side of a through run. -/
def runNeighbor (D : Decomposition G) (x : V) : D.RunSlot x → V
  | .inl i => ((D.path i.val).toward x).walk.reverse.snd
  | .inr (i, false) =>
    ((D.path i.val).takeTo x (through_hyp D x i).1 (through_hyp D x i).2.1).walk.reverse.snd
  | .inr (i, true) =>
    ((D.path i.val).dropFrom x (through_hyp D x i).1
      (through_hyp D x i).2.2.symm).walk.snd

/-- Every run slot's spoke really belongs to its recorded carrier. -/
theorem run_spoke_mem (D : Decomposition G) (x : V) (r : D.RunSlot x) :
    s(x, D.runNeighbor x r) ∈ (D.path (D.runOwner x r)).walk.edges := by
  rcases r with i | ⟨i, b⟩
  · exact ((D.path i.val).terminal_spoke_iff x _ (terminal_hyp D x i)).mpr rfl
  · have h := through_hyp D x i
    apply ((D.path i.val).through_spoke_iff x _ h.1 h.2.1 h.2.2.symm).mpr
    cases b
    · exact Or.inl rfl
    · exact Or.inr rfl

/-- Realize a terminal/through run slot as its actual owned spoke. -/
def runToSpokeSlot (D : Decomposition G) (x : V) (r : D.RunSlot x) : D.SpokeSlot x :=
  ⟨⟨D.runOwner x r, D.runNeighbor x r⟩,
    (D.path (D.runOwner x r)).walk.edges_subset_edgeSet (D.run_spoke_mem x r),
    D.run_spoke_mem x r⟩

/-- No owned spoke is omitted by the terminal/through run inventory. -/
theorem runToSpokeSlot_surjective (D : Decomposition G) (x : V) :
    Function.Surjective (D.runToSpokeSlot x) := by
  intro s
  rcases D.slot_owner_terminal_or_through x s with ht | hp
  · let i : D.TerminalIndex x := ⟨s.val.1, ht⟩
    have hv := ((D.path i.val).terminal_spoke_iff x s.val.2 (terminal_hyp D x i)).mp s.property.2
    refine ⟨.inl i, ?_⟩
    apply Subtype.ext
    exact Prod.ext rfl hv.symm
  · let i : D.ThroughIndex x := ⟨s.val.1, hp⟩
    have h := through_hyp D x i
    have hv := ((D.path i.val).through_spoke_iff x s.val.2 h.1 h.2.1 h.2.2.symm).mp s.property.2
    rcases hv with hleft | hright
    · refine ⟨.inr (i, false), ?_⟩
      apply Subtype.ext
      exact Prod.ext rfl hleft.symm
    · refine ⟨.inr (i, true), ?_⟩
      apply Subtype.ext
      exact Prod.ext rfl hright.symm

/-- Different terminal/through run slots never realize the same owned spoke. -/
theorem runToSpokeSlot_injective (D : Decomposition G) (x : V) :
    Function.Injective (D.runToSpokeSlot x) := by
  intro r s heq
  have ho : D.runOwner x r = D.runOwner x s := congrArg (fun q : D.SpokeSlot x => q.val.1) heq
  have hn : D.runNeighbor x r = D.runNeighbor x s := congrArg (fun q : D.SpokeSlot x => q.val.2) heq
  rcases r with i | ⟨i, b⟩ <;> rcases s with j | ⟨j, c⟩
  · exact congrArg Sum.inl (Subtype.ext ho)
  · have hj : j.val ∈ D.terminalCarriers x := by
      change i.val = j.val at ho
      rw [← ho]
      exact i.property
    exact False.elim ((Finset.disjoint_left.mp (D.disjoint_terminal_through x)) hj j.property)
  · have hi : i.val ∈ D.terminalCarriers x := by
      change i.val = j.val at ho
      rw [ho]
      exact j.property
    exact False.elim ((Finset.disjoint_left.mp (D.disjoint_terminal_through x)) hi i.property)
  · have hij : i = j := Subtype.ext ho
    subst j
    have h := through_hyp D x i
    have hne := (D.path i.val).release_attachments_ne x h.1 h.2.1 h.2.2.symm
    cases b <;> cases c
    · rfl
    · exact False.elim (hne hn)
    · exact False.elim (hne hn.symm)
    · rfl

/-- The terminal/through inventory is exactly the owned-spoke inventory. -/
noncomputable def runSlotEquivSpoke (D : Decomposition G) (x : V) :
    D.RunSlot x ≃ D.SpokeSlot x :=
  Equiv.ofBijective (D.runToSpokeSlot x)
    ⟨D.runToSpokeSlot_injective x, D.runToSpokeSlot_surjective x⟩

/-- Actual terminal/through slots bijectively label the hub neighbours. -/
noncomputable def runSlotEquivNeighbor (D : Decomposition G) (x : V) :
    D.RunSlot x ≃ G.neighborSet x :=
  (D.runSlotEquivSpoke x).trans (D.spokeSlotEquivNeighbor x)

/-- Enumerate the actual terminal carriers without changing their ownership. -/
noncomputable def terminalIndexEquivFin (D : Decomposition G) (x : V) :
    D.TerminalIndex x ≃ Fin (D.endpointCount x) :=
  Finset.equivFinOfCardEq (D.card_terminalCarriers x)

/-- Enumerate the actual through carriers without separating their two sides. -/
noncomputable def throughIndexEquivFin (D : Decomposition G) (x : V) :
    D.ThroughIndex x ≃ Fin (D.throughCount x) :=
  Finset.equivFinOfCardEq (D.card_throughCarriers x)

/-- Order slots with terminals first and each through carrier's two sides consecutive. -/
noncomputable def orderedRunSlotEquiv (D : Decomposition G) (x : V) :
    Fin (D.endpointCount x + D.throughCount x * 2) ≃ D.RunSlot x :=
  finSumFinEquiv.symm.trans
    (Equiv.sumCongr (D.terminalIndexEquivFin x).symm
      (finProdFinEquiv.symm.trans
        (Equiv.prodCongr (D.throughIndexEquivFin x).symm finTwoEquiv)))

/-- The first block of the ordering consists exactly of the enumerated terminals. -/
theorem orderedRunSlotEquiv_terminal (D : Decomposition G) (x : V)
    (i : Fin (D.endpointCount x)) :
    D.orderedRunSlotEquiv x (Fin.castAdd (D.throughCount x * 2) i) =
      Sum.inl ((D.terminalIndexEquivFin x).symm i) := by
  simp [orderedRunSlotEquiv]

/-- The remaining ordering keeps the two sides of each through carrier together. -/
theorem orderedRunSlotEquiv_through (D : Decomposition G) (x : V)
    (i : Fin (D.throughCount x)) (b : Fin 2) :
    D.orderedRunSlotEquiv x (Fin.natAdd (D.endpointCount x) (finProdFinEquiv (i, b))) =
      Sum.inr ((D.throughIndexEquivFin x).symm i, finTwoEquiv b) := by
  simp [orderedRunSlotEquiv]

/-- Ordered run slots label every neighbour, respecting terminal and through structure. -/
noncomputable def orderedNeighborEquiv (D : Decomposition G) (x : V) :
    Fin (D.endpointCount x + D.throughCount x * 2) ≃ G.neighborSet x :=
  (D.orderedRunSlotEquiv x).trans (D.runSlotEquivNeighbor x)

/-- The ordered terminal anchor is the attachment of its actual oriented carrier. -/
theorem orderedNeighborEquiv_terminal (D : Decomposition G) (x : V)
    (i : Fin (D.endpointCount x)) :
    (D.orderedNeighborEquiv x (Fin.castAdd (D.throughCount x * 2) i)).val =
      D.runNeighbor x (.inl ((D.terminalIndexEquivFin x).symm i)) := by
  change D.runNeighbor x (D.orderedRunSlotEquiv x _) = _
  rw [D.orderedRunSlotEquiv_terminal]

/-- The ordered through anchors are the actual released attachments, in side order. -/
theorem orderedNeighborEquiv_through (D : Decomposition G) (x : V)
    (i : Fin (D.throughCount x)) (b : Fin 2) :
    (D.orderedNeighborEquiv x
      (Fin.natAdd (D.endpointCount x) (finProdFinEquiv (i, b)))).val =
      D.runNeighbor x (.inr ((D.throughIndexEquivFin x).symm i, finTwoEquiv b)) := by
  change D.runNeighbor x (D.orderedRunSlotEquiv x _) = _
  rw [D.orderedRunSlotEquiv_through]

variable [Fintype V] [DecidableRel G.Adj]

/-- A degree-four hub admits a complete run-compatible labelling by four anchors. -/
noncomputable def fourNeighborEquiv (D : Decomposition G) (x : V)
    (hdegree : G.degree x = 4) : Fin 4 ≃ G.neighborSet x :=
  (finCongr (by have h := D.degree_eq_endpoint_add_twice_through x; omega)).trans
    (D.orderedNeighborEquiv x)

/-- Terminal number i occupies anchor i in the four-neighbour labelling. -/
theorem fourNeighborEquiv_terminal (D : Decomposition G) (x : V)
    (hdegree : G.degree x = 4) (i : Fin (D.endpointCount x)) :
    (D.fourNeighborEquiv x hdegree
      ⟨i.val, by have h := D.degree_eq_endpoint_add_twice_through x; omega⟩).val =
      D.runNeighbor x (.inl ((D.terminalIndexEquivFin x).symm i)) := by
  change (D.orderedNeighborEquiv x _).val = _
  convert D.orderedNeighborEquiv_terminal x i using 1
  congr 2

/-- Through number i occupies consecutive anchors after all the terminals. -/
theorem fourNeighborEquiv_through (D : Decomposition G) (x : V)
    (hdegree : G.degree x = 4) (i : Fin (D.throughCount x)) (b : Fin 2) :
    (D.fourNeighborEquiv x hdegree
      ⟨D.endpointCount x + (2 * i.val + b.val), by
        have h := D.degree_eq_endpoint_add_twice_through x; omega⟩).val =
      D.runNeighbor x (.inr ((D.throughIndexEquivFin x).symm i, finTwoEquiv b)) := by
  change (D.orderedNeighborEquiv x _).val = _
  convert D.orderedNeighborEquiv_through x i b using 1
  congr 2
  apply Fin.ext
  simp [finProdFinEquiv, Nat.add_comm]

/-- The four run-compatible anchor labels are pairwise distinct. -/
theorem fourNeighborEquiv_injective (D : Decomposition G) (x : V)
    (hdegree : G.degree x = 4) :
    Function.Injective (fun i => (D.fourNeighborEquiv x hdegree i).val) := by
  intro i j hij
  exact (D.fourNeighborEquiv x hdegree).injective (Subtype.ext hij)

/-- Every neighbour occurs among the four run-compatible anchor labels. -/
theorem fourNeighborEquiv_covers (D : Decomposition G) (x v : V)
    (hdegree : G.degree x = 4) :
    G.Adj x v ↔ ∃ i : Fin 4, (D.fourNeighborEquiv x hdegree i).val = v := by
  constructor
  · intro hv
    obtain ⟨i, hi⟩ := (D.fourNeighborEquiv x hdegree).surjective ⟨v, hv⟩
    exact ⟨i, congrArg Subtype.val hi⟩
  · rintro ⟨i, hi⟩
    exact hi ▸ (D.fourNeighborEquiv x hdegree i).property

end Gallai.Decomposition
