/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.Operations.Transport
public import Gallai.Operations.Trim
public import Gallai.Foundations.Endpoints
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

@[expose] public section

/-! # Erasing a carrier and exactly its edges -/

namespace Gallai.Decomposition

universe u v

variable {V : Type u} {G : SimpleGraph V}

/-- Reindex any exact finite path family by the standard finite index type. -/
noncomputable def ofFamily {I : Type v} [Fintype I] (paths : I → NonemptyPath G)
    (hcover : ∀ e ∈ G.edgeSet, ∃! i, e ∈ (paths i).walk.edges) : Decomposition G where
  size := Fintype.card I
  path := fun i => paths ((Fintype.equivFin I).symm i)
  covers := by
    intro e he
    obtain ⟨i, hi, hu⟩ := hcover e he
    refine ⟨Fintype.equivFin I i, ?_, ?_⟩
    · have hp : paths ((Fintype.equivFin I).symm (Fintype.equivFin I i)) = paths i :=
        congrArg paths ((Fintype.equivFin I).symm_apply_apply i)
      exact (congrArg (fun P : NonemptyPath G => e ∈ P.walk.edges) hp).mpr hi
    intro j hj
    apply (Fintype.equivFin I).symm.injective
    simpa using hu ((Fintype.equivFin I).symm j) hj

/-- Finite reindexing preserves the exact number of paths. -/
@[simp] theorem ofFamily_size {I : Type v} [Fintype I] (paths : I → NonemptyPath G)
    (hcover : ∀ e ∈ G.edgeSet, ∃! i, e ∈ (paths i).walk.edges) :
    (ofFamily paths hcover).size = Fintype.card I := rfl

/-- Endpoint counting commutes with finite reindexing. -/
theorem ofFamily_endpointCount [DecidableEq V] {I : Type v} [Fintype I]
    (paths : I → NonemptyPath G)
    (hcover : ∀ e ∈ G.edgeSet, ∃! i, e ∈ (paths i).walk.edges) (w : V) :
    (ofFamily paths hcover).endpointCount w =
      ∑ i, ((if (paths i).start = w then 1 else 0) + (if (paths i).finish = w then 1 else 0)) := by
  let ends (i : I) :=
    (if (paths i).start = w then 1 else 0) + (if (paths i).finish = w then 1 else 0 : ℕ)
  change (∑ j : Fin (Fintype.card I), ends ((Fintype.equivFin I).symm j)) = ∑ i, ends i
  exact (Fintype.equivFin I).symm.sum_comp ends

def eraseFamily (D : Decomposition G) (i : Fin D.size)
    (j : {j : Fin D.size // j ≠ i}) :
    NonemptyPath (G.deleteEdges {e | e ∈ (D.path i).walk.edges}) :=
  (D.path j.val).transfer _ (fun e he => by
    rw [SimpleGraph.edgeSet_deleteEdges]
    refine ⟨(D.path j.val).walk.edges_subset_edgeSet he, ?_⟩
    intro hi
    obtain ⟨k, _, hu⟩ := D.covers e ((D.path j.val).walk.edges_subset_edgeSet he)
    exact j.property ((hu j.val he).trans (hu i hi).symm))

theorem eraseFamily_covers (D : Decomposition G) (i : Fin D.size) :
    ∀ e ∈ (G.deleteEdges {e | e ∈ (D.path i).walk.edges}).edgeSet,
      ∃! j, e ∈ (eraseFamily D i j).walk.edges := by
  intro e he
  rw [SimpleGraph.edgeSet_deleteEdges] at he
  obtain ⟨j, hj, hu⟩ := D.covers e he.1
  have hji : j ≠ i := fun h => he.2 (h ▸ hj)
  refine ⟨⟨j, hji⟩, ?_, ?_⟩
  · simpa only [eraseFamily, NonemptyPath.transfer_edges] using hj
  · intro k hk
    apply Subtype.ext
    exact hu k.val (by simpa only [eraseFamily, NonemptyPath.transfer_edges] using hk)

/-- Delete a whole carrier and its edge set, retaining every other carrier. -/
noncomputable def eraseCarrier (D : Decomposition G) (i : Fin D.size) :
    Decomposition (G.deleteEdges {e | e ∈ (D.path i).walk.edges}) :=
  ofFamily (eraseFamily D i) (eraseFamily_covers D i)

/-- Exactly one carrier disappears, including when it is the only carrier. -/
@[simp] theorem eraseCarrier_size (D : Decomposition G) (i : Fin D.size) :
    (D.eraseCarrier i).size = D.size - 1 := by
  change Fintype.card {j : Fin D.size // j ≠ i} = _
  rw [Fintype.card_subtype_compl]
  simp

/-- Erasing a carrier removes precisely its two endpoint incidences. -/
theorem eraseCarrier_endpointCount [DecidableEq V] (D : Decomposition G)
    (i : Fin D.size) (w : V) :
    (D.eraseCarrier i).endpointCount w +
      ((if (D.path i).start = w then 1 else 0) + (if (D.path i).finish = w then 1 else 0)) =
      D.endpointCount w := by
  let ends (j : Fin D.size) :=
    (if (D.path j).start = w then 1 else 0) + (if (D.path j).finish = w then 1 else 0 : ℕ)
  rw [eraseCarrier, ofFamily_endpointCount]
  change (∑ j : {j : Fin D.size // j ≠ i}, ends j.val) + ends i = ∑ j, ends j
  have h := Fintype.sum_subtype_add_sum_subtype (fun j : Fin D.size => j = i) ends
  have hd : (default : {j : Fin D.size // j = i}).val = i :=
    (default : {j : Fin D.size // j = i}).property
  simpa [hd, add_comm] using h

/-- Erasing a carrier leaves the endpoint count at a vertex unchanged when
that carrier has neither endpoint there.  This is the endpoint-preservation
interface used when a local reconstruction replaces a different carrier. -/
theorem eraseCarrier_endpointCount_of_not_endpoint [DecidableEq V]
    (D : Decomposition G) (i : Fin D.size) (w : V)
    (hstart : (D.path i).start ≠ w) (hfinish : (D.path i).finish ≠ w) :
    (D.eraseCarrier i).endpointCount w = D.endpointCount w := by
  have h := D.eraseCarrier_endpointCount i w
  simp [hstart, hfinish] at h
  exact h

/-- For a single-edge carrier its entire edge set is exactly its first edge. -/
theorem singleCarrier_edgeSet (D : Decomposition G) (i : Fin D.size)
    (hone : (D.path i).walk.length = 1) :
    {e | e ∈ (D.path i).walk.edges} = {s((D.path i).start, (D.path i).walk.snd)} := by
  have hnil := ((D.path i).tail_nil_iff_length_one).mpr hone
  have htail : (D.path i).walk.tail.edges = [] := by
    apply List.length_eq_zero_iff.mp
    simpa only [SimpleGraph.Walk.length_edges] using hnil.length_eq_zero
  ext e
  rw [← (D.path i).firstEdge_cons_tail_edges, htail]
  simp

/-- Deleting a single-edge carrier has the required one-edge-deleted graph as target. -/
theorem singleCarrier_deletedGraph (D : Decomposition G) (i : Fin D.size)
    (hone : (D.path i).walk.length = 1) :
    G.deleteEdges {e | e ∈ (D.path i).walk.edges} =
      G.deleteEdges {s((D.path i).start, (D.path i).walk.snd)} := by
  rw [D.singleCarrier_edgeSet i hone]

def eraseManyFamily (D : Decomposition G) (S : Finset (Fin D.size))
    (j : {j : Fin D.size // j ∉ S}) :
    NonemptyPath (G.deleteEdges {e | ∃ i ∈ S, e ∈ (D.path i).walk.edges}) :=
  (D.path j.val).transfer _ (fun e he => by
    rw [SimpleGraph.edgeSet_deleteEdges]
    refine ⟨(D.path j.val).walk.edges_subset_edgeSet he, ?_⟩
    rintro ⟨i, hi, he'⟩
    obtain ⟨k, _, hu⟩ := D.covers e ((D.path j.val).walk.edges_subset_edgeSet he)
    have hji : j.val = i := (hu j.val he).trans (hu i he').symm
    exact j.property (hji ▸ hi))

theorem eraseManyFamily_covers (D : Decomposition G) (S : Finset (Fin D.size)) :
    ∀ e ∈ (G.deleteEdges {e | ∃ i ∈ S, e ∈ (D.path i).walk.edges}).edgeSet,
      ∃! j, e ∈ (eraseManyFamily D S j).walk.edges := by
  intro e he
  rw [SimpleGraph.edgeSet_deleteEdges] at he
  obtain ⟨j, hj, hu⟩ := D.covers e he.1
  have hjs : j ∉ S := fun hs => he.2 ⟨j, hs, hj⟩
  refine ⟨⟨j, hjs⟩, by simpa [eraseManyFamily] using hj, ?_⟩
  intro k hk
  apply Subtype.ext
  exact hu k.val (by simpa [eraseManyFamily] using hk)

/-- Remove an arbitrary finite set of carriers and exactly their edges. -/
noncomputable def eraseCarriers (D : Decomposition G) (S : Finset (Fin D.size)) :
    Decomposition (G.deleteEdges {e | ∃ i ∈ S, e ∈ (D.path i).walk.edges}) :=
  ofFamily (eraseManyFamily D S) (eraseManyFamily_covers D S)

/-- The exact size of the retained carrier family. -/
@[simp] theorem eraseCarriers_size (D : Decomposition G) (S : Finset (Fin D.size)) :
    (D.eraseCarriers S).size = D.size - S.card := by
  change Fintype.card {j : Fin D.size // j ∉ S} = _
  rw [Fintype.card_subtype_compl]
  simp

/-- Removing a finite carrier family removes exactly the endpoint incidences
of those carriers.  This is the multi-carrier analogue of
`eraseCarrier_endpointCount`. -/
theorem eraseCarriers_endpointCount [DecidableEq V] (D : Decomposition G)
    (S : Finset (Fin D.size)) (w : V) :
    (D.eraseCarriers S).endpointCount w +
      ∑ i ∈ S, ((if (D.path i).start = w then 1 else 0) +
        (if (D.path i).finish = w then 1 else 0)) = D.endpointCount w := by
  let ends (j : Fin D.size) :=
    (if (D.path j).start = w then 1 else 0) +
      (if (D.path j).finish = w then 1 else 0 : ℕ)
  classical
  rw [eraseCarriers, ofFamily_endpointCount]
  simp only [eraseManyFamily, NonemptyPath.transfer]
  simp only [Decomposition.endpointCount]
  change (∑ j : {j : Fin D.size // j ∉ S}, ends j.val) + ∑ j ∈ S, ends j =
    ∑ j, ends j
  have hcomp : (∑ j : {j : Fin D.size // j ∉ S}, ends j.val) =
      ∑ j ∈ Sᶜ, ends j := by
    exact (Finset.sum_subtype Sᶜ (by intro j; simp) ends).symm
  calc
    _ = (∑ j ∈ Sᶜ, ends j) + ∑ j ∈ S, ends j := by rw [hcomp]
    _ = _ := Finset.sum_compl_add_sum S ends

end Gallai.Decomposition
