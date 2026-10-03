/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.Repair.FirstEdge
public import Gallai.Operations.Reversal
public import Gallai.Operations.SpokeMembership

@[expose] public section

/-!
# Deleting a terminal edge in either orientation

The selected edge, not an assumed first edge, determines the auxiliary graph.
Reversal preserves the input counts. Terminality of the other endpoint
distinguishes the single-edge carrier from the longer terminal carrier.
-/

namespace Gallai.Decomposition

universe u

variable {V : Type u} {G : SimpleGraph V} [DecidableEq V]

/-- Delete an edge incident with the initial endpoint of its unique carrier. -/
theorem exists_delete_at_start (D : Decomposition G) (i : Fin D.size) (x y : V)
    (he : s(x, y) ∈ (D.path i).walk.edges) (hs : (D.path i).start = x) :
    ∃ E : Decomposition (G.deleteEdges {s(x, y)}),
      E.size + (if (D.path i).start = y ∨ (D.path i).finish = y then 1 else 0) = D.size ∧
      E.endpointCount x + 1 = D.endpointCount x ∧
      E.endpointCount y + (if (D.path i).start = y ∨ (D.path i).finish = y then 2 else 0) =
        D.endpointCount y + 1 ∧
      ∀ w, w ≠ x → w ≠ y → E.endpointCount w = D.endpointCount w := by
  have hxy : x ≠ y := (show G.Adj x y from (D.path i).walk.edges_subset_edgeSet he).ne
  have hspoke := (D.path i).first_spoke_iff y
  have he' : s((D.path i).start, y) ∈ (D.path i).walk.edges := by
    simpa only [hs] using he
  have hsecond : (D.path i).walk.snd = y := (hspoke.mp he').symm
  have hshort : (D.path i).walk.length = 1 ↔
      (D.path i).start = y ∨ (D.path i).finish = y := by
    simpa only [hsecond, hs, if_false, hxy, false_or, eq_comm] using
      (D.path i).snd_eq_finish_iff.symm
  have hedge : s((D.path i).start, (D.path i).walk.snd) = s(x, y) :=
    congrArg₂ Sym2.mk hs hsecond
  have h := D.exists_delete_first i
  rw [hedge] at h
  simpa only [hshort, hs, hsecond] using h

/-- Delete a chosen terminal edge, including its single-edge-carrier case. -/
theorem exists_delete_terminal (D : Decomposition G) (i : Fin D.size) (x y : V)
    (he : s(x, y) ∈ (D.path i).walk.edges)
    (hx : (D.path i).start = x ∨ (D.path i).finish = x) :
    ∃ E : Decomposition (G.deleteEdges {s(x, y)}),
      E.size + (if (D.path i).start = y ∨ (D.path i).finish = y then 1 else 0) = D.size ∧
      E.endpointCount x + 1 = D.endpointCount x ∧
      E.endpointCount y + (if (D.path i).start = y ∨ (D.path i).finish = y then 2 else 0) =
        D.endpointCount y + 1 ∧
      ∀ w, w ≠ x → w ≠ y → E.endpointCount w = D.endpointCount w := by
  rcases hx with hs | ht
  · exact D.exists_delete_at_start i x y he hs
  · have he' : s(x, y) ∈ (D.reverse.path i).walk.edges := by
      simpa only [reverse, NonemptyPath.reverse_edges, List.mem_reverse] using he
    have h := D.reverse.exists_delete_at_start i x y he' ht
    simp only [reverse_endpointCount, reverse_size] at h
    simpa only [reverse, NonemptyPath.reverse, or_comm] using h

end Gallai.Decomposition
