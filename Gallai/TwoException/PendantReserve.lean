/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.Repair.FirstEdge

@[expose] public section

/-!
# Pendant trimming with an endpoint reserve

A terminal edge can be deleted directly from its carrier.  The carrier is
either shortened or, when it consists of that one edge, removed.  In both
cases no new carrier is created.  The exact endpoint accounting in
`exists_delete_first` then shows that three endpoint occurrences at the hub
leave two after the deletion.
-/

namespace Gallai.TwoException

universe u

variable {V : Type u} {G : SimpleGraph V} [DecidableEq V]

/-- Deleting the first, terminal edge of a chosen carrier preserves a
two-endpoint reserve at its hub when the input reserve is at least three. -/
theorem trim_pendant_preserving_reserve (D : Decomposition G) (i : Fin D.size)
    (h w : V) (hstart : (D.path i).start = h) (hsecond : (D.path i).walk.snd = w)
    (hreserve : 3 ≤ D.endpointCount h) :
    ∃ E : Decomposition (G.deleteEdges {s(h, w)}),
      E.size ≤ D.size ∧ 2 ≤ E.endpointCount h ∧
      ∀ v, v ≠ h → v ≠ w → E.endpointCount v = D.endpointCount v := by
  obtain ⟨E, hsize, hhub, hleaf, hother⟩ := D.exists_delete_first i
  subst h
  subst w
  have hsize_le : E.size ≤ D.size := by
    split_ifs at hsize
    · omega
    · omega
  have hhub' : E.endpointCount (D.path i).start + 1 =
      D.endpointCount (D.path i).start := by
    simpa using hhub
  have hreserve' : 2 ≤ E.endpointCount (D.path i).start := by
    omega
  refine ⟨E, hsize_le, hreserve', ?_⟩
  intro v hvh hvw
  exact hother v hvh hvw

end Gallai.TwoException
