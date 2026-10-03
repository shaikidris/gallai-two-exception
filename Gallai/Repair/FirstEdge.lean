/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.Operations.DecompositionTrim
public import Gallai.Operations.EraseCarrier

@[expose] public section

/-!
# Exact deletion of a selected carrier's first edge

The remainder is either a shorter nonempty carrier or nothing. The balanced
natural-number identities retain the negative cost of erasing a single edge
without truncating subtraction or counting a trivial path.
-/

namespace Gallai

universe u

variable {V : Type u} {G : SimpleGraph V}

/-- The second vertex is the final vertex exactly for a one-edge simple path. -/
theorem NonemptyPath.snd_eq_finish_iff (P : NonemptyPath G) :
    P.walk.snd = P.finish ↔ P.walk.length = 1 :=
  P.isPath.tail.nil_iff_eq.symm.trans P.tail_nil_iff_length_one

variable [DecidableEq V]

/-- Delete the first edge, recording exact size, both endpoint changes and all other counts. -/
theorem Decomposition.exists_delete_first (D : Decomposition G) (i : Fin D.size) :
    ∃ E : Decomposition (G.deleteEdges {s((D.path i).start, (D.path i).walk.snd)}),
      E.size + (if (D.path i).walk.length = 1 then 1 else 0) = D.size ∧
      E.endpointCount (D.path i).start + 1 = D.endpointCount (D.path i).start ∧
      E.endpointCount (D.path i).walk.snd +
          (if (D.path i).walk.length = 1 then 2 else 0) =
        D.endpointCount (D.path i).walk.snd + 1 ∧
      ∀ w, w ≠ (D.path i).start → w ≠ (D.path i).walk.snd →
        E.endpointCount w = D.endpointCount w := by
  have hne : (D.path i).start ≠ (D.path i).walk.snd :=
    ((D.path i).walk.adj_snd (D.path i).nonempty).ne
  by_cases hone : (D.path i).walk.length = 1
  · have hfinish := (D.path i).snd_eq_finish_iff.mpr hone
    rw [← D.singleCarrier_deletedGraph i hone]
    refine ⟨D.eraseCarrier i, ?_, ?_, ?_, ?_⟩
    · rw [D.eraseCarrier_size, if_pos hone]
      have hi := i.isLt
      omega
    · have h := D.eraseCarrier_endpointCount i (D.path i).start
      simpa [← hfinish, hne.symm] using h
    · have h := D.eraseCarrier_endpointCount i (D.path i).walk.snd
      simp only [← hfinish, if_neg hne, if_true, zero_add] at h
      rw [if_pos hone]
      omega
    · intro w hws hwt
      have h := D.eraseCarrier_endpointCount i w
      simpa [← hfinish, hws.symm, hwt.symm] using h
  · have hpos := SimpleGraph.Walk.not_nil_iff_lt_length.mp (D.path i).nonempty
    have hlong : 1 < (D.path i).walk.length := by omega
    refine ⟨D.trimFirst i hlong, ?_, ?_, ?_, ?_⟩
    · simp [hone]
    · have h := D.trimFirst_endpointCount i hlong (D.path i).start
      simpa [hne.symm] using h
    · have h := D.trimFirst_endpointCount i hlong (D.path i).walk.snd
      simpa [hone, hne] using h
    · intro w hws hwt
      have h := D.trimFirst_endpointCount i hlong w
      simpa [hws.symm, hwt.symm] using h

end Gallai
