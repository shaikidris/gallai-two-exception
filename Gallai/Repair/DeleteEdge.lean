/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.Repair.TerminalEdge
public import Gallai.Operations.DecompositionSplit

@[expose] public section

/-!
# Arbitrary edge deletion with exact endpoint accounting

If neither end of the selected edge is terminal on its carrier, split at
one end first. The edge then lies on a terminal carrier, and trimming it
gives the internal-edge case. All identities use balanced natural counts.
-/

namespace Gallai.Decomposition

universe u

variable {V : Type u} {G : SimpleGraph V} [DecidableEq V]

/-- The retained split index carries the prefix ending at the cut. -/
theorem splitAt_path_left (D : Decomposition G) (i : Fin D.size) (v : V)
    (hv : v ∈ (D.path i).walk.support) (hs : (D.path i).start ≠ v)
    (ht : v ≠ (D.path i).finish) :
    (D.splitAt i v hv hs ht).path i.castSucc = (D.path i).takeTo v hv hs := by
  change Fin.lastCases (motive := fun _ => NonemptyPath G) ((D.path i).dropFrom v hv ht)
    (fun j => if j = i then (D.path i).takeTo v hv hs else D.path j) i.castSucc = _
  rw [Fin.lastCases_castSucc, if_pos rfl]

/-- The new last index carries the suffix starting at the cut. -/
theorem splitAt_path_right (D : Decomposition G) (i : Fin D.size) (v : V)
    (hv : v ∈ (D.path i).walk.support) (hs : (D.path i).start ≠ v)
    (ht : v ≠ (D.path i).finish) :
    (D.splitAt i v hv hs ht).path (Fin.last D.size) = (D.path i).dropFrom v hv ht := by
  change Fin.lastCases (motive := fun _ => NonemptyPath G) ((D.path i).dropFrom v hv ht)
    (fun j => if j = i then (D.path i).takeTo v hv hs else D.path j) (Fin.last D.size) = _
  rw [Fin.lastCases_last]

/-- Deleting an internal edge creates one path and one endpoint at each end. -/
theorem exists_delete_internal (D : Decomposition G) (i : Fin D.size) (x y : V)
    (he : s(x, y) ∈ (D.path i).walk.edges)
    (hxs : (D.path i).start ≠ x) (hxt : (D.path i).finish ≠ x)
    (hys : (D.path i).start ≠ y) (hyt : (D.path i).finish ≠ y) :
    ∃ E : Decomposition (G.deleteEdges {s(x, y)}),
      E.size = D.size + 1 ∧ E.endpointCount x = D.endpointCount x + 1 ∧
      E.endpointCount y = D.endpointCount y + 1 ∧
      ∀ w, w ≠ x → w ≠ y → E.endpointCount w = D.endpointCount w := by
  have hxy : x ≠ y := (show G.Adj x y from (D.path i).walk.edges_subset_edgeSet he).ne
  have hv := (D.path i).walk.fst_mem_support_of_mem_edges he
  let D₁ := D.splitAt i x hv hxs hxt.symm
  have hleft := D.splitAt_path_left i x hv hxs hxt.symm
  have hright := D.splitAt_path_right i x hv hxs hxt.symm
  have hselected : ∃ j : Fin D₁.size,
      s(x, y) ∈ (D₁.path j).walk.edges ∧
      ((D₁.path j).start = x ∨ (D₁.path j).finish = x) ∧
      ¬ ((D₁.path j).start = y ∨ (D₁.path j).finish = y) := by
    rw [← (D.path i).prefix_edges_append_suffix_edges x hv hxs hxt.symm,
      List.mem_append] at he
    rcases he with he | he
    · refine ⟨i.castSucc, ?_, ?_, ?_⟩
      · change s(x, y) ∈ ((D.splitAt i x hv hxs hxt.symm).path i.castSucc).walk.edges
        rw [hleft]
        exact he
      · rw [hleft]
        exact Or.inr rfl
      · rw [hleft]
        exact not_or.mpr ⟨hys, hxy⟩
    · refine ⟨Fin.last D.size, ?_, ?_, ?_⟩
      · change s(x, y) ∈
          ((D.splitAt i x hv hxs hxt.symm).path (Fin.last D.size)).walk.edges
        rw [hright]
        exact he
      · rw [hright]
        exact Or.inl rfl
      · rw [hright]
        exact not_or.mpr ⟨hxy, hyt⟩
  obtain ⟨j, hj, hx, hy⟩ := hselected
  obtain ⟨E, hsize, hex, hey, hother⟩ := D₁.exists_delete_terminal j x y hj hx
  simp only [if_neg hy, Nat.add_zero] at hsize hey
  have hcount (w : V) : D₁.endpointCount w =
      D.endpointCount w + (if x = w then 2 else 0) :=
    D.splitAt_endpointCount i x hv hxs hxt.symm w
  refine ⟨E, hsize.trans (D.splitAt_size i x hv hxs hxt.symm), ?_, ?_, ?_⟩
  · rw [hcount] at hex
    simp only [if_true] at hex
    omega
  · simpa only [hcount, if_neg hxy, Nat.add_zero] using hey
  · intro w hwx hwy
    rw [hother w hwx hwy, hcount, if_neg hwx.symm, Nat.add_zero]

/-- Every chosen edge has an exact deletion within its terminality-dependent budget. -/
theorem exists_delete_edge (D : Decomposition G) (i : Fin D.size) (x y : V)
    (he : s(x, y) ∈ (D.path i).walk.edges) :
    ∃ E : Decomposition (G.deleteEdges {s(x, y)}),
      E.size + (if (D.path i).start = x ∨ (D.path i).finish = x then 1 else 0) +
          (if (D.path i).start = y ∨ (D.path i).finish = y then 1 else 0) = D.size + 1 ∧
      E.endpointCount x + (if (D.path i).start = x ∨ (D.path i).finish = x then 2 else 0) =
        D.endpointCount x + 1 ∧
      E.endpointCount y + (if (D.path i).start = y ∨ (D.path i).finish = y then 2 else 0) =
        D.endpointCount y + 1 ∧
      ∀ w, w ≠ x → w ≠ y → E.endpointCount w = D.endpointCount w := by
  by_cases hx : (D.path i).start = x ∨ (D.path i).finish = x
  · obtain ⟨E, hsize, hex, hey, hother⟩ := D.exists_delete_terminal i x y he hx
    refine ⟨E, ?_, ?_, hey, hother⟩
    · rw [if_pos hx]
      omega
    · rw [if_pos hx]
      omega
  · by_cases hy : (D.path i).start = y ∨ (D.path i).finish = y
    · have he' : s(y, x) ∈ (D.path i).walk.edges := Sym2.eq_swap ▸ he
      have h := D.exists_delete_terminal i y x he' hy
      rw [show s(y, x) = s(x, y) from Sym2.eq_swap] at h
      obtain ⟨E, hsize, hey, hex, hother⟩ := h
      refine ⟨E, ?_, hex, ?_, fun w hwx hwy => hother w hwy hwx⟩
      · simp only [if_neg hx, Nat.add_zero] at hsize ⊢
        rw [if_pos hy, hsize]
      · rw [if_pos hy]
        omega
    · obtain ⟨hxs, hxt⟩ := not_or.mp hx
      obtain ⟨hys, hyt⟩ := not_or.mp hy
      obtain ⟨E, hsize, hex, hey, hother⟩ :=
        D.exists_delete_internal i x y he hxs hxt hys hyt
      refine ⟨E, ?_, ?_, ?_, hother⟩ <;>
        simp only [if_neg hx, if_neg hy, Nat.add_zero] <;> assumption

end Gallai.Decomposition
