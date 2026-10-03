/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.Repair.DeleteEdge
public import Gallai.Repair.Exposure

@[expose] public section

/-!
# Endpoint-preserving edge deletion and its exact repair cost

Delete the chosen edge, then split precisely at endpoints whose counts became
zero. The terminal reserve counts the original terminal endpoints with at
least three occurrences. The resulting cost is exactly one minus that reserve.
This is the cost of this construction, not a minimum-cost assertion.
-/

namespace Gallai.Decomposition

open scoped Finset

universe u

variable {V : Type u} {G : SimpleGraph V} [DecidableEq V]

/-- Terminal ends of the selected carrier having at least three original endpoint occurrences. -/
def terminalReserve (D : Decomposition G) (i : Fin D.size) (x y : V) : ℕ :=
  #(({x, y} : Finset V).filter fun v =>
    ((D.path i).start = v ∨ (D.path i).finish = v) ∧ 3 ≤ D.endpointCount v)

/-- For distinct edge ends, the reserve is the sum of the two endpoint indicators. -/
theorem terminalReserve_eq (D : Decomposition G) (i : Fin D.size) (x y : V) (hxy : x ≠ y) :
    D.terminalReserve i x y =
      (if ((D.path i).start = x ∨ (D.path i).finish = x) ∧ 3 ≤ D.endpointCount x
        then 1 else 0) +
      (if ((D.path i).start = y ∨ (D.path i).finish = y) ∧ 3 ≤ D.endpointCount y
        then 1 else 0) := by
  by_cases hx : ((D.path i).start = x ∨ (D.path i).finish = x) ∧ 3 ≤ D.endpointCount x <;>
    by_cases hy : ((D.path i).start = y ∨ (D.path i).finish = y) ∧ 3 ≤ D.endpointCount y <;>
    simp only [terminalReserve, Finset.filter_insert, Finset.filter_singleton,
      hx, hy, if_false] <;> simp [hxy]

private theorem repair_flag_accounting (a b : ℕ) (p : Prop) [Decidable p]
    (h : b + (if p then 2 else 0) = a + 1) (hb : b % 2 = 0) :
    (if p then 1 else 0) = (if b = 0 then 1 else 0) + (if p ∧ 3 ≤ a then 1 else 0) := by
  by_cases hp : p
  · simp only [if_pos hp] at h
    by_cases hz : b = 0
    · have ha : a = 1 := by omega
      simp [hp, hz, ha]
    · have ha : 3 ≤ a := by omega
      simp [hp, hz, ha]
  · simp only [if_neg hp, Nat.add_zero] at h
    have hz : b ≠ 0 := by omega
    simp [hp, hz]

variable [Fintype V] [DecidableRel G.Adj]

/-- Deletion followed by necessary exposure repairs has exact balanced cost one minus reserve. -/
theorem exists_delete_edge_repair (D : Decomposition G) (i : Fin D.size) (x y : V)
    (he : s(x, y) ∈ (D.path i).walk.edges)
    (hxp : 0 < (G.deleteEdges {s(x, y)}).degree x)
    (hxe : Even ((G.deleteEdges {s(x, y)}).degree x))
    (hyp : 0 < (G.deleteEdges {s(x, y)}).degree y)
    (hye : Even ((G.deleteEdges {s(x, y)}).degree y)) :
    ∃ E : Decomposition (G.deleteEdges {s(x, y)}),
      E.size + D.terminalReserve i x y = D.size + 1 ∧
      2 ≤ E.endpointCount x ∧ 2 ≤ E.endpointCount y ∧
      ∀ w, w ≠ x → w ≠ y → E.endpointCount w = D.endpointCount w := by
  have hxy : x ≠ y := (show G.Adj x y from (D.path i).walk.edges_subset_edgeSet he).ne
  obtain ⟨D₁, hsize₁, hex, hey, hother₁⟩ := D.exists_delete_edge i x y he
  obtain ⟨D₂, hsize₂, hx, hy, hother₂⟩ :=
    D₁.exists_expose_two_even x y hxy hxp hxe hyp hye
  have hparx : D₁.endpointCount x % 2 = 0 :=
    (D₁.endpointCount_mod_two x).trans (Nat.even_iff.mp hxe)
  have hpary : D₁.endpointCount y % 2 = 0 :=
    (D₁.endpointCount_mod_two y).trans (Nat.even_iff.mp hye)
  have hflagx := repair_flag_accounting _ _ _ hex hparx
  have hflagy := repair_flag_accounting _ _ _ hey hpary
  refine ⟨D₂, ?_, hx, hy, ?_⟩
  · rw [hsize₂, D.terminalReserve_eq i x y hxy]
    omega
  · intro w hwx hwy
    rw [hother₂ w hwx hwy, hother₁ w hwx hwy]

/-- Exact endpoint-repair cost for any actual carrier of the deleted edge. -/
theorem endpoint_preserving_edge_deletion_exact (D : Decomposition G)
    (i : Fin D.size) (x y : V) (he : s(x, y) ∈ (D.path i).walk.edges)
    (hxp : 0 < (G.deleteEdges {s(x, y)}).degree x)
    (hxe : Even ((G.deleteEdges {s(x, y)}).degree x))
    (hyp : 0 < (G.deleteEdges {s(x, y)}).degree y)
    (hye : Even ((G.deleteEdges {s(x, y)}).degree y)) :
    ∃ E : Decomposition (G.deleteEdges {s(x, y)}),
      E.size = D.size + 1 - D.terminalReserve i x y ∧
      2 ≤ E.endpointCount x ∧ 2 ≤ E.endpointCount y ∧
      ∀ w, w ≠ x → w ≠ y → E.endpointCount w = D.endpointCount w := by
  obtain ⟨E, hsize, hx, hy, hother⟩ := D.exists_delete_edge_repair i x y he hxp hxe hyp hye
  exact ⟨E, by omega, hx, hy, hother⟩

/-- Removing any edge with positive even residual end degrees costs at most one path. -/
theorem endpoint_preserving_edge_deletion (D : Decomposition G) (x y : V) (he : G.Adj x y)
    (hxp : 0 < (G.deleteEdges {s(x, y)}).degree x)
    (hxe : Even ((G.deleteEdges {s(x, y)}).degree x))
    (hyp : 0 < (G.deleteEdges {s(x, y)}).degree y)
    (hye : Even ((G.deleteEdges {s(x, y)}).degree y)) :
    ∃ E : Decomposition (G.deleteEdges {s(x, y)}),
      E.size ≤ D.size + 1 ∧ 2 ≤ E.endpointCount x ∧ 2 ≤ E.endpointCount y ∧
      ∀ w, w ≠ x → w ≠ y → E.endpointCount w = D.endpointCount w := by
  obtain ⟨i, hi, _⟩ := D.covers s(x, y) he
  obtain ⟨E, hsize, hx, hy, hother⟩ := D.exists_delete_edge_repair i x y hi hxp hxe hyp hye
  exact ⟨E, by omega, hx, hy, hother⟩

end Gallai.Decomposition
