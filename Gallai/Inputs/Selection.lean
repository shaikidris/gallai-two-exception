/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.Inputs.Reachability

@[expose] public section

/-!
# Selecting the finite switched runs

Injective predecessor heads and the missing root spoke prevent a reachable
sequence from repeating a run. The selected finite set has an exact boundary
identity, usable for both edge multiplicities and endpoint counts.
-/

namespace Gallai.Decomposition

open scoped Finset

universe u

variable {V : Type u} {G : SimpleGraph V} [DecidableEq V]

/-- A finite reachable sequence selects distinct runs with its literal telescoping boundary. -/
theorem exists_selected_runs (D : Decomposition G) (a b v : V)
    (hmissing : ¬ G.Adj a b) (h : Relation.ReflTransGen (D.HubStep a) b v) :
    ∃ R : Finset (D.RunSlot a),
      (∀ r ∈ R, D.runEndpoint a r ≠ v) ∧
      (∀ r ∈ R, D.runEndpoint a r = b ∨ G.Adj a (D.runEndpoint a r)) ∧
      ∀ f : V → ℕ,
        (∑ r ∈ R, f (D.runEndpoint a r)) + f v =
          (∑ r ∈ R, f (D.runNeighbor a r)) + f b := by
  classical
  induction h with
  | refl => exact ⟨∅, by simp, by simp, by simp⟩
  | @tail v w hv step ih =>
    obtain ⟨R, hlast, hshape, hsum⟩ := ih
    obtain ⟨r, hr, hw⟩ := step
    have hrR : r ∉ R := fun hm => hlast r hm hr
    have hhead : ∀ s ∈ R, D.runNeighbor a s ≠ w := by
      intro s hs he
      have hsr := D.runNeighbor_injective a (he.trans hw.symm)
      exact hrR (hsr ▸ hs)
    have hwb : w ≠ b := by
      intro he
      exact hmissing (he ▸ D.hubStep_adj a v w ⟨r, hr, hw⟩)
    have hz := hsum (fun t => if t = w then 1 else 0)
    have hzero : (∑ s ∈ R, if D.runNeighbor a s = w then 1 else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro s hs
      exact if_neg (hhead s hs)
    rw [hzero, if_neg hwb.symm, Nat.zero_add] at hz
    have hvw : v ≠ w := by
      intro he
      rw [if_pos he] at hz
      omega
    have htail : ∀ s ∈ R, D.runEndpoint a s ≠ w := by
      intro s hs he
      have hle := Finset.single_le_sum
        (f := fun t : D.RunSlot a => if D.runEndpoint a t = w then 1 else 0)
        (fun t _ => Nat.zero_le _) hs
      rw [if_pos he] at hle
      omega
    refine ⟨insert r R, ?_, ?_, ?_⟩
    · intro s hs
      rcases Finset.mem_insert.mp hs with rfl | hs
      · exact hr ▸ hvw
      · exact htail s hs
    · intro s hs
      rcases Finset.mem_insert.mp hs with rfl | hs
      · rw [hr]
        exact D.reachable_eq_root_or_adj a b v hv
      · exact hshape s hs
    · intro f
      rw [Finset.sum_insert hrR, Finset.sum_insert hrR, hr, hw]
      have hh := hsum f
      omega

end Gallai.Decomposition
