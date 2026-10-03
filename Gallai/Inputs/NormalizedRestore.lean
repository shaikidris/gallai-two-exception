/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.Inputs.MatchingBase
public import Gallai.Inputs.UniqueEvenRestore

@[expose] public section

/-! # Normalized return for the unique-even branch of the Lovasz induction -/

namespace Gallai

universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The unique-even restoration preserves the exact normalized endpoint target. -/
theorem Decomposition.restore_unique_even_normalized (x y : V) (hxy : G.Adj x y)
    (hx : Even (G.degree x))
    (hunique : ∀ v, 0 < G.degree v → Even (G.degree v) → v = x)
    (D : Decomposition (G.deleteEdges {s(x, y)}))
    (hn : ∀ v, D.endpointCount v = (G.deleteEdges {s(x, y)}).degree v % 2) :
    ∃ E : Decomposition G, E.size = D.size ∧
      ∀ v, E.endpointCount v = G.degree v % 2 := by
  have hyodd : Odd (G.degree y) := by
    apply Nat.not_even_iff_odd.mp
    intro he
    have hp := (G.degree_pos_iff_exists_adj y).mpr ⟨x, hxy.symm⟩
    exact hxy.ne.symm (hunique y hp he)
  have hdy := degree_delete_edge_add_one G y x hxy.symm
  have he : s(y, x) = s(x, y) := Sym2.eq_swap
  rw [he] at hdy
  have hny := hn y
  rw [Nat.odd_iff] at hyodd
  have hyzero : D.endpointCount y = 0 := by omega
  obtain ⟨E, hs, hb⟩ := D.restore_unique_even_edge x y hxy hx hunique
  refine ⟨E, hs, ?_⟩
  intro v
  have hp := E.endpointCount_mod_two v
  have hbalance := hb v
  have hnv := hn v
  have hbound : E.endpointCount v ≤ 1 := by
    by_cases hv : y = v
    · subst v
      have hby := hb y
      simp [hxy.ne, hyzero] at hby
      omega
    · simp only [if_neg hv] at hbalance
      split_ifs at hbalance <;> omega
  omega

end Gallai
