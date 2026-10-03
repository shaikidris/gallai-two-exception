/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.Structure.OneExceptionStarPuncture
public import Gallai.Inputs.OddEvenStarRestore
public import Gallai.Inputs.OneExceptionCutSelf

@[expose] public section

/-! # Odd E-degree at the designated vertex is reducible

The connected puncture has a floor decomposition by the proved floor-or-SET
theorem. Odd-star restoration preserves this budget and exposes the hub twice.
-/

namespace Gallai

universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

/-- An even designated hub of odd E-degree satisfies the stronger floor bound
when its deletion is connected. No supplied puncture decomposition is needed. -/
theorem one_exception_of_odd_eDegree (G : SimpleGraph V) [DecidableRel G.Adj]
    (x : V) (hx : Even (G.degree x)) (ho : Odd (eDegree G x))
    (hcap : ∀ v, Even (G.degree v) → v ≠ x → eDegree G v ≤ 3)
    (hc : (G.induce {v | v ≠ x}).Connected) :
    ∃ D : Decomposition G, D.size ≤ Fintype.card V / 2 ∧ 2 ≤ D.endpointCount x := by
  obtain ⟨D, hd⟩ := one_exception_evenStarPuncture_floor G x hcap
    (odd_evenStarPuncture_connected G x hx ho hc)
  obtain ⟨P, hs, hp⟩ := D.restore_odd_even_star_exposing x hx ho
    (fun v hv => hcap v ((mem_evenNeighbors x v).mp hv).2
      ((mem_evenNeighbors x v).mp hv).1.ne.symm)
  exact ⟨P, by omega, hp⟩

/-- The designated-vertex part of the E-degree parity claim in a strict
minimum counterexample. Claim 1 supplies the connected deletion internally. -/
theorem one_exception_designated_eDegree_even (G : SimpleGraph V)
    [DecidableRel G.Adj] (x : V) (hconn : G.Connected)
    (hxpos : 0 < G.degree x) (hxEven : Even (G.degree x))
    (hcap : ∀ v, Even (G.degree v) → v ≠ x → eDegree G v ≤ 3)
    (hnot : ¬ ∃ D : Decomposition G,
      D.size ≤ (Fintype.card V + 1) / 2 ∧ 2 ≤ D.endpointCount x)
    (hmin : ∀ (W : Type u) [Fintype W] [DecidableEq W]
      (J : SimpleGraph W) [DecidableRel J.Adj],
      J.edgeFinset.card < G.edgeFinset.card → J.Connected →
      ∀ y : W, 0 < J.degree y → Even (J.degree y) →
        (∀ v, Even (J.degree v) → v ≠ y → eDegree J v ≤ 3) →
        ∃ D : Decomposition J, D.size ≤ (Fintype.card W + 1) / 2 ∧
          2 ≤ D.endpointCount y) : Even (eDegree G x) := by
  by_contra hn
  have hc := one_exception_delete_self_connected G x hconn hxpos hxEven hcap hnot hmin
  obtain ⟨D, hd, he⟩ := one_exception_of_odd_eDegree G x hxEven
    (Nat.not_even_iff_odd.mp hn) hcap hc
  exact hnot ⟨D, by omega, he⟩

end Gallai
