/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.Inputs.OneExceptionRemoteParity

@[expose] public section

/-! # The final cap-two consequence once the designated E-degree vanishes -/

namespace Gallai

universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

/-- After the designated E-degree is zero, every other even vertex is remote
from x. The already-proved remote parity claim reduces its cap three to two.
The zero hypothesis is explicit: proving it remains a separate obligation. -/
theorem one_exception_cap_two_of_designated_zero (G : SimpleGraph V)
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
          2 ≤ D.endpointCount y)
    (hxzero : eDegree G x = 0) :
    ∀ v, Even (G.degree v) → eDegree G v ≤ 2 := by
  intro v hv
  by_cases hvx : v = x
  · subst v
    omega
  · have hmissing : ¬ G.Adj v x := by
      intro ha
      have hm : v ∈ evenNeighbors G x := (mem_evenNeighbors x v).mpr ⟨ha.symm, hv⟩
      have hp : 0 < eDegree G x := Finset.card_pos.mpr ⟨v, hm⟩
      omega
    have he := one_exception_nonadjacent_eDegree_even G x hconn hxpos hxEven hcap
      hnot hmin v hv hvx hmissing
    have hc := hcap v hv hvx
    rw [Nat.even_iff] at he
    omega

end Gallai
