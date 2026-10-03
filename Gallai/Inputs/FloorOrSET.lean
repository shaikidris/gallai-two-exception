/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.Inputs.FloorOrSETEndgame

@[expose] public section

/-! # The unconditional floor-or-SET theorem -/

namespace Gallai

universe u

/-- Every connected finite simple graph with even-subgraph maximum degree at
most three has a floor-budget path decomposition or is a SET graph. All
smaller-graph inputs are discharged by strict edge-count induction. -/
theorem floor_or_set {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hconn : G.Connected) (hcap : ∀ v, Even (G.degree v) → eDegree G v ≤ 3) :
    HasPathBudget G (Fintype.card V / 2) ∨ IsSET G := by
  classical
  suffices hall : ∀ n : ℕ, ∀ (W : Type u) [Fintype W] [DecidableEq W]
      (J : SimpleGraph W) [DecidableRel J.Adj],
      J.edgeFinset.card = n → J.Connected →
      (∀ w, Even (J.degree w) → eDegree J w ≤ 3) →
      HasPathBudget J (Fintype.card W / 2) ∨ IsSET J by
    exact hall G.edgeFinset.card V G rfl hconn hcap
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro W _ _ J _ hn hconnJ hcapJ
    by_cases hf : HasPathBudget J (Fintype.card W / 2)
    · exact Or.inl hf
    by_cases hs : IsSET J
    · exact Or.inr hs
    exfalso
    apply minimal_counterexample_floor_or_set_false hconnJ hcapJ hf hs
    intro U _ K _ hlt hconnK hcapK
    exact ih K.edgeFinset.card (by omega) U K rfl hconnK hcapK

end Gallai
