/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.Inputs.OneExceptionEndgame

@[expose] public section

/-! # The unconditional one-exception endpoint theorem

The designated vertex has positive even degree because project decompositions
contain nonempty paths. All recursive premises are discharged by edge induction.
-/

namespace Gallai

universe u

/-- Fan--Hou--Zhou's endpoint theorem in the nonempty-path convention: a
connected graph with at most one E-degree exception admits a ceiling-budget
decomposition exposing its designated positive-degree even vertex twice. -/
theorem one_exception_endpoint {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V) (hconn : G.Connected)
    (hxpos : 0 < G.degree x) (hxEven : Even (G.degree x))
    (hcap : ∀ v, Even (G.degree v) → v ≠ x → eDegree G v ≤ 3) :
    ∃ D : Decomposition G, D.size ≤ (Fintype.card V + 1) / 2 ∧
      2 ≤ D.endpointCount x := by
  classical
  suffices hall : ∀ n : ℕ, ∀ (W : Type u) [Fintype W] [DecidableEq W]
      (J : SimpleGraph W) [DecidableRel J.Adj], J.edgeFinset.card = n →
      ∀ y : W, J.Connected → 0 < J.degree y → Even (J.degree y) →
        (∀ v, Even (J.degree v) → v ≠ y → eDegree J v ≤ 3) →
        ∃ D : Decomposition J, D.size ≤ (Fintype.card W + 1) / 2 ∧
          2 ≤ D.endpointCount y by
    exact hall G.edgeFinset.card V G rfl x hconn hxpos hxEven hcap
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro W _ _ J _ hn y hc hp he hcapJ
    by_contra hnot
    apply one_exception_minimal_false J y hc hp he hcapJ hnot
    intro U _ _ K _ hlt hcK z hpK heK hcapK
    exact ih K.edgeFinset.card (by omega) U K rfl z hcK hpK heK hcapK

end Gallai
