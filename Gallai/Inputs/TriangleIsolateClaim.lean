/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.Structure.CliqueComponents
public import Gallai.Inputs.EvenNeighborClosure

@[expose] public section

/-! # Claim 4: every even-subgraph component is a triangle or an isolate -/

namespace Gallai

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Literal component version of source Claim 4, under strict minimality. -/
theorem minimal_counterexample_even_components
    (hconn : G.Connected) (hcap : ∀ v, Even (G.degree v) → eDegree G v ≤ 3)
    (hnot : ¬ HasPathBudget G (Fintype.card V / 2)) (hset : ¬ IsSET G)
    (hmin : ∀ (U : Set V) [DecidablePred (· ∈ U)]
      (J : SimpleGraph U) [DecidableRel J.Adj],
      J.edgeFinset.card < G.edgeFinset.card → J.Connected →
      (∀ v, Even (J.degree v) → eDegree J v ≤ 3) →
      HasPathBudget J (Fintype.card U / 2) ∨ IsSET J)
    (C : (evenSubgraph G).ConnectedComponent) :
    (C.supp.ncard = 1 ∨ C.supp.ncard = 3) ∧ C.toSimpleGraph = ⊤ := by
  apply components_singleton_or_triangle
  · intro v
    rw [← eDegree_eq_induced_degree v]
    exact minimal_counterexample_even_eDegree_zero_or_two hconn hcap hnot hset hmin v v.property
  · intro u a b hua hub hab
    exact minimal_counterexample_even_neighbor_clique hconn hcap hnot hset hmin
      u a b u.property ((mem_evenNeighbors (G := G) u a).mpr ⟨hua, a.property⟩)
      ((mem_evenNeighbors (G := G) u b).mpr ⟨hub, b.property⟩)
      (fun h => hab (Subtype.ext h))

end Gallai
