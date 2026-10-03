/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.Structure.TriangleHubLabels

@[expose] public section

/-! # Local triangle deletion in the odd-neighbour component argument

A full triangle loses three spokes. A partial triangle loses the first spoke
and the opposite edge. Every private vertex loses exactly one incident edge.
-/

namespace Gallai

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Source Claim 5's local removed graph for ordered triangle labels. -/
def triangleHubDeletion (G : SimpleGraph V) [DecidableRel G.Adj] (u a b c : V) :
    SimpleGraph V :=
  if G.Adj u c then SimpleGraph.edge u a ⊔ SimpleGraph.edge u b ⊔ SimpleGraph.edge u c
  else SimpleGraph.edge u a ⊔ SimpleGraph.edge b c

omit [DecidableEq V] in
/-- Ordered adjacency guarantees that every selected deletion edge exists. -/
theorem triangleHubDeletion_le (u a b c : V) (ha : G.Adj u a)
    (horder : G.Adj u c → G.Adj u b) (hbc : G.Adj b c) :
    triangleHubDeletion G u a b c ≤ G := by
  unfold triangleHubDeletion
  split_ifs with hc
  · exact sup_le (sup_le ((SimpleGraph.edge_le_iff G).mpr (Or.inr ha))
      ((SimpleGraph.edge_le_iff G).mpr (Or.inr (horder hc))))
      ((SimpleGraph.edge_le_iff G).mpr (Or.inr hc))
  · exact sup_le ((SimpleGraph.edge_le_iff G).mpr (Or.inr ha))
      ((SimpleGraph.edge_le_iff G).mpr (Or.inr hbc))

variable [Fintype V]

/-- Finite adjacency decision for the selected local deletion graph. -/
noncomputable local instance triangleDeletionAdj (u a b c : V) :
    DecidableRel (triangleHubDeletion G u a b c).Adj :=
  fun _ _ => Classical.propDecidable _

/-- The complete local degree vector: one at each triangle vertex, one or
three at the hub, and zero elsewhere. This is independent of the middle
vertex's adjacency to the hub in the partial case. -/
theorem triangleHubDeletion_degree (u a b c : V)
    (hua : u ≠ a) (hub : u ≠ b) (huc : u ≠ c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (v : V) :
    (triangleHubDeletion G u a b c).degree v =
      if v = u then (if G.Adj u c then 3 else 1)
      else if v = a ∨ v = b ∨ v = c then 1 else 0 := by
  classical
  let F := triangleHubDeletion G u a b c
  have hn : F.neighborFinset v =
      if v = u then (if G.Adj u c then {a, b, c} else {a})
      else if v = a then {u}
      else if v = b then (if G.Adj u c then {u} else {c})
      else if v = c then (if G.Adj u c then {u} else {b}) else ∅ := by
    ext w
    rw [SimpleGraph.mem_neighborFinset]
    by_cases hfull : G.Adj u c <;>
      by_cases hvu : v = u <;> by_cases hva : v = a <;>
      by_cases hvb : v = b <;> by_cases hvc : v = c <;>
      simp_all [F, triangleHubDeletion, SimpleGraph.edge_adj, eq_comm] <;> aesop
  change F.degree v = _
  rw [← SimpleGraph.card_neighborFinset_eq_degree, hn]
  by_cases hfull : G.Adj u c <;>
    by_cases hvu : v = u <;> by_cases hva : v = a <;>
    by_cases hvb : v = b <;> by_cases hvc : v = c <;>
    simp_all

end Gallai
