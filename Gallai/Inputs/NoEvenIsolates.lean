/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.Inputs.ComponentModifiedRestore

@[expose] public section

/-! # A minimal counterexample has only triangle even components

An isolated even vertex would be the sole even neighbour of any adjacent
odd vertex. Claims 2 and 5 exclude that case, including the edgeless boundary.
-/

namespace Gallai

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- No even component of a strict minimal counterexample is a singleton. -/
theorem minimal_counterexample_even_component_not_singleton
    (hconn : G.Connected) (hcap : ∀ v, Even (G.degree v) → eDegree G v ≤ 3)
    (hnot : ¬ HasPathBudget G (Fintype.card V / 2)) (hset : ¬ IsSET G)
    (hmin : ∀ (U : Set V) [DecidablePred (· ∈ U)]
      (J : SimpleGraph U) [DecidableRel J.Adj],
      J.edgeFinset.card < G.edgeFinset.card → J.Connected →
      (∀ v, Even (J.degree v) → eDegree J v ≤ 3) →
      HasPathBudget J (Fintype.card U / 2) ∨ IsSET J)
    (C : (evenSubgraph G).ConnectedComponent) : C.supp.ncard ≠ 1 := by
  classical
  intro hcard
  obtain ⟨x, hx⟩ := Set.ncard_eq_one.mp hcard
  have hxin : x ∈ C.supp := by simp [hx]
  have hne : G ≠ ⊥ := by
    intro h
    subst G
    exact hnot ⟨Decomposition.empty, Nat.zero_le _⟩
  obtain ⟨a, b, hab⟩ := SimpleGraph.ne_bot_iff_exists_adj.mp hne
  let : Nontrivial V := ⟨⟨a, b, hab.ne⟩⟩
  obtain ⟨u, hxu⟩ := hconn.preconnected.exists_adj_of_nontrivial (x : V)
  have hu : Odd (G.degree u) := by
    apply Nat.not_even_iff_odd.mp
    intro huEven
    have huC : (⟨u, huEven⟩ : evenVertices G) ∈ C.supp :=
      C.mem_supp_of_adj_mem_supp hxin hxu
    have heq : (⟨u, huEven⟩ : evenVertices G) = x := by simpa [hx] using huC
    exact hxu.ne (congrArg Subtype.val heq).symm
  have hunique : ∀ v, G.Adj u v → Even (G.degree v) → v = (x : V) := by
    intro v huv hvEven
    let w : evenVertices G := ⟨v, hvEven⟩
    let E := (evenSubgraph G).connectedComponentMk w
    have hwE : w ∈ E.supp := by simp [E, SimpleGraph.ConnectedComponent.mem_supp_iff]
    have hCE := minimal_counterexample_odd_neighbors_one_component u hu
      hconn hcap hnot hset hmin C E ⟨x, hxin, hxu.symm⟩ ⟨w, hwE, huv⟩
    have hwC : w ∈ C.supp := by rw [hCE]; exact hwE
    have hwx : w = x := by simpa [hx] using hwC
    exact congrArg Subtype.val hwx
  have hneighbors : evenNeighbors G u = {(x : V)} := by
    ext v
    simp only [mem_evenNeighbors, Finset.mem_singleton]
    constructor
    · exact fun h => hunique v h.1 h.2
    · intro h
      subst v
      exact ⟨hxu.symm, x.property⟩
  apply minimal_counterexample_eDegree_ne_one hconn hcap hnot hset hmin u
  simp [eDegree, hneighbors]

/-- Every even component is a complete three-vertex graph, not merely a
triangle-or-isolate alternative. This is the source's next structural input. -/
theorem minimal_counterexample_even_components_triangles
    (hconn : G.Connected) (hcap : ∀ v, Even (G.degree v) → eDegree G v ≤ 3)
    (hnot : ¬ HasPathBudget G (Fintype.card V / 2)) (hset : ¬ IsSET G)
    (hmin : ∀ (U : Set V) [DecidablePred (· ∈ U)]
      (J : SimpleGraph U) [DecidableRel J.Adj],
      J.edgeFinset.card < G.edgeFinset.card → J.Connected →
      (∀ v, Even (J.degree v) → eDegree J v ≤ 3) →
      HasPathBudget J (Fintype.card U / 2) ∨ IsSET J)
    (C : (evenSubgraph G).ConnectedComponent) :
    C.supp.ncard = 3 ∧ C.toSimpleGraph = ⊤ := by
  obtain ⟨hcard, hcomplete⟩ := minimal_counterexample_even_components
    hconn hcap hnot hset hmin C
  exact ⟨hcard.resolve_left (minimal_counterexample_even_component_not_singleton
    hconn hcap hnot hset hmin C), hcomplete⟩

end Gallai
