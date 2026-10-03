/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.Inputs.DonorComponent
public import Gallai.Operations.PartitionAssembly

@[expose] public section

/-! # No unique even neighbour in a minimal counterexample

This is Claim 2 as a guarded minimal-counterexample consumer, not the global
floor-or-SET theorem. Component witnesses are constructed before restoration.
-/

namespace Gallai

universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- An existing unique-even-neighbour edge contradicts smaller-edge minimality.
Equal and distinct puncture-component cases both assemble actual decompositions. -/
theorem unique_even_neighbor_contradiction (x y : V) (hxy : G.Adj x y)
    (hy : Even (G.degree y))
    (hu : ∀ v, G.Adj x v → Even (G.degree v) → v = y)
    (hconn : G.Connected) (hcap : ∀ v, Even (G.degree v) → eDegree G v ≤ 3)
    (hnot : ¬ HasPathBudget G (Fintype.card V / 2)) (hset : ¬ IsSET G)
    (hmin : ∀ (U : Set V) [DecidablePred (· ∈ U)]
      (J : SimpleGraph U) [DecidableRel J.Adj],
      J.edgeFinset.card < G.edgeFinset.card → J.Connected →
      (∀ v, Even (J.degree v) → eDegree J v ≤ 3) →
      HasPathBudget J (Fintype.card U / 2) ∨ IsSET J) : False := by
  classical
  let H := G.deleteEdges {s(x, y)}
  let Cx := H.connectedComponentMk x
  let Cy := H.connectedComponentMk y
  have hS := unique_even_neighbor_all_components_floor x y hxy hy hu hconn hcap hnot hset hmin Cx
  have hT := unique_even_neighbor_all_components_floor x y hxy hy hu hconn hcap hnot hset hmin Cy
  have hcover (v : V) : v ∈ Cx.supp ∨ v ∈ Cy.supp := by
    rcases edge_puncture_reachable_from_end hconn x y v with h | h
    · exact Or.inl (SimpleGraph.ConnectedComponent.sound h).symm
    · exact Or.inr (SimpleGraph.ConnectedComponent.sound h).symm
  have hp : HasPathBudget H (Fintype.card V / 2) := by
    by_cases he : Cx = Cy
    · apply floor_of_induce_all H Cx.supp ?_ hS
      intro v
      rcases hcover v with h | h
      · exact h
      · simpa only [he] using h
    · exact floor_of_closed_partition H Cx.supp Cy.supp
        (Set.eq_univ_of_forall hcover) (H.pairwise_disjoint_supp_connectedComponent he)
        (fun _ hv _ hw => Cx.mem_supp_of_adj_mem_supp hv hw)
        (fun _ hv _ hw => Cy.mem_supp_of_adj_mem_supp hv hw) hS hT
  obtain ⟨D, hD⟩ := hp
  obtain ⟨E, hE, _⟩ := D.restore_unique_even_neighbor x y hxy hy hu
  exact hnot ⟨E, hE.le.trans hD⟩

/-- Theorem 13 Claim 2: every vertex of a minimal counterexample has E-degree
different from one. The smaller-graph hypothesis retains its strict measure guard. -/
theorem minimal_counterexample_eDegree_ne_one
    (hconn : G.Connected) (hcap : ∀ v, Even (G.degree v) → eDegree G v ≤ 3)
    (hnot : ¬ HasPathBudget G (Fintype.card V / 2)) (hset : ¬ IsSET G)
    (hmin : ∀ (U : Set V) [DecidablePred (· ∈ U)]
      (J : SimpleGraph U) [DecidableRel J.Adj],
      J.edgeFinset.card < G.edgeFinset.card → J.Connected →
      (∀ v, Even (J.degree v) → eDegree J v ≤ 3) →
      HasPathBudget J (Fintype.card U / 2) ∨ IsSET J) (x : V) :
    eDegree G x ≠ 1 := by
  classical
  intro hx
  obtain ⟨y, hy⟩ := Finset.card_eq_one.mp hx
  have hm : y ∈ evenNeighbors G x := by rw [hy]; exact Finset.mem_singleton_self _
  obtain ⟨hxy, hey⟩ := (mem_evenNeighbors x y).mp hm
  apply unique_even_neighbor_contradiction x y hxy hey ?_ hconn hcap hnot hset hmin
  intro v hv he
  have hm := (mem_evenNeighbors x v).mpr ⟨hv, he⟩
  simpa only [hy, Finset.mem_singleton] using hm

end Gallai
