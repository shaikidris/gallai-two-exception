/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.Inputs.ComponentModifiedShape

@[expose] public section

/-! # The modified component puncture has the source's floor budget -/

namespace Gallai

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {u : V}

/-- Decision instance for the modified removed graph. -/
noncomputable local instance modifiedFloorAdj
    (d : ∀ C : (evenSubgraph G).ConnectedComponent, ComponentDeletionChoice G u C)
    (e : V × V) : DecidableRel (componentModifiedDeletion d e).Adj :=
  fun _ _ => Classical.propDecidable _

/-- Decision instance for the original component deletion. -/
noncomputable local instance unmodifiedFloorAdj
    (d : ∀ C : (evenSubgraph G).ConnectedComponent, ComponentDeletionChoice G u C) :
    DecidableRel (componentDeletionUnion d).Adj := fun _ _ => Classical.propDecidable _

/-- Every originally even hub neighbour remains active after the exchange.
The sole removed matching donor is not a hub neighbour. -/
theorem componentModifiedDeletion_covers
    (d : ∀ C : (evenSubgraph G).ConnectedComponent, ComponentDeletionChoice G u C)
    (hu : Odd (G.degree u)) (e : V × V) (he : e ∈ componentDeletionPairs d)
    (ha : G.Adj u e.1) (v : V) (hv : Even (G.degree v)) (huv : G.Adj u v) :
    0 < (componentModifiedDeletion d e).degree v := by
  classical
  have hp := componentDeletionUnion_covers d hu v hv huv
  obtain ⟨w, hw⟩ := ((componentDeletionUnion d).degree_pos_iff_exists_adj v).mp hp
  have hle : componentDeletionUnion d ≤
      componentModifiedDeletion d e ⊔ SimpleGraph.edge e.1 e.2 := by
    rw [componentModifiedDeletion_exchange d e he]
    exact le_sup_left
  rcases hle hw with h | h
  · exact h.degree_pos_left
  · rcases (SimpleGraph.edge_adj ..).mp h with ⟨⟨h, _⟩ | ⟨h, _⟩, _⟩
    · subst v
      have hnew : (componentModifiedDeletion d e).Adj e.1 u := by
        apply Or.inl
        exact (Finset.le_sup (f := SimpleGraph.edge u) (Finset.mem_insert_self _ _))
          ((SimpleGraph.edge_adj ..).mpr ⟨Or.inr ⟨rfl, rfl⟩, ha.ne.symm⟩)
      exact hnew.degree_pos_left
    · exact ((componentDeletionPairs_edge_data d e he).2.2.2.2 (h ▸ huv)).elim

/-- The modified puncture has the even-leaf parity interface, without
asserting that the untouched donor is active. -/
theorem componentModifiedDeletion_parity
    (d : ∀ C : (evenSubgraph G).ConnectedComponent, ComponentDeletionChoice G u C)
    (hu : Odd (G.degree u)) (e : V × V) (he : e ∈ componentDeletionPairs d)
    (ha : G.Adj u e.1) :
    (∀ v, v ≠ u → 0 < (componentModifiedDeletion d e).degree v →
      Odd ((G \ componentModifiedDeletion d e).degree v)) ∧
    (∀ v, v ≠ u → Even ((G \ componentModifiedDeletion d e).degree v) →
      Even (G.degree v)) :=
  even_star_puncture_parity (componentModifiedDeletion_le d e ha) u
    (componentModifiedDeletion_degree_le_one d hu e he)
    (componentModifiedDeletion_active_even d hu e he)

/-- All retained hub neighbours are odd in the modified puncture. -/
theorem componentModifiedDeletion_centre
    (d : ∀ C : (evenSubgraph G).ConnectedComponent, ComponentDeletionChoice G u C)
    (hu : Odd (G.degree u)) (e : V × V) (he : e ∈ componentDeletionPairs d)
    (ha : G.Adj u e.1) (v : V) (hv : (G \ componentModifiedDeletion d e).Adj u v) :
    ¬ Even ((G \ componentModifiedDeletion d e).degree v) := by
  intro hvEven
  obtain ⟨ho, hk⟩ := componentModifiedDeletion_parity d hu e he ha
  have hg := hk v hv.ne.symm hvEven
  exact Nat.not_even_iff_odd.mpr
    (ho v hv.ne.symm (componentModifiedDeletion_covers d hu e he ha v hg hv.1)) hvEven

/-- The literal punctured-centre Fan theorem supplies a floor decomposition
of the actual modified graph under the same strict-minimality guards. -/
theorem componentModifiedDeletion_floor
    (d : ∀ C : (evenSubgraph G).ConnectedComponent, ComponentDeletionChoice G u C)
    (hu : Odd (G.degree u)) (e : V × V) (he : e ∈ componentDeletionPairs d)
    (ha : G.Adj u e.1)
    (hconn : G.Connected) (hcap : ∀ v, Even (G.degree v) → eDegree G v ≤ 3)
    (hnot : ¬ HasPathBudget G (Fintype.card V / 2)) (hset : ¬ IsSET G)
    (hmin : ∀ (U : Set V) [DecidablePred (· ∈ U)]
      (J : SimpleGraph U) [DecidableRel J.Adj],
      J.edgeFinset.card < G.edgeFinset.card → J.Connected →
      (∀ v, Even (J.degree v) → eDegree J v ≤ 3) →
      HasPathBudget J (Fintype.card U / 2) ∨ IsSET J) :
    HasPathBudget (G \ componentModifiedDeletion d e) (Fintype.card V / 2) := by
  classical
  have hactive : ∃ a b, (componentModifiedDeletion d e).Adj a b := by
    refine ⟨u, e.1, Or.inl ?_⟩
    exact (Finset.le_sup (f := SimpleGraph.edge u) (Finset.mem_insert_self _ _))
      ((SimpleGraph.edge_adj ..).mpr ⟨Or.inl ⟨rfl, rfl⟩, ha.ne⟩)
  exact even_star_puncture_floor (componentModifiedDeletion_le d e ha) u hactive
    (componentModifiedDeletion_degree_le_one d hu e he)
    (componentModifiedDeletion_active_even d hu e he)
    (componentModifiedDeletion_centre d hu e he ha)
    hconn hcap hnot hset hmin

/-- The untouched opposite donor retains its original even degree parity. -/
theorem componentModifiedDeletion_donor_even
    (d : ∀ C : (evenSubgraph G).ConnectedComponent, ComponentDeletionChoice G u C)
    (hu : Odd (G.degree u)) (e : V × V) (he : e ∈ componentDeletionPairs d)
    (ha : G.Adj u e.1) : Even ((G \ componentModifiedDeletion d e).degree e.2) := by
  have hd := degree_sdiff_add_of_le (componentModifiedDeletion_le d e ha) e.2
  rw [componentModifiedDeletion_donor_degree_zero d hu e he, Nat.add_zero] at hd
  rw [hd]
  exact (componentDeletionPairs_edge_data d e he).2.2.2.1

end Gallai
