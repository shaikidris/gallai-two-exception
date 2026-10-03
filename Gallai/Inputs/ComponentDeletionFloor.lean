/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.Structure.ComponentDeletionChoice
public import Gallai.Inputs.ComponentPieceParity
public import Gallai.Inputs.FanPunctureFloor
public import Gallai.Inputs.TriangleIsolateClaim

@[expose] public section

/-! # The actual component-choice puncture has a floor decomposition

The choice family retains isolate/triangle labels for restoration. Its floor
budget is derived, not assumed, from the source-faithful even-leaf consumer.
-/

namespace Gallai

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {u : V}

/-- Union of the actual component deletion choices, including untouched components. -/
noncomputable def componentDeletionUnion
    (d : ∀ C : (evenSubgraph G).ConnectedComponent, ComponentDeletionChoice G u C) :
    SimpleGraph V := by
  classical
  exact Finset.univ.sup (fun C => (d C).graph)

/-- Decision instance for degree and puncture statements. -/
noncomputable local instance componentDeletionUnionAdj
    (d : ∀ C : (evenSubgraph G).ConnectedComponent, ComponentDeletionChoice G u C) :
    DecidableRel (componentDeletionUnion d).Adj := fun _ _ => Classical.propDecidable _

/-- Every originally even hub neighbour is active in the actual union. -/
theorem componentDeletionUnion_covers
    (d : ∀ C : (evenSubgraph G).ConnectedComponent, ComponentDeletionChoice G u C)
    (hu : Odd (G.degree u)) (v : V) (hv : Even (G.degree v)) (ha : G.Adj u v) :
    0 < (componentDeletionUnion d).degree v := by
  classical
  let C := (evenSubgraph G).connectedComponentMk ⟨v, hv⟩
  have hm : v ∈ evenComponentVertices C := ⟨⟨v, hv⟩, rfl, rfl⟩
  have hp := (d C).covers_neighbor hu v hm ha
  obtain ⟨w, hw⟩ := ((d C).graph.degree_pos_iff_exists_adj v).mp hp
  apply SimpleGraph.Adj.degree_pos_left (w := w)
  exact (Finset.le_sup (f := fun C => (d C).graph) (Finset.mem_univ C)) hw

/-- Every data-preserving component choice yields a floor puncture under
strict minimality, with all Fan shape, parity, centre and cap facts derived. -/
theorem componentDeletionUnion_floor
    (d : ∀ C : (evenSubgraph G).ConnectedComponent, ComponentDeletionChoice G u C)
    (hu : Odd (G.degree u)) (htouch : ∃ v, Even (G.degree v) ∧ G.Adj u v)
    (hconn : G.Connected) (hcap : ∀ v, Even (G.degree v) → eDegree G v ≤ 3)
    (hnot : ¬ HasPathBudget G (Fintype.card V / 2)) (hset : ¬ IsSET G)
    (hmin : ∀ (U : Set V) [DecidablePred (· ∈ U)]
      (J : SimpleGraph U) [DecidableRel J.Adj],
      J.edgeFinset.card < G.edgeFinset.card → J.Connected →
      (∀ v, Even (J.degree v) → eDegree J v ≤ 3) →
      HasPathBudget J (Fintype.card U / 2) ∨ IsSET J) :
    HasPathBudget (G \ componentDeletionUnion d) (Fintype.card V / 2) := by
  classical
  let K := fun C => (d C).graph
  have hle : ∀ C ∈ (Finset.univ : Finset (evenSubgraph G).ConnectedComponent), K C ≤ G :=
    fun C _ => (d C).graph_le
  have hs : ∀ C ∈ (Finset.univ : Finset (evenSubgraph G).ConnectedComponent),
      ∀ v w, (K C).Adj v w → v = u ∨ v ∈ evenComponentVertices C :=
    fun C _ => (d C).supported hu
  have hl : ∀ C ∈ (Finset.univ : Finset (evenSubgraph G).ConnectedComponent),
      ∀ v, v ≠ u → (K C).degree v ≤ 1 := fun C _ => (d C).degree_le_one hu
  have hcover : ∀ v, G.Adj u v → Even (G.degree v) → 0 < (Finset.univ.sup K).degree v :=
    fun v ha hv => componentDeletionUnion_covers d hu v hv ha
  have hactive : ∃ v w, (Finset.univ.sup K).Adj v w := by
    obtain ⟨v, hv, ha⟩ := htouch
    obtain ⟨w, hw⟩ := ((Finset.univ.sup K).degree_pos_iff_exists_adj v).mp (hcover v ha hv)
    exact ⟨v, w, hw⟩
  exact even_star_puncture_floor (Finset.sup_le hle) u hactive
    (even_component_piece_union_degree_le_one Finset.univ K u hs hl)
    (even_component_piece_union_active_even Finset.univ K u hs)
    (component_piece_puncture_centre Finset.univ K u hle hs hl hcover)
    hconn hcap hnot hset hmin

/-- Claim 4 constructs the full choice family and the floor witness for an
odd hub with even neighbours. No favourable piece family is assumed. -/
theorem minimal_counterexample_component_puncture
    (u : V) (hu : Odd (G.degree u)) (htouch : ∃ v, Even (G.degree v) ∧ G.Adj u v)
    (hconn : G.Connected) (hcap : ∀ v, Even (G.degree v) → eDegree G v ≤ 3)
    (hnot : ¬ HasPathBudget G (Fintype.card V / 2)) (hset : ¬ IsSET G)
    (hmin : ∀ (U : Set V) [DecidablePred (· ∈ U)]
      (J : SimpleGraph U) [DecidableRel J.Adj],
      J.edgeFinset.card < G.edgeFinset.card → J.Connected →
      (∀ v, Even (J.degree v) → eDegree J v ≤ 3) →
      HasPathBudget J (Fintype.card U / 2) ∨ IsSET J) :
    ∃ d : ∀ C : (evenSubgraph G).ConnectedComponent, ComponentDeletionChoice G u C,
      HasPathBudget (G \ componentDeletionUnion d) (Fintype.card V / 2) := by
  classical
  let d := fun C => Classical.choice (componentDeletionChoice_nonempty u C
    (minimal_counterexample_even_components hconn hcap hnot hset hmin C))
  exact ⟨d, componentDeletionUnion_floor d hu htouch hconn hcap hnot hset hmin⟩

end Gallai
