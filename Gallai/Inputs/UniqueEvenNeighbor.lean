/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.Structure.EdgeDeletion
public import Gallai.Structure.SET
public import Gallai.Inputs.SingleEdge
public import Gallai.Foundations.EndpointBounds

@[expose] public section

/-! # Deleting the unique even-neighbour edge

The condition concerns the neighbours of one vertex, not all even vertices
of the graph. These are the puncture and restoration consumers of Claim 2.
-/

namespace Gallai

open scoped Finset
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The even donor becomes odd and every remaining neighbour of the recipient
is odd after deleting its sole even-neighbour edge. -/
theorem unique_even_neighbor_puncture (x y : V) (hxy : G.Adj x y)
    (hy : Even (G.degree y))
    (hu : ∀ v, G.Adj x v → Even (G.degree v) → v = y) :
    Odd ((G.deleteEdges {s(x, y)}).degree y) ∧
      ∀ v, (G.deleteEdges {s(x, y)}).Adj x v →
        Odd ((G.deleteEdges {s(x, y)}).degree v) := by
  have hd := degree_delete_edge_add_one G y x hxy.symm
  rw [Sym2.eq_swap] at hd
  have hoy : Odd ((G.deleteEdges {s(x, y)}).degree y) := by
    rw [Nat.even_iff] at hy
    rw [Nat.odd_iff]
    omega
  refine ⟨hoy, ?_⟩
  intro v hv
  have ha := (SimpleGraph.deleteEdges_adj.mp hv).1
  have hne : v ≠ y := by
    intro he
    subst v
    exact (SimpleGraph.deleteEdges_adj.mp hv).2 rfl
  rw [degree_delete_edge_of_ne G x y v ha.ne.symm hne]
  exact Nat.not_even_iff_odd.mp (fun he => hne (hu v ha he))

/-- The punctured recipient has no even neighbours, regardless of its own parity. -/
theorem unique_even_neighbor_puncture_eDegree (x y : V) (hxy : G.Adj x y)
    (hy : Even (G.degree y))
    (hu : ∀ v, G.Adj x v → Even (G.degree v) → v = y) :
    eDegree (G.deleteEdges {s(x, y)}) x = 0 := by
  obtain ⟨_, hn⟩ := unique_even_neighbor_puncture x y hxy hy hu
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro v hv
  obtain ⟨ha, he⟩ := (mem_evenNeighbors x v).mp hv
  exact Nat.not_even_iff_odd.mpr (hn v ha) he

/-- The induced-even degree cap survives this puncture: a newly even x has
no even neighbours, so it cannot add an E-neighbour to another even vertex. -/
theorem unique_even_neighbor_puncture_cap (x y : V) (hxy : G.Adj x y)
    (hy : Even (G.degree y))
    (hu : ∀ v, G.Adj x v → Even (G.degree v) → v = y)
    (c : ℕ) (hcap : ∀ v, Even (G.degree v) → eDegree G v ≤ c) :
    ∀ v, Even ((G.deleteEdges {s(x, y)}).degree v) →
      eDegree (G.deleteEdges {s(x, y)}) v ≤ c := by
  obtain ⟨hoy, hn⟩ := unique_even_neighbor_puncture x y hxy hy hu
  intro v hv
  by_cases hvx : v = x
  · subst v
    rw [unique_even_neighbor_puncture_eDegree x y hxy hy hu]
    exact Nat.zero_le _
  have hvy : v ≠ y := fun h => Nat.not_even_iff_odd.mpr hoy (h ▸ hv)
  have hvg : Even (G.degree v) := by
    rwa [degree_delete_edge_of_ne G x y v hvx hvy] at hv
  apply (Finset.card_le_card (s := evenNeighbors (G.deleteEdges {s(x, y)}) v)
    (t := evenNeighbors G v) ?_).trans (hcap v hvg)
  intro w hw
  obtain ⟨ha, he⟩ := (mem_evenNeighbors v w).mp hw
  have hwx : w ≠ x := by
    intro h
    subst w
    exact Nat.not_even_iff_odd.mpr (hn v ha.symm) hv
  have hwy : w ≠ y := fun h => Nat.not_even_iff_odd.mpr hoy (h ▸ he)
  exact (mem_evenNeighbors v w).mpr ⟨(SimpleGraph.deleteEdges_adj.mp ha).1, by
    rwa [degree_delete_edge_of_ne G x y w hwx hwy] at he⟩

/-- The full puncture cannot be SET, because its recipient has E-degree zero. -/
theorem unique_even_neighbor_puncture_not_set (x y : V) (hxy : G.Adj x y)
    (hy : Even (G.degree y))
    (hu : ∀ v, G.Adj x v → Even (G.degree v) → v = y) :
    ¬ IsSET (G.deleteEdges {s(x, y)}) := by
  intro h
  have hz := unique_even_neighbor_puncture_eDegree x y hxy hy hu
  rcases h.eDegree_two_or_three x with h | h <;> omega

/-- Every puncture decomposition restores the unique even-neighbour edge for
free, moving one endpoint from y to x and preserving all other counts. -/
theorem Decomposition.restore_unique_even_neighbor (x y : V) (hxy : G.Adj x y)
    (hy : Even (G.degree y))
    (hu : ∀ v, G.Adj x v → Even (G.degree v) → v = y)
    (D : Decomposition (G.deleteEdges {s(x, y)})) :
    ∃ E : Decomposition G, E.size = D.size ∧
      ∀ v, E.endpointCount v + (if y = v then 1 else 0) =
        D.endpointCount v + if x = v then 1 else 0 := by
  classical
  obtain ⟨hoy, hn⟩ := unique_even_neighbor_puncture x y hxy hy hu
  have hz : #{v ∈ (G.deleteEdges {s(x, y)}).neighborFinset x | D.endpointCount v = 0} = 0 := by
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro v hv
    obtain ⟨ha, he⟩ := Finset.mem_filter.mp hv
    have hp := D.endpointCount_pos_of_odd_degree v
      (hn v ((G.deleteEdges {s(x, y)}).mem_neighborFinset x v |>.mp ha))
    omega
  have hm : ¬ (G.deleteEdges {s(x, y)}).Adj x y := by simp [SimpleGraph.deleteEdges_adj]
  have hr := D.single_edge_addibility x y hxy.ne hm
    (by rw [hz]; exact D.endpointCount_pos_of_odd_degree y hoy)
  rw [delete_edge_sup_edge G x y hxy] at hr
  exact hr

/-- If the unique-even-neighbour puncture is connected, its strictly smaller
floor-or-SET induction outcome restores a floor decomposition of the original. -/
theorem unique_even_neighbor_connected_floor (x y : V) (hxy : G.Adj x y)
    (hy : Even (G.degree y))
    (hu : ∀ v, G.Adj x v → Even (G.degree v) → v = y)
    (hcap : ∀ v, Even (G.degree v) → eDegree G v ≤ 3)
    (hconn : (G.deleteEdges {s(x, y)}).Connected)
    (hmin : ∀ (J : SimpleGraph V) [DecidableRel J.Adj],
      J.edgeFinset.card < G.edgeFinset.card → J.Connected →
      (∀ v, Even (J.degree v) → eDegree J v ≤ 3) →
      HasPathBudget J (Fintype.card V / 2) ∨ IsSET J) :
    HasPathBudget G (Fintype.card V / 2) := by
  classical
  have hlt : (G.deleteEdges {s(x, y)}).edgeFinset.card < G.edgeFinset.card := by
    apply Finset.card_lt_card
    apply SimpleGraph.edgeFinset_strict_mono
    refine lt_of_le_not_ge (G.deleteEdges_le _) ?_
    intro hle
    have he := hle hxy
    exact (SimpleGraph.deleteEdges_adj.mp he).2 rfl
  have hc := unique_even_neighbor_puncture_cap x y hxy hy hu 3 hcap
  rcases hmin (G.deleteEdges {s(x, y)}) hlt hconn hc with ⟨D, hD⟩ | hs
  · obtain ⟨E, hE, _⟩ := D.restore_unique_even_neighbor x y hxy hy hu
    exact ⟨E, hE.le.trans hD⟩
  · exact (unique_even_neighbor_puncture_not_set x y hxy hy hu hs).elim

end Gallai
