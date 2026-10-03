/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.Structure.EdgeDeletion
public import Gallai.Inputs.SingleEdge
public import Gallai.Foundations.EndpointBounds

@[expose] public section

/-!
# Direct restoration in the unique-positive-even-vertex case

This is the positive-even branch of the planned direct Lovasz base proof,
not the complete base theorem. Deletion moves the possible positive even
vertex from x to y. Addibility then restores the deleted edge towards y.
Isolated vertices are allowed and excluded from the positive-even condition.
-/

namespace Gallai

open scoped Finset

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Deleting an edge at a positive even vertex moves the possible positive
even exception to its other end, including when that end becomes isolated. -/
theorem unique_even_after_delete (x y : V) (hxy : G.Adj x y)
    (hx : Even (G.degree x))
    (hunique : ∀ v, 0 < G.degree v → Even (G.degree v) → v = x) :
    Odd ((G.deleteEdges {s(x, y)}).degree x) ∧
      ∀ v, 0 < (G.deleteEdges {s(x, y)}).degree v →
        Even ((G.deleteEdges {s(x, y)}).degree v) → v = y := by
  have hdx := degree_delete_edge_add_one G x y hxy
  have hxodd : Odd ((G.deleteEdges {s(x, y)}).degree x) := by
    rw [Nat.even_iff] at hx
    rw [Nat.odd_iff]
    omega
  refine ⟨hxodd, ?_⟩
  intro v hp he
  by_cases hvx : v = x
  · subst v
    exact (Nat.not_even_iff_odd.mpr hxodd he).elim
  by_cases hvy : v = y
  · exact hvy
  have hd := degree_delete_edge_of_ne G x y v hvx hvy
  rw [hd] at hp he
  exact (hvx (hunique v hp he)).elim

/-- Any decomposition of the edge puncture lifts at unchanged size when x
is the sole possible positive even vertex of the original graph. -/
theorem Decomposition.restore_unique_even_edge (x y : V) (hxy : G.Adj x y)
    (hx : Even (G.degree x))
    (hunique : ∀ v, 0 < G.degree v → Even (G.degree v) → v = x)
    (D : Decomposition (G.deleteEdges {s(x, y)})) :
    ∃ E : Decomposition G, E.size = D.size ∧
      ∀ v, E.endpointCount v + (if x = v then 1 else 0) =
        D.endpointCount v + if y = v then 1 else 0 := by
  classical
  obtain ⟨hxodd, heven⟩ := unique_even_after_delete x y hxy hx hunique
  have hpassing :
      #{v ∈ (G.deleteEdges {s(x, y)}).neighborFinset y | D.endpointCount v = 0} = 0 := by
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro v hv
    obtain ⟨hadj, hz⟩ := Finset.mem_filter.mp hv
    have hadj := ((G.deleteEdges {s(x, y)}).mem_neighborFinset y v).mp hadj
    have hp : 0 < (G.deleteEdges {s(x, y)}).degree v :=
      ((G.deleteEdges {s(x, y)}).degree_pos_iff_exists_adj v).mpr ⟨y, hadj.symm⟩
    have ho : Odd ((G.deleteEdges {s(x, y)}).degree v) := by
      apply Nat.not_even_iff_odd.mp
      intro he
      exact hadj.ne (heven v hp he).symm
    have h := D.endpointCount_pos_of_odd_degree v ho
    omega
  have hm : ¬ (G.deleteEdges {s(x, y)}).Adj y x := by
    simp [SimpleGraph.deleteEdges_adj, Sym2.eq_swap]
  have hbudget := D.single_edge_addibility y x hxy.ne.symm hm
    (by rw [hpassing]; exact D.endpointCount_pos_of_odd_degree x hxodd)
  have hg : G.deleteEdges {s(x, y)} ⊔ SimpleGraph.edge y x = G := by
    rw [SimpleGraph.edge_comm]
    exact delete_edge_sup_edge G x y hxy
  rw [hg] at hbudget
  exact hbudget

end Gallai
