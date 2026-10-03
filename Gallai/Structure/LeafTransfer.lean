/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.Structure.EdgeDeletion
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Lean.Elab.Tactic.Omega

@[expose] public section

/-! # The leaf-transfer auxiliary for the all-odd reduction -/

namespace Gallai
open scoped Finset
universe u
variable {V : Type u}

/-- Replace xy by an edge from a new leaf to y; old vertices are embedded by inl. -/
abbrev leafTransfer (G : SimpleGraph V) (x y : V) : SimpleGraph (V ⊕ Unit) :=
  (G.deleteEdges {s(x,y)}).map (Function.Embedding.inl : V ↪ V ⊕ Unit) ⊔
    SimpleGraph.edge (Sum.inr ()) (Sum.inl y)

/-- Edges between old vertices are precisely the original puncture. -/
theorem leafTransfer_adj_old (G : SimpleGraph V) (x y a b : V) :
    (leafTransfer G x y).Adj (.inl a) (.inl b) ↔
      (G.deleteEdges {s(x,y)}).Adj a b := by
  simp [leafTransfer, SimpleGraph.edge_adj]

/-- The new vertex has exactly the one prescribed neighbour. -/
theorem leafTransfer_adj_new (G : SimpleGraph V) (x y : V) (v : V ⊕ Unit) :
    (leafTransfer G x y).Adj (.inr ()) v ↔ v = .inl y := by
  cases v <;> simp [leafTransfer, SimpleGraph.map_adj, SimpleGraph.edge_adj, eq_comm]

variable [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Local classical adjacency decision for finite degree statements. -/
noncomputable local instance (x y : V) : DecidableRel (leafTransfer G x y).Adj :=
  fun _ _ => Classical.propDecidable _

/-- Degree at an old vertex is the punctured degree plus its new-leaf incidence. -/
theorem leafTransfer_degree_old (x y v : V) :
    (leafTransfer G x y).degree (.inl v) =
      (G.deleteEdges {s(x,y)}).degree v + if v = y then 1 else 0 := by
  classical
  have hset : (leafTransfer G x y).neighborFinset (.inl v) =
      ((G.deleteEdges {s(x,y)}).neighborFinset v).map Function.Embedding.inl ∪
        (if v = y then {Sum.inr ()} else ∅) := by
    ext w
    cases w with
    | inl w => by_cases h : v = y <;> simp [leafTransfer, SimpleGraph.edge_adj, h]
    | inr w =>
      cases w
      by_cases h : v = y
      · subst v
        simp [leafTransfer, SimpleGraph.edge_adj]
      · simp [leafTransfer, SimpleGraph.edge_adj, h]
  have hdis : Disjoint
      (((G.deleteEdges {s(x,y)}).neighborFinset v).map
        (Function.Embedding.inl : V ↪ V ⊕ Unit))
      (if v = y then {Sum.inr ()} else ∅) := by
    split <;> simp
  rw [← SimpleGraph.card_neighborFinset_eq_degree, hset, Finset.card_union_of_disjoint hdis]
  simp only [Finset.card_map, SimpleGraph.card_neighborFinset_eq_degree]
  split <;> simp_all

omit [DecidableEq V] [DecidableRel G.Adj] in
/-- The new vertex is a leaf. -/
theorem leafTransfer_degree_new (x y : V) :
    (leafTransfer G x y).degree (.inr ()) = 1 := by
  have hs : (leafTransfer G x y).neighborFinset (.inr ()) = {Sum.inl y} := by
    ext v
    simp only [SimpleGraph.mem_neighborFinset, leafTransfer_adj_new, Finset.mem_singleton]
  rw [← SimpleGraph.card_neighborFinset_eq_degree, hs, Finset.card_singleton]

/-- The donor loses one incident edge. -/
theorem leafTransfer_degree_donor (x y : V) (hxy : G.Adj x y) :
    (leafTransfer G x y).degree (.inl x) + 1 = G.degree x := by
  rw [leafTransfer_degree_old]
  simpa [hxy.ne] using degree_delete_edge_add_one G x y hxy

/-- All old vertices other than the donor keep their degrees. -/
theorem leafTransfer_degree_other (x y v : V) (hxy : G.Adj x y) (hv : v ≠ x) :
    (leafTransfer G x y).degree (.inl v) = G.degree v := by
  rw [leafTransfer_degree_old]
  by_cases hy : v = y
  · subst v
    have hd := degree_delete_edge_add_one G y x hxy.symm
    have he : s(y, x) = s(x, y) := Sym2.eq_swap
    rw [he] at hd
    simpa using hd
  · simp [hy, degree_delete_edge_of_ne G x y v hv hy]

/-- Transferring an edge from an odd donor of degree at least three creates
exactly one positive even vertex; isolated old vertices cause no exception. -/
theorem leafTransfer_unique_positive_even (x y : V) (hxy : G.Adj x y)
    (hx : 3 ≤ G.degree x) (hodd : ∀ v, 0 < G.degree v → Odd (G.degree v)) :
    0 < (leafTransfer G x y).degree (.inl x) ∧
      Even ((leafTransfer G x y).degree (.inl x)) ∧
      ∀ v, 0 < (leafTransfer G x y).degree v →
        Even ((leafTransfer G x y).degree v) → v = .inl x := by
  have hd := leafTransfer_degree_donor G x y hxy
  have ho := hodd x (by omega)
  rw [Nat.odd_iff] at ho
  refine ⟨by omega, ?_, ?_⟩
  · rw [Nat.even_iff]
    omega
  · intro v hp he
    cases v with
    | inl v =>
      by_cases hv : v = x
      · subst v
        rfl
      · rw [leafTransfer_degree_other G x y v hxy hv] at hp he
        exact (Nat.not_even_iff_odd.mpr (hodd v hp) he).elim
    | inr v =>
      cases v
      rw [leafTransfer_degree_new G x y, Nat.even_iff] at he
      omega

end Gallai
