/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.Inputs.HangingParity
public import Gallai.Inputs.UniqueEvenComponent

@[expose] public section

/-! # The donor puncture component is hanging at its even vertex

The original graph is split into the mapped component and its edge
complement. The only possible overlap with the complement is the donor.
-/

namespace Gallai

universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- Restoring an edge with one endpoint outside S does not change its induced graph. -/
theorem induce_puncture_eq_of_notMem (x y : V) (S : Set V) (hx : x ∉ S) :
    (G.deleteEdges {s(x, y)}).induce S = G.induce S := by
  ext a b
  constructor
  · exact fun h => (SimpleGraph.deleteEdges_adj.mp h).1
  · intro h
    refine SimpleGraph.deleteEdges_adj.mpr ⟨h, ?_⟩
    intro he
    rcases Sym2.eq_iff.mp (show s(a.val, b.val) = s(x, y) from he) with he | he
    · exact hx (he.1 ▸ a.property)
    · exact hx (he.2 ▸ b.property)

omit [Fintype V] [DecidableRel G.Adj] in
/-- The edge complement of a closed puncture part can touch that part only at y. -/
theorem puncture_part_complement_support (x y : V) (S : Set V) (hx : x ∉ S)
    (hs : ∀ v ∈ S, (G.deleteEdges {s(x, y)}).neighborSet v ⊆ S) :
    (G \ (G.induce S).spanningCoe).support ⊆ Sᶜ ∪ {y} := by
  classical
  rintro v ⟨w, hvw⟩
  by_cases hv : v ∈ S
  · right
    by_contra hvy
    have hvx : v ≠ x := fun h => hx (h ▸ hv)
    have hp : (G.deleteEdges {s(x, y)}).Adj v w := by
      refine SimpleGraph.deleteEdges_adj.mpr ⟨hvw.1, ?_⟩
      intro he
      rcases Sym2.eq_iff.mp (show s(v, w) = s(x, y) from he) with he | he
      · exact hvx he.1
      · exact hvy he.1
    have hw : w ∈ S := hs v hv hp
    apply hvw.2
    exact (SimpleGraph.map_adj (Function.Embedding.subtype _) (G.induce S) v w).mpr
      ⟨⟨v, hv⟩, ⟨w, hw⟩, hvw.1, rfl, rfl⟩
  · exact Or.inl hv

/-- A donor component separated from x cannot be SET in a minimal counterexample.
The hanging interface is derived from the actual component and deleted edge. -/
theorem donor_component_not_set (x y : V)
    (hy : Even (G.degree y)) (hconn : G.Connected)
    (hcap : ∀ v, Even (G.degree v) → eDegree G v ≤ 3)
    (hnot : ¬ HasPathBudget G (Fintype.card V / 2)) (hset : ¬ IsSET G)
    (C : (G.deleteEdges {s(x, y)}).ConnectedComponent)
    [DecidablePred (· ∈ C.supp)] (hcy : y ∈ C.supp) (hcx : x ∉ C.supp)
    (hmin : ∀ (U : Set V) [DecidablePred (· ∈ U)]
      (J : SimpleGraph U) [DecidableRel J.Adj],
      J.edgeFinset.card < G.edgeFinset.card → J.Connected →
      (∀ v, Even (J.degree v) → eDegree J v ≤ 3) →
      HasPathBudget J (Fintype.card U / 2) ∨ IsSET J) :
    ¬ IsSET ((G.deleteEdges {s(x, y)}).induce C.supp) := by
  classical
  intro hC
  let A := (G.induce C.supp).spanningCoe
  let B := G \ A
  let T := C.suppᶜ ∪ {y}
  have hA : A ≤ G := G.spanningCoe_induce_le C.supp
  have hG : A ⊔ B = G := by
    ext a b
    change (A.Adj a b ∨ G.Adj a b ∧ ¬ A.Adj a b) ↔ G.Adj a b
    constructor
    · rintro (h | h)
      · exact hA h
      · exact h.1
    · intro h
      by_cases ha : A.Adj a b
      · exact Or.inl ha
      · exact Or.inr ⟨h, ha⟩
  have haS : A.support ⊆ C.supp := by
    intro v hv
    rw [SimpleGraph.support_spanningCoe] at hv
    obtain ⟨w, _, rfl⟩ := hv
    exact w.property
  have hbT : B.support ⊆ T := puncture_part_complement_support x y C.supp hcx
    (fun _ hv _ hw => C.mem_supp_of_adj_mem_supp hv hw)
  have he : IsESETAt (A.induce C.supp) ⟨y, hcy⟩ := by
    have hh : A.induce C.supp = (G.deleteEdges {s(x, y)}).induce C.supp := by
      rw [induce_puncture_eq_of_notMem x y C.supp hcx]
      exact SimpleGraph.induce_spanningCoe
    simpa only [hh] using hC.isESETAt ⟨y, hcy⟩
  have hp := hanging_eset_joint_parity A B C.supp T y hcy (Or.inr rfl)
    (by ext v; simp [T]) (by
      ext v
      change (v ∈ C.supp ∧ (v ∉ C.supp ∨ v = y)) ↔ v = y
      constructor
      · rintro ⟨hv, hn | he⟩
        · exact (hn hv).elim
        · exact he
      · rintro rfl
        exact ⟨hcy, Or.inr rfl⟩) haS hbT he
    (by simpa only [hG] using hconn) (by
      simpa only [SimpleGraph.degree, SimpleGraph.neighborFinset,
        ← Set.ncard_eq_toFinset_card', hG] using hcap)
    (by simpa only [hG] using hnot) (by simpa only [hG] using hset)
    (by simpa only [SimpleGraph.edgeFinset, ← Set.ncard_eq_toFinset_card', hG] using hmin)
  have ho : Odd (G.degree y) := by
    simpa only [SimpleGraph.degree, SimpleGraph.neighborFinset,
      ← Set.ncard_eq_toFinset_card', hG] using hp.1
  exact Nat.not_even_iff_odd.mpr ho hy

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- After deleting one edge of a connected graph, every vertex is reachable
from at least one of the two ends in the puncture. -/
theorem edge_puncture_reachable_from_end (hconn : G.Connected) (x y v : V) :
    (G.deleteEdges {s(x, y)}).Reachable x v ∨
      (G.deleteEdges {s(x, y)}).Reachable y v := by
  classical
  let H := G.deleteEdges {s(x, y)}
  have transport : ∀ {a b : V}, G.Walk a b →
      (H.Reachable x a ∨ H.Reachable y a) →
      H.Reachable x b ∨ H.Reachable y b := by
    intro a b p
    induction p with
    | nil => exact id
    | @cons a b c hab p ih =>
      intro hh
      apply ih
      by_cases he : H.Adj a b
      · rcases hh with hh | hh
        · exact Or.inl (hh.trans he.reachable)
        · exact Or.inr (hh.trans he.reachable)
      · have heq : s(a, b) = s(x, y) := by
          by_contra hn
          exact he (SimpleGraph.deleteEdges_adj.mpr ⟨hab, hn⟩)
        rcases Sym2.eq_iff.mp heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact Or.inr (SimpleGraph.Reachable.refl _)
        · exact Or.inl (SimpleGraph.Reachable.refl _)
  obtain ⟨p⟩ := hconn x v
  exact transport p (Or.inl (SimpleGraph.Reachable.refl _))

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- Every actual component of a one-edge puncture contains a deleted-edge end. -/
theorem edge_puncture_component_contains_end (hconn : G.Connected) (x y : V)
    (C : (G.deleteEdges {s(x, y)}).ConnectedComponent) :
    x ∈ C.supp ∨ y ∈ C.supp := by
  obtain ⟨v, hv⟩ := C.nonempty_supp
  rcases edge_puncture_reachable_from_end hconn x y v with h | h
  · exact Or.inl ((SimpleGraph.ConnectedComponent.sound h).trans hv)
  · exact Or.inr ((SimpleGraph.ConnectedComponent.sound h).trans hv)

/-- Every actual puncture component has a floor decomposition under bounded
minimality: the recipient uses zero E-degree, the donor uses Claim 1. -/
theorem unique_even_neighbor_all_components_floor (x y : V) (hxy : G.Adj x y)
    (hy : Even (G.degree y))
    (hu : ∀ v, G.Adj x v → Even (G.degree v) → v = y)
    (hconn : G.Connected) (hcap : ∀ v, Even (G.degree v) → eDegree G v ≤ 3)
    (hnot : ¬ HasPathBudget G (Fintype.card V / 2)) (hset : ¬ IsSET G)
    (hmin : ∀ (U : Set V) [DecidablePred (· ∈ U)]
      (J : SimpleGraph U) [DecidableRel J.Adj],
      J.edgeFinset.card < G.edgeFinset.card → J.Connected →
      (∀ v, Even (J.degree v) → eDegree J v ≤ 3) →
      HasPathBudget J (Fintype.card U / 2) ∨ IsSET J)
    (C : (G.deleteEdges {s(x, y)}).ConnectedComponent)
    [DecidablePred (· ∈ C.supp)] :
    HasPathBudget ((G.deleteEdges {s(x, y)}).induce C.supp) (Fintype.card C.supp / 2) := by
  classical
  by_cases hx : x ∈ C.supp
  · exact unique_even_neighbor_component_floor x y hxy hy hu hcap C hx hmin
  · have hcy := (edge_puncture_component_contains_end hconn x y C).resolve_left hx
    have hns := donor_component_not_set x y hy hconn hcap hnot hset C hcy hx hmin
    have hc := even_degree_cap_induce_of_closed (G.deleteEdges {s(x, y)}) C.supp
      (fun _ hv _ hw => C.mem_supp_of_adj_mem_supp hv hw) 3
      (unique_even_neighbor_puncture_cap x y hxy hy hu 3 hcap)
    exact (hmin C.supp ((G.deleteEdges {s(x, y)}).induce C.supp)
      (induced_puncture_edge_count_lt x y hxy C.supp) C.connected_toSimpleGraph hc).resolve_right hns

end Gallai
