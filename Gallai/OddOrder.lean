/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.Inputs.FloorOrSET
public import Gallai.Repair.Endpoints
public import Gallai.Structure.SETBoundary

@[expose] public section

/-! # Simultaneous exposure under two nonadjacent exceptions -/

namespace Gallai

open scoped Finset

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- At every order, the two-exception hypotheses supply the floor budget
plus one path, exposing both even hubs. No lower E-degree bound is needed. -/
theorem two_exception_floor_add_one
    (hconn : G.Connected) (x y : V) (hne : x ≠ y) (hmissing : ¬ G.Adj x y)
    (hx : Even (G.degree x)) (hy : Even (G.degree y))
    (hcap : ∀ v, Even (G.degree v) → v ≠ x → v ≠ y → eDegree G v ≤ 3) :
    ∃ P : Decomposition G, P.size ≤ Fintype.card V / 2 + 1 ∧
      2 ≤ P.endpointCount x ∧ 2 ≤ P.endpointCount y := by
  classical
  let J := G ⊔ SimpleGraph.edge x y
  have hJxy : J.Adj x y := Or.inr ((SimpleGraph.edge_adj ..).mpr ⟨Or.inl ⟨rfl, rfl⟩, hne⟩)
  have hdel : J.deleteEdges {s(x, y)} = G := by
    ext a b
    simp only [J, SimpleGraph.deleteEdges_adj, SimpleGraph.sup_adj,
      Set.mem_singleton_iff, Sym2.eq_iff, SimpleGraph.edge_adj]
    constructor
    · rintro ⟨ha | ⟨ha, _⟩, hn⟩
      · exact ha
      · exact (hn ha).elim
    · intro ha
      refine ⟨Or.inl ha, ?_⟩
      rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · exact hmissing ha
      · exact hmissing ha.symm
  have hdx : J.degree x = G.degree x + 1 := by
    have hd := degree_delete_edge_add_one J x y hJxy
    simpa only [SimpleGraph.degree, SimpleGraph.neighborFinset,
      ← Set.ncard_eq_toFinset_card', hdel] using hd.symm
  have hdy : J.degree y = G.degree y + 1 := by
    have hd := degree_delete_edge_add_one J y x hJxy.symm
    have hs : s(y, x) = s(x, y) := Sym2.eq_swap
    rw [hs] at hd
    simpa only [SimpleGraph.degree, SimpleGraph.neighborFinset,
      ← Set.ncard_eq_toFinset_card', hdel] using hd.symm
  have hoff (v : V) (hvx : v ≠ x) (hvy : v ≠ y) : J.degree v = G.degree v := by
    have hd := degree_delete_edge_of_ne J x y v hvx hvy
    simpa only [SimpleGraph.degree, SimpleGraph.neighborFinset,
      ← Set.ncard_eq_toFinset_card', hdel] using hd.symm
  have hparity (v : V) : Even (J.degree v) ↔ Even (G.degree v) ∧ v ≠ x ∧ v ≠ y := by
    by_cases hvx : v = x
    · subst v
      have ho : Odd (J.degree x) := by rw [hdx]; exact hx.add_odd (by decide : Odd 1)
      simp [Nat.not_even_iff_odd.mpr ho]
    by_cases hvy : v = y
    · subst v
      have ho : Odd (J.degree y) := by rw [hdy]; exact hy.add_odd (by decide : Odd 1)
      simp [Nat.not_even_iff_odd.mpr ho]
    rw [hoff v hvx hvy]
    simp [hvx, hvy]
  have hJcap (v : V) (hv : Even (J.degree v)) : eDegree J v ≤ 3 := by
    obtain ⟨hvG, hvx, hvy⟩ := (hparity v).mp hv
    have hs : evenNeighbors J v ⊆ evenNeighbors G v := by
      intro w hw
      obtain ⟨ha, he⟩ := (mem_evenNeighbors v w).mp hw
      refine (mem_evenNeighbors v w).mpr ⟨?_, ((hparity w).mp he).1⟩
      rcases ha with ha | ha
      · exact ha
      · rcases (SimpleGraph.edge_adj ..).mp ha with ⟨ha | ha, _⟩
        · exact (hvx ha.1).elim
        · exact (hvy ha.1).elim
    exact (Finset.card_le_card hs).trans (hcap v hvG hvx hvy)
  have hnotSET : ¬ IsSET J := by
    intro hs
    have hxo : Odd (J.degree x) := by rw [hdx]; exact hx.add_odd (by decide : Odd 1)
    have hyo : Odd (J.degree y) := by rw [hdy]; exact hy.add_odd (by decide : Odd 1)
    obtain ⟨w, hxw, hyw, hew⟩ := hs.common_even_neighbor x y hxo hyo
    obtain ⟨hewG, hwx, hwy⟩ := (hparity w).mp hew
    have hback (v : V) (ha : J.Adj w v) : G.Adj w v := by
      rcases ha with ha | ha
      · exact ha
      · rcases (SimpleGraph.edge_adj ..).mp ha with ⟨ha | ha, _⟩
        · exact (hwx ha.1).elim
        · exact (hwy ha.1).elim
    have hnx : x ∉ evenNeighbors J w := by
      intro hm
      exact (Nat.not_even_iff_odd.mpr hxo) ((mem_evenNeighbors w x).mp hm).2
    have hny : y ∉ evenNeighbors J w := by
      intro hm
      exact (Nat.not_even_iff_odd.mpr hyo) ((mem_evenNeighbors w y).mp hm).2
    have hsub : insert x (insert y (evenNeighbors J w)) ⊆ evenNeighbors G w := by
      intro v hv
      rcases Finset.mem_insert.mp hv with rfl | hv
      · exact (mem_evenNeighbors _ _).mpr ⟨hback _ hxw.symm, hx⟩
      rcases Finset.mem_insert.mp hv with rfl | hv
      · exact (mem_evenNeighbors _ _).mpr ⟨hback _ hyw.symm, hy⟩
      obtain ⟨ha, he⟩ := (mem_evenNeighbors w v).mp hv
      exact (mem_evenNeighbors w v).mpr ⟨hback v ha, ((hparity v).mp he).1⟩
    have hc := Finset.card_le_card hsub
    rw [Finset.card_insert_of_notMem (by simp [hne, hnx]),
      Finset.card_insert_of_notMem hny] at hc
    have ht := hs.eDegree_even w hew
    have hu := hcap w hewG hwx hwy
    unfold eDegree at ht hu
    omega
  have hJconn : J.Connected := hconn.mono le_sup_left
  obtain ⟨D, hD⟩ := (floor_or_set J hJconn hJcap).resolve_right hnotSET
  have : Nontrivial V := ⟨⟨x, y, hne⟩⟩
  have hxp : 0 < (J.deleteEdges {s(x, y)}).degree x := by
    simpa only [SimpleGraph.degree, SimpleGraph.neighborFinset,
      ← Set.ncard_eq_toFinset_card', hdel] using hconn.preconnected.degree_pos_of_nontrivial x
  have hyp : 0 < (J.deleteEdges {s(x, y)}).degree y := by
    simpa only [SimpleGraph.degree, SimpleGraph.neighborFinset,
      ← Set.ncard_eq_toFinset_card', hdel] using hconn.preconnected.degree_pos_of_nontrivial y
  have hxe : Even ((J.deleteEdges {s(x, y)}).degree x) := by
    simpa only [SimpleGraph.degree, SimpleGraph.neighborFinset,
      ← Set.ncard_eq_toFinset_card', hdel] using hx
  have hye : Even ((J.deleteEdges {s(x, y)}).degree y) := by
    simpa only [SimpleGraph.degree, SimpleGraph.neighborFinset,
      ← Set.ncard_eq_toFinset_card', hdel] using hy
  obtain ⟨P, hP, hPx, hPy, _⟩ := D.endpoint_preserving_edge_deletion x y hJxy hxp hxe hyp hye
  have hout : ∃ P : Decomposition (J.deleteEdges {s(x, y)}),
      P.size ≤ Fintype.card V / 2 + 1 ∧ 2 ≤ P.endpointCount x ∧ 2 ≤ P.endpointCount y :=
    ⟨P, by omega, hPx, hPy⟩
  rwa [hdel] at hout

/-- The strengthened odd-order manuscript proposition, without a hub-degree guard. -/
theorem odd_order_two_exception_of_cap (m : ℕ) (horder : Fintype.card V = 2 * m + 1)
    (hconn : G.Connected) (x y : V) (hne : x ≠ y) (hmissing : ¬ G.Adj x y)
    (hx : Even (G.degree x)) (hy : Even (G.degree y))
    (hcap : ∀ v, Even (G.degree v) → v ≠ x → v ≠ y → eDegree G v ≤ 3) :
    ∃ P : Decomposition G, P.size ≤ m + 1 ∧
      2 ≤ P.endpointCount x ∧ 2 ≤ P.endpointCount y := by
  obtain ⟨P, hp, hxP, hyP⟩ := two_exception_floor_add_one hconn x y hne hmissing hx hy hcap
  exact ⟨P, by omega, hxP, hyP⟩

/-- Compatibility version of the earlier guarded proposition. The new proof
does not use the extra bound; existing whole-bowtie consumers remain valid. -/
theorem odd_order_two_exception (m : ℕ) (horder : Fintype.card V = 2 * m + 1)
    (hconn : G.Connected) (x y : V) (hne : x ≠ y) (hmissing : ¬ G.Adj x y)
    (hx : Even (G.degree x)) (hy : Even (G.degree y))
    (hcap : ∀ v, Even (G.degree v) → v ≠ x → v ≠ y → eDegree G v ≤ 3)
    (_hlarge : 4 ≤ max (eDegree G x) (eDegree G y)) :
    ∃ P : Decomposition G, P.size ≤ m + 1 ∧
      2 ≤ P.endpointCount x ∧ 2 ≤ P.endpointCount y :=
  odd_order_two_exception_of_cap m horder hconn x y hne hmissing hx hy hcap

end Gallai
