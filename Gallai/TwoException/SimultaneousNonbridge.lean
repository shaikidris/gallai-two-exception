/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.Inputs.FloorOrSET
public import Gallai.Operations.InsertEdge
public import Gallai.Structure.EdgeDeletion
public import Gallai.Structure.SETBoundary

@[expose] public section

/-!
# Simultaneous endpoints across a non-bridge edge

Deleting an adjacent pair of even designated vertices makes them odd. A floor
decomposition of the connected puncture, followed by a singleton restoration
of the deleted edge, exposes both vertices with one unit of path slack.
-/

namespace Gallai.TwoException

open scoped Finset

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The adjacent non-bridge branch of simultaneous endpoint exposure. -/
theorem simultaneous_of_nonbridge
    (hconn : G.Connected) (h x : V) (hne : h ≠ x) (hedge : G.Adj h x)
    (hnotBridge : ¬ G.IsBridge s(h, x))
    (hh : Even (G.degree h)) (hx : Even (G.degree x))
    (hcap : ∀ v, Even (G.degree v) → v ≠ h → v ≠ x → eDegree G v ≤ 3) :
    ∃ D : Decomposition G, D.size ≤ Fintype.card V / 2 + 1 ∧
      2 ≤ D.endpointCount h ∧ 2 ≤ D.endpointCount x := by
  classical
  let J := G.deleteEdges {s(h, x)}
  have hJconn : J.Connected := by
    exact hconn.preconnected.connected_deleteEdges_of_not_isBridge hnotBridge
  have hdh : J.degree h + 1 = G.degree h := by
    simpa [J] using degree_delete_edge_add_one G h x hedge
  have hdx : J.degree x + 1 = G.degree x := by
    have hd := degree_delete_edge_add_one G x h hedge.symm
    have hs : s(x, h) = s(h, x) := Sym2.eq_swap
    rw [hs] at hd
    simpa [J] using hd
  have hoff (v : V) (hvh : v ≠ h) (hvx : v ≠ x) : J.degree v = G.degree v := by
    simpa [J] using degree_delete_edge_of_ne G h x v hvh hvx
  have hparity (v : V) : Even (J.degree v) ↔ Even (G.degree v) ∧ v ≠ h ∧ v ≠ x := by
    by_cases hvh : v = h
    · subst v
      have ho : Odd (J.degree h) := by
        rcases hh with ⟨q, hq⟩
        exact ⟨q - 1, by omega⟩
      simp [Nat.not_even_iff_odd.mpr ho]
    by_cases hvx : v = x
    · subst v
      have ho : Odd (J.degree x) := by
        rcases hx with ⟨q, hq⟩
        exact ⟨q - 1, by omega⟩
      simp [Nat.not_even_iff_odd.mpr ho]
    rw [hoff v hvh hvx]
    simp [hvh, hvx]
  have hJle {a b : V} (hab : J.Adj a b) : G.Adj a b := by
    change (G.deleteEdges {s(h, x)}).Adj a b at hab
    exact (SimpleGraph.deleteEdges_adj.mp hab).1
  have hho : Odd (J.degree h) := by
    rcases hh with ⟨q, hq⟩
    exact ⟨q - 1, by omega⟩
  have hxo : Odd (J.degree x) := by
    rcases hx with ⟨q, hq⟩
    exact ⟨q - 1, by omega⟩
  have hJcap (v : V) (hv : Even (J.degree v)) : eDegree J v ≤ 3 := by
    obtain ⟨hvG, hvh, hvx⟩ := (hparity v).mp hv
    have hs : evenNeighbors J v ⊆ evenNeighbors G v := by
      intro w hw
      obtain ⟨ha, he⟩ := (mem_evenNeighbors v w).mp hw
      exact (mem_evenNeighbors v w).mpr ⟨hJle ha,
        ((hparity w).mp he).1⟩
    exact (Finset.card_le_card hs).trans (hcap v hvG hvh hvx)
  have hnotSET : ¬ IsSET J := by
    intro hs
    obtain ⟨w, hhw, hxw, hew⟩ := hs.common_even_neighbor h x hho hxo
    obtain ⟨hewG, hwh, hwx⟩ := (hparity w).mp hew
    have hnh : h ∉ evenNeighbors J w := by
      intro hm
      exact (Nat.not_even_iff_odd.mpr hho) ((mem_evenNeighbors w h).mp hm).2
    have hnx : x ∉ evenNeighbors J w := by
      intro hm
      exact (Nat.not_even_iff_odd.mpr hxo) ((mem_evenNeighbors w x).mp hm).2
    have hsub : insert h (insert x (evenNeighbors J w)) ⊆ evenNeighbors G w := by
      intro v hv
      rcases Finset.mem_insert.mp hv with rfl | hv
      · exact (mem_evenNeighbors _ _).mpr ⟨hJle hhw.symm, hh⟩
      rcases Finset.mem_insert.mp hv with rfl | hv
      · exact (mem_evenNeighbors _ _).mpr ⟨hJle hxw.symm, hx⟩
      obtain ⟨ha, he⟩ := (mem_evenNeighbors w v).mp hv
      exact (mem_evenNeighbors w v).mpr ⟨hJle ha, ((hparity v).mp he).1⟩
    have hc := Finset.card_le_card hsub
    rw [Finset.card_insert_of_notMem (by simp [hne, hnh]),
      Finset.card_insert_of_notMem hnx] at hc
    have ht := hs.eDegree_even w hew
    have hu := hcap w hewG hwh hwx
    unfold eDegree at ht hu
    omega
  obtain ⟨P, hP⟩ := (floor_or_set J hJconn hJcap).resolve_right hnotSET
  have hmissing : ¬ J.Adj h x := by simp [J, SimpleGraph.deleteEdges_adj]
  let D := P.insertEdge h x hne hmissing
  have hgraph : J ⊔ SimpleGraph.edge h x = G := by
    simpa [J] using delete_edge_sup_edge G h x hedge
  have hsize : D.size ≤ Fintype.card V / 2 + 1 := by
    rw [show D = P.insertEdge h x hne hmissing by rfl, Decomposition.insertEdge_size]
    omega
  have hP_h : 0 < P.endpointCount h :=
    P.endpointCount_pos_of_odd_degree h (by simpa only [J] using hho)
  have hP_x : 0 < P.endpointCount x :=
    P.endpointCount_pos_of_odd_degree x (by simpa only [J] using hxo)
  have hDh : 2 ≤ D.endpointCount h := by
    rw [show D = P.insertEdge h x hne hmissing by rfl,
      Decomposition.insertEdge_endpointCount]
    simp
    omega
  have hDx : 2 ≤ D.endpointCount x := by
    rw [show D = P.insertEdge h x hne hmissing by rfl,
      Decomposition.insertEdge_endpointCount]
    simp [hne]
    omega
  have hout : ∃ D : Decomposition (J ⊔ SimpleGraph.edge h x),
      D.size ≤ Fintype.card V / 2 + 1 ∧
        2 ≤ D.endpointCount h ∧ 2 ≤ D.endpointCount x :=
    ⟨D, hsize, hDh, hDx⟩
  rwa [hgraph] at hout

end Gallai.TwoException
