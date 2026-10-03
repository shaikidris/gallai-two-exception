/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.Operations.AddEdge
public import Gallai.Operations.SingleMerge
public import Gallai.Operations.Union
public import Gallai.Inputs.OneException
public import Gallai.Inputs.FloorOrSET
public import Gallai.Inputs.SETReserve
public import Gallai.Inputs.EvenStarReserveRestore
public import Gallai.Structure.CutVertexPieces
public import Gallai.TwoException.AdjacentEndgame
public import Mathlib.Combinatorics.SimpleGraph.Acyclic

@[expose] public section

/-! # The singleton-edge hub-cut branch of Xie's odd/odd case

When the opposite hub-cut piece is the single edge `xw`, deleting that edge
leaves `w` isolated.  The `y`-output in Xie's Case 2.2(ii) therefore has a
small independent reconstruction: attach `w` to an actual carrier ending at
`x`.  This file records that endpoint-preserving operation before the more
substantial half-star construction for the separate `x`-output.
-/

namespace Gallai.TwoException

open scoped Finset

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- Fix the puncture adjacency decision for the full-star source branch. -/
noncomputable local instance singletonEvenStarAdj (G : SimpleGraph V)
    [DecidableRel G.Adj] (x : V) :
    DecidableRel (evenStarPuncture G x).Adj := fun _ _ => Classical.propDecidable _

/-- Deleting the full even-neighbour star at one adjacent exception makes the
other exception an odd leaf of the puncture.  Hence only the deleted-star hub
can remain an E-degree exception.  This is the cap calculation in the
even-`m` x-output of Xie's singleton-edge branch. -/
theorem singleton_full_star_puncture_cap_except_x
    (G : SimpleGraph V) [DecidableRel G.Adj] (x y : V)
    (H : AdjacentInstance G x y) :
    ∀ v, Even ((evenStarPuncture G x).degree v) → v ≠ x →
      eDegree (evenStarPuncture G x) v ≤ 3 := by
  intro v hv hvx
  obtain ⟨hvG, hvS⟩ := evenStarPuncture_even_off_center G x v hvx hv
  have hxy : x ≠ y := H.2.1
  have hyS : y ∈ evenNeighbors G x :=
    (mem_evenNeighbors x y).mpr ⟨H.2.2.1, H.2.2.2.2.1⟩
  have hvy : v ≠ y := by
    intro h
    subst v
    exact hvS hyS
  have hcapG := H.2.2.2.2.2 v hvG hvx hvy
  apply (Finset.card_le_card (s := evenNeighbors (evenStarPuncture G x) v)
    (t := evenNeighbors G v) ?_).trans hcapG
  intro w hw
  obtain ⟨hvw, hwEven⟩ := (mem_evenNeighbors (G := evenStarPuncture G x) v w).mp hw
  have hwx : w ≠ x := by
    intro h
    subst w
    exact evenStarPuncture_no_even_neighbor G x v hvw.symm hv
  exact (mem_evenNeighbors (G := G) v w).mpr
    ⟨hvw.1, (evenStarPuncture_even_off_center G x w hwx hwEven).1⟩

/-- The `m`-even x-output in Xie's singleton-edge branch.  Once the full
even-star puncture is connected and retains positive degree at `x`, the
published one-exception theorem supplies two ends at `x`; the designated
half-star restoration then keeps `y` selected and restores all remaining
spokes at no path-count cost. -/
theorem singleton_even_star_x_output
    (G : SimpleGraph V) [DecidableRel G.Adj] (x y : V)
    (H : AdjacentInstance G x y)
    (hconn : (evenStarPuncture G x).Connected)
    (hmEven : Even (eDegree G x))
    (hxpos : 0 < (evenStarPuncture G x).degree x) :
    ∃ P : Decomposition G, P.size ≤ (Fintype.card V + 1) / 2 ∧
      2 ≤ P.endpointCount x := by
  let I := evenStarPuncture G x
  have hxy : x ≠ y := H.2.1
  have hxEven : Even (I.degree x) := by
    have hd := evenStarPuncture_degree_center G x
    have hxGeven := H.2.2.2.1
    rw [Nat.even_iff] at hxGeven hmEven ⊢
    change I.degree x + eDegree G x = G.degree x at hd
    omega
  obtain ⟨D, hDsize, hDx⟩ := one_exception_endpoint I x (by simpa [I] using hconn)
    (by simpa [I] using hxpos) hxEven (by
      simpa [I] using singleton_full_star_puncture_cap_except_x G x y H)
  have hyS : y ∈ evenNeighbors G x :=
    (mem_evenNeighbors x y).mpr ⟨H.2.2.1, H.2.2.2.2.1⟩
  have hleafcap (v : V) (hv : v ∈ evenNeighbors G x) (hvy : v ≠ y) :
      #((evenNeighbors G v).erase x) ≤ 2 := by
    obtain ⟨hvxAdj, hvEven⟩ := (mem_evenNeighbors x v).mp hv
    have hvx : v ≠ x := hvxAdj.ne.symm
    have hxv : x ∈ evenNeighbors G v :=
      (mem_evenNeighbors v x).mpr ⟨hvxAdj.symm, H.2.2.2.1⟩
    have hcard := Finset.card_erase_add_one hxv
    have hcap := H.2.2.2.2.2 v hvEven hvx hvy
    change #(evenNeighbors G v) ≤ 3 at hcap
    omega
  have hneighbors (v : V) (hv : G.Adj x v) : 0 < D.endpointCount v := by
    apply D.endpointCount_pos_of_odd_degree
    simpa [I] using evenStarPuncture_odd_neighbor G x v hv
  obtain ⟨P, hPsize, hPx, _⟩ := D.restore_partial_even_star_with_reserve x
    (evenNeighbors G x) (by exact fun _ h => h) y hyS hleafcap (by simpa [I] using hDx)
      hneighbors
  exact ⟨P, by rw [hPsize]; exact hDsize, hPx⟩

/-- Source-facing even-star form: after deleting the shared hub, a retained
non-even neighbour reconnects the full even-star puncture.  This packages the
only graph-theoretic use of the strict source inequality
`d_F(x) < d_{G₁}(x)`; extracting that retained neighbour from the literal
cut-piece degree accounting remains separate. -/
theorem singleton_even_star_x_output_of_delete_vertex_connected
    (G : SimpleGraph V) [DecidableRel G.Adj] (x y : V)
    (H : AdjacentInstance G x y)
    (hdelete : (G.induce {v | v ≠ x}).Connected)
    (hmEven : Even (eDegree G x))
    (hretain : ∃ w, (evenStarPuncture G x).Adj x w) :
    ∃ P : Decomposition G, P.size ≤ (Fintype.card V + 1) / 2 ∧
      2 ≤ P.endpointCount x := by
  obtain ⟨w, hw⟩ := hretain
  apply singleton_even_star_x_output G x y H
    (starPuncture_connected G x (evenNeighbors G x) hdelete ⟨w, hw⟩) hmEven
  exact ((evenStarPuncture G x).degree_pos_iff_exists_adj x).mpr ⟨w, hw⟩

/-- Deleting a leaf edge incident with a vertex absent from an induced graph
does not alter that induced graph.  This is the source transport from
`G₁ - x` to `G - x` in the singleton-edge branch. -/
theorem singleton_delete_leaf_induce_delete_hub_eq
    (G : SimpleGraph V) [DecidableRel G.Adj] (x w : V) :
    (G.deleteEdges {s(x, w)}).induce {v | v ≠ x} =
      G.induce {v | v ≠ x} := by
  exact induce_puncture_eq_of_notMem (G := G) x w {v | v ≠ x} (by simp)

/-- The strict source degree inequality leaves a retained edge at the hub
after the entire even-neighbour star is deleted. -/
theorem singleton_even_star_retained_neighbor_of_strict_degree
    (G : SimpleGraph V) [DecidableRel G.Adj] (x w : V) (hxw : G.Adj x w)
    (hlt : eDegree G x < (G.deleteEdges {s(x, w)}).degree x) :
    ∃ z, (evenStarPuncture G x).Adj x z := by
  have hdelete := degree_delete_edge_add_one G x w hxw
  have hstar := evenStarPuncture_degree_center G x
  have hpos : 0 < (evenStarPuncture G x).degree x := by
    change (evenStarPuncture G x).degree x + eDegree G x = G.degree x at hstar
    omega
  exact ((evenStarPuncture G x).degree_pos_iff_exists_adj x).mp hpos

/-- Source-facing even singleton-edge geometry.  The actual connected
puncture is `G - xw`; after deleting `x`, that graph is definitionally the
same induced graph as `G - x`.  Xie's strict degree inequality yields the
retained non-even edge required to reconnect the full even-star puncture. -/
theorem singleton_even_star_x_output_of_leaf_geometry
    (G : SimpleGraph V) [DecidableRel G.Adj] (x y w : V)
    (H : AdjacentInstance G x y) (hxw : G.Adj x w)
    (hcut : ((G.deleteEdges {s(x, w)}).induce {v | v ≠ x}).Connected)
    (hmEven : Even (eDegree G x))
    (hlt : eDegree G x < (G.deleteEdges {s(x, w)}).degree x) :
    ∃ P : Decomposition G, P.size ≤ (Fintype.card V + 1) / 2 ∧
      2 ≤ P.endpointCount x := by
  have hdelete : (G.induce {v | v ≠ x}).Connected := by
    rw [← singleton_delete_leaf_induce_delete_hub_eq G x w]
    exact hcut
  exact singleton_even_star_x_output_of_delete_vertex_connected G x y H
    hdelete hmEven
    (singleton_even_star_retained_neighbor_of_strict_degree G x w hxw hlt)

/-- The all-star reconstruction portion of Xie's singleton-edge equality
branch.  It consumes precisely the decomposition that the source constructs
on the disconnected full-star puncture: a ceiling-budget decomposition with a
positive endpoint at `x` and endpoint supply at every original neighbour.
The remaining source obligation is therefore only to assemble this input from
the connected double puncture and the singleton edge `xw`. -/
theorem singleton_odd_star_x_output_of_puncture_certificate
    (G : SimpleGraph V) [DecidableRel G.Adj] (x y : V)
    (H : AdjacentInstance G x y)
    (hmOdd : Odd (eDegree G x))
    (D : Decomposition (evenStarPuncture G x))
    (hDsize : D.size ≤ (Fintype.card V + 1) / 2)
    (hDx : 0 < D.endpointCount x)
    (hneighbors : ∀ v, G.Adj x v → 0 < D.endpointCount v) :
    ∃ P : Decomposition G, P.size ≤ (Fintype.card V + 1) / 2 ∧
      2 ≤ P.endpointCount x := by
  have hyS : y ∈ evenNeighbors G x :=
    (mem_evenNeighbors x y).mpr ⟨H.2.2.1, H.2.2.2.2.1⟩
  have hleafcap (v : V) (hv : v ∈ evenNeighbors G x) (hvy : v ≠ y) :
      #((evenNeighbors G v).erase x) ≤ 2 := by
    obtain ⟨hvxAdj, hvEven⟩ := (mem_evenNeighbors x v).mp hv
    have hvx : v ≠ x := hvxAdj.ne.symm
    have hxv : x ∈ evenNeighbors G v :=
      (mem_evenNeighbors v x).mpr ⟨hvxAdj.symm, H.2.2.2.1⟩
    have hcard := Finset.card_erase_add_one hxv
    have hcap := H.2.2.2.2.2 v hvEven hvx hvy
    change #(evenNeighbors G v) ≤ 3 at hcap
    omega
  have hneighbors (v : V) (hv : G.Adj x v) : 0 < D.endpointCount v := by
    exact hneighbors v hv
  obtain ⟨P, hPsize, hPx, _⟩ := D.restore_partial_odd_star_with_reserve x
    (evenNeighbors G x) (by exact fun _ h => h) hmOdd y hyS hleafcap
    hDx hneighbors
  exact ⟨P, by rw [hPsize]; exact hDsize, hPx⟩

/-- The `m`-odd strict x-output in Xie's singleton-edge branch.  When the
full-star puncture is connected, its floor-or-SET output supplies the
puncture certificate required by the all-star reconstruction.  In the SET
alternative the endpoint-reserve construction supplies positivity at `x`. -/
theorem singleton_odd_star_x_output
    (G : SimpleGraph V) [DecidableRel G.Adj] (x y : V)
    (H : AdjacentInstance G x y)
    (hconn : (evenStarPuncture G x).Connected)
    (hmOdd : Odd (eDegree G x)) :
    ∃ P : Decomposition G, P.size ≤ (Fintype.card V + 1) / 2 ∧
      2 ≤ P.endpointCount x := by
  let I := evenStarPuncture G x
  have hxOdd : Odd (I.degree x) := by
    have hd := evenStarPuncture_degree_center G x
    have hxGeven := H.2.2.2.1
    rw [Nat.even_iff] at hxGeven
    rw [Nat.odd_iff] at hmOdd ⊢
    change I.degree x + eDegree G x = G.degree x at hd
    omega
  have hcapI : ∀ v, Even (I.degree v) → eDegree I v ≤ 3 := by
    intro v hv
    by_cases hvx : v = x
    · subst v
      exact False.elim ((Nat.not_even_iff_odd.mpr hxOdd) hv)
    exact singleton_full_star_puncture_cap_except_x G x y H v (by simpa [I] using hv) hvx
  obtain ⟨D, hDsize, hDx⟩ : ∃ D : Decomposition I,
      D.size ≤ (Fintype.card V + 1) / 2 ∧ 0 < D.endpointCount x := by
    rcases floor_or_set I (by simpa [I] using hconn) hcapI with ⟨D, hD⟩ | hset
    · exact ⟨D, by omega, D.endpointCount_pos_of_odd_degree x hxOdd⟩
    · obtain ⟨D, hD, hDx⟩ := hset.endpoint_reserve x
      exact ⟨D, hD, by omega⟩
  apply singleton_odd_star_x_output_of_puncture_certificate G x y H hmOdd D hDsize hDx
  intro v hv
  apply D.endpointCount_pos_of_odd_degree
  simpa [I] using evenStarPuncture_odd_neighbor G x v hv

/-- Source-facing odd-star form: connectivity of the graph with the shared
hub deleted is enough.  The existing puncture-connectivity lemma restores the
hub through an unselected odd neighbour; no retained-degree witness is needed
when the deleted even-neighbour star has odd cardinality. -/
theorem singleton_odd_star_x_output_of_delete_vertex_connected
    (G : SimpleGraph V) [DecidableRel G.Adj] (x y : V)
    (H : AdjacentInstance G x y)
    (hdelete : (G.induce {v | v ≠ x}).Connected)
    (hmOdd : Odd (eDegree G x)) :
    ∃ P : Decomposition G, P.size ≤ (Fintype.card V + 1) / 2 ∧
      2 ≤ P.endpointCount x := by
  apply singleton_odd_star_x_output G x y H
    (odd_evenStarPuncture_connected G x H.2.2.2.1 hmOdd hdelete) hmOdd

/-- In the singleton cut-piece branch, deleting the leaf edge makes the
shared hub odd and isolates the leaf.  Thus every surviving even vertex other
than the retained exceptional vertex `y` inherits the original subcubic
E-degree cap.  This is the precise cap input for the source's one-exception
call on `G - xw`. -/
theorem singleton_leaf_puncture_cap
    (G : SimpleGraph V) [DecidableRel G.Adj] (x y w : V)
    (H : AdjacentInstance G x y) (hxw : G.Adj x w) (hwy : w ≠ y)
    (hleaf : ∀ v, G.Adj w v → v = x) :
    ∀ v, Even ((G.deleteEdges {s(x, w)}).degree v) → v ≠ y →
      eDegree (G.deleteEdges {s(x, w)}) v ≤ 3 := by
  let I := G.deleteEdges {s(x, w)}
  have hxy : x ≠ y := H.2.1
  have hwx : w ≠ x := hxw.ne.symm
  have hdx : I.degree x + 1 = G.degree x := by
    simpa [I] using degree_delete_edge_add_one G x w hxw
  have hxodd : Odd (I.degree x) := by
    rcases H.2.2.2.1 with ⟨q, hq⟩
    exact ⟨q - 1, by omega⟩
  have hIle : I ≤ G := by
    intro a b hab
    exact (SimpleGraph.deleteEdges_adj.mp hab).1
  have hIisolated : ∀ v, ¬ I.Adj w v := by
    intro v hwv
    have hwvG : G.Adj w v := (SimpleGraph.deleteEdges_adj.mp hwv).1
    have hvx : v = x := hleaf v hwvG
    subst v
    exact (SimpleGraph.deleteEdges_adj.mp hwv).2 (by simp [Sym2.eq_swap])
  have hIwdegree : I.degree w = 0 := by
    rw [← I.card_neighborFinset_eq_degree]
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro v hv
    exact hIisolated v (I.mem_neighborFinset w v |>.mp hv)
  intro v hv hvy
  by_cases hvx : v = x
  · subst v
    exact False.elim ((Nat.not_even_iff_odd.mpr hxodd) hv)
  by_cases hvw : v = w
  · subst v
    have hle := eDegree_le_degree (G := I) w
    rw [hIwdegree] at hle
    change eDegree I w ≤ 3
    omega
  have hvG : Even (G.degree v) := by
    have hd : I.degree v = G.degree v := by
      simpa [I] using degree_delete_edge_of_ne G x w v hvx hvw
    rwa [hd] at hv
  have hcapG := H.2.2.2.2.2 v hvG hvx hvy
  apply (Finset.card_le_card (s := evenNeighbors I v) (t := evenNeighbors G v) ?_).trans hcapG
  intro z hz
  obtain ⟨hvz, hzEven⟩ := (mem_evenNeighbors (G := I) v z).mp hz
  have hvzG : G.Adj v z := hIle hvz
  have hzw : z ≠ w := by
    intro h
    subst z
    exact hvx (hleaf v hvzG.symm)
  have hzx : z ≠ x := by
    intro h
    subst z
    exact (Nat.not_even_iff_odd.mpr hxodd) hzEven
  have hdz : I.degree z = G.degree z := by
    simpa [I] using degree_delete_edge_of_ne G x w z hzx hzw
  exact (mem_evenNeighbors (G := G) v z).mpr ⟨hvzG, by rwa [hdz] at hzEven⟩

/-- In the literal singleton cut-piece configuration, deleting the sole spoke
leaves the cut leaf isolated.  This is deliberately separate from connectedness:
the connected one-exception input must be applied after removing this ambient
isolate. -/
theorem singleton_leaf_deleted_edge_isolated
    (G : SimpleGraph V) [DecidableRel G.Adj] (x w : V) (hxw : G.Adj x w)
    (hleaf : ∀ v, G.Adj w v → v = x) :
    ∀ v, ¬ (G.deleteEdges {s(x, w)}).Adj w v := by
  intro v hwv
  have hwvG : G.Adj w v := (SimpleGraph.deleteEdges_adj.mp hwv).1
  have hvx : v = x := hleaf v hwvG
  subst v
  exact (SimpleGraph.deleteEdges_adj.mp hwv).2 (by simp [Sym2.eq_swap])

/-- Removing the literal singleton cut leaf leaves the connected nontrivial
piece.  This is the correct connected input for the y-output reconstruction;
the edge-deleted spanning graph itself has an isolate. -/
theorem singleton_leaf_induce_delete_leaf_connected
    (G : SimpleGraph V) [DecidableRel G.Adj] (x w : V)
    (hconn : G.Connected) (hxw : G.Adj x w)
    (hleaf : ∀ v, G.Adj w v → v = x) :
    (G.induce {v | v ≠ w}).Connected := by
  have hwdegree : G.degree w = 1 := by
    rw [SimpleGraph.degree_eq_one_iff_existsUnique_adj]
    exact ⟨x, hxw.symm, fun v hwv => hleaf v hwv⟩
  have hset : {v : V | v ≠ w} = ({w} : Set V)ᶜ := by
    ext v
    simp
  rw [hset]
  exact hconn.induce_compl_singleton_of_degree_eq_one hwdegree

/-- The literal one-edge cut piece has its own one-carrier decomposition, with
the two endpoint incidences recorded explicitly. -/
theorem singleton_edge_decomposition (x w : V) (h : x ≠ w) :
    ∃ E : Decomposition (SimpleGraph.edge x w), E.size = 1 ∧
      ∀ v, E.endpointCount v =
        (if x = v then 1 else 0) + (if w = v then 1 else 0) := by
  let P : NonemptyPath (SimpleGraph.edge x w) :=
    ⟨x, w, .cons (by simp [SimpleGraph.edge_adj, h]) .nil,
      by simp [SimpleGraph.Walk.cons_isPath_iff, h], by simp⟩
  let E : Decomposition (SimpleGraph.edge x w) := {
    size := 1
    path := fun _ => P
    covers := by
      intro e he
      rw [SimpleGraph.edgeSet_edge_of_ne h] at he
      subst e
      refine ⟨0, ?_, ?_⟩
      · simp [P]
      · intro j hj
        exact Fin.eq_zero j
  }
  refine ⟨E, rfl, ?_⟩
  intro v
  simp [E, P, Decomposition.endpointCount]

/-- Adjoining the singleton cut edge to a disjoint double-puncture
decomposition increases the path count by one and adds exactly one endpoint
at each end of that edge. -/
theorem union_singleton_edge
    (R : SimpleGraph V) [DecidableRel R.Adj] (D : Decomposition R)
    (x w : V) (hxw : x ≠ w)
    (hdis : Disjoint R.edgeSet (SimpleGraph.edge x w).edgeSet) :
    ∃ E : Decomposition (R ⊔ SimpleGraph.edge x w), E.size = D.size + 1 ∧
      ∀ v, E.endpointCount v = D.endpointCount v +
        (if x = v then 1 else 0) + (if w = v then 1 else 0) := by
  obtain ⟨Q, hQsize, hQends⟩ := singleton_edge_decomposition (V := V) x w hxw
  obtain ⟨E, hEsize, hEends⟩ := D.union_disjoint_endpoints Q hdis
  refine ⟨E, ?_, ?_⟩
  · rw [hEsize, hQsize]
  · intro v
    rw [hEends, hQends]
    omega

/-- The source's all-star equality schedule, factored at its exact assembly
point.  A decomposition of the connected double puncture is combined with
the isolated cut edge `xw`; once that union is identified with the full
even-star puncture, the checked all-star restoration produces the x output.
This leaves only the theorem-specific construction of the double-puncture
decomposition as a source obligation. -/
theorem singleton_odd_star_x_output_of_double_puncture_certificate
    (G R : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel R.Adj]
    (x y w : V) (H : AdjacentInstance G x y)
    (hxw : G.Adj x w) (hmOdd : Odd (eDegree G x))
    (D : Decomposition R)
    (hdis : Disjoint R.edgeSet (SimpleGraph.edge x w).edgeSet)
    (hpuncture : R ⊔ SimpleGraph.edge x w = evenStarPuncture G x)
    (hbudget : D.size + 1 ≤ (Fintype.card V + 1) / 2)
    (hleaves : ∀ v, G.Adj x v → v ≠ w → 0 < D.endpointCount v) :
    ∃ P : Decomposition G, P.size ≤ (Fintype.card V + 1) / 2 ∧
      2 ≤ P.endpointCount x := by
  have hxwne : x ≠ w := hxw.ne
  obtain ⟨F0, hF0size, hF0ends⟩ :=
    union_singleton_edge R D x w hxwne hdis
  let F : Decomposition (evenStarPuncture G x) := hpuncture ▸ F0
  have castSize {A B : SimpleGraph V} (h : A = B) (Q : Decomposition A) :
      (h ▸ Q).size = Q.size := by
    subst B
    rfl
  have castEnds {A B : SimpleGraph V} (h : A = B) (Q : Decomposition A) (v : V) :
      (h ▸ Q).endpointCount v = Q.endpointCount v := by
    subst B
    rfl
  have hFsize : F.size ≤ (Fintype.card V + 1) / 2 := by
    rw [show F.size = F0.size by exact castSize hpuncture F0, hF0size]
    exact hbudget
  have hFends (v : V) : F.endpointCount v = F0.endpointCount v :=
    castEnds hpuncture F0 v
  have hFx : 0 < F.endpointCount x := by
    rw [hFends, hF0ends]
    simp [hxwne]
  have hFneighbors (v : V) (hv : G.Adj x v) : 0 < F.endpointCount v := by
    by_cases hvw : v = w
    · subst v
      rw [hFends, hF0ends]
      simp [hxwne]
    · have hvx : x ≠ v := hv.ne
      have hwv : w ≠ v := Ne.symm hvw
      rw [hFends, hF0ends]
      simp [hvx, hwv, hleaves v hv hvw]
  exact singleton_odd_star_x_output_of_puncture_certificate G x y H hmOdd F
    hFsize hFx hFneighbors

/-- A decomposition on an induced core lifts to its ambient spanning graph
without changing either its path count or endpoint incidences on the core.
This small transport is kept in the singleton module because the source core
is obtained by removing both the shared hub and the singleton cut leaf. -/
theorem singleton_lift_induced_core {R : SimpleGraph V} (S : Set V)
    [DecidablePred (· ∈ S)] (hs : R.support ⊆ S) (D : Decomposition (R.induce S)) :
    ∃ E : Decomposition R, E.size = D.size ∧
      ∀ v : S, E.endpointCount v.val = D.endpointCount v := by
  have hgraph : (R.induce S).map (Function.Embedding.subtype _) = R :=
    (R.spanningCoe_induce_eq_self S).mpr hs
  have hout : ∃ E : Decomposition ((R.induce S).map (Function.Embedding.subtype _)),
      E.size = D.size ∧ ∀ v : S, E.endpointCount v.val = D.endpointCount v :=
    ⟨D.map (Function.Embedding.subtype _), rfl,
      fun v => D.map_endpointCount (Function.Embedding.subtype _) v⟩
  rwa [hgraph] at hout

/-- Source-facing equality-core consumer for Xie's singleton-edge branch.
The hypotheses are exactly the data still supplied by the literal cut
configuration: the double puncture is supported on its connected core, its
even vertices are subcubic, and every surviving leaf of the deleted star is
odd in that core.  The proof itself now constructs the required puncture
decomposition from the published floor-or-SET theorem rather than accepting a
decomposition certificate as an opaque input. -/
theorem singleton_odd_star_x_output_of_connected_core
    (G R : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel R.Adj]
    (S : Set V) [DecidablePred (· ∈ S)] (z : S)
    (x y w : V) (H : AdjacentInstance G x y)
    (hxw : G.Adj x w) (hmOdd : Odd (eDegree G x))
    (hsupport : R.support ⊆ S)
    (hconn : (R.induce S).Connected)
    (hcap : ∀ v : S, Even ((R.induce S).degree v) →
      eDegree (R.induce S) v ≤ 3)
    (hdis : Disjoint R.edgeSet (SimpleGraph.edge x w).edgeSet)
    (hpuncture : R ⊔ SimpleGraph.edge x w = evenStarPuncture G x)
    (hbudget : (Fintype.card S + 1) / 2 + 1 ≤ (Fintype.card V + 1) / 2)
    (hleaves : ∀ v, G.Adj x v → v ≠ w →
      ∃ hvS : v ∈ S, Odd ((R.induce S).degree ⟨v, hvS⟩)) :
    ∃ P : Decomposition G, P.size ≤ (Fintype.card V + 1) / 2 ∧
      2 ≤ P.endpointCount x := by
  obtain ⟨D0, hD0size⟩ : ∃ D0 : Decomposition (R.induce S),
      D0.size ≤ (Fintype.card S + 1) / 2 := by
    rcases floor_or_set (R.induce S) hconn hcap with ⟨D0, hD0⟩ | hset
    · exact ⟨D0, by omega⟩
    · obtain ⟨D0, hD0, _⟩ := hset.endpoint_reserve z
      exact ⟨D0, hD0⟩
  obtain ⟨D, hDsize, hDends⟩ := singleton_lift_induced_core S hsupport D0
  apply singleton_odd_star_x_output_of_double_puncture_certificate G R x y w H
    hxw hmOdd D hdis hpuncture
  · rw [hDsize]
    omega
  · intro v hv hvw
    obtain ⟨hvS, hvOdd⟩ := hleaves v hv hvw
    rw [hDends ⟨v, hvS⟩]
    exact D0.endpointCount_pos_of_odd_degree ⟨v, hvS⟩ hvOdd

/-- The singleton cut leaf is odd, so its retained spoke is not removed by
the full even-neighbour-star puncture at the shared hub. -/
theorem singleton_leaf_spoke_survives_evenStarPuncture
    (G : SimpleGraph V) [DecidableRel G.Adj] (x w : V)
    (hxw : G.Adj x w) (hleaf : ∀ v, G.Adj w v → v = x) :
    (evenStarPuncture G x).Adj x w := by
  have hwdegree : G.degree w = 1 := by
    rw [SimpleGraph.degree_eq_one_iff_existsUnique_adj]
    exact ⟨x, hxw.symm, fun v hwv => hleaf v hwv⟩
  have hwodd : Odd (G.degree w) := by
    simpa [hwdegree] using (show Odd 1 from ⟨0, rfl⟩)
  have hwnot : w ∉ evenNeighbors G x := by
    intro hw
    exact (Nat.not_even_iff_odd.mpr hwodd) ((mem_evenNeighbors x w).mp hw).2
  change G.Adj x w ∧ ¬ ((evenNeighbors G x).sup (SimpleGraph.edge x)).Adj x w
  refine ⟨hxw, ?_⟩
  intro hs
  exact hwnot ((star_sup_adj_center x (evenNeighbors G x) (by simp) w).mp hs)

/-- Deleting the retained singleton spoke makes its edge set disjoint from
that spoke.  This is the exact disjointness premise for unioning the source's
one-edge carrier back into the double puncture. -/
theorem singleton_delete_edge_disjoint
    (Q : SimpleGraph V) [DecidableRel Q.Adj] (x w : V) (hxw : Q.Adj x w) :
    Disjoint (Q.deleteEdges {s(x, w)}).edgeSet (SimpleGraph.edge x w).edgeSet := by
  apply Set.disjoint_left.mpr
  intro e he hEdge
  rw [SimpleGraph.edgeSet_deleteEdges] at he
  rw [SimpleGraph.edgeSet_edge_of_ne hxw.ne] at hEdge
  have heq : e = s(x, w) := Set.mem_singleton_iff.mp hEdge
  subst e
  exact he.2 rfl

/-- Two isolated vertices do not occur in the support of a graph, so the
ambient graph is supported on the corresponding double-complement subtype. -/
theorem support_subset_double_compl_of_isolated
    (R : SimpleGraph V) (x w : V)
    (hxisolated : ∀ v, ¬ R.Adj x v)
    (hwisolated : ∀ v, ¬ R.Adj w v) :
    R.support ⊆ {v | v ≠ x ∧ v ≠ w} := by
  intro v hv
  rw [SimpleGraph.mem_support] at hv
  obtain ⟨u, huv⟩ := hv
  constructor
  · intro hvx
    subst v
    exact hxisolated u huv
  · intro hvw
    subst v
    exact hwisolated u huv

/-- In the equality branch, the full even-star puncture has exactly the
singleton leaf spoke at the hub. Deleting it isolates both the hub and the
leaf, hence the resulting double puncture is automatically supported on the
native core `V \ {x,w}`. -/
theorem singleton_literal_double_puncture_support
    (G : SimpleGraph V) [DecidableRel G.Adj] (x w : V)
    (hxw : G.Adj x w) (hleaf : ∀ v, G.Adj w v → v = x)
    (hdegree : (evenStarPuncture G x).degree x = 1) :
    ((evenStarPuncture G x).deleteEdges {s(x, w)}).support ⊆
      {v | v ≠ x ∧ v ≠ w} := by
  let Q : SimpleGraph V := evenStarPuncture G x
  let R : SimpleGraph V := Q.deleteEdges {s(x, w)}
  have hxwQ : Q.Adj x w := by
    simpa [Q] using singleton_leaf_spoke_survives_evenStarPuncture G x w hxw hleaf
  have hRdegree : R.degree x = 0 := by
    have hd : R.degree x + 1 = Q.degree x := by
      simpa [R] using degree_delete_edge_add_one Q x w hxwQ
    have hQdegree : Q.degree x = 1 := by
      simpa [Q] using hdegree
    omega
  have hxisolated (v : V) : ¬ R.Adj x v := by
    intro hxv
    have hp : 0 < R.degree x := hxv.degree_pos_left
    omega
  have hQleaf (v : V) (hwv : Q.Adj w v) : v = x := by
    apply hleaf v
    change G.Adj w v ∧ ¬ ((evenNeighbors G x).sup (SimpleGraph.edge x)).Adj w v at hwv
    exact hwv.1
  have hwisolated : ∀ v, ¬ R.Adj w v := by
    simpa [R] using singleton_leaf_deleted_edge_isolated Q x w hxwQ hQleaf
  simpa [R] using support_subset_double_compl_of_isolated R x w hxisolated hwisolated

/-- Every hub neighbour other than the retained singleton leaf is odd in the
induced double-puncture core.  This eliminates the corresponding endpoint
positivity premise: every path decomposition of that core already exposes the
leaf by endpoint parity. -/
theorem singleton_literal_core_leaf_odd
    (G : SimpleGraph V) [DecidableRel G.Adj] (x w : V)
    (S : Set V) [DecidablePred (· ∈ S)]
    (hsupport : ((evenStarPuncture G x).deleteEdges {s(x, w)}).support ⊆ S)
    (v : V) (hxv : G.Adj x v) (hvS : v ∈ S) (hvw : v ≠ w) :
    Odd ((((evenStarPuncture G x).deleteEdges {s(x, w)}).induce S).degree
      ⟨v, hvS⟩) := by
  let Q : SimpleGraph V := evenStarPuncture G x
  let R : SimpleGraph V := Q.deleteEdges {s(x, w)}
  have hQodd : Odd (Q.degree v) := by
    simpa [Q] using evenStarPuncture_odd_neighbor G x v hxv
  have hRdegree : R.degree v = Q.degree v := by
    simpa [R] using degree_delete_edge_of_ne Q x w v hxv.ne.symm hvw
  have hind : (R.induce S).degree ⟨v, hvS⟩ = R.degree v :=
    SimpleGraph.degree_induce_of_support_subset (by simpa [Q, R] using hsupport) ⟨v, hvS⟩
  simpa [Q, R, hind, hRdegree] using hQodd

/-- The singleton cut leaf cannot be the other adjacent exception: that
exception has even degree, whereas a literal cut leaf has degree one. -/
theorem singleton_leaf_ne_other_exception
    (G : SimpleGraph V) [DecidableRel G.Adj] (x y w : V)
    (H : AdjacentInstance G x y) (hxw : G.Adj x w)
    (hleaf : ∀ v, G.Adj w v → v = x) : w ≠ y := by
  intro hwy
  subst w
  have hdegree : G.degree y = 1 := by
    rw [SimpleGraph.degree_eq_one_iff_existsUnique_adj]
    exact ⟨x, H.2.2.1.symm, fun v hyv => hleaf v hyv⟩
  have hyodd : Odd (G.degree y) := by
    rw [hdegree]
    exact ⟨0, rfl⟩
  exact (Nat.not_even_iff_odd.mpr hyodd) H.2.2.2.2.1

/-- The induced native double puncture inherits the subcubic E-degree cap.
The only exceptional vertices of the original graph are `x,y`; the equality
puncture isolates `x`, while `y` is an odd core leaf by the preceding parity
transport. Every remaining even core vertex therefore inherits the original
cap through the two edge deletions and the support-preserving induction. -/
theorem singleton_literal_double_core_cap
    (G : SimpleGraph V) [DecidableRel G.Adj] (x y w : V)
    (H : AdjacentInstance G x y) (hxw : G.Adj x w)
    (hleaf : ∀ u, G.Adj w u → u = x)
    (hdegree : (evenStarPuncture G x).degree x = 1)
    (v : {u | u ≠ x ∧ u ≠ w})
    (hv : Even ((((evenStarPuncture G x).deleteEdges {s(x, w)}).induce
      {u | u ≠ x ∧ u ≠ w}).degree v)) :
    eDegree (((evenStarPuncture G x).deleteEdges {s(x, w)}).induce
      {u | u ≠ x ∧ u ≠ w}) v ≤ 3 := by
  classical
  let S : Set V := {u | u ≠ x ∧ u ≠ w}
  let Q : SimpleGraph V := evenStarPuncture G x
  let R : SimpleGraph V := Q.deleteEdges {s(x, w)}
  have hsupport : R.support ⊆ S := by
    simpa [Q, R, S] using singleton_literal_double_puncture_support G x w hxw hleaf hdegree
  have hRdegree : R.degree v.val = Q.degree v.val := by
    simpa [R] using degree_delete_edge_of_ne Q x w v.val v.property.1 v.property.2
  have hind : (R.induce S).degree v = R.degree v.val :=
    SimpleGraph.degree_induce_of_support_subset hsupport v
  have hReven : Even (R.degree v.val) := by
    rw [← hind]
    simpa [Q, R, S] using hv
  have hQeven : Even (Q.degree v.val) := by
    rwa [← hRdegree]
  have hcapQ : eDegree Q v.val ≤ 3 :=
    singleton_full_star_puncture_cap_except_x G x y H v.val hQeven v.property.1
  have hRleQ : R ≤ Q := by
    change Q.deleteEdges {s(x, w)} ≤ Q
    intro a b hab
    exact (SimpleGraph.deleteEdges_adj.mp hab).1
  rw [eDegree_induce_of_support_subset R S hsupport v]
  apply (Finset.card_le_card (s := evenNeighbors R v.val)
    (t := evenNeighbors Q v.val) ?_).trans hcapQ
  intro q hq
  obtain ⟨hvq, hqEven⟩ := (mem_evenNeighbors (G := R) v.val q).mp hq
  have hqS : q ∈ S := hsupport ((SimpleGraph.mem_support R).mpr ⟨v.val, hvq.symm⟩)
  have hqdegree : R.degree q = Q.degree q := by
    simpa [R] using degree_delete_edge_of_ne Q x w q hqS.1 hqS.2
  have hqEvenQ : Even (Q.degree q) := by
    rwa [← hqdegree]
  exact (mem_evenNeighbors (G := Q) v.val q).mpr ⟨hRleQ hvq, hqEvenQ⟩

/-- Removing two distinct vertices from a finite ambient type leaves exactly
two units of order slack. Consequently a ceiling decomposition of the native
double core may absorb one singleton carrier without exceeding the ambient
ceiling. -/
theorem double_compl_ceiling_add_one_le (x w : V) (hxw : x ≠ w) :
    (Fintype.card {v : V | v ≠ x ∧ v ≠ w} + 1) / 2 + 1 ≤
      (Fintype.card V + 1) / 2 := by
  classical
  have hfilter : (Finset.univ.filter fun v : V => v ≠ x ∧ v ≠ w) =
      (Finset.univ.erase x).erase w := by
    ext v
    simp [and_comm, hxw]
  have hcard : Fintype.card {v : V | v ≠ x ∧ v ≠ w} =
      #((Finset.univ.erase x).erase w) := by
    rw [Fintype.card_subtype]
    exact congrArg Finset.card hfilter
  have hxmem : x ∈ (Finset.univ : Finset V) := Finset.mem_univ _
  have hwmem : w ∈ (Finset.univ.erase x) := by simp [hxw.symm]
  have hxcard := Finset.card_erase_add_one hxmem
  have hwcard := Finset.card_erase_add_one hwmem
  rw [Finset.card_univ] at hxcard
  rw [hcard]
  omega

/-- Literal version of the connected-core consumer.  The double puncture is
defined by deleting the surviving singleton leaf spoke from the full
even-star puncture, so the union identity and edge disjointness are derived
here rather than remaining external assumptions. -/
theorem singleton_odd_star_x_output_of_literal_connected_core
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Set V) [DecidablePred (· ∈ S)] (z : S)
    (x y w : V) (H : AdjacentInstance G x y)
    (hxw : G.Adj x w) (hleaf : ∀ v, G.Adj w v → v = x)
    (hmOdd : Odd (eDegree G x))
    (hsupport : ((evenStarPuncture G x).deleteEdges {s(x, w)}).support ⊆ S)
    (hconn : (((evenStarPuncture G x).deleteEdges {s(x, w)}).induce S).Connected)
    (hcap : ∀ v : S,
      Even ((((evenStarPuncture G x).deleteEdges {s(x, w)}).induce S).degree v) →
      eDegree (((evenStarPuncture G x).deleteEdges {s(x, w)}).induce S) v ≤ 3)
    (hbudget : (Fintype.card S + 1) / 2 + 1 ≤ (Fintype.card V + 1) / 2)
    (hleaves : ∀ v, G.Adj x v → v ≠ w →
      ∃ hvS : v ∈ S,
        Odd ((((evenStarPuncture G x).deleteEdges {s(x, w)}).induce S).degree
          ⟨v, hvS⟩)) :
    ∃ P : Decomposition G, P.size ≤ (Fintype.card V + 1) / 2 ∧
      2 ≤ P.endpointCount x := by
  let Q : SimpleGraph V := evenStarPuncture G x
  let R : SimpleGraph V := Q.deleteEdges {s(x, w)}
  have hxwQ : Q.Adj x w := by
    simpa [Q] using singleton_leaf_spoke_survives_evenStarPuncture G x w hxw hleaf
  have hdis : Disjoint R.edgeSet (SimpleGraph.edge x w).edgeSet := by
    simpa [R] using singleton_delete_edge_disjoint Q x w hxwQ
  have hpuncture : R ⊔ SimpleGraph.edge x w = evenStarPuncture G x := by
    change Q.deleteEdges {s(x, w)} ⊔ SimpleGraph.edge x w = Q
    exact delete_edge_sup_edge Q x w hxwQ
  apply singleton_odd_star_x_output_of_connected_core G R S z x y w H hxw hmOdd
    (by simpa [Q, R] using hsupport)
    (by simpa [Q, R] using hconn)
    (by simpa [Q, R] using hcap)
    hdis hpuncture hbudget
  intro v hv hvw
  simpa [Q, R] using hleaves v hv hvw

/-- Equality-branch native-core wrapper.  Once Xie's literal cut supplies the
connected core and its cardinal budget, all remaining floor-or-SET premises
are now derived internally: support, cap, and odd endpoint supply follow from
the singleton leaf and the degree-one equality at the punctured hub. -/
theorem singleton_odd_star_x_output_of_native_core
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (x y w : V) (H : AdjacentInstance G x y)
    (hxw : G.Adj x w) (hleaf : ∀ v, G.Adj w v → v = x)
    (hmOdd : Odd (eDegree G x))
    (hdegree : (evenStarPuncture G x).degree x = 1)
    (z : {v | v ≠ x ∧ v ≠ w})
    (hconn : (((evenStarPuncture G x).deleteEdges {s(x, w)}).induce
      {v | v ≠ x ∧ v ≠ w}).Connected)
    (hbudget : (Fintype.card {v | v ≠ x ∧ v ≠ w} + 1) / 2 + 1 ≤
      (Fintype.card V + 1) / 2) :
    ∃ P : Decomposition G, P.size ≤ (Fintype.card V + 1) / 2 ∧
      2 ≤ P.endpointCount x := by
  classical
  let S : Set V := {v | v ≠ x ∧ v ≠ w}
  have hsupport : ((evenStarPuncture G x).deleteEdges {s(x, w)}).support ⊆ S := by
    simpa [S] using singleton_literal_double_puncture_support G x w hxw hleaf hdegree
  apply singleton_odd_star_x_output_of_literal_connected_core G S (by simpa [S] using z)
    x y w H hxw hleaf hmOdd hsupport
    (by simpa [S] using hconn)
  · intro v hv
    simpa [S] using singleton_literal_double_core_cap G x y w H hxw hleaf hdegree v
      (by simpa [S] using hv)
  · simpa [S] using hbudget
  · intro v hxv hvw
    let hvS : v ∈ S := ⟨hxv.ne.symm, hvw⟩
    refine ⟨hvS, ?_⟩
    exact singleton_literal_core_leaf_odd G x w S hsupport v hxv hvS hvw

/-- Final equality-branch interface.  The other adjacent exception belongs to
the native core (it cannot be the degree-one cut leaf), so connectedness of
that core supplies the designated SET-reserve vertex. The cardinal payment for
the singleton carrier is universal, leaving no additional numerical premise. -/
theorem singleton_odd_star_x_output_of_native_core_connected
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (x y w : V) (H : AdjacentInstance G x y)
    (hxw : G.Adj x w) (hleaf : ∀ v, G.Adj w v → v = x)
    (hmOdd : Odd (eDegree G x))
    (hdegree : (evenStarPuncture G x).degree x = 1)
    (hconn : (((evenStarPuncture G x).deleteEdges {s(x, w)}).induce
      {v | v ≠ x ∧ v ≠ w}).Connected) :
    ∃ P : Decomposition G, P.size ≤ (Fintype.card V + 1) / 2 ∧
      2 ≤ P.endpointCount x := by
  classical
  have hwy : w ≠ y := singleton_leaf_ne_other_exception G x y w H hxw hleaf
  let z : {v | v ≠ x ∧ v ≠ w} := ⟨y, H.2.1.symm, hwy.symm⟩
  apply singleton_odd_star_x_output_of_native_core G x y w H hxw hleaf hmOdd hdegree z hconn
  exact double_compl_ceiling_add_one_le x w hxw.ne

/-- Xie's equality case is stated using the local degree in the non-singleton
cut piece.  Since deleting the singleton carrier lowers the hub degree by
one, that equality says exactly that the full even-star puncture has one
surviving hub spoke. -/
theorem singleton_evenStar_degree_one_of_cut_equality
    (G : SimpleGraph V) [DecidableRel G.Adj] (x w : V)
    (hxw : G.Adj x w)
    (heq : eDegree G x = (G.deleteEdges {s(x, w)}).degree x) :
    (evenStarPuncture G x).degree x = 1 := by
  have hdelete : (G.deleteEdges {s(x, w)}).degree x + 1 = G.degree x :=
    degree_delete_edge_add_one G x w hxw
  have hpuncture : (evenStarPuncture G x).degree x + eDegree G x = G.degree x :=
    evenStarPuncture_degree_center G x
  omega

/-- Source-facing equality singleton-cut branch. The hypotheses are now the
literal two facts supplied by Xie's cut construction: the native double core
is connected, and the even-star size equals the hub degree on the non-singleton
cut piece. All subsequent reconstruction and budget facts are compiled. -/
theorem singleton_odd_star_x_output_of_singleton_cut_equality
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (x y w : V) (H : AdjacentInstance G x y)
    (hxw : G.Adj x w) (hleaf : ∀ v, G.Adj w v → v = x)
    (hcore : (((evenStarPuncture G x).deleteEdges {s(x, w)}).induce
      {v | v ≠ x ∧ v ≠ w}).Connected)
    (hmOdd : Odd (eDegree G x))
    (heq : eDegree G x = (G.deleteEdges {s(x, w)}).degree x) :
    ∃ P : Decomposition G, P.size ≤ (Fintype.card V + 1) / 2 ∧
      2 ≤ P.endpointCount x := by
  apply singleton_odd_star_x_output_of_native_core_connected G x y w H hxw hleaf hmOdd
    (singleton_evenStar_degree_one_of_cut_equality G x w hxw heq) hcore

/-- A star puncture remains connected across a literal singleton cut leaf
when the double puncture away from the hub and leaf is connected, the leaf
spoke remains, and a second retained hub edge reaches the double puncture. -/
theorem starPuncture_connected_of_singleton_leaf
    (G : SimpleGraph V) [DecidableRel G.Adj] (x w : V) (B : Finset V)
    (hconn : (G.induce {v | v ≠ x ∧ v ≠ w}).Connected)
    (hxw : (starPuncture G x B).Adj x w)
    (hretain : ∃ z, (starPuncture G x B).Adj x z ∧ z ≠ w) :
    (starPuncture G x B).Connected := by
  letI : Nonempty V := ⟨x⟩
  let H : SimpleGraph V := starPuncture G x B
  let S : Set V := {v | v ≠ x ∧ v ≠ w}
  let f : (G.induce S) →g H :=
    { toFun := Subtype.val
      map_rel' := by
        intro a b hab
        refine ⟨hab, ?_⟩
        intro hs
        exact b.property.1 ((star_sup_adj_off_center x B a b a.property.1).mp hs).2 }
  have hr (a b : V) (ha : a ∈ S) (hb : b ∈ S) : H.Reachable a b :=
    (hconn.preconnected ⟨a, ha⟩ ⟨b, hb⟩).map f
  obtain ⟨z, hxz, hzw⟩ := hretain
  have hzx : z ≠ x := hxz.ne.symm
  have hzS : z ∈ S := ⟨hzx, hzw⟩
  have reach (v : V) : H.Reachable x v := by
    by_cases hvx : v = x
    · subst v
      exact SimpleGraph.Reachable.refl _
    by_cases hvw : v = w
    · subst v
      exact hxw.reachable
    exact hxz.reachable.trans (hr z v hzS ⟨hvx, hvw⟩)
  exact ⟨fun a b => (reach a).symm.trans (reach b)⟩

/-- In the strict singleton branch, the retained edge at the hub is not merely
the leaf spoke: after the even-neighbour star is deleted, a second hub edge
survives and reaches the connected double puncture. -/
theorem singleton_even_star_retained_nonleaf_neighbor_of_strict_degree
    (G : SimpleGraph V) [DecidableRel G.Adj] (x w : V) (hxw : G.Adj x w)
    (hleaf : ∀ v, G.Adj w v → v = x)
    (hlt : eDegree G x < (G.deleteEdges {s(x, w)}).degree x) :
    ∃ z, (evenStarPuncture G x).Adj x z ∧ z ≠ w := by
  let J : SimpleGraph V := evenStarPuncture G x
  have hwdegree : G.degree w = 1 := by
    rw [SimpleGraph.degree_eq_one_iff_existsUnique_adj]
    exact ⟨x, hxw.symm, fun v hwv => hleaf v hwv⟩
  have hwodd : Odd (G.degree w) := by
    simpa [hwdegree] using (show Odd 1 from ⟨0, rfl⟩)
  have hwnot : w ∉ evenNeighbors G x := by
    intro hw
    exact (Nat.not_even_iff_odd.mpr hwodd) ((mem_evenNeighbors x w).mp hw).2
  have hxwJ : J.Adj x w := by
    change G.Adj x w ∧ ¬ ((evenNeighbors G x).sup (SimpleGraph.edge x)).Adj x w
    refine ⟨hxw, ?_⟩
    intro hs
    exact hwnot ((star_sup_adj_center x (evenNeighbors G x) (by simp) w).mp hs)
  have hJdeg : 1 < J.degree x := by
    have hdelete : (G.deleteEdges {s(x, w)}).degree x + 1 = G.degree x :=
      degree_delete_edge_add_one G x w hxw
    have hstar : J.degree x + eDegree G x = G.degree x := by
      simpa [J] using evenStarPuncture_degree_center G x
    omega
  by_contra h
  push_neg at h
  have hdeg : J.degree x = 1 := by
    rw [SimpleGraph.degree_eq_one_iff_existsUnique_adj]
    exact ⟨w, hxwJ, fun z hz => h z hz⟩
  omega

/-- Source-faithful strict singleton-cut branch.  The connected graph supplied
by the cut decomposition is the double puncture `G - {x,w}`; the literal leaf
spoke and the strict retained-degree inequality reconnect the full even-star
puncture before the existing endpoint theorem is invoked. -/
theorem singleton_even_star_x_output_of_singleton_cut_strict
    (G : SimpleGraph V) [DecidableRel G.Adj] (x y w : V)
    (H : AdjacentInstance G x y) (hxw : G.Adj x w)
    (hleaf : ∀ v, G.Adj w v → v = x)
    (hcore : (G.induce {v | v ≠ x ∧ v ≠ w}).Connected)
    (hmEven : Even (eDegree G x))
    (hlt : eDegree G x < (G.deleteEdges {s(x, w)}).degree x) :
    ∃ P : Decomposition G, P.size ≤ (Fintype.card V + 1) / 2 ∧
      2 ≤ P.endpointCount x := by
  let J : SimpleGraph V := evenStarPuncture G x
  have hwdegree : G.degree w = 1 := by
    rw [SimpleGraph.degree_eq_one_iff_existsUnique_adj]
    exact ⟨x, hxw.symm, fun v hwv => hleaf v hwv⟩
  have hwodd : Odd (G.degree w) := by
    simpa [hwdegree] using (show Odd 1 from ⟨0, rfl⟩)
  have hwnot : w ∉ evenNeighbors G x := by
    intro hw
    exact (Nat.not_even_iff_odd.mpr hwodd) ((mem_evenNeighbors x w).mp hw).2
  have hxwJ : J.Adj x w := by
    change G.Adj x w ∧ ¬ ((evenNeighbors G x).sup (SimpleGraph.edge x)).Adj x w
    refine ⟨hxw, ?_⟩
    intro hs
    exact hwnot ((star_sup_adj_center x (evenNeighbors G x) (by simp) w).mp hs)
  obtain ⟨z, hxz, hzw⟩ :=
    singleton_even_star_retained_nonleaf_neighbor_of_strict_degree G x w hxw hleaf hlt
  have hconn : J.Connected := by
    simpa [J] using starPuncture_connected_of_singleton_leaf G x w
      (evenNeighbors G x) hcore hxwJ ⟨z, hxz, hzw⟩
  have hxpos : 0 < J.degree x :=
    (J.degree_pos_iff_exists_adj x).mpr ⟨z, hxz⟩
  exact singleton_even_star_x_output G x y H (by simpa [J] using hconn)
    hmEven (by simpa [J] using hxpos)

/-- The correct typed interface for the singleton-cut `y` output.  The
one-exception theorem runs on the connected induced graph with the isolated
leaf `w` removed, and the resulting decomposition is lifted back before
reattaching `xw`.  Degree/cap transport into that induced graph remains an
explicit source obligation. -/
theorem singleton_leaf_y_output_of_induced_endpoint
    (G : SimpleGraph V) [DecidableRel G.Adj] (x y w : V)
    (H : AdjacentInstance G x y) (hxw : G.Adj x w) (hwy : w ≠ y)
    (hleaf : ∀ v, G.Adj w v → v = x)
    (hconn : ((G.deleteEdges {s(x, w)}).induce {v | v ≠ w}).Connected)
    (hypos : 0 < ((G.deleteEdges {s(x, w)}).induce {v | v ≠ w}).degree ⟨y, hwy.symm⟩)
    (hyEven : Even (((G.deleteEdges {s(x, w)}).induce {v | v ≠ w}).degree ⟨y, hwy.symm⟩))
    (hcap : ∀ v, Even (((G.deleteEdges {s(x, w)}).induce {v | v ≠ w}).degree v) →
      v ≠ ⟨y, hwy.symm⟩ → eDegree ((G.deleteEdges {s(x, w)}).induce {v | v ≠ w}) v ≤ 3)
    (hxodd : Odd (((G.deleteEdges {s(x, w)}).induce {v | v ≠ w}).degree ⟨x, hxw.ne⟩)) :
    ∃ E : Decomposition G, E.size ≤ (Fintype.card V + 1) / 2 ∧
      2 ≤ E.endpointCount y := by
  let S : Set V := {v | v ≠ w}
  let I : SimpleGraph V := G.deleteEdges {s(x, w)}
  let J : SimpleGraph S := I.induce S
  have hwyS : y ∈ S := hwy.symm
  have hxwS : x ∈ S := hxw.ne
  have hconnJ : J.Connected := by simpa [I, J, S] using hconn
  have hyposJ : 0 < J.degree ⟨y, hwyS⟩ := by simpa [I, J, S] using hypos
  have hyEvenJ : Even (J.degree ⟨y, hwyS⟩) := by simpa [I, J, S] using hyEven
  have hcapJ : ∀ v, Even (J.degree v) → v ≠ ⟨y, hwyS⟩ → eDegree J v ≤ 3 := by
    simpa [I, J, S] using hcap
  obtain ⟨D, hDsize, hDy⟩ := one_exception_endpoint J ⟨y, hwyS⟩
    hconnJ hyposJ hyEvenJ hcapJ
  have hxoddJ : Odd (J.degree ⟨x, hxwS⟩) := by simpa [I, J, S] using hxodd
  have hDx : 0 < D.endpointCount ⟨x, hxwS⟩ :=
    D.endpointCount_pos_of_odd_degree ⟨x, hxwS⟩ hxoddJ
  obtain ⟨i, hi⟩ := D.exists_terminal_of_pos ⟨x, hxwS⟩ hDx
  have hIisolated : ∀ v, ¬ I.Adj w v := by
    simpa [I] using singleton_leaf_deleted_edge_isolated G x w hxw hleaf
  have hsupp : I.support ⊆ S := by
    intro v hv hvw
    obtain ⟨q, hvq⟩ := hv
    exact hIisolated q (hvw ▸ hvq)
  have hgraph : (I.induce S).map (Function.Embedding.subtype _) = I :=
    (I.spanningCoe_induce_eq_self S).mpr hsupp
  let E0 : Decomposition ((I.induce S).map (Function.Embedding.subtype _)) :=
    D.map (Function.Embedding.subtype _)
  let E1 : Decomposition I := hgraph ▸ E0
  have castSize {A B : SimpleGraph V} (q : A = B) (P : Decomposition A) :
      (q ▸ P).size = P.size := by subst B; rfl
  have castEnds {A B : SimpleGraph V} (q : A = B) (P : Decomposition A) (v : V) :
      (q ▸ P).endpointCount v = P.endpointCount v := by subst B; rfl
  have castTerminal {A B : SimpleGraph V} (q : A = B) (P : Decomposition A)
      (j : Fin P.size) (a : V)
      (hj : (P.path j).start = a ∨ (P.path j).finish = a) :
      (((q ▸ P).path (Fin.cast (castSize q P).symm j)).start = a ∨
        ((q ▸ P).path (Fin.cast (castSize q P).symm j)).finish = a) := by
    subst B
    simpa using hj
  have hE0term : (E0.path i).start = x ∨ (E0.path i).finish = x := by
    rcases hi with hi | hi
    · left
      change (D.path i).start.val = x
      simpa [hi]
    · right
      change (D.path i).finish.val = x
      simpa [hi]
  have hE1size : E1.size = D.size := by
    rw [show E1.size = E0.size by exact castSize hgraph E0]
    simp [E0]
  have hE1y : E1.endpointCount y = D.endpointCount ⟨y, hwyS⟩ := by
    rw [show E1.endpointCount y = E0.endpointCount y by exact castEnds hgraph E0 y]
    simpa [E0] using D.map_endpointCount (Function.Embedding.subtype _) ⟨y, hwyS⟩
  let i1 : Fin E1.size := Fin.cast (castSize hgraph E0).symm i
  have hE1term : (E1.path i1).start = x ∨ (E1.path i1).finish = x := by
    exact castTerminal hgraph E0 i x hE0term
  have hgraphI : I ⊔ SimpleGraph.edge x w = G := by
    simpa [I] using delete_edge_sup_edge G x w hxw
  have hmissing : ¬ I.Adj w x := hIisolated x
  have hwi : w ∉ (E1.path i1).walk.support :=
    (E1.path i1).notMem_support_of_isolated w hIisolated
  obtain ⟨E0', hE0'size, hE0'ends⟩ :=
    E1.exists_add_of_avoiding_endpoint i1 w x hE1term hwi hmissing
  have hgraph' : I ⊔ SimpleGraph.edge w x = G := by
    simpa only [SimpleGraph.edge_comm] using hgraphI
  let E : Decomposition G := hgraph' ▸ E0'
  have hEsize : E.size = E1.size := by
    calc
      E.size = E0'.size := castSize hgraph' E0'
      _ = E1.size := hE0'size
  have hEy : E.endpointCount y = E1.endpointCount y := by
    calc
      E.endpointCount y = E0'.endpointCount y := castEnds hgraph' E0' y
      _ = E1.endpointCount y := by simpa [H.2.1, hwy] using hE0'ends y
  refine ⟨E, ?_, ?_⟩
  · rw [hEsize, hE1size]
    have hcard : Fintype.card S ≤ Fintype.card V :=
      Fintype.card_le_of_injective (Function.Embedding.subtype S)
        (Function.Embedding.subtype S).injective
    omega
  · rw [hEy, hE1y]
    exact hDy

/-- Literal singleton-leaf geometry supplies every input to the induced
one-exception reconstruction.  The connectedness hypothesis is on `G - w`,
the nontrivial cut piece, rather than on the disconnected edge deletion
`G - xw`. -/
theorem singleton_leaf_y_output_of_leaf_geometry
    (G : SimpleGraph V) [DecidableRel G.Adj] (x y w : V)
    (H : AdjacentInstance G x y) (hxw : G.Adj x w) (hwy : w ≠ y)
    (hleaf : ∀ v, G.Adj w v → v = x) :
    ∃ E : Decomposition G, E.size ≤ (Fintype.card V + 1) / 2 ∧
      2 ≤ E.endpointCount y := by
  let S : Set V := {v | v ≠ w}
  let I : SimpleGraph V := G.deleteEdges {s(x, w)}
  have hconn : (G.induce S).Connected := by
    simpa [S] using singleton_leaf_induce_delete_leaf_connected G x w H.1 hxw hleaf
  have hwyS : y ∈ S := hwy.symm
  have hxwS : x ∈ S := hxw.ne
  have hIisolated : ∀ v, ¬ I.Adj w v := by
    simpa [I] using singleton_leaf_deleted_edge_isolated G x w hxw hleaf
  have hsupp : I.support ⊆ S := by
    intro v hv hvw
    obtain ⟨q, hvq⟩ := hv
    exact hIisolated q (hvw ▸ hvq)
  have hInduce : I.induce S = G.induce S := by
    simpa [I, S, Sym2.eq_swap] using
      (induce_puncture_eq_of_notMem (G := G) w x {v | v ≠ w} (by simp))
  have hconnI : (I.induce S).Connected := by
    rw [hInduce]
    simpa [S] using hconn
  have hIyadj : I.Adj y x := by
    apply SimpleGraph.deleteEdges_adj.mpr
    refine ⟨H.2.2.1.symm, ?_⟩
    intro he
    rcases Sym2.eq_iff.mp he with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact H.2.1 h1.symm
    · exact hwy h1.symm
  have hIypos : 0 < I.degree y :=
    (I.degree_pos_iff_exists_adj y).mpr ⟨x, hIyadj⟩
  have hIyd : I.degree y = G.degree y := by
    simpa [I] using degree_delete_edge_of_ne G x w y H.2.1.symm hwy.symm
  have hIxodd : Odd (I.degree x) := by
    have hdx : I.degree x + 1 = G.degree x := by
      simpa [I] using degree_delete_edge_add_one G x w hxw
    rcases H.2.2.2.1 with ⟨q, hq⟩
    exact ⟨q - 1, by omega⟩
  have hypos : 0 < (I.induce S).degree ⟨y, hwyS⟩ := by
    rw [SimpleGraph.degree_induce_of_support_subset hsupp]
    exact hIypos
  have hyEven : Even ((I.induce S).degree ⟨y, hwyS⟩) := by
    rw [SimpleGraph.degree_induce_of_support_subset hsupp, hIyd]
    exact H.2.2.2.2.1
  have hxodd : Odd ((I.induce S).degree ⟨x, hxwS⟩) := by
    rw [SimpleGraph.degree_induce_of_support_subset hsupp]
    exact hIxodd
  have hcapI := singleton_leaf_puncture_cap G x y w H hxw hwy hleaf
  have hcap : ∀ v, Even ((I.induce S).degree v) →
      v ≠ ⟨y, hwyS⟩ → eDegree (I.induce S) v ≤ 3 := by
    intro v hv hvy
    rw [eDegree_induce_of_support_subset I S hsupp v]
    apply hcapI v.val ?_ (fun h => hvy (Subtype.ext h))
    rwa [SimpleGraph.degree_induce_of_support_subset hsupp v] at hv
  exact singleton_leaf_y_output_of_induced_endpoint G x y w H hxw hwy hleaf
    hconnI hypos hyEven hcap hxodd

/-- The isolated-edge puncture in Xie's singleton branch has the required
one-exception decomposition at `y`, together with an actual terminal carrier
at the newly odd shared hub.  The explicit connectedness premise is the
source's choice of the non-singleton cut piece. -/
theorem singleton_leaf_puncture_y_certificate
    (G : SimpleGraph V) [DecidableRel G.Adj] (x y w : V)
    (H : AdjacentInstance G x y) (hxw : G.Adj x w) (hwy : w ≠ y)
    (hleaf : ∀ v, G.Adj w v → v = x)
    (hconn : (G.deleteEdges {s(x, w)}).Connected) :
    ∃ D : Decomposition (G.deleteEdges {s(x, w)}),
      D.size ≤ (Fintype.card V + 1) / 2 ∧ 2 ≤ D.endpointCount y ∧
        ∃ i : Fin D.size,
          ((D.path i).start = x ∨ (D.path i).finish = x) ∧
            w ∉ (D.path i).walk.support := by
  let I := G.deleteEdges {s(x, w)}
  have hxy : x ≠ y := H.2.1
  have hwx : w ≠ x := hxw.ne.symm
  have hdx : I.degree x + 1 = G.degree x := by
    simpa [I] using degree_delete_edge_add_one G x w hxw
  have hxodd : Odd (I.degree x) := by
    rcases H.2.2.2.1 with ⟨q, hq⟩
    exact ⟨q - 1, by omega⟩
  have hdy : I.degree y = G.degree y := by
    simpa [I] using degree_delete_edge_of_ne G x w y hxy.symm hwy.symm
  have hypos : 0 < I.degree y := by
    apply (I.degree_pos_iff_exists_adj y).mpr
    refine ⟨x, ?_⟩
    apply SimpleGraph.deleteEdges_adj.mpr
    refine ⟨H.2.2.1.symm, ?_⟩
    intro he
    rcases Sym2.eq_iff.mp he with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact hxy h1.symm
    · exact hwy h1.symm
  have hyEven : Even (I.degree y) := by
    rw [hdy]
    exact H.2.2.2.2.1
  obtain ⟨D, hDsize, hDy⟩ := one_exception_endpoint I y (by simpa [I] using hconn)
    hypos hyEven (by
      simpa [I] using singleton_leaf_puncture_cap G x y w H hxw hwy hleaf)
  have hDx : 0 < D.endpointCount x :=
    D.endpointCount_pos_of_odd_degree x (by simpa [I] using hxodd)
  obtain ⟨i, hi⟩ := D.exists_terminal_of_pos x hDx
  have hIisolated : ∀ v, ¬ I.Adj w v := by
    intro v hwv
    have hwvG : G.Adj w v := (SimpleGraph.deleteEdges_adj.mp hwv).1
    have hvx : v = x := hleaf v hwvG
    subst v
    exact (SimpleGraph.deleteEdges_adj.mp hwv).2 (by simp [Sym2.eq_swap])
  refine ⟨D, hDsize, hDy, i, hi, ?_⟩
  exact (D.path i).notMem_support_of_isolated w hIisolated

/-- Reattaching a deleted isolated leaf edge to an `x`-terminal carrier does
not change the path count or the endpoint multiplicity at a third vertex.
This is the complete reconstruction used for the `y` output of the
singleton-edge hub-cut branch; the hypotheses are stated on the actual
puncture decomposition. -/
theorem restore_isolated_single_edge_preserves_other_endpoint
    (I G : SimpleGraph V) [DecidableRel I.Adj]
    (x w y : V) (D : Decomposition I) (i : Fin D.size)
    (hgraph : I ⊔ SimpleGraph.edge x w = G)
    (hx : (D.path i).start = x ∨ (D.path i).finish = x)
    (hw : w ∉ (D.path i).walk.support)
    (hmissing : ¬ I.Adj w x)
    (hxy : x ≠ y) (hwy : w ≠ y) :
    ∃ E : Decomposition G, E.size = D.size ∧
      E.endpointCount y = D.endpointCount y := by
  have hgraph' : I ⊔ SimpleGraph.edge w x = G := by
    simpa only [SimpleGraph.edge_comm] using hgraph
  obtain ⟨E0, hsE0, heE0⟩ :=
    D.exists_add_of_avoiding_endpoint i w x hx hw hmissing
  let E : Decomposition G := hgraph' ▸ E0
  have castSize {L M : SimpleGraph V} (q : L = M)
      (P : Decomposition L) : (q ▸ P).size = P.size := by
    subst M
    rfl
  have castEnds {L M : SimpleGraph V} (q : L = M)
      (P : Decomposition L) (v : V) :
      (q ▸ P).endpointCount v = P.endpointCount v := by
    subst M
    rfl
  refine ⟨E, ?_, ?_⟩
  · rw [show E.size = E0.size by exact castSize hgraph' E0]
    exact hsE0
  · rw [show E.endpointCount y = E0.endpointCount y by
      exact castEnds hgraph' E0 y]
    simpa [hxy, hwy] using heE0 y

/-- The source's complete `y`-output in the singleton cut-piece branch.
The one-exception decomposition of the connected puncture supplies the
terminal carrier; reattaching the isolated leaf preserves the endpoint
reserve at `y`. -/
theorem singleton_leaf_y_output
    (G : SimpleGraph V) [DecidableRel G.Adj] (x y w : V)
    (H : AdjacentInstance G x y) (hxw : G.Adj x w) (hwy : w ≠ y)
    (hleaf : ∀ v, G.Adj w v → v = x)
    (hconn : (G.deleteEdges {s(x, w)}).Connected) :
    ∃ E : Decomposition G, E.size ≤ (Fintype.card V + 1) / 2 ∧
      2 ≤ E.endpointCount y := by
  let I := G.deleteEdges {s(x, w)}
  have hxy : x ≠ y := H.2.1
  obtain ⟨D, hDsize, hDy, i, hi, hwi⟩ :=
    singleton_leaf_puncture_y_certificate G x y w H hxw hwy hleaf hconn
  have hgraph : I ⊔ SimpleGraph.edge x w = G := by
    simpa [I] using delete_edge_sup_edge G x w hxw
  have hmissing : ¬ I.Adj w x := by
    intro h
    exact (SimpleGraph.deleteEdges_adj.mp h).2 (by simp [Sym2.eq_swap])
  obtain ⟨E, hEsize, hEy⟩ :=
    restore_isolated_single_edge_preserves_other_endpoint I G x w y D i hgraph
      hi hwi hmissing hxy hwy
  refine ⟨E, ?_, ?_⟩
  · rw [hEsize]
    exact hDsize
  · rw [hEy]
    exact hDy

/-- The singleton-edge branch closes an adjacent minimal counterexample as
soon as its two source puncture certificates are supplied: the odd-star
puncture gives the `x` output and the isolated-edge puncture gives the `y`
output.  This keeps the two reconstructions separate, as in Xie's proof. -/
theorem singleton_edge_two_output_not_minimal
    (G I : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel I.Adj]
    (x y w : V) (M : AdjacentCounterexample G x y)
    (S : Finset V) (hxy : x ≠ y) (hyS : y ∉ S)
    (hS : S ⊆ evenNeighbors G x) (hodd : Odd #S)
    (hleaves : ∀ v ∈ S, #((evenNeighbors G v).erase x) ≤ 2)
    (DX : Decomposition (starPuncture G x S))
    (hDXsize : DX.size ≤ (Fintype.card V + 1) / 2)
    (hxDX : 0 < DX.endpointCount x)
    (hneighbors : ∀ v, G.Adj x v → 0 < DX.endpointCount v)
    (DY : Decomposition I) (i : Fin DY.size)
    (hgraph : I ⊔ SimpleGraph.edge x w = G)
    (hxDY : (DY.path i).start = x ∨ (DY.path i).finish = x)
    (hwDY : w ∉ (DY.path i).walk.support)
    (hmissing : ¬ I.Adj w x) (hwy : w ≠ y)
    (hDYsize : DY.size ≤ (Fintype.card V + 1) / 2)
    (hyDY : 2 ≤ DY.endpointCount y) : False := by
  obtain ⟨PX, hsPX, hxPX, _⟩ :=
    xie_adjacent_odd_puncture_endgame x y S hxy hyS hS hodd hleaves DX hxDX hneighbors
  obtain ⟨PY, hsPY, hyPY⟩ :=
    restore_isolated_single_edge_preserves_other_endpoint I G x w y DY i hgraph
      hxDY hwDY hmissing hxy hwy
  apply M.2
  refine ⟨⟨PX, ?_, hxPX⟩, ⟨PY, ?_, ?_⟩⟩
  · rw [hsPX]
    exact hDXsize
  · rw [hsPY]
    exact hDYsize
  · rw [hyPY]
    exact hyDY

/-- The singleton cut-piece branch contradicts adjacent minimality once the
source's independent odd-star puncture certificate for the `x` output is
available.  Unlike the preceding generic consumer, the `y` output is derived
here from the literal leaf-edge geometry and the one-exception theorem. -/
theorem singleton_leaf_two_output_not_minimal
    (G : SimpleGraph V) [DecidableRel G.Adj] (x y w : V)
    (M : AdjacentCounterexample G x y) (hxw : G.Adj x w) (hwy : w ≠ y)
    (hleaf : ∀ v, G.Adj w v → v = x)
    (S : Finset V) (hyS : y ∉ S)
    (hS : S ⊆ evenNeighbors G x) (hodd : Odd #S)
    (hleaves : ∀ v ∈ S, #((evenNeighbors G v).erase x) ≤ 2)
    (DX : Decomposition (starPuncture G x S))
    (hDXsize : DX.size ≤ (Fintype.card V + 1) / 2)
    (hxDX : 0 < DX.endpointCount x)
    (hneighbors : ∀ v, G.Adj x v → 0 < DX.endpointCount v) : False := by
  have H := M.1
  have hxy : x ≠ y := H.2.1
  obtain ⟨PX, hsPX, hxPX, _⟩ :=
    xie_adjacent_odd_puncture_endgame x y S hxy hyS hS hodd hleaves DX hxDX hneighbors
  obtain ⟨PY, hsPY, hyPY⟩ :=
    singleton_leaf_y_output_of_leaf_geometry G x y w H hxw hwy hleaf
  apply M.2
  refine ⟨⟨PX, ?_, hxPX⟩, ⟨PY, hsPY, hyPY⟩⟩
  rw [hsPX]
  exact hDXsize

/-- The even full-star singleton branch contradicts adjacent minimality once
the literal source punctures are connected.  Its x- and y-endpoint outputs
are intentionally assembled as two separate decompositions. -/
theorem singleton_leaf_even_star_two_output_not_minimal
    (G : SimpleGraph V) [DecidableRel G.Adj] (x y w : V)
    (M : AdjacentCounterexample G x y) (hxw : G.Adj x w) (hwy : w ≠ y)
    (hleaf : ∀ v, G.Adj w v → v = x)
    (hcut : ((G.deleteEdges {s(x, w)}).induce {v | v ≠ x}).Connected)
    (hmEven : Even (eDegree G x))
    (hlt : eDegree G x < (G.deleteEdges {s(x, w)}).degree x) : False := by
  have H := M.1
  obtain ⟨PX, hPXsize, hPX⟩ :=
    singleton_even_star_x_output_of_leaf_geometry G x y w H hxw hcut hmEven hlt
  obtain ⟨PY, hPYsize, hPY⟩ :=
    singleton_leaf_y_output_of_leaf_geometry G x y w H hxw hwy hleaf
  apply M.2
  exact ⟨⟨PX, hPXsize, hPX⟩, ⟨PY, hPYsize, hPY⟩⟩

/-- The odd full-star singleton branch has the same two-output assembly.  In
this parity the retained-neighbour inequality is unnecessary: odd full-star
deletion itself supplies an unselected edge at the hub. -/
theorem singleton_leaf_odd_star_two_output_not_minimal
    (G : SimpleGraph V) [DecidableRel G.Adj] (x y w : V)
    (M : AdjacentCounterexample G x y) (hxw : G.Adj x w) (hwy : w ≠ y)
    (hleaf : ∀ v, G.Adj w v → v = x)
    (hcut : ((G.deleteEdges {s(x, w)}).induce {v | v ≠ x}).Connected)
    (hmOdd : Odd (eDegree G x)) : False := by
  have H := M.1
  have hdelete : (G.induce {v | v ≠ x}).Connected := by
    rw [← singleton_delete_leaf_induce_delete_hub_eq G x w]
    exact hcut
  obtain ⟨PX, hPXsize, hPX⟩ :=
    singleton_odd_star_x_output_of_delete_vertex_connected G x y H hdelete hmOdd
  obtain ⟨PY, hPYsize, hPY⟩ :=
    singleton_leaf_y_output_of_leaf_geometry G x y w H hxw hwy hleaf
  apply M.2
  exact ⟨⟨PX, hPXsize, hPX⟩, ⟨PY, hPYsize, hPY⟩⟩

/-- The equality alternative in Xie's singleton odd/odd hub-cut branch has
the same independent-output contradiction as the strict alternative.  Here
the `x` output is supplied by the connected double puncture: equality leaves
exactly the singleton leaf spoke after the full even-neighbour star is
deleted. -/
theorem singleton_leaf_odd_star_equality_two_output_not_minimal
    (G : SimpleGraph V) [DecidableRel G.Adj] (x y w : V)
    (M : AdjacentCounterexample G x y) (hxw : G.Adj x w)
    (hleaf : ∀ v, G.Adj w v → v = x)
    (hcore : (((evenStarPuncture G x).deleteEdges {s(x, w)}).induce
      {v | v ≠ x ∧ v ≠ w}).Connected)
    (hmOdd : Odd (eDegree G x))
    (heq : eDegree G x = (G.deleteEdges {s(x, w)}).degree x) : False := by
  have H := M.1
  have hwy : w ≠ y := singleton_leaf_ne_other_exception G x y w H hxw hleaf
  obtain ⟨PX, hPXsize, hPX⟩ :=
    singleton_odd_star_x_output_of_singleton_cut_equality G x y w H hxw hleaf
      hcore hmOdd heq
  obtain ⟨PY, hPYsize, hPY⟩ :=
    singleton_leaf_y_output_of_leaf_geometry G x y w H hxw hwy hleaf
  apply M.2
  exact ⟨⟨PX, hPXsize, hPX⟩, ⟨PY, hPYsize, hPY⟩⟩

/-- In a cut partition whose opposite piece is the singleton edge `xw`, the
selected side with the hub removed is exactly the double complement of
`x,w`.  This is the set-level source transport for Xie's equality branch. -/
theorem singleton_cut_core_set_eq (S T : Set V) (x w : V)
    (hcover : S ∪ T = Set.univ) (hinter : S ∩ T = {x})
    (hT : T = {x, w}) :
    {v | v ∈ S ∧ v ≠ x} = {v | v ≠ x ∧ v ≠ w} := by
  ext v
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨hvS, hvx⟩
    refine ⟨hvx, ?_⟩
    intro hvw
    have hvT : v ∈ T := by
      rw [hT]
      simp [hvw]
    have hvI : v ∈ S ∩ T := ⟨hvS, hvT⟩
    have hvx' : v = x := by
      have : v ∈ ({x} : Set V) := hinter ▸ hvI
      simpa using this
    exact hvx hvx'
  · rintro ⟨hvx, hvw⟩
    refine ⟨?_, hvx⟩
    have hvall : v ∈ S ∪ T := by
      rw [hcover]
      exact Set.mem_univ v
    rcases hvall with hvS | hvT
    · exact hvS
    · rw [hT] at hvT
      rcases hvT with hvx' | hvw'
      · exact (hvx hvx').elim
      · exact (hvw hvw').elim

/-- The literal double puncture used in the singleton equality branch induces
exactly the original graph after both the hub and its singleton opposite leaf
are discarded.  The full-star deletion and the reserved leaf deletion are
therefore invisible on this core. -/
theorem singleton_literal_double_puncture_induce_eq
    (G : SimpleGraph V) [DecidableRel G.Adj] (x w : V) :
    (((evenStarPuncture G x).deleteEdges {s(x, w)}).induce
      {v | v ≠ x ∧ v ≠ w}) =
      G.induce {v | v ≠ x ∧ v ≠ w} := by
  rw [induce_puncture_eq_of_notMem (G := evenStarPuncture G x) x w
    {v | v ≠ x ∧ v ≠ w} (by simp)]
  exact induce_evenStarPuncture_eq_of_notMem G x {v | v ≠ x ∧ v ≠ w} (by simp)

/-- Connectedness of the selected source cut piece after discarding its hub
transports to the literal double puncture in the equality reconstruction.
The graph equality is independent of parity; all star and reserved-edge
deletions vanish after `x,w` are removed. -/
theorem singleton_literal_core_connected_of_cut_piece
    (G : SimpleGraph V) [DecidableRel G.Adj] (S T : Set V) (x w : V)
    (hcover : S ∪ T = Set.univ) (hinter : S ∩ T = {x})
    (hT : T = {x, w})
    (hconn : (G.induce {v | v ∈ S ∧ v ≠ x}).Connected) :
    (((evenStarPuncture G x).deleteEdges {s(x, w)}).induce
      {v | v ≠ x ∧ v ≠ w}).Connected := by
  rw [singleton_literal_double_puncture_induce_eq]
  rw [← singleton_cut_core_set_eq S T x w hcover hinter hT]
  exact hconn

/-- In a literal singleton cut partition, the source degree of the hub on its
selected piece is its degree after deleting the unique opposite carrier
`xw`.  This translates Xie's local equality into the equality consumed by
the double-puncture reconstruction. -/
theorem singleton_cut_piece_degree_eq_delete_edge
    (G : SimpleGraph V) [DecidableRel G.Adj] (S T : Set V)
    [DecidablePred (· ∈ S)] (x w : V)
    (hxw : G.Adj x w)
    (hcover : S ∪ T = Set.univ) (hinter : S ∩ T = {x})
    (hT : T = {x, w}) :
    (G.induce S).degree ⟨x, by
      have hxI : x ∈ S ∩ T := by rw [hinter]; simp
      exact hxI.1⟩ = (G.deleteEdges {s(x, w)}).degree x := by
  classical
  let H : SimpleGraph V := G.deleteEdges {s(x, w)}
  have hxS : x ∈ S := by
    have hxI : x ∈ S ∩ T := by rw [hinter]; simp
    exact hxI.1
  have hwS : w ∉ S := by
    intro hwS
    have hwT : w ∈ T := by rw [hT]; simp
    have hwI : w ∈ S ∩ T := ⟨hwS, hwT⟩
    have hwx : w = x := by
      have : w ∈ ({x} : Set V) := hinter ▸ hwI
      simpa using this
    exact hxw.ne hwx.symm
  have hclosed : H.neighborSet x ⊆ S := by
    intro v hv
    change H.Adj x v at hv
    have hvall : v ∈ S ∪ T := by
      rw [hcover]
      exact Set.mem_univ v
    rcases hvall with hvS | hvT
    · exact hvS
    · rw [hT] at hvT
      rcases hvT with hvx | hvw
      · subst v
        exact (H.irrefl hv).elim
      · subst v
        exact ((SimpleGraph.deleteEdges_adj.mp hv).2 rfl).elim
  have hInduce : H.induce S = G.induce S := by
    simpa [H, Sym2.eq_swap] using
      (induce_puncture_eq_of_notMem (G := G) w x S hwS)
  have hdegree : (H.induce S).degree ⟨x, hxS⟩ = H.degree x :=
    SimpleGraph.degree_induce_of_neighborSet_subset hclosed
  have hdegreeInd : (G.induce S).degree ⟨x, hxS⟩ =
      (H.induce S).degree ⟨x, hxS⟩ := by
    rw [← SimpleGraph.card_neighborFinset_eq_degree,
      ← SimpleGraph.card_neighborFinset_eq_degree]
    congr 1
    ext v
    simp only [SimpleGraph.mem_neighborFinset]
    rw [hInduce]
  simpa [H] using hdegreeInd.trans hdegree

/-- The local equality in a singleton source cut, stated on the punctured
selected piece, is the deleted-edge equality used by the all-star consumer. -/
theorem singleton_cut_piece_equality_to_delete_edge
    (G : SimpleGraph V) [DecidableRel G.Adj] (S T : Set V)
    [DecidablePred (· ∈ S)] (x w : V)
    (hxw : G.Adj x w)
    (hcover : S ∪ T = Set.univ) (hinter : S ∩ T = {x})
    (hT : T = {x, w})
    (heq : eDegree G x =
      (G.induce S).degree ⟨x, by
        have hxI : x ∈ S ∩ T := by rw [hinter]; simp
        exact hxI.1⟩) :
    eDegree G x = (G.deleteEdges {s(x, w)}).degree x :=
  heq.trans (singleton_cut_piece_degree_eq_delete_edge G S T x w hxw hcover hinter hT)

/-- Complete source-facing equality branch for a literal singleton cut side.
The selected piece provides the two source facts—connectedness after removing
the hub and local degree equality—and the preceding transport theorems turn
them into the exact inputs of the compiled reconstruction contradiction. -/
theorem singleton_leaf_odd_star_equality_cut_piece_not_minimal
    (G : SimpleGraph V) [DecidableRel G.Adj] (x y w : V)
    (M : AdjacentCounterexample G x y) (hxw : G.Adj x w)
    (hleaf : ∀ v, G.Adj w v → v = x)
    (S T : Set V) [DecidablePred (· ∈ S)]
    (hcover : S ∪ T = Set.univ) (hinter : S ∩ T = {x})
    (hT : T = {x, w})
    (hconn : (G.induce {v | v ∈ S ∧ v ≠ x}).Connected)
    (hmOdd : Odd (eDegree G x))
    (heq : eDegree G x =
      (G.induce S).degree ⟨x, by
        have hxI : x ∈ S ∩ T := by rw [hinter]; simp
        exact hxI.1⟩) : False := by
  apply singleton_leaf_odd_star_equality_two_output_not_minimal G x y w M hxw hleaf
  · exact singleton_literal_core_connected_of_cut_piece G S T x w hcover hinter hT hconn
  · exact hmOdd
  · exact singleton_cut_piece_equality_to_delete_edge G S T x w hxw hcover hinter hT heq

/-- In a literal cut partition whose opposite side is just `xw`, the vertex
`w` is a genuine degree-one leaf.  The graph-union clause rules out any edge
from `w` into the selected side; the singleton side then leaves only `x`.
This removes the leaf hypothesis from the source-facing strict branch. -/
theorem singleton_leaf_of_cut_partition
    (G : SimpleGraph V) [DecidableRel G.Adj] (S T : Set V)
    (x w : V) (hxw : G.Adj x w)
    (hinter : S ∩ T = {x}) (hT : T = {x, w})
    (hgraph : (G.induce S).spanningCoe ⊔ (G.induce T).spanningCoe = G) :
    ∀ v, G.Adj w v → v = x := by
  intro v hwv
  have hwT : w ∈ T := by rw [hT]; simp
  have hwS : w ∉ S := by
    intro hws
    have hwI : w ∈ S ∩ T := ⟨hws, hwT⟩
    have hwx : w = x := by
      have : w ∈ ({x} : Set V) := hinter ▸ hwI
      simpa using this
    exact hxw.ne hwx.symm
  rw [← hgraph] at hwv
  rcases hwv with hS | hTadj
  · exact (hwS ((spanning_induce_adj_iff G S w v).mp hS).2.1).elim
  · obtain ⟨hGwv, _, hvT⟩ := (spanning_induce_adj_iff G T w v).mp hTadj
    rw [hT] at hvT
    rcases hvT with hvx | hvw
    · simpa using hvx
    · have hvw' : v = w := by simpa using hvw
      exact (G.irrefl (hvw' ▸ hGwv)).elim

/-- Complete source-facing strict alternative for the singleton opposite
cut piece.  Its connected selected core and local strict degree inequality
are translated to the exact all-star reconstruction inputs; the leaf property
is derived from the literal graph partition itself. -/
theorem singleton_leaf_even_star_strict_cut_piece_not_minimal
    (G : SimpleGraph V) [DecidableRel G.Adj] (x y w : V)
    (M : AdjacentCounterexample G x y) (hxw : G.Adj x w)
    (S T : Set V) [DecidablePred (· ∈ S)]
    (hcover : S ∪ T = Set.univ) (hinter : S ∩ T = {x})
    (hT : T = {x, w})
    (hgraph : (G.induce S).spanningCoe ⊔ (G.induce T).spanningCoe = G)
    (hconn : (G.induce {v | v ∈ S ∧ v ≠ x}).Connected)
    (hmEven : Even (eDegree G x))
    (hlt : eDegree G x <
      (G.induce S).degree ⟨x, by
        have hxI : x ∈ S ∩ T := by rw [hinter]; simp
        exact hxI.1⟩) : False := by
  have H := M.1
  have hleaf : ∀ v, G.Adj w v → v = x :=
    singleton_leaf_of_cut_partition G S T x w hxw hinter hT hgraph
  have hwy : w ≠ y := singleton_leaf_ne_other_exception G x y w H hxw hleaf
  have hcore : (G.induce {v | v ≠ x ∧ v ≠ w}).Connected := by
    rw [← singleton_cut_core_set_eq S T x w hcover hinter hT]
    exact hconn
  have hlt' : eDegree G x < (G.deleteEdges {s(x, w)}).degree x := by
    rw [← singleton_cut_piece_degree_eq_delete_edge G S T x w hxw hcover hinter hT]
    exact hlt
  obtain ⟨PX, hPXsize, hPX⟩ :=
    singleton_even_star_x_output_of_singleton_cut_strict G x y w H hxw hleaf
      hcore hmEven hlt'
  obtain ⟨PY, hPYsize, hPY⟩ :=
    singleton_leaf_y_output_of_leaf_geometry G x y w H hxw hwy hleaf
  apply M.2
  exact ⟨⟨PX, hPXsize, hPX⟩, ⟨PY, hPYsize, hPY⟩⟩

/-- In the odd strict singleton branch, the literal double core and the two
surviving hub edges reconnect the full even-star puncture.  This is the
source's connectedness assertion for `H = G - E_F(x)`; it does not replace
the singleton leaf by an invalid connected graph after the leaf edge is
deleted. -/
theorem singleton_odd_star_puncture_connected_of_singleton_cut_strict
    (G : SimpleGraph V) [DecidableRel G.Adj] (x w : V) (hxw : G.Adj x w)
    (hleaf : ∀ v, G.Adj w v → v = x)
    (hcore : (G.induce {v | v ≠ x ∧ v ≠ w}).Connected)
    (hlt : eDegree G x < (G.deleteEdges {s(x, w)}).degree x) :
    (evenStarPuncture G x).Connected := by
  let J : SimpleGraph V := evenStarPuncture G x
  have hwdegree : G.degree w = 1 := by
    rw [SimpleGraph.degree_eq_one_iff_existsUnique_adj]
    exact ⟨x, hxw.symm, fun v hwv => hleaf v hwv⟩
  have hwodd : Odd (G.degree w) := by
    simpa [hwdegree] using (show Odd 1 from ⟨0, rfl⟩)
  have hwnot : w ∉ evenNeighbors G x := by
    intro hw
    exact (Nat.not_even_iff_odd.mpr hwodd) ((mem_evenNeighbors x w).mp hw).2
  have hxwJ : J.Adj x w := by
    change G.Adj x w ∧ ¬ ((evenNeighbors G x).sup (SimpleGraph.edge x)).Adj x w
    refine ⟨hxw, ?_⟩
    intro hs
    exact hwnot ((star_sup_adj_center x (evenNeighbors G x) (by simp) w).mp hs)
  obtain ⟨z, hxz, hzw⟩ :=
    singleton_even_star_retained_nonleaf_neighbor_of_strict_degree G x w hxw hleaf hlt
  simpa [J] using starPuncture_connected_of_singleton_leaf G x w
    (evenNeighbors G x) hcore hxwJ ⟨z, hxz, hzw⟩

/-- Complete source-facing odd strict alternative for a singleton opposite
cut piece.  The strict selected-side degree inequality provides the second
retained hub edge; the full puncture is connected and the existing odd-star
floor-or-SET reconstruction supplies the `x` output. -/
theorem singleton_leaf_odd_star_strict_cut_piece_not_minimal
    (G : SimpleGraph V) [DecidableRel G.Adj] (x y w : V)
    (M : AdjacentCounterexample G x y) (hxw : G.Adj x w)
    (S T : Set V) [DecidablePred (· ∈ S)]
    (hcover : S ∪ T = Set.univ) (hinter : S ∩ T = {x})
    (hT : T = {x, w})
    (hgraph : (G.induce S).spanningCoe ⊔ (G.induce T).spanningCoe = G)
    (hconn : (G.induce {v | v ∈ S ∧ v ≠ x}).Connected)
    (hmOdd : Odd (eDegree G x))
    (hlt : eDegree G x <
      (G.induce S).degree ⟨x, by
        have hxI : x ∈ S ∩ T := by rw [hinter]; simp
        exact hxI.1⟩) : False := by
  have H := M.1
  have hleaf : ∀ v, G.Adj w v → v = x :=
    singleton_leaf_of_cut_partition G S T x w hxw hinter hT hgraph
  have hwy : w ≠ y := singleton_leaf_ne_other_exception G x y w H hxw hleaf
  have hcore : (G.induce {v | v ≠ x ∧ v ≠ w}).Connected := by
    rw [← singleton_cut_core_set_eq S T x w hcover hinter hT]
    exact hconn
  have hlt' : eDegree G x < (G.deleteEdges {s(x, w)}).degree x := by
    rw [← singleton_cut_piece_degree_eq_delete_edge G S T x w hxw hcover hinter hT]
    exact hlt
  obtain ⟨PX, hPXsize, hPX⟩ :=
    singleton_odd_star_x_output G x y H
      (singleton_odd_star_puncture_connected_of_singleton_cut_strict G x w hxw
        hleaf hcore hlt') hmOdd
  obtain ⟨PY, hPYsize, hPY⟩ :=
    singleton_leaf_y_output_of_leaf_geometry G x y w H hxw hwy hleaf
  apply M.2
  exact ⟨⟨PX, hPXsize, hPX⟩, ⟨PY, hPYsize, hPY⟩⟩

/-- Deleting a literal singleton cut leaf cannot remove an even neighbour of
its hub: the leaf has degree one and is odd.  Thus the hub's original
E-degree is bounded by its ordinary degree after the leaf edge is deleted.
This is the source inequality that yields the strict/equality case split. -/
theorem singleton_eDegree_le_delete_edge_degree
    (G : SimpleGraph V) [DecidableRel G.Adj] (x w : V)
    (hxw : G.Adj x w) (hleaf : ∀ v, G.Adj w v → v = x) :
    eDegree G x ≤ (G.deleteEdges {s(x, w)}).degree x := by
  classical
  let H : SimpleGraph V := G.deleteEdges {s(x, w)}
  have hwdegree : G.degree w = 1 := by
    rw [SimpleGraph.degree_eq_one_iff_existsUnique_adj]
    exact ⟨x, hxw.symm, fun v hwv => hleaf v hwv⟩
  have hwodd : Odd (G.degree w) := by
    simpa [hwdegree] using (show Odd 1 from ⟨0, rfl⟩)
  have hsubset : evenNeighbors G x ⊆ H.neighborFinset x := by
    intro v hv
    obtain ⟨hxv, hvEven⟩ := (mem_evenNeighbors x v).mp hv
    have hvw : v ≠ w := by
      intro h
      subst v
      exact (Nat.not_even_iff_odd.mpr hwodd) hvEven
    rw [SimpleGraph.mem_neighborFinset]
    refine (SimpleGraph.deleteEdges_adj).mpr ⟨hxv, ?_⟩
    simp only [Set.mem_singleton_iff]
    intro h
    exact hvw (Sym2.congr_right.mp h)
  rw [eDegree, ← H.card_neighborFinset_eq_degree]
  exact Finset.card_le_card hsubset

/-- Source-facing form of the singleton hub-degree bound.  The selected
piece degree agrees with the deleted-edge degree, so the comparison used in
the source's strict/equality split is derived from the literal cut geometry. -/
theorem singleton_eDegree_le_cut_piece_degree
    (G : SimpleGraph V) [DecidableRel G.Adj] (S T : Set V)
    [DecidablePred (· ∈ S)] (x w : V)
    (hxw : G.Adj x w) (hleaf : ∀ v, G.Adj w v → v = x)
    (hcover : S ∪ T = Set.univ) (hinter : S ∩ T = {x})
    (hT : T = {x, w}) :
    eDegree G x ≤ (G.induce S).degree ⟨x, by
      have hxI : x ∈ S ∩ T := by rw [hinter]; simp
      exact hxI.1⟩ := by
  rw [singleton_cut_piece_degree_eq_delete_edge G S T x w hxw hcover hinter hT]
  exact singleton_eDegree_le_delete_edge_degree G x w hxw hleaf

/-- The literal singleton branch has the exact strict-or-equality dichotomy
used in Xie's proof; it follows from the preceding cut-piece comparison and
does not need to be retained as an additional source premise. -/
theorem singleton_eDegree_lt_or_eq_cut_piece_degree
    (G : SimpleGraph V) [DecidableRel G.Adj] (S T : Set V)
    [DecidablePred (· ∈ S)] (x w : V)
    (hxw : G.Adj x w) (hleaf : ∀ v, G.Adj w v → v = x)
    (hcover : S ∪ T = Set.univ) (hinter : S ∩ T = {x})
    (hT : T = {x, w}) :
    eDegree G x < (G.induce S).degree ⟨x, by
      have hxI : x ∈ S ∩ T := by rw [hinter]; simp
      exact hxI.1⟩ ∨
    eDegree G x = (G.induce S).degree ⟨x, by
      have hxI : x ∈ S ∩ T := by rw [hinter]; simp
      exact hxI.1⟩ :=
  lt_or_eq_of_le (singleton_eDegree_le_cut_piece_degree G S T x w hxw hleaf
    hcover hinter hT)

/-- In the equality alternative, global even degree at the hub makes its
E-degree odd: deleting the singleton leaf edge reverses the hub parity.
This supplies the parity premise of the compiled equality reconstruction. -/
theorem singleton_eDegree_odd_of_delete_edge_equality
    (G : SimpleGraph V) [DecidableRel G.Adj] (x w : V)
    (hxw : G.Adj x w) (hxEven : Even (G.degree x))
    (heq : eDegree G x = (G.deleteEdges {s(x, w)}).degree x) :
    Odd (eDegree G x) := by
  have hdelete : (G.deleteEdges {s(x, w)}).degree x + 1 = G.degree x :=
    degree_delete_edge_add_one G x w hxw
  rw [heq, Nat.odd_iff]
  rw [← hdelete, Nat.even_iff] at hxEven
  omega

/-- The one-edge opposite-piece branch is reducible when the hub has even
E-degree.  The selected piece is classified as `{x,w}` from its one-edge
cardinality, and the internally derived strict/equality split either invokes
the strict all-star reconstruction or contradicts parity in the equality
alternative. -/
theorem singleton_one_edge_even_eDegree_not_minimal
    (G : SimpleGraph V) [DecidableRel G.Adj] (x y : V)
    (M : AdjacentCounterexample G x y)
    (S T : Set V) [DecidablePred (· ∈ S)] [DecidablePred (· ∈ T)]
    (hxT : x ∈ T) (hother : ∃ b ∈ T, b ≠ x)
    (hconnT : (G.induce T).Connected)
    (hedge : (G.induce T).edgeFinset.card = 1)
    (hcover : S ∪ T = Set.univ) (hinter : S ∩ T = {x})
    (hgraph : (G.induce S).spanningCoe ⊔ (G.induce T).spanningCoe = G)
    (hcore : (G.induce {v | v ∈ S ∧ v ≠ x}).Connected)
    (hmEven : Even (eDegree G x)) : False := by
  have H := M.1
  obtain ⟨w, hwx, hxw, hT⟩ :=
    connected_induced_one_edge_eq G T x hxT hother hconnT hedge
  have hleaf : ∀ v, G.Adj w v → v = x :=
    singleton_leaf_of_cut_partition G S T x w hxw hinter hT hgraph
  rcases singleton_eDegree_lt_or_eq_cut_piece_degree G S T x w hxw hleaf
    hcover hinter hT with hlt | heq
  · exact singleton_leaf_even_star_strict_cut_piece_not_minimal G x y w M hxw
      S T hcover hinter hT hgraph hcore hmEven hlt
  · have hdeleteEq : eDegree G x = (G.deleteEdges {s(x, w)}).degree x :=
      singleton_cut_piece_equality_to_delete_edge G S T x w hxw hcover hinter hT heq
    have hodd : Odd (eDegree G x) :=
      singleton_eDegree_odd_of_delete_edge_equality G x w hxw H.2.2.2.1 hdeleteEq
    exact (Nat.not_even_iff_odd.mpr hodd) hmEven

/-- Complete source-facing one-edge opposite-piece branch.  Once the selected
cut partition has been obtained, its connected one-edge side is literally
`{x,w}`.  Parity of the hub E-degree and the internally derived
strict-or-equality degree split exhaust the three Xie subcases. -/
theorem singleton_one_edge_not_minimal
    (G : SimpleGraph V) [DecidableRel G.Adj] (x y : V)
    (M : AdjacentCounterexample G x y)
    (S T : Set V) [DecidablePred (· ∈ S)] [DecidablePred (· ∈ T)]
    (hxT : x ∈ T) (hother : ∃ b ∈ T, b ≠ x)
    (hconnT : (G.induce T).Connected)
    (hedge : (G.induce T).edgeFinset.card = 1)
    (hcover : S ∪ T = Set.univ) (hinter : S ∩ T = {x})
    (hgraph : (G.induce S).spanningCoe ⊔ (G.induce T).spanningCoe = G)
    (hcore : (G.induce {v | v ∈ S ∧ v ≠ x}).Connected) : False := by
  obtain hmEven | hmOdd := Nat.even_or_odd (eDegree G x)
  · exact singleton_one_edge_even_eDegree_not_minimal G x y M S T hxT hother hconnT hedge
      hcover hinter hgraph hcore hmEven
  obtain ⟨w, hwx, hxw, hT⟩ :=
    connected_induced_one_edge_eq G T x hxT hother hconnT hedge
  have hleaf : ∀ v, G.Adj w v → v = x :=
    singleton_leaf_of_cut_partition G S T x w hxw hinter hT hgraph
  rcases singleton_eDegree_lt_or_eq_cut_piece_degree G S T x w hxw hleaf
    hcover hinter hT with hlt | heq
  · exact singleton_leaf_odd_star_strict_cut_piece_not_minimal G x y w M hxw
      S T hcover hinter hT hgraph hcore hmOdd hlt
  · exact singleton_leaf_odd_star_equality_cut_piece_not_minimal G x y w M hxw hleaf
      S T hcover hinter hT hcore hmOdd heq

/-- The singleton opposite-piece branch is independent of how minimality was
obtained: its reconstruction only consumes the failed adjacent conclusion.
Consequently it is available under Xie's source-faithful edge-minimal resource
as well as under the older lexicographic wrapper. -/
theorem singleton_one_edge_not_edge_minimal
    (G : SimpleGraph V) [DecidableRel G.Adj] (x y : V)
    (M : AdjacentEdgeMinimalCounterexample G x y)
    (S T : Set V) [DecidablePred (· ∈ S)] [DecidablePred (· ∈ T)]
    (hxT : x ∈ T) (hother : ∃ b ∈ T, b ≠ x)
    (hconnT : (G.induce T).Connected)
    (hedge : (G.induce T).edgeFinset.card = 1)
    (hcover : S ∪ T = Set.univ) (hinter : S ∩ T = {x})
    (hgraph : (G.induce S).spanningCoe ⊔ (G.induce T).spanningCoe = G)
    (hcore : (G.induce {v | v ∈ S ∧ v ≠ x}).Connected) : False := by
  exact singleton_one_edge_not_minimal G x y M.counterexample S T hxT hother hconnT
    hedge hcover hinter hgraph hcore

end Gallai.TwoException
