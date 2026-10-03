/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.Inputs.UniqueEvenRestore
public import Gallai.Inputs.UniqueEvenComponent
public import Gallai.TwoException.BareMinimality
public import Gallai.TwoException.ComponentBudget
public import Gallai.TwoException.BareHangingSET
public import Gallai.TwoException.BareCuts
public import Gallai.TwoException.BridgePartition
public import Gallai.Structure.PunctureBoundary

@[expose] public section

/-! # Protected restoration for an ordinary E-degree-one edge

The ordinary-component reduction deletes an edge from an originally even
vertex with a unique even neighbour.  The standard restoration identity is
endpoint-sensitive; this small wrapper records the exact fact needed by B0:
the prescribed bare vertex is unchanged when it is distinct from both ends.
The connected/disconnected puncture budgets are deliberately not assumed here.
-/

namespace Gallai.TwoException

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Deleting an edge between two originally even vertices preserves the fact
that any third, nonincident vertex with no even neighbours has E-degree zero. -/
theorem bare_vertex_puncture_eDegree_zero
    (h w v : V) (hwv : G.Adj w v) (hhw : h ≠ w) (hhv : h ≠ v)
    (hwEven : Even (G.degree w)) (hvEven : Even (G.degree v))
    (hzero : eDegree G h = 0) :
    eDegree (G.deleteEdges {s(w, v)}) h = 0 := by
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro a ha
  obtain ⟨hha, haEven⟩ := (mem_evenNeighbors h a).mp ha
  have haw : a ≠ w := by
    intro heq
    subst a
    have hd := degree_delete_edge_add_one G w v hwv
    have hodd : Odd ((G.deleteEdges {s(w, v)}).degree w) := by
      rw [Nat.even_iff] at hwEven
      rw [Nat.odd_iff]
      omega
    exact Nat.not_even_iff_odd.mpr hodd haEven
  have hav : a ≠ v := by
    intro heq
    subst a
    have hd := degree_delete_edge_add_one G v w hwv.symm
    rw [Sym2.eq_swap] at hd
    have hodd : Odd ((G.deleteEdges {s(w, v)}).degree v) := by
      rw [Nat.even_iff] at hvEven
      rw [Nat.odd_iff]
      omega
    exact Nat.not_even_iff_odd.mpr hodd haEven
  have haGEven : Even (G.degree a) := by
    rwa [degree_delete_edge_of_ne G w v a haw hav] at haEven
  have hhaG : G.Adj h a := (SimpleGraph.deleteEdges_adj.mp hha).1
  have hempty : evenNeighbors G h = ∅ := Finset.card_eq_zero.mp hzero
  have hmem : a ∈ (∅ : Finset V) := by
    simpa [hempty] using (mem_evenNeighbors h a).mpr ⟨hhaG, haGEven⟩
  simpa using hmem

/-- A component of a one-edge puncture has no surviving edge to its
complement.  Consequently, every original crossing edge is the deleted edge.
This is the boundary half of the K-ORD1 assertion that a SET on the `v`-side
is induced in the original graph and has only the removed edge as a possible
boundary. -/
theorem puncture_component_crossing_eq_deleted_edge
    (w v a b : V) (C : (G.deleteEdges {s(w, v)}).ConnectedComponent)
    (ha : a ∈ C.supp) (hb : b ∉ C.supp) (hab : G.Adj a b) :
    s(a, b) = s(w, v) := by
  by_contra hne
  have hpuncture : (G.deleteEdges {s(w, v)}).Adj a b :=
    SimpleGraph.deleteEdges_adj.mpr ⟨hab, hne⟩
  exact hb (C.mem_supp_of_adj_mem_supp ha hpuncture)

/-- If the puncture component contains the recipient `v` but not the other
deleted-edge endpoint `w`, its oriented original boundary is exactly `v-w`.
This eliminates the swapped orientation using component membership. -/
theorem puncture_component_crossing_is_vw
    (w v a b : V) (C : (G.deleteEdges {s(w, v)}).ConnectedComponent)
    (hv : v ∈ C.supp) (hw : w ∉ C.supp)
    (ha : a ∈ C.supp) (hb : b ∉ C.supp) (hab : G.Adj a b) :
    a = v ∧ b = w := by
  have heq := puncture_component_crossing_eq_deleted_edge w v a b C ha hb hab
  rcases Sym2.eq_iff.mp heq with ⟨haw, hbv⟩ | ⟨hav, hbw⟩
  · exact (hw (haw ▸ ha)).elim
  · exact ⟨hav, hbw⟩

/-- Away from the recipient `v`, the `v`-side puncture component is closed
under original neighbours.  The only original edge that can cross its
puncture boundary is `v-w`; hence a different component vertex has no
original neighbour outside the component.  This is the local structural
input needed to analyse whether the second exception can lie in a v-side
SET component. -/
theorem v_side_neighbor_closed_away_from_v
    (w v t : V) (C : (G.deleteEdges {s(w, v)}).ConnectedComponent)
    (hv : v ∈ C.supp) (hw : w ∉ C.supp)
    (ht : t ∈ C.supp) (htv : t ≠ v) :
    G.neighborSet t ⊆ C.supp := by
  intro a hta
  by_contra ha
  obtain ⟨htv', haw⟩ :=
    puncture_component_crossing_is_vw w v t a C hv hw ht ha hta
  exact htv htv'

/-- The recipient `v` is odd in its component after deleting the original
even--even edge `w-v`.  Together with
`v_side_neighbor_closed_away_from_v`, this records the exact parity boundary
of the sharp recipient-side SET branch: the exceptional vertex changes parity,
whereas every other component vertex has no original boundary edge. -/
theorem v_side_recipient_odd_in_puncture_component
    (w v : V) (C : (G.deleteEdges {s(w, v)}).ConnectedComponent)
    (hv : v ∈ C.supp) (hwv : G.Adj w v)
    (hvEven : Even (G.degree v)) :
    Odd (((G.deleteEdges {s(w, v)}).induce C.supp).degree ⟨v, hv⟩) := by
  have hclosed : ∀ u ∈ C.supp,
      (G.deleteEdges {s(w, v)}).neighborSet u ⊆ C.supp := by
    intro u hu a hua
    exact C.mem_supp_of_adj_mem_supp hu hua
  have hvodd : Odd ((G.deleteEdges {s(w, v)}).degree v) := by
    have hd := degree_delete_edge_add_one G v w hwv.symm
    rw [Sym2.eq_swap] at hd
    rw [Nat.even_iff] at hvEven
    rw [Nat.odd_iff]
    omega
  rwa [SimpleGraph.degree_induce_of_neighborSet_subset (hclosed v hv)]

/-- The `v`-side component of the one-edge puncture is induced in the
original graph.  Since it excludes `w`, the removed edge cannot be internal
to it.  In particular any SET certificate on this component is an induced
SET certificate in `G`, rather than merely in the puncture. -/
theorem puncture_component_induce_eq_original_of_v_side
    (w v : V) (C : (G.deleteEdges {s(w, v)}).ConnectedComponent)
    (hv : v ∈ C.supp) (hw : w ∉ C.supp) :
    (G.deleteEdges {s(w, v)}).induce C.supp = G.induce C.supp := by
  apply induce_eq_of_singleton_puncture_boundary
    (H := G.deleteEdges {s(w, v)})
    (fun a b hab => (SimpleGraph.deleteEdges_adj.mp hab).1) C.supp v
  intro a ha b hab hnot
  have heq : s(a, b) = s(w, v) := by
    by_contra hne
    exact hnot (SimpleGraph.deleteEdges_adj.mpr ⟨hab, hne⟩)
  rcases Sym2.eq_iff.mp heq with ⟨haw, hbv⟩ | ⟨hav, hbw⟩
  · exact (hw (haw ▸ ha)).elim
  · exact hav

/-- In a connected one-edge puncture, a component that does not contain the
ordinary endpoint `w` contains the other endpoint `v`.  This is the missing
side-membership step for applying the literal v-side hanging-SET consumer. -/
theorem puncture_component_contains_v_of_not_mem_w
    (w v : V) (C : (G.deleteEdges {s(w, v)}).ConnectedComponent)
    (hconn : G.Connected) (hwv : G.Adj w v) (hw : w ∉ C.supp) :
    v ∈ C.supp := by
  obtain ⟨a, ha⟩ := C.nonempty_supp
  have ha' : (G.deleteEdges {s(w, v)}).connectedComponentMk a = C := by
    simpa only [SimpleGraph.ConnectedComponent.mem_supp_iff,
      SimpleGraph.ConnectedComponent.eq] using ha
  rcases puncture_reachable_from_h_or_x (G := G) hconn w v a hwv.ne with hwa | hva
  · apply False.elim
    apply hw
    rw [SimpleGraph.ConnectedComponent.mem_supp_iff]
    calc
      (G.deleteEdges {s(w, v)}).connectedComponentMk w =
          (G.deleteEdges {s(w, v)}).connectedComponentMk a :=
        SimpleGraph.ConnectedComponent.eq.mpr hwa
      _ = C := ha'
  · rw [SimpleGraph.ConnectedComponent.mem_supp_iff]
    calc
      (G.deleteEdges {s(w, v)}).connectedComponentMk v =
          (G.deleteEdges {s(w, v)}).connectedComponentMk a :=
        SimpleGraph.ConnectedComponent.eq.mpr hva
      _ = C := ha'

/-- A SET component of the ordinary one-edge puncture is necessarily v-side.
The component containing w is excluded by the unique-even-neighbour witness;
connectedness then places every remaining component at v. -/
theorem puncture_set_component_is_v_side
    (w v : V) (C : (G.deleteEdges {s(w, v)}).ConnectedComponent)
    (hconn : G.Connected) (hwv : G.Adj w v) (hvEven : Even (G.degree v))
    (hunique : ∀ a, G.Adj w a → Even (G.degree a) → a = v)
    (hset : IsSET ((G.deleteEdges {s(w, v)}).induce C.supp)) :
    v ∈ C.supp ∧ w ∉ C.supp := by
  have hw : w ∉ C.supp := by
    intro hwm
    exact unique_even_neighbor_component_not_set w v hwv hvEven hunique C hwm hset
  exact ⟨puncture_component_contains_v_of_not_mem_w w v C hconn hwv hw, hw⟩

/-- A SET component contains a vertex distinct from any specified boundary
vertex.  The witness comes from its three even vertices, so it is intrinsic to
the component and does not require an ambient degree argument. -/
theorem puncture_set_component_exists_ne
    (w v : V) (C : (G.deleteEdges {s(w, v)}).ConnectedComponent)
    (hset : IsSET ((G.deleteEdges {s(w, v)}).induce C.supp)) :
    ∃ r, r ∈ C.supp ∧ r ≠ v := by
  let E : Finset C.supp := Finset.univ.filter fun u =>
    Even (((G.deleteEdges {s(w, v)}).induce C.supp).degree u)
  have hE : E.card = 3 := by
    simpa [E] using hset.card_even
  obtain ⟨a, b, c, hab, hac, hbc, hEeq⟩ := Finset.card_eq_three.mp hE
  by_cases ha : a.val = v
  · refine ⟨b.val, b.property, ?_⟩
    intro hb
    apply hab
    apply Subtype.ext
    exact ha.trans hb.symm
  · exact ⟨a.val, a.property, ha⟩

/-- The prescribed bare vertex cannot lie in a SET component of the ordinary
puncture: it remains even with E-degree zero after deleting the disjoint
even--even edge. -/
theorem puncture_set_component_not_mem_bare
    (z w v h : V) (H : BareMinimalCounterexample G h z)
    (C : (G.deleteEdges {s(w, v)}).ConnectedComponent)
    (hwv : G.Adj w v) (hwEven : Even (G.degree w))
    (hvEven : Even (G.degree v))
    (hset : IsSET ((G.deleteEdges {s(w, v)}).induce C.supp)) :
    h ∉ C.supp := by
  intro hh
  have hbare := H.counterexample.1
  have hhw : h ≠ w := by
    intro heq
    subst w
    have hmem : v ∈ evenNeighbors G h :=
      (mem_evenNeighbors h v).mpr ⟨hwv, hvEven⟩
    have hzero := hbare.2.2.2.2.2.1
    change (evenNeighbors G h).card = 0 at hzero
    have hpos : 0 < (evenNeighbors G h).card := Finset.card_pos.mpr ⟨v, hmem⟩
    omega
  have hhv : h ≠ v := by
    intro heq
    subst v
    have hmem : w ∈ evenNeighbors G h :=
      (mem_evenNeighbors h w).mpr ⟨hwv.symm, hwEven⟩
    have hzero := hbare.2.2.2.2.2.1
    change (evenNeighbors G h).card = 0 at hzero
    have hpos : 0 < (evenNeighbors G h).card := Finset.card_pos.mpr ⟨w, hmem⟩
    omega
  have hPzero := bare_vertex_puncture_eDegree_zero h w v hwv hhw hhv
    hwEven hvEven hbare.2.2.2.2.2.1
  have hPdeg : (G.deleteEdges {s(w, v)}).degree h = G.degree h :=
    degree_delete_edge_of_ne G w v h hhw hhv
  have hPeven : Even ((G.deleteEdges {s(w, v)}).degree h) := by
    rw [hPdeg]
    exact hbare.2.2.2.1
  have hclosed : ∀ u ∈ C.supp,
      (G.deleteEdges {s(w, v)}).neighborSet u ⊆ C.supp := by
    intro u hu a hua
    exact C.mem_supp_of_adj_mem_supp hu hua
  have hzero : eDegree ((G.deleteEdges {s(w, v)}).induce C.supp) ⟨h, hh⟩ = 0 := by
    rw [eDegree_induce_of_closed (G.deleteEdges {s(w, v)}) C.supp hclosed]
    exact hPzero
  have htwo := hset.eDegree_even ⟨h, hh⟩ (by
    rwa [SimpleGraph.degree_induce_of_neighborSet_subset (hclosed h hh)])
  omega

/-- In the SET branch of an ordinary one-edge puncture, the second exception
can occur in the v-side component only at the recipient `v`.  Away from `v`,
the exact boundary closure transports every original even neighbour into the
SET, except possibly `v` itself.  Hence the original E-degree is at most the
two SET neighbours plus `v`, contradicting bare minimality. -/
theorem puncture_set_component_exception_eq_recipient
    (z w v h : V) (H : BareMinimalCounterexample G h z)
    (C : (G.deleteEdges {s(w, v)}).ConnectedComponent)
    (hconn : G.Connected) (hwv : G.Adj w v) (hwEven : Even (G.degree w))
    (hvEven : Even (G.degree v))
    (hunique : ∀ a, G.Adj w a → Even (G.degree a) → a = v)
    (hz : z ∈ C.supp)
    (hset : IsSET ((G.deleteEdges {s(w, v)}).induce C.supp)) :
    z = v := by
  classical
  obtain ⟨hv, hw⟩ := puncture_set_component_is_v_side w v C hconn hwv hvEven
    hunique hset
  by_contra hzv
  have hbare := H.counterexample.1
  have hzw : z ≠ w := by
    intro hzw
    subst z
    exact hw hz
  let P := G.deleteEdges {s(w, v)}
  let J := P.induce C.supp
  have hPclosed : ∀ u ∈ C.supp, P.neighborSet u ⊆ C.supp := by
    intro u hu a hua
    exact C.mem_supp_of_adj_mem_supp hu hua
  have hzPdeg : P.degree z = G.degree z := by
    exact degree_delete_edge_of_ne G w v z hzw hzv
  have hzJdeg : J.degree ⟨z, hz⟩ = G.degree z := by
    rw [SimpleGraph.degree_induce_of_neighborSet_subset (hPclosed z hz)]
    exact hzPdeg
  have hzJeven : Even (J.degree ⟨z, hz⟩) := by
    rw [hzJdeg]
    exact hbare.2.2.2.2.1
  have hsub : evenNeighbors G z ⊆
      insert v ((evenNeighbors J ⟨z, hz⟩).map (Function.Embedding.subtype _)) := by
    intro a ha
    by_cases hav : a = v
    · simpa [hav]
    · have hza : G.Adj z a := (mem_evenNeighbors z a).mp ha |>.1
      have haEven : Even (G.degree a) := (mem_evenNeighbors z a).mp ha |>.2
      have haC : a ∈ C.supp :=
        v_side_neighbor_closed_away_from_v w v z C hv hw hz hzv hza
      have haw : a ≠ w := by
        intro haw
        subst a
        exact hw haC
      have hPa : P.Adj z a := by
        apply SimpleGraph.deleteEdges_adj.mpr
        refine ⟨hza, ?_⟩
        intro heq
        rcases Sym2.eq_iff.mp heq with ⟨hzw', hav'⟩ | ⟨hzv', haw'⟩
        · exact hzw hzw'
        · exact hzv hzv'
      have haPdeg : P.degree a = G.degree a := by
        exact degree_delete_edge_of_ne G w v a haw hav
      have haJdeg : J.degree ⟨a, haC⟩ = P.degree a := by
        exact SimpleGraph.degree_induce_of_neighborSet_subset (hPclosed a haC)
      have hJa : J.Adj ⟨z, hz⟩ ⟨a, haC⟩ := hPa
      have haJeven : Even (J.degree ⟨a, haC⟩) := by
        rw [haJdeg, haPdeg]
        exact haEven
      refine Finset.mem_insert.mpr (Or.inr ?_)
      refine Finset.mem_map.mpr ⟨⟨a, haC⟩, ?_, rfl⟩
      rw [mem_evenNeighbors]
      exact ⟨hJa, haJeven⟩
  have hcap : eDegree G z ≤ 3 := by
    calc
      eDegree G z = (evenNeighbors G z).card := rfl
      _ ≤ (insert v ((evenNeighbors J ⟨z, hz⟩).map
          (Function.Embedding.subtype _))).card := Finset.card_le_card hsub
      _ ≤ ((evenNeighbors J ⟨z, hz⟩).map
          (Function.Embedding.subtype _)).card + 1 := Finset.card_insert_le _ _
      _ = (evenNeighbors J ⟨z, hz⟩).card + 1 := by simp
      _ = eDegree J ⟨z, hz⟩ + 1 := by simp [eDegree]
      _ = 3 := by rw [hset.eDegree_even ⟨z, hz⟩ hzJeven]
  have hgt := BareCounterexample.exception_gt_three H.counterexample
  omega

/-- A v-side SET component of the ordinary one-edge puncture is a literal
hanging SET in the original graph.  The endpoint, boundary orientation and
inducedness facts are all derived from the puncture component itself; only
the component's membership and SET certificate are supplied. -/
theorem bare_v_side_hanging_set_false
    (z w v h r : V) (H : BareMinimalCounterexample G h z)
    (C : (G.deleteEdges {s(w, v)}).ConnectedComponent)
    (hv : v ∈ C.supp) (hw : w ∉ C.supp)
    (hr : r ∈ C.supp) (hrv : r ≠ v)
    (hh : h ∉ C.supp) (hz : z ∉ C.supp)
    (hwv : G.Adj w v) (hset : IsSET (G.induce C.supp)) : False := by
  refine bare_hanging_set_literal_false h z H C.supp v w r hv hw hr hrv hh hz hwv.symm ?_ hset
  intro a b ha hb hab
  exact puncture_component_crossing_is_vw w v a b C hv hw ha hb hab

/-- The SET branch of an ordinary unique-even-neighbour puncture is absorbed
without separately supplying its side, original-inducedness, or boundary
orientation.  Only the genuinely structural exclusions and non-joint witness
remain as inputs. -/
theorem bare_puncture_set_component_false
    (z w v h : V) (H : BareMinimalCounterexample G h z)
    (C : (G.deleteEdges {s(w, v)}).ConnectedComponent)
    (hconn : G.Connected) (hwv : G.Adj w v) (hwEven : Even (G.degree w))
    (hvEven : Even (G.degree v))
    (hunique : ∀ a, G.Adj w a → Even (G.degree a) → a = v)
    (hz : z ∉ C.supp)
    (hset : IsSET ((G.deleteEdges {s(w, v)}).induce C.supp)) : False := by
  obtain ⟨hv, hw⟩ := puncture_set_component_is_v_side w v C hconn hwv hvEven
    hunique hset
  obtain ⟨r, hr, hrv⟩ := puncture_set_component_exists_ne w v C hset
  have hh := puncture_set_component_not_mem_bare z w v h H C hwv hwEven hvEven hset
  have hsetG : IsSET (G.induce C.supp) := by
    simpa only [puncture_component_induce_eq_original_of_v_side w v C hv hw] using hset
  exact bare_v_side_hanging_set_false z w v h r H C hv hw hr hrv hh hz hwv hsetG

/-- The ordinary puncture SET branch is completely excluded whenever the
second exception is not the recipient.  The only unresolved configuration is
therefore the sharp local branch in which the exceptional vertex is exactly
the endpoint whose parity was flipped by deleting `w-v`. -/
theorem bare_puncture_set_component_false_of_exception_ne_recipient
    (z w v h : V) (H : BareMinimalCounterexample G h z)
    (C : (G.deleteEdges {s(w, v)}).ConnectedComponent)
    (hconn : G.Connected) (hwv : G.Adj w v) (hwEven : Even (G.degree w))
    (hvEven : Even (G.degree v))
    (hunique : ∀ a, G.Adj w a → Even (G.degree a) → a = v)
    (hzv : z ≠ v)
    (hset : IsSET ((G.deleteEdges {s(w, v)}).induce C.supp)) : False := by
  by_cases hz : z ∈ C.supp
  · exact hzv (puncture_set_component_exception_eq_recipient z w v h H C hconn
      hwv hwEven hvEven hunique hz hset)
  · exact bare_puncture_set_component_false z w v h H C hconn hwv hwEven hvEven
      hunique hz hset

/-- Every SET component in the ordinary unique-even-neighbour puncture is
confined to the sharp recipient branch: it contains the second exception, and
that exception is the parity-flipped endpoint `v` of the deleted edge.  This
is a classification interface for the later contact-packet schedule, not an
attempt to absorb the recipient branch by the hanging-SET argument. -/
theorem bare_puncture_set_component_requires_recipient
    (z w v h : V) (H : BareMinimalCounterexample G h z)
    (C : (G.deleteEdges {s(w, v)}).ConnectedComponent)
    (hconn : G.Connected) (hwv : G.Adj w v) (hwEven : Even (G.degree w))
    (hvEven : Even (G.degree v))
    (hunique : ∀ a, G.Adj w a → Even (G.degree a) → a = v)
    (hset : IsSET ((G.deleteEdges {s(w, v)}).induce C.supp)) :
    z = v ∧ z ∈ C.supp := by
  by_cases hz : z ∈ C.supp
  · exact ⟨puncture_set_component_exception_eq_recipient z w v h H C hconn
      hwv hwEven hvEven hunique hz hset, hz⟩
  · exact False.elim (bare_puncture_set_component_false z w v h H C hconn
      hwv hwEven hvEven hunique hz hset)

/-- The puncture component containing the ordinary vertex `w` cannot be SET:
the deleted edge was its unique originally even-neighbour edge, so `w` has
no even neighbours in that component. -/
theorem puncture_w_side_not_set
    (w v : V) (C : (G.deleteEdges {s(w, v)}).ConnectedComponent)
    (hwv : G.Adj w v) (hvEven : Even (G.degree v))
    (hunique : ∀ a, G.Adj w a → Even (G.degree a) → a = v)
    (hw : w ∈ C.supp) :
    ¬ IsSET ((G.deleteEdges {s(w, v)}).induce C.supp) := by
  exact unique_even_neighbor_component_not_set w v hwv hvEven hunique C hw

/-- Restoring a unique-even-neighbour edge leaves every third vertex's
endpoint count unchanged.  This is the protected endpoint interface used when
the deleted ordinary edge lies away from the bare prescribed vertex. -/
theorem restore_unique_even_neighbor_preserves_bare
    (x y h : V) (D : Decomposition (G.deleteEdges {s(x, y)}))
    (hxy : G.Adj x y) (hyEven : Even (G.degree y))
    (hunique : ∀ v, G.Adj x v → Even (G.degree v) → v = y)
    (hhx : h ≠ x) (hhy : h ≠ y) :
    ∃ E : Decomposition G, E.size = D.size ∧
      E.endpointCount h = D.endpointCount h := by
  obtain ⟨E, hsize, hends⟩ := D.restore_unique_even_neighbor x y hxy hyEven hunique
  refine ⟨E, hsize, ?_⟩
  have hh := hends h
  simp only [hhy.symm, hhx.symm, if_false, Nat.add_zero] at hh
  exact hh

/-- A literal K-ORD1 consumer.  Once a puncture at an ordinary vertex's
unique originally even neighbour already has the bare ceiling conclusion,
the protected restoration interface contradicts B0 failure.  This theorem
deliberately takes the puncture decomposition and its budget as hypotheses:
the remaining ordinary-component proof must obtain them from its connected
component or induced hanging-SET alternatives. -/
theorem bare_counterexample_false_of_unique_even_puncture
    (z w v h : V) (H : BareCounterexample G h z)
    (D : Decomposition (G.deleteEdges {s(w, v)}))
    (hwv : G.Adj w v) (hvEven : Even (G.degree v))
    (hunique : ∀ a, G.Adj w a → Even (G.degree a) → a = v)
    (hhw : h ≠ w) (hhv : h ≠ v)
    (hsize : D.size ≤ (Fintype.card V + 1) / 2)
    (hends : 2 ≤ D.endpointCount h) : False := by
  obtain ⟨E, hEsize, hEends⟩ :=
    restore_unique_even_neighbor_preserves_bare w v h D hwv hvEven hunique hhw hhv
  apply H.2
  refine ⟨E, ?_, ?_⟩
  · rw [hEsize]
    exact hsize
  · rw [hEends]
    exact hends

/-- In the ordinary E-degree-one configuration, the bare prescribed vertex
cannot be either end of the removed even--even edge: it has no even
neighbours at all. -/
theorem bare_not_mem_even_edge
    (z w v h : V) (H : BareCounterexample G h z)
    (hwv : G.Adj w v) (hwEven : Even (G.degree w))
    (hvEven : Even (G.degree v)) :
    h ≠ w ∧ h ≠ v := by
  constructor
  · intro hhw
    subst w
    have hmem : v ∈ evenNeighbors G h :=
      (mem_evenNeighbors h v).mpr ⟨hwv, hvEven⟩
    have hzero := H.1.2.2.2.2.2.1
    change (evenNeighbors G h).card = 0 at hzero
    have hpos : 0 < (evenNeighbors G h).card := Finset.card_pos.mpr ⟨v, hmem⟩
    omega
  · intro hhv
    subst v
    have hmem : w ∈ evenNeighbors G h :=
      (mem_evenNeighbors h w).mpr ⟨hwv.symm, hwEven⟩
    have hzero := H.1.2.2.2.2.2.1
    change (evenNeighbors G h).card = 0 at hzero
    have hpos : 0 < (evenNeighbors G h).card := Finset.card_pos.mpr ⟨w, hmem⟩
    omega

/-- The K-ORD1 puncture consumer with the two protected-vertex inequalities
derived from bare minimality rather than supplied separately. -/
theorem bare_counterexample_false_of_even_unique_puncture
    (z w v h : V) (H : BareCounterexample G h z)
    (D : Decomposition (G.deleteEdges {s(w, v)}))
    (hwv : G.Adj w v) (hwEven : Even (G.degree w))
    (hvEven : Even (G.degree v))
    (hunique : ∀ a, G.Adj w a → Even (G.degree a) → a = v)
    (hsize : D.size ≤ (Fintype.card V + 1) / 2)
    (hends : 2 ≤ D.endpointCount h) : False := by
  obtain ⟨hhw, hhv⟩ := bare_not_mem_even_edge z w v h H hwv hwEven hvEven
  exact bare_counterexample_false_of_unique_even_puncture z w v h H D hwv hvEven
    hunique hhw hhv hsize hends

/-- The componentwise form of the K-ORD1 consumer.  A ceiling decomposition
on the actual puncture component containing the bare vertex, together with
floor decompositions on every other puncture component, assembles to the
explicit puncture premise of `bare_counterexample_false_of_even_unique_puncture`.
This is the exact interface required by the ordinary-component argument; it
does not assert that its component hypotheses hold automatically. -/
theorem bare_counterexample_false_of_even_unique_puncture_components
    (z w v h : V) (H : BareCounterexample G h z)
    (D : Decomposition ((G.deleteEdges {s(w, v)}).induce
      ((G.deleteEdges {s(w, v)}).connectedComponentMk h).supp))
    (hwv : G.Adj w v) (hwEven : Even (G.degree w))
    (hvEven : Even (G.degree v))
    (hunique : ∀ a, G.Adj w a → Even (G.degree a) → a = v)
    (hD : D.size ≤ (Fintype.card
      ((G.deleteEdges {s(w, v)}).connectedComponentMk h).supp + 1) / 2)
    (hends : 2 ≤ D.endpointCount ⟨h, rfl⟩)
    (hf : ∀ C : (G.deleteEdges {s(w, v)}).ConnectedComponent,
      C ≠ (G.deleteEdges {s(w, v)}).connectedComponentMk h →
      HasPathBudget ((G.deleteEdges {s(w, v)}).induce C.supp)
        (Fintype.card C.supp / 2)) : False := by
  obtain ⟨E, hEsize, hEends⟩ :=
    assemble_one_ceiling (G.deleteEdges {s(w, v)}) h D hD hends hf
  exact bare_counterexample_false_of_even_unique_puncture z w v h H E hwv hwEven
    hvEven hunique hEsize hEends

/-- In an ordinary even component, the unique even neighbour is not the
exceptional hub. This is the structural guard needed by the puncture SET
exclusion; the unrestricted recipient-equals-exception branch is irrelevant
to this ordinary-component consumer. -/
theorem ordinary_even_neighbor_ne_exception
    (z w v : evenVertices G) (C : (evenSubgraph G).ConnectedComponent)
    (hz : z ∉ C.supp) (hw : w ∈ C.supp)
    (hwv : G.Adj (w : V) (v : V)) : (z : V) ≠ (v : V) := by
  have hv : v ∈ C.supp := C.mem_supp_of_adj_mem_supp hw hwv
  intro heq
  exact hz (by simpa only [show z = v from Subtype.ext heq] using hv)

/-- Every SET component of the ordinary unique-even-neighbour puncture is
excluded once the removed edge is placed in its actual ordinary component. -/
theorem bare_ordinary_puncture_component_not_set
    (z w v : evenVertices G) (h : V)
    (H : BareMinimalCounterexample G h (z : V))
    (C : (evenSubgraph G).ConnectedComponent)
    (hz : z ∉ C.supp) (hw : w ∈ C.supp)
    (hconn : G.Connected) (hwv : G.Adj (w : V) (v : V))
    (hunique : ∀ a, G.Adj (w : V) a → Even (G.degree a) → a = (v : V))
    (D : (G.deleteEdges {s((w : V), (v : V))}).ConnectedComponent) :
    ¬ IsSET ((G.deleteEdges {s((w : V), (v : V))}).induce D.supp) := by
  intro hset
  exact bare_puncture_set_component_false_of_exception_ne_recipient
    (z : V) (w : V) (v : V) h H D hconn hwv w.property v.property hunique
    (ordinary_even_neighbor_ne_exception z w v C hz hw hwv) hset

/-- Deleting an even--even edge introduces no new even vertex. -/
theorem even_edge_puncture_even_preserved
    (w v a : V) (hwv : G.Adj w v)
    (hw : Even (G.degree w)) (hv : Even (G.degree v))
    (ha : Even ((G.deleteEdges {s(w, v)}).degree a)) : Even (G.degree a) := by
  have haw : a ≠ w := by
    intro heq
    subst a
    have hd := degree_delete_edge_add_one G w v hwv
    rw [Nat.even_iff] at hw ha
    omega
  have hav : a ≠ v := by
    intro heq
    subst a
    have hd := degree_delete_edge_add_one G v w hwv.symm
    rw [Sym2.eq_swap] at hd
    rw [Nat.even_iff] at hv ha
    omega
  rwa [degree_delete_edge_of_ne G w v a haw hav] at ha

/-- Every retained vertex loses, rather than gains, even neighbours under an
even--even edge deletion. -/
theorem even_edge_puncture_eDegree_le
    (w v a : V) (hwv : G.Adj w v)
    (hw : Even (G.degree w)) (hv : Even (G.degree v)) :
    eDegree (G.deleteEdges {s(w, v)}) a ≤ eDegree G a := by
  apply Finset.card_le_card
  intro b hb
  obtain ⟨hab, hbe⟩ := (mem_evenNeighbors a b).mp hb
  exact (mem_evenNeighbors a b).mpr ⟨(SimpleGraph.deleteEdges_adj.mp hab).1,
    even_edge_puncture_even_preserved w v b hwv hw hv hbe⟩

/-- The connected ordinary degree-one puncture is a literal smaller bare
instance. Its minimality conclusion restores the deleted edge without
spending either the path budget or the prescribed endpoint reserve. -/
theorem bare_ordinary_degree_one_connected_puncture_false
    (z w v : evenVertices G) (h : V)
    (H : BareMinimalCounterexample G h (z : V))
    (C : (evenSubgraph G).ConnectedComponent)
    (hz : z ∉ C.supp) (hw : w ∈ C.supp)
    (hwv : G.Adj (w : V) (v : V))
    (hunique : ∀ a, G.Adj (w : V) a → Even (G.degree a) → a = (v : V))
    (hP : (G.deleteEdges {s((w : V), (v : V))}).Connected) : False := by
  classical
  obtain ⟨hhw, hhv⟩ := bare_not_mem_even_edge (z : V) (w : V) (v : V) h
    H.counterexample hwv w.property v.property
  have hzw : (z : V) ≠ (w : V) := by
    intro heq
    exact hz (by simpa only [show z = w from Subtype.ext heq] using hw)
  have hzv := ordinary_even_neighbor_ne_exception z w v C hz hw hwv
  obtain ⟨_, hhz, hhpos, hheven, hzeven, hhbare, hcap⟩ := H.counterexample.1
  have hinst : BareInstance (G.deleteEdges {s((w : V), (v : V))}) h (z : V) := by
    refine ⟨hP, hhz, ?_, ?_, ?_, ?_, ?_⟩
    · rwa [degree_delete_edge_of_ne G (w : V) (v : V) h hhw hhv]
    · rwa [degree_delete_edge_of_ne G (w : V) (v : V) h hhw hhv]
    · rwa [degree_delete_edge_of_ne G (w : V) (v : V) (z : V) hzw hzv]
    · exact bare_vertex_puncture_eDegree_zero h (w : V) (v : V) hwv hhw hhv
        w.property v.property hhbare
    · intro a ha hah haz
      exact (even_edge_puncture_eDegree_le (w : V) (v : V) a hwv
        w.property v.property).trans (hcap a
          (even_edge_puncture_even_preserved (w : V) (v : V) a hwv
            w.property v.property ha) hah haz)
  have hlt : (G.deleteEdges {s((w : V), (v : V))}).edgeFinset.card <
      G.edgeFinset.card := by
    apply Finset.card_lt_card
    apply SimpleGraph.edgeFinset_strict_mono
    refine lt_of_le_not_ge (G.deleteEdges_le _) ?_
    intro hle
    exact (SimpleGraph.deleteEdges_adj.mp (hle hwv)).2 rfl
  obtain ⟨D, hsize, hends⟩ := H.of_edge_smaller V _ h (z : V) rfl hlt hinst
  exact bare_counterexample_false_of_even_unique_puncture (z : V) (w : V) (v : V)
    h H.counterexample D hwv w.property v.property hunique hsize hends

/-- A puncture component retaining both designated vertices is an admissible
native bare instance. All degree and E-degree facts are transported through
the component's closed neighbourhoods. -/
theorem bare_even_puncture_component_instance
    (z w v : evenVertices G) (h : V)
    (H : BareMinimalCounterexample G h (z : V))
    (hwv : G.Adj (w : V) (v : V))
    (hzw : (z : V) ≠ (w : V)) (hzv : (z : V) ≠ (v : V))
    (C : (G.deleteEdges {s((w : V), (v : V))}).ConnectedComponent)
    (hh : h ∈ C.supp) (hz : (z : V) ∈ C.supp) :
    BareInstance ((G.deleteEdges {s((w : V), (v : V))}).induce C.supp)
      ⟨h, hh⟩ ⟨(z : V), hz⟩ := by
  classical
  let P := G.deleteEdges {s((w : V), (v : V))}
  have hclosed : ∀ a ∈ C.supp, P.neighborSet a ⊆ C.supp := by
    intro a ha b hab
    exact C.mem_supp_of_adj_mem_supp ha hab
  have hdeg : ∀ a : C.supp, (P.induce C.supp).degree a = P.degree a.val := by
    intro a
    exact SimpleGraph.degree_induce_of_neighborSet_subset (hclosed a.val a.property)
  obtain ⟨hhw, hhv⟩ := bare_not_mem_even_edge (z : V) (w : V) (v : V) h
    H.counterexample hwv w.property v.property
  obtain ⟨_, hhz, hhpos, hheven, hzeven, hhbare, hcap⟩ := H.counterexample.1
  have hhd : P.degree h = G.degree h :=
    degree_delete_edge_of_ne G (w : V) (v : V) h hhw hhv
  have hzd : P.degree (z : V) = G.degree (z : V) :=
    degree_delete_edge_of_ne G (w : V) (v : V) (z : V) hzw hzv
  refine ⟨C.connected_toSimpleGraph, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro heq
    exact hhz (congrArg Subtype.val heq)
  · rw [hdeg, hhd]
    exact hhpos
  · rw [hdeg, hhd]
    exact hheven
  · rw [hdeg, hzd]
    exact hzeven
  · rw [eDegree_induce_of_closed P C.supp hclosed]
    exact bare_vertex_puncture_eDegree_zero h (w : V) (v : V) hwv hhw hhv
      w.property v.property hhbare
  · intro a ha hah haz
    have haP : Even (P.degree a.val) := by rwa [hdeg] at ha
    have haG := even_edge_puncture_even_preserved (w : V) (v : V) a.val hwv
      w.property v.property haP
    have hah' : a.val ≠ h := fun heq => hah (Subtype.ext heq)
    have haz' : a.val ≠ (z : V) := fun heq => haz (Subtype.ext heq)
    rw [eDegree_induce_of_closed P C.supp hclosed]
    exact (even_edge_puncture_eDegree_le (w : V) (v : V) a.val hwv
      w.property v.property).trans (hcap a.val haG hah' haz')

/-- A proper puncture component retaining the two designated vertices gets
the bare ceiling and endpoint reserve from literal vertex minimality. -/
theorem bare_even_puncture_protected_component_conclusion
    (z w v : evenVertices G) (h r : V)
    (H : BareMinimalCounterexample G h (z : V))
    (hwv : G.Adj (w : V) (v : V))
    (hzw : (z : V) ≠ (w : V)) (hzv : (z : V) ≠ (v : V))
    (C : (G.deleteEdges {s((w : V), (v : V))}).ConnectedComponent)
    (hh : h ∈ C.supp) (hz : (z : V) ∈ C.supp) (hr : r ∉ C.supp) :
    BareConclusion ((G.deleteEdges {s((w : V), (v : V))}).induce C.supp) ⟨h, hh⟩ := by
  classical
  exact H.of_vertex_smaller C.supp _ ⟨h, hh⟩ ⟨(z : V), hz⟩
    (Fintype.card_subtype_lt hr)
    (bare_even_puncture_component_instance z w v h H hwv hzw hzv C hh hz)

/-- A nonprotected component of an ordinary degree-one puncture, missing
the exceptional hub, has the published floor bound: its even-degree cap is
transported from the original graph, and the ordinary-component guard
excludes SET. -/
theorem bare_ordinary_puncture_component_floor
    (z w v : evenVertices G) (h : V)
    (H : BareMinimalCounterexample G h (z : V))
    (C : (evenSubgraph G).ConnectedComponent)
    (hz : z ∉ C.supp) (hw : w ∈ C.supp)
    (hwv : G.Adj (w : V) (v : V))
    (hunique : ∀ a, G.Adj (w : V) a → Even (G.degree a) → a = (v : V))
    (D : (G.deleteEdges {s((w : V), (v : V))}).ConnectedComponent)
    (hzD : (z : V) ∉ D.supp) :
    HasPathBudget ((G.deleteEdges {s((w : V), (v : V))}).induce D.supp)
      (Fintype.card D.supp / 2) := by
  classical
  let P := G.deleteEdges {s((w : V), (v : V))}
  have hclosed : ∀ a ∈ D.supp, P.neighborSet a ⊆ D.supp := by
    intro a ha b hab
    exact D.mem_supp_of_adj_mem_supp ha hab
  have hcap : ∀ a, Even ((P.induce D.supp).degree a) →
      eDegree (P.induce D.supp) a ≤ 3 := by
    intro a ha
    have haP : Even (P.degree a.val) := by
      rwa [SimpleGraph.degree_induce_of_neighborSet_subset
        (hclosed a.val a.property)] at ha
    have haG := even_edge_puncture_even_preserved (w : V) (v : V) a.val hwv
      w.property v.property haP
    have haz : a.val ≠ (z : V) := fun heq => hzD (heq ▸ a.property)
    have hbound : eDegree G a.val ≤ 3 := by
      by_cases hah : a.val = h
      · rw [hah, H.counterexample.1.2.2.2.2.2.1]
        omega
      · exact H.counterexample.1.2.2.2.2.2.2 a.val haG hah haz
    rw [eDegree_induce_of_closed P D.supp hclosed]
    exact (even_edge_puncture_eDegree_le (w : V) (v : V) a.val hwv
      w.property v.property).trans hbound
  rcases floor_or_set (P.induce D.supp) D.connected_toSimpleGraph hcap with hf | hs
  · exact hf
  · exact (bare_ordinary_puncture_component_not_set z w v h H C hz hw
      H.counterexample.1.1 hwv hunique D hs).elim

/-- An even edge puncture away from the designated vertices cannot separate
them: an avoiding path supplied by the even-separator exclusion also avoids
the deleted edge. -/
theorem bare_even_puncture_designated_reachable
    (z w v : evenVertices G) (h : V)
    (H : BareCounterexample G h (z : V))
    (hwv : G.Adj (w : V) (v : V))
    (hzw : (z : V) ≠ (w : V)) :
    (G.deleteEdges {s((w : V), (v : V))}).Reachable h (z : V) := by
  classical
  obtain ⟨hhw, _⟩ := bare_not_mem_even_edge (z : V) (w : V) (v : V) h H
    hwv w.property v.property
  have hr : (G.induce {a | a ≠ (w : V)}).Reachable
      ⟨h, hhw⟩ ⟨(z : V), hzw⟩ := by
    by_contra hnot
    exact bare_even_separator_separating_hubs_false G (w : V) h (z : V) H
      hhw.symm hzw.symm w.property hnot
  let φ : (G.induce {a | a ≠ (w : V)}) →g
      (G.deleteEdges {s((w : V), (v : V))}) :=
    { toFun := Subtype.val
      map_rel' := by
        intro a b hab
        refine SimpleGraph.deleteEdges_adj.mpr ⟨hab, ?_⟩
        intro heq
        rcases Sym2.eq_iff.mp heq with ⟨haw, _⟩ | ⟨_, hbw⟩
        · exact a.property haw
        · exact b.property hbw }
  exact hr.map φ

/-- The ordinary unique-even-neighbour configuration is reducible, including
both connected and disconnected edge punctures. -/
theorem bare_ordinary_unique_even_neighbor_false
    (z w v : evenVertices G) (h : V)
    (H : BareMinimalCounterexample G h (z : V))
    (C : (evenSubgraph G).ConnectedComponent)
    (hz : z ∉ C.supp) (hw : w ∈ C.supp)
    (hwv : G.Adj (w : V) (v : V))
    (hunique : ∀ a, G.Adj (w : V) a → Even (G.degree a) → a = (v : V)) : False := by
  classical
  let P := G.deleteEdges {s((w : V), (v : V))}
  by_cases hP : P.Connected
  · exact bare_ordinary_degree_one_connected_puncture_false z w v h H C hz hw
      hwv hunique hP
  have hreached := bare_even_puncture_designated_reachable z w v h H.counterexample hwv
    (by intro heq; exact hz (by simpa only [show z = w from Subtype.ext heq] using hw))
  let C₀ := P.connectedComponentMk h
  have hh₀ : h ∈ C₀.supp := rfl
  have hz₀ : (z : V) ∈ C₀.supp := by
    exact SimpleGraph.ConnectedComponent.eq.mpr hreached.symm
  have hex : ∃ r, ¬ P.Reachable h r := by
    by_contra hnot
    push_neg at hnot
    exact hP (P.connected_iff_exists_forall_reachable.mpr ⟨h, hnot⟩)
  obtain ⟨r, hr⟩ := hex
  have hr₀ : r ∉ C₀.supp := by
    intro hrC
    exact hr (C₀.reachable_of_mem_supp hh₀ hrC)
  have hzw : (z : V) ≠ (w : V) := by
    intro heq
    exact hz (by simpa only [show z = w from Subtype.ext heq] using hw)
  have hzv := ordinary_even_neighbor_ne_exception z w v C hz hw hwv
  obtain ⟨D, hD, hhD⟩ := bare_even_puncture_protected_component_conclusion
    z w v h r H hwv hzw hzv C₀ hh₀ hz₀ hr₀
  apply bare_counterexample_false_of_even_unique_puncture_components (z : V)
    (w : V) (v : V) h H.counterexample D hwv w.property v.property hunique hD hhD
  intro B hB
  apply bare_ordinary_puncture_component_floor z w v h H C hz hw hwv hunique B
  intro hzB
  apply hB
  change P.connectedComponentMk (z : V) = B at hzB
  change P.connectedComponentMk (z : V) = C₀ at hz₀
  exact hzB.symm.trans hz₀

/-- Every originally even vertex in a component outside the exceptional
hub's component has E-degree different from one. -/
theorem bare_ordinary_no_degree_one
    (z w : evenVertices G) (h : V)
    (H : BareMinimalCounterexample G h (z : V))
    (C : (evenSubgraph G).ConnectedComponent)
    (hz : z ∉ C.supp) (hw : w ∈ C.supp) : eDegree G (w : V) ≠ 1 := by
  classical
  intro hdegree
  obtain ⟨v, hNv⟩ := Finset.card_eq_one.mp hdegree
  have hvN : v ∈ evenNeighbors G (w : V) := by rw [hNv]; simp
  obtain ⟨hwv, hvEven⟩ := (mem_evenNeighbors (w : V) v).mp hvN
  let ve : evenVertices G := ⟨v, hvEven⟩
  apply bare_ordinary_unique_even_neighbor_false z w ve h H C hz hw hwv
  intro a ha he
  have haN := (mem_evenNeighbors (w : V) a).mpr ⟨ha, he⟩
  rw [hNv] at haN
  exact Finset.mem_singleton.mp haN

end Gallai.TwoException
