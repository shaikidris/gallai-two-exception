/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.BareHubDegreeOne
public import Gallai.Inputs.EvenNeighborClosure
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Mathlib.Data.Fintype.EquivFin

@[expose] public section

/-! # First structural stage of the bare hub-component normal form

After the degree-one and degree-three corridor reductions, every private
vertex reachable from the exceptional hub has E-degree two.  This is the
degree input for the subsequent cycle and triangle-petal analysis.
-/

namespace Gallai.TwoException

open scoped Finset

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The two separated edge deletions used to puncture a hub cycle at four
successive vertices. -/
abbrev twoEdgeCyclePuncture (x a b c : V) : SimpleGraph V :=
  (G.deleteEdges {s(x, a)}).deleteEdges {s(b, c)}

/-- The two-edge puncture has decidable adjacency on its finite ambient type. -/
noncomputable instance instDecidableRelAdjTwoEdgeCyclePuncture (x a b c : V) :
    DecidableRel (twoEdgeCyclePuncture (G := G) x a b c).Adj := by
  change DecidableRel ((G.deleteEdges {s(x, a)}).deleteEdges {s(b, c)}).Adj
  infer_instance

private theorem odd_of_add_one_eq_even {u v : ℕ}
    (huv : u + 1 = v) (hv : Even v) : Odd u := by
  apply Nat.not_even_iff_odd.mp
  rintro ⟨k, hk⟩
  rcases hv with ⟨l, hl⟩
  omega

/-- Deleting the separated edges `xa` and `bc` of a four-vertex path flips
the degree parity at exactly its four displayed vertices.  This is the local
parity ledger for the long-cycle puncture; it carries no component or budget
claim. -/
theorem twoEdgeCyclePuncture_odd_profile
    (x a b c : V) (hxa : G.Adj x a) (hbc : G.Adj b c)
    (hxb : x ≠ b) (hxc : x ≠ c) (hab : a ≠ b) (hac : a ≠ c)
    (hxEven : Even (G.degree x)) (haEven : Even (G.degree a))
    (hbEven : Even (G.degree b)) (hcEven : Even (G.degree c)) :
    Odd ((twoEdgeCyclePuncture (G := G) x a b c).degree x) ∧
      Odd ((twoEdgeCyclePuncture (G := G) x a b c).degree a) ∧
      Odd ((twoEdgeCyclePuncture (G := G) x a b c).degree b) ∧
      Odd ((twoEdgeCyclePuncture (G := G) x a b c).degree c) := by
  classical
  have hbc₁ : (G.deleteEdges {s(x, a)}).Adj b c := by
    apply adj_delete_edge_of_ne G x a b c hbc
    intro he
    rw [Sym2.eq_iff] at he
    rcases he with ⟨hbx, _⟩ | ⟨hba, _⟩
    · exact hxb hbx.symm
    · exact hab hba.symm
  have hx₁ : (G.deleteEdges {s(x, a)}).degree x + 1 = G.degree x :=
    degree_delete_edge_add_one G x a hxa
  have hx₂ : (twoEdgeCyclePuncture (G := G) x a b c).degree x =
      (G.deleteEdges {s(x, a)}).degree x := by
    exact degree_delete_edge_of_ne (G.deleteEdges {s(x, a)}) b c x hxb hxc
  have ha₁ : (G.deleteEdges {s(x, a)}).degree a + 1 = G.degree a :=
    degree_delete_edge_add_one_other G x a hxa
  have ha₂ : (twoEdgeCyclePuncture (G := G) x a b c).degree a =
      (G.deleteEdges {s(x, a)}).degree a := by
    exact degree_delete_edge_of_ne (G.deleteEdges {s(x, a)}) b c a hab hac
  have hb₁ : (G.deleteEdges {s(x, a)}).degree b = G.degree b := by
    exact degree_delete_edge_of_ne G x a b hxb.symm hab.symm
  have hb₂ : (twoEdgeCyclePuncture (G := G) x a b c).degree b + 1 =
      (G.deleteEdges {s(x, a)}).degree b :=
    degree_delete_edge_add_one (G.deleteEdges {s(x, a)}) b c hbc₁
  have hc₁ : (G.deleteEdges {s(x, a)}).degree c = G.degree c := by
    exact degree_delete_edge_of_ne G x a c hxc.symm hac.symm
  have hc₂ : (twoEdgeCyclePuncture (G := G) x a b c).degree c + 1 =
      (G.deleteEdges {s(x, a)}).degree c :=
    degree_delete_edge_add_one_other (G.deleteEdges {s(x, a)}) b c hbc₁
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact odd_of_add_one_eq_even (by omega) hxEven
  · exact odd_of_add_one_eq_even (by omega) haEven
  · exact odd_of_add_one_eq_even (by omega) hbEven
  · exact odd_of_add_one_eq_even (by omega) hcEven

/-- A vertex outside the four displayed endpoints retains its degree under the
two-edge cycle puncture. -/
theorem twoEdgeCyclePuncture_degree_away
    (x a b c v : V) (hvx : v ≠ x) (hva : v ≠ a) (hvb : v ≠ b) (hvc : v ≠ c) :
    (twoEdgeCyclePuncture (G := G) x a b c).degree v = G.degree v := by
  classical
  have h₁ : (G.deleteEdges {s(x, a)}).degree v = G.degree v :=
    degree_delete_edge_of_ne G x a v hvx hva
  have h₂ : (twoEdgeCyclePuncture (G := G) x a b c).degree v =
      (G.deleteEdges {s(x, a)}).degree v :=
    degree_delete_edge_of_ne (G.deleteEdges {s(x, a)}) b c v hvb hvc
  omega

/-- The two-edge puncture introduces no new even vertices: every displayed
endpoint is odd afterwards, and every other degree is unchanged. -/
theorem twoEdgeCyclePuncture_even_preserved
    (x a b c : V) (hxa : G.Adj x a) (hbc : G.Adj b c)
    (hxb : x ≠ b) (hxc : x ≠ c) (hab : a ≠ b) (hac : a ≠ c)
    (hxEven : Even (G.degree x)) (haEven : Even (G.degree a))
    (hbEven : Even (G.degree b)) (hcEven : Even (G.degree c)) :
    ∀ v, Even ((twoEdgeCyclePuncture (G := G) x a b c).degree v) →
      Even (G.degree v) := by
  intro v hv
  obtain ⟨hxOdd, haOdd, hbOdd, hcOdd⟩ :=
    twoEdgeCyclePuncture_odd_profile (G := G) x a b c hxa hbc hxb hxc hab hac
      hxEven haEven hbEven hcEven
  by_cases hvx : v = x
  · subst v
    exact False.elim ((Nat.not_even_iff_odd.mpr hxOdd) hv)
  by_cases hva : v = a
  · subst v
    exact False.elim ((Nat.not_even_iff_odd.mpr haOdd) hv)
  by_cases hvb : v = b
  · subst v
    exact False.elim ((Nat.not_even_iff_odd.mpr hbOdd) hv)
  by_cases hvc : v = c
  · subst v
    exact False.elim ((Nat.not_even_iff_odd.mpr hcOdd) hv)
  rw [twoEdgeCyclePuncture_degree_away (G := G) x a b c v hvx hva hvb hvc] at hv
  exact hv

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- The literal two-edge cycle puncture is a subgraph of the original graph. -/
theorem twoEdgeCyclePuncture_le (x a b c : V) :
    twoEdgeCyclePuncture (G := G) x a b c ≤ G := by
  intro u v huv
  exact (SimpleGraph.deleteEdges_adj.mp (SimpleGraph.deleteEdges_adj.mp huv).1).1

omit [DecidableEq V] in
/-- A vertex has E-degree zero when none of its neighbours is even in the
displayed graph. -/
theorem eDegree_eq_zero_of_no_even_neighbor
    {J : SimpleGraph V} [DecidableRel J.Adj] (u : V)
    (hno : ∀ w, J.Adj u w → Even (J.degree w) → False) :
    eDegree J u = 0 := by
  change (evenNeighbors J u).card = 0
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro w hw
  obtain ⟨huw, hwEven⟩ := (mem_evenNeighbors (G := J) u w).mp hw
  exact hno w huw hwEven

/-- An edge from a distinguished hub to an even-degree vertex cannot be a
bridge when every other vertex has even degree.  The component of the leaf
after deleting a supposed bridge would contain the leaf as its only
odd-degree vertex, contradicting the handshaking lemma. -/
theorem nonbridge_of_even_degree_off_hub
    {K : SimpleGraph V} [DecidableRel K.Adj] (x a : V) (hxa : K.Adj x a)
    (heven : ∀ v, v ≠ x → Even (K.degree v)) :
    ¬ K.IsBridge s(x, a) := by
  classical
  intro hbridge
  let J : SimpleGraph V := K.deleteEdges {s(x, a)}
  let C : J.ConnectedComponent := J.connectedComponentMk a
  have haC : a ∈ C.supp := by simp [C]
  have hxC : x ∉ C.supp := by
    intro hxC
    have hreach : J.Reachable x a :=
      (C.reachable_of_mem_supp hxC haC)
    exact (SimpleGraph.isBridge_iff.mp hbridge) (by simpa [J] using hreach)
  have hclosed : ∀ v ∈ C.supp, J.neighborSet v ⊆ C.supp := by
    intro v hv w hw
    exact C.mem_supp_of_adj_mem_supp hv hw
  have haEven : Even (K.degree a) := heven a hxa.ne.symm
  have haJ : J.degree a + 1 = K.degree a := by
    simpa [J] using degree_delete_edge_add_one_other K x a hxa
  have haOdd : Odd ((J.induce C.supp).degree ⟨a, haC⟩) := by
    rw [SimpleGraph.degree_induce_of_neighborSet_subset (hclosed a haC)]
    exact odd_of_add_one_eq_even haJ haEven
  obtain ⟨v, hva, hvOdd⟩ :=
    (J.induce C.supp).exists_ne_odd_degree_of_exists_odd_degree ⟨a, haC⟩ haOdd
  have hvA : (v : V) ≠ a := by
    intro hEq
    exact hva (Subtype.ext hEq)
  have hvX : (v : V) ≠ x := by
    intro hEq
    apply hxC
    simpa [hEq] using v.property
  have hvJ : J.degree (v : V) = K.degree (v : V) := by
    simpa [J] using degree_delete_edge_of_ne K x a (v : V) hvX hvA
  have hvOddK : Odd (K.degree (v : V)) := by
    rw [SimpleGraph.degree_induce_of_neighborSet_subset (hclosed (v : V) v.property), hvJ] at hvOdd
    exact hvOdd
  exact (Nat.not_even_iff_odd.mpr hvOddK) (heven (v : V) hvX)

/-- A non-bridge edge lies on a simple cycle.  This packages the exact
bridge definition into the cycle witness consumed by the hub-petal route. -/
theorem nonbridge_adj_exists_cycle
    {K : SimpleGraph V} [DecidableRel K.Adj] (x a : V) (hxa : K.Adj x a)
    (hnotBridge : ¬ K.IsBridge s(x, a)) :
    ∃ (u : V) (p : K.Walk u u), p.IsCycle ∧ s(x, a) ∈ p.edges := by
  have hreach : (K.deleteEdges {s(x, a)}).Reachable x a := by
    by_contra hnotReach
    exact hnotBridge (SimpleGraph.isBridge_iff.mpr hnotReach)
  exact SimpleGraph.adj_and_reachable_delete_edges_iff_exists_cycle.mp
    ⟨hxa, hreach⟩

/-- A zero E-degree centre has no neighbour with zero endpoint count in any
path decomposition: zero endpoint count forces even degree by the endpoint
parity invariant. -/
theorem zero_endpoint_neighbor_card_eq_zero_of_eDegree_zero
    {J : SimpleGraph V} [DecidableRel J.Adj]
    (D : Decomposition J) (u : V) (hzero : eDegree J u = 0) :
    #{v ∈ J.neighborFinset u | D.endpointCount v = 0} = 0 := by
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro v hv
  obtain ⟨hvN, hvEnd⟩ := Finset.mem_filter.mp hv
  have huv : J.Adj u v := (SimpleGraph.mem_neighborFinset _ _ _).mp hvN
  have hmod := D.endpointCount_mod_two v
  rw [hvEnd] at hmod
  have hvEven : Even (J.degree v) := by
    rw [Nat.even_iff]
    omega
  have hmem : v ∈ evenNeighbors J u :=
    (mem_evenNeighbors (G := J) u v).mpr ⟨huv, hvEven⟩
  change (evenNeighbors J u).card = 0 at hzero
  have hempty : evenNeighbors J u = ∅ := Finset.card_eq_zero.mp hzero
  rw [hempty] at hmem
  simpa using hmem

/-- In a punctured four-vertex even path `x-a-b-c`, the two consecutive
private vertices `a,b` have E-degree zero, provided their original
E-degree-two neighbourhoods are the displayed cycle neighbours. -/
theorem twoEdgeCyclePuncture_middle_eDegree_zero
    (x a b c : V) (hxa : G.Adj x a) (habAdj : G.Adj a b) (hbc : G.Adj b c)
    (hxb : x ≠ b) (hxc : x ≠ c) (hab : a ≠ b) (hac : a ≠ c)
    (hxEven : Even (G.degree x)) (haEven : Even (G.degree a))
    (hbEven : Even (G.degree b)) (hcEven : Even (G.degree c))
    (haDeg : eDegree G a = 2) (hbDeg : eDegree G b = 2) :
    eDegree (twoEdgeCyclePuncture (G := G) x a b c) a = 0 ∧
      eDegree (twoEdgeCyclePuncture (G := G) x a b c) b = 0 := by
  have hpunctureEven := twoEdgeCyclePuncture_even_preserved (G := G) x a b c
    hxa hbc hxb hxc hab hac hxEven haEven hbEven hcEven
  obtain ⟨hxOdd, haOdd, hbOdd, hcOdd⟩ :=
    twoEdgeCyclePuncture_odd_profile (G := G) x a b c hxa hbc hxb hxc hab hac
      hxEven haEven hbEven hcEven
  have haxmem : x ∈ evenNeighbors G a :=
    (mem_evenNeighbors (G := G) a x).mpr ⟨hxa.symm, hxEven⟩
  have habmem : b ∈ evenNeighbors G a :=
    (mem_evenNeighbors (G := G) a b).mpr ⟨habAdj, hbEven⟩
  have hbamem : a ∈ evenNeighbors G b :=
    (mem_evenNeighbors (G := G) b a).mpr ⟨habAdj.symm, haEven⟩
  have hbcmem : c ∈ evenNeighbors G b :=
    (mem_evenNeighbors (G := G) b c).mpr ⟨hbc, hcEven⟩
  refine ⟨?_, ?_⟩
  · apply eDegree_eq_zero_of_no_even_neighbor
    intro w haw hwEven
    have hwEvenG := hpunctureEven w hwEven
    have hawG := twoEdgeCyclePuncture_le (G := G) x a b c haw
    rcases even_neighbors_pair_of_degree_two a x b haDeg haxmem habmem hxb w hawG hwEvenG with
      rfl | rfl
    · exact (Nat.not_even_iff_odd.mpr hxOdd) hwEven
    · exact (Nat.not_even_iff_odd.mpr hbOdd) hwEven
  · apply eDegree_eq_zero_of_no_even_neighbor
    intro w hbw hwEven
    have hwEvenG := hpunctureEven w hwEven
    have hbwG := twoEdgeCyclePuncture_le (G := G) x a b c hbw
    rcases even_neighbors_pair_of_degree_two b a c hbDeg hbamem hbcmem hac w hbwG hwEvenG with
      rfl | rfl
    · exact (Nat.not_even_iff_odd.mpr haOdd) hwEven
    · exact (Nat.not_even_iff_odd.mpr hcOdd) hwEven

/-- The first long-cycle restoration inequality is automatic on the puncture:
`b` has E-degree zero, hence no passing neighbour, while `c` is odd and
therefore occurs as a path endpoint. -/
theorem twoEdgeCyclePuncture_first_restoration_strict
    (x a b c : V) (D : Decomposition (twoEdgeCyclePuncture (G := G) x a b c))
    (hbZero : eDegree (twoEdgeCyclePuncture (G := G) x a b c) b = 0)
    (hcOdd : Odd ((twoEdgeCyclePuncture (G := G) x a b c).degree c)) :
    #{v ∈ (twoEdgeCyclePuncture (G := G) x a b c).neighborFinset b |
        D.endpointCount v = 0} < D.endpointCount c := by
  rw [zero_endpoint_neighbor_card_eq_zero_of_eDegree_zero D b hbZero]
  exact D.endpointCount_pos_of_odd_degree c hcOdd

/-- After restoring `bc` towards `b`, the second long-cycle restoration
inequality is also strict.  A zero-endpoint neighbour of `a` cannot be `b`,
which has just received an endpoint; cannot be `c`, which is not an
even-neighbour of the degree-two vertex `a` in the original graph; and cannot
be any other vertex, since that would already be an even zero-endpoint
neighbour of `a` in the puncture. -/
theorem twoEdgeCyclePuncture_second_restoration_strict
    (x a b c : V)
    (D : Decomposition (twoEdgeCyclePuncture (G := G) x a b c))
    (E : Decomposition ((twoEdgeCyclePuncture (G := G) x a b c) ⊔
      SimpleGraph.edge b c))
    (hends : ∀ w, E.endpointCount w + (if c = w then 1 else 0) =
      D.endpointCount w + if b = w then 1 else 0)
    (haZero : eDegree (twoEdgeCyclePuncture (G := G) x a b c) a = 0)
    (hxOdd : Odd ((twoEdgeCyclePuncture (G := G) x a b c).degree x))
    (hxa : G.Adj x a) (habAdj : G.Adj a b) (hbc : G.Adj b c)
    (hxb : x ≠ b) (hxc : x ≠ c) (hab : a ≠ b) (hac : a ≠ c)
    (hxEven : Even (G.degree x)) (hbEven : Even (G.degree b))
    (hcEven : Even (G.degree c)) (haDeg : eDegree G a = 2) :
    #{v ∈ ((twoEdgeCyclePuncture (G := G) x a b c) ⊔
        SimpleGraph.edge b c).neighborFinset a | E.endpointCount v = 0} <
      E.endpointCount x := by
  classical
  have hbPos : 0 < E.endpointCount b := by
    have hb := hends b
    simp [hbc.ne, hbc.ne.symm] at hb
    omega
  have hxPos : 0 < E.endpointCount x := by
    have hxD : 0 < D.endpointCount x := D.endpointCount_pos_of_odd_degree x hxOdd
    have hx := hends x
    simp [hxb, hxb.symm, hxc, hxc.symm] at hx
    omega
  have hacNot : ¬ ((twoEdgeCyclePuncture (G := G) x a b c) ⊔
      SimpleGraph.edge b c).Adj a c := by
    intro hacQ
    rw [SimpleGraph.sup_adj, SimpleGraph.edge_adj] at hacQ
    rcases hacQ with hacP | hacEdge
    · have hacG := twoEdgeCyclePuncture_le (G := G) x a b c hacP
      have haxmem : x ∈ evenNeighbors G a :=
        (mem_evenNeighbors (G := G) a x).mpr ⟨hxa.symm, hxEven⟩
      have habmem : b ∈ evenNeighbors G a :=
        (mem_evenNeighbors (G := G) a b).mpr ⟨habAdj, hbEven⟩
      rcases even_neighbors_pair_of_degree_two a x b haDeg haxmem habmem hxb
        c hacG hcEven with hcx | hcb
      · exact hxc hcx.symm
      · exact hbc.ne hcb.symm
    · rcases hacEdge with ⟨hab', _⟩ | ⟨hac', _⟩
      · exact hab hab'
      · exact hac hac'
  have hzero : #{v ∈ ((twoEdgeCyclePuncture (G := G) x a b c) ⊔
      SimpleGraph.edge b c).neighborFinset a | E.endpointCount v = 0} = 0 := by
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro v hv
    obtain ⟨hva, hvEnd⟩ := Finset.mem_filter.mp hv
    by_cases hvb : v = b
    · subst v
      exact (Nat.ne_of_gt hbPos) hvEnd
    by_cases hvc : v = c
    · subst v
      exact hacNot ((SimpleGraph.mem_neighborFinset _ _ _).mp hva)
    have hvaP : (twoEdgeCyclePuncture (G := G) x a b c).Adj a v := by
      have hvaAdj : ((twoEdgeCyclePuncture (G := G) x a b c) ⊔
          SimpleGraph.edge b c).Adj a v :=
        (SimpleGraph.mem_neighborFinset _ _ _).mp hva
      rw [SimpleGraph.sup_adj, SimpleGraph.edge_adj] at hvaAdj
      rcases hvaAdj with hP | hEdge
      · exact hP
      rcases hEdge with ⟨hab', hcv⟩ | ⟨hac', hbv⟩
      · exact (hab hab').elim
      · exact (hac hac').elim
    have hvD : D.endpointCount v = 0 := by
      have hv := hends v
      simp [hvb, Ne.symm hvb, hvc, Ne.symm hvc] at hv
      omega
    have hvEven : Even ((twoEdgeCyclePuncture (G := G) x a b c).degree v) := by
      have hmod := D.endpointCount_mod_two v
      rw [hvD] at hmod
      rw [Nat.even_iff]
      omega
    have hmem : v ∈ evenNeighbors (twoEdgeCyclePuncture (G := G) x a b c) a :=
      (mem_evenNeighbors (G := twoEdgeCyclePuncture (G := G) x a b c) a v).mpr
        ⟨hvaP, hvEven⟩
    change (evenNeighbors (twoEdgeCyclePuncture (G := G) x a b c) a).card = 0 at haZero
    have hempty : evenNeighbors (twoEdgeCyclePuncture (G := G) x a b c) a = ∅ :=
      Finset.card_eq_zero.mp haZero
    rw [hempty] at hmem
    simpa using hmem
  rw [hzero]
  exact hxPos

/-- Attaching a pendant edge at an even vertex disjoint from the punctured
four-vertex path makes all four puncture vertices, the attachment, and the
fresh leaf odd.  This is the exact local input used by the long-cycle
floor-or-SET budget argument. -/
theorem twoEdgeCyclePuncture_pendant_odd_profile
    (h x a b c : V) (hxa : G.Adj x a) (hbc : G.Adj b c)
    (hxb : x ≠ b) (hxc : x ≠ c) (hab : a ≠ b) (hac : a ≠ c)
    (hhx : h ≠ x) (hha : h ≠ a) (hhb : h ≠ b) (hhc : h ≠ c)
    (hhEven : Even (G.degree h)) (hxEven : Even (G.degree x))
    (haEven : Even (G.degree a)) (hbEven : Even (G.degree b))
    (hcEven : Even (G.degree c)) :
    Odd ((pendantExtension (twoEdgeCyclePuncture (G := G) x a b c) h).degree (.inl x)) ∧
      Odd ((pendantExtension (twoEdgeCyclePuncture (G := G) x a b c) h).degree (.inl a)) ∧
      Odd ((pendantExtension (twoEdgeCyclePuncture (G := G) x a b c) h).degree (.inl b)) ∧
      Odd ((pendantExtension (twoEdgeCyclePuncture (G := G) x a b c) h).degree (.inl c)) ∧
      Odd ((pendantExtension (twoEdgeCyclePuncture (G := G) x a b c) h).degree (.inl h)) ∧
      Odd ((pendantExtension (twoEdgeCyclePuncture (G := G) x a b c) h).degree (.inr ())) := by
  classical
  obtain ⟨hxOdd, haOdd, hbOdd, hcOdd⟩ :=
    twoEdgeCyclePuncture_odd_profile (G := G) x a b c hxa hbc hxb hxc hab hac
      hxEven haEven hbEven hcEven
  have hhP : Even ((twoEdgeCyclePuncture (G := G) x a b c).degree h) := by
    rw [twoEdgeCyclePuncture_degree_away (G := G) x a b c h hhx hha hhb hhc]
    exact hhEven
  refine ⟨?_, ?_, ?_, ?_, ?_, pendantExtension_odd_new _ _⟩
  · exact (pendantExtension_odd_old_ne _ h x hhx.symm).mpr hxOdd
  · exact (pendantExtension_odd_old_ne _ h a hha.symm).mpr haOdd
  · exact (pendantExtension_odd_old_ne _ h b hhb.symm).mpr hbOdd
  · exact (pendantExtension_odd_old_ne _ h c hhc.symm).mpr hcOdd
  · exact (pendantExtension_odd_attach_iff _ h).mpr hhP

/-- A bare-instance cap transfers through the two-edge cycle puncture and its
pendant extension once the puncture's even-preservation, odd exceptional hub,
and retained-even bare hub facts have been supplied. -/
theorem twoEdgeCyclePuncture_pendant_cap_of_bare
    (h x a b c : V)
    (hhP : Even ((twoEdgeCyclePuncture (G := G) x a b c).degree h))
    (hxOddP : Odd ((twoEdgeCyclePuncture (G := G) x a b c).degree x))
    (hbare : eDegree G h = 0)
    (hpunctureEven : ∀ v, Even ((twoEdgeCyclePuncture (G := G) x a b c).degree v) →
      Even (G.degree v))
    (hcap : ∀ v, Even (G.degree v) → v ≠ h → v ≠ x → eDegree G v ≤ 3) :
    ∀ v, Even ((pendantExtension (twoEdgeCyclePuncture (G := G) x a b c) h).degree v) →
      eDegree (pendantExtension (twoEdgeCyclePuncture (G := G) x a b c) h) v ≤ 3 := by
  have hpunctureCap : ∀ v, Even ((twoEdgeCyclePuncture (G := G) x a b c).degree v) →
      eDegree (twoEdgeCyclePuncture (G := G) x a b c) v ≤ 3 := by
    intro v hv
    have hle : eDegree (twoEdgeCyclePuncture (G := G) x a b c) v ≤ eDegree G v :=
      eDegree_le_of_subgraph_of_even_preservation
        (G := G) (J := twoEdgeCyclePuncture (G := G) x a b c)
        (twoEdgeCyclePuncture_le (G := G) x a b c) hpunctureEven v
    by_cases hvh : v = h
    · subst v
      rw [hbare] at hle
      omega
    by_cases hvx : v = x
    · subst v
      exact False.elim ((Nat.not_even_iff_odd.mpr hxOddP) hv)
    exact hle.trans (hcap v (hpunctureEven v hv) hvh hvx)
  exact pendantExtension_cap (twoEdgeCyclePuncture (G := G) x a b c) h hhP hpunctureCap

/-- The preceding cap transfer specialized to a literal bare minimal
counterexample.  A long-cycle witness supplies the three non-hub even
vertices and their disjointness from the bare prescribed vertex; no extra
ambient cap assumption is introduced. -/
theorem twoEdgeCyclePuncture_pendant_cap_of_bare_counterexample
    (h x a b c : V) (H : BareMinimalCounterexample G h x)
    (hxa : G.Adj x a) (hbc : G.Adj b c)
    (hxb : x ≠ b) (hxc : x ≠ c) (hab : a ≠ b) (hac : a ≠ c)
    (hha : h ≠ a) (hhb : h ≠ b) (hhc : h ≠ c)
    (haEven : Even (G.degree a)) (hbEven : Even (G.degree b))
    (hcEven : Even (G.degree c)) :
    ∀ v, Even ((pendantExtension (twoEdgeCyclePuncture (G := G) x a b c) h).degree v) →
      eDegree (pendantExtension (twoEdgeCyclePuncture (G := G) x a b c) h) v ≤ 3 := by
  rcases H.counterexample.1 with ⟨_, hhx, _, hhEven, hxEven, hbare, hcap⟩
  have hhP : Even ((twoEdgeCyclePuncture (G := G) x a b c).degree h) := by
    rw [twoEdgeCyclePuncture_degree_away (G := G) x a b c h hhx hha hhb hhc]
    exact hhEven
  have hxOddP : Odd ((twoEdgeCyclePuncture (G := G) x a b c).degree x) :=
    (twoEdgeCyclePuncture_odd_profile (G := G) x a b c hxa hbc hxb hxc hab hac
      hxEven haEven hbEven hcEven).1
  exact twoEdgeCyclePuncture_pendant_cap_of_bare (G := G) h x a b c hhP hxOddP hbare
    (twoEdgeCyclePuncture_even_preserved (G := G) x a b c hxa hbc hxb hxc hab hac
      hxEven haEven hbEven hcEven) hcap

/-- A pendant extension preserves an E-degree-zero witness at an old vertex
different from the attachment: the attachment and the fresh leaf are both
odd, and every remaining even neighbour would already have been an even
neighbour before the extension. -/
theorem pendantExtension_eDegree_zero_old_ne
    {J : SimpleGraph V} [DecidableRel J.Adj] (h u : V) (huh : u ≠ h)
    (hhEven : Even (J.degree h)) (hzero : eDegree J u = 0) :
    eDegree (pendantExtension J h) (.inl u) = 0 := by
  apply eDegree_eq_zero_of_no_even_neighbor
  intro w huw hwEven
  cases w with
  | inr w =>
    cases w
    exact (Nat.not_even_iff_odd.mpr (pendantExtension_odd_new J h)) hwEven
  | inl v =>
    have huv : J.Adj u v := (pendantExtension_adj_old J h u v).mp huw
    by_cases hvh : v = h
    · subst v
      exact (Nat.not_even_iff_odd.mpr
        ((pendantExtension_odd_attach_iff J h).mpr hhEven)) hwEven
    · have hvEven : Even (J.degree v) :=
        (pendantExtension_even_old_ne J h v hvh).mp hwEven
      have hmem : v ∈ evenNeighbors J u :=
        (mem_evenNeighbors (G := J) u v).mpr ⟨huv, hvEven⟩
      have hempty : evenNeighbors J u = ∅ := by
        apply Finset.card_eq_zero.mp
        exact hzero
      rw [hempty] at hmem
      simpa using hmem

/-- Away from an even pendant attachment, every even neighbour in the
extension maps to an old even neighbour. -/
theorem pendantExtension_eDegree_le_old_ne
    {J : SimpleGraph V} [DecidableRel J.Adj] (h u : V) (huh : u ≠ h)
    (hhEven : Even (J.degree h)) :
    eDegree (pendantExtension J h) (.inl u) ≤ eDegree J u := by
  have hsubset : evenNeighbors (pendantExtension J h) (.inl u) ⊆
      (evenNeighbors J u).map (Function.Embedding.inl : V ↪ V ⊕ Unit) := by
    intro w hw
    obtain ⟨huw, hwEven⟩ :=
      (mem_evenNeighbors (G := pendantExtension J h) (.inl u) w).mp hw
    cases w with
    | inr w =>
      cases w
      exact False.elim
        ((Nat.not_even_iff_odd.mpr (pendantExtension_odd_new J h)) hwEven)
    | inl v =>
      have huv : J.Adj u v := (pendantExtension_adj_old J h u v).mp huw
      have hvh : v ≠ h := by
        intro hvh
        subst v
        exact False.elim ((Nat.not_even_iff_odd.mpr
          ((pendantExtension_odd_attach_iff J h).mpr hhEven)) hwEven)
      have hvEven : Even (J.degree v) :=
        (pendantExtension_even_old_ne J h v hvh).mp hwEven
      exact Finset.mem_map.mpr ⟨v,
        (mem_evenNeighbors (G := J) u v).mpr ⟨huv, hvEven⟩, rfl⟩
  change (evenNeighbors (pendantExtension J h) (.inl u)).card ≤
    (evenNeighbors J u).card
  rw [← Finset.card_map (Function.Embedding.inl : V ↪ V ⊕ Unit)]
  exact Finset.card_le_card hsubset

/-- The component-local odd SET obstruction extends to an odd vertex with at
most one even neighbour, since every odd vertex in a SET graph has at least
two even neighbours. -/
theorem component_not_set_of_odd_eDegree_le_one
    {J : SimpleGraph V} [DecidableRel J.Adj]
    (C : J.ConnectedComponent) [DecidablePred (· ∈ C.supp)]
    (v : V) (hv : v ∈ C.supp) (hodd : Odd (J.degree v))
    (hle : eDegree J v ≤ 1) :
    ¬ IsSET (J.induce C.supp) := by
  intro hset
  have hclosed : ∀ u ∈ C.supp, J.neighborSet u ⊆ C.supp := by
    intro u hu w huw
    exact C.mem_supp_of_adj_mem_supp hu huw
  have hoddC : Odd ((J.induce C.supp).degree ⟨v, hv⟩) := by
    rw [SimpleGraph.degree_induce_of_neighborSet_subset (hclosed v hv)]
    exact hodd
  have hleC : eDegree (J.induce C.supp) ⟨v, hv⟩ ≤ 1 := by
    rw [eDegree_induce_of_closed J C.supp hclosed]
    exact hle
  have htwo := hset.odd_neighbors ⟨v, hv⟩ hoddC
  omega

/-- Deleting `bc` from the two-edge cycle puncture leaves the final displayed
vertex `c` with at most one even neighbour: all surviving even neighbours are
old ones, but the old even neighbour `b` has become odd. -/
theorem twoEdgeCyclePuncture_end_eDegree_le_one
    (x a b c : V) (hxa : G.Adj x a) (hbc : G.Adj b c)
    (hxb : x ≠ b) (hxc : x ≠ c) (hab : a ≠ b) (hac : a ≠ c)
    (hxEven : Even (G.degree x)) (haEven : Even (G.degree a))
    (hbEven : Even (G.degree b)) (hcEven : Even (G.degree c))
    (hcDeg : eDegree G c = 2) :
    eDegree (twoEdgeCyclePuncture (G := G) x a b c) c ≤ 1 := by
  have hpunctureEven := twoEdgeCyclePuncture_even_preserved (G := G) x a b c
    hxa hbc hxb hxc hab hac hxEven haEven hbEven hcEven
  have hbOdd := (twoEdgeCyclePuncture_odd_profile (G := G) x a b c
    hxa hbc hxb hxc hab hac hxEven haEven hbEven hcEven).2.2.1
  have hbmem : b ∈ evenNeighbors G c :=
    (mem_evenNeighbors (G := G) c b).mpr ⟨hbc.symm, hbEven⟩
  have herase : ((evenNeighbors G c).erase b).card = 1 := by
    have hcard := Finset.card_erase_add_one hbmem
    change (evenNeighbors G c).card = 2 at hcDeg
    omega
  have hsubset : evenNeighbors (twoEdgeCyclePuncture (G := G) x a b c) c ⊆
      (evenNeighbors G c).erase b := by
    intro w hw
    obtain ⟨hcw, hwEven⟩ :=
      (mem_evenNeighbors (G := twoEdgeCyclePuncture (G := G) x a b c) c w).mp hw
    have hcwG := twoEdgeCyclePuncture_le (G := G) x a b c hcw
    have hwEvenG := hpunctureEven w hwEven
    apply Finset.mem_erase.mpr
    refine ⟨?_, (mem_evenNeighbors (G := G) c w).mpr ⟨hcwG, hwEvenG⟩⟩
    intro hwb
    subst w
    exact (Nat.not_even_iff_odd.mpr hbOdd) hwEven
  change (evenNeighbors (twoEdgeCyclePuncture (G := G) x a b c) c).card ≤ 1
  exact (Finset.card_le_card hsubset).trans_eq herase

/-- The `c`-side component in the long-cycle pendant auxiliary is not SET:
the puncture makes `c` odd and leaves it with at most one even neighbour. -/
theorem twoEdgeCyclePuncture_pendant_end_component_not_set
    (h x a b c : V) (hxa : G.Adj x a) (hbc : G.Adj b c)
    (hxb : x ≠ b) (hxc : x ≠ c) (hab : a ≠ b) (hac : a ≠ c)
    (hhx : h ≠ x) (hha : h ≠ a) (hhb : h ≠ b) (hhc : h ≠ c)
    (hhEven : Even (G.degree h)) (hxEven : Even (G.degree x))
    (haEven : Even (G.degree a)) (hbEven : Even (G.degree b))
    (hcEven : Even (G.degree c)) (hcDeg : eDegree G c = 2)
    (C : (pendantExtension (twoEdgeCyclePuncture (G := G) x a b c) h).ConnectedComponent)
    [DecidablePred (· ∈ C.supp)]
    (hcC : (.inl c : V ⊕ Unit) ∈ C.supp) :
    ¬ IsSET ((pendantExtension (twoEdgeCyclePuncture (G := G) x a b c) h).induce C.supp) := by
  let J : SimpleGraph V := twoEdgeCyclePuncture (G := G) x a b c
  have hhJ : Even (J.degree h) := by
    dsimp [J]
    rw [twoEdgeCyclePuncture_degree_away (G := G) x a b c h hhx hha hhb hhc]
    exact hhEven
  have hcOdd := (twoEdgeCyclePuncture_odd_profile (G := G) x a b c
    hxa hbc hxb hxc hab hac hxEven haEven hbEven hcEven).2.2.2
  have hcOddP : Odd ((pendantExtension J h).degree (.inl c)) :=
    (pendantExtension_odd_old_ne J h c hhc.symm).mpr hcOdd
  have hcLe : eDegree J c ≤ 1 :=
    twoEdgeCyclePuncture_end_eDegree_le_one (G := G) x a b c hxa hbc hxb hxc hab hac
      hxEven haEven hbEven hcEven hcDeg
  have hcLeP : eDegree (pendantExtension J h) (.inl c) ≤ 1 :=
    (pendantExtension_eDegree_le_old_ne h c hhc.symm hhJ).trans hcLe
  exact component_not_set_of_odd_eDegree_le_one C (.inl c) hcC hcOddP hcLeP

/-- A SET component of a pendant extension containing an old vertex and no
fresh leaf contains a second, distinct old vertex. -/
theorem pendantExtension_set_component_exists_second_old_of_mem
    {J : SimpleGraph V} [DecidableRel J.Adj] (h v : V)
    (C : (pendantExtension J h).ConnectedComponent)
    [DecidablePred (· ∈ C.supp)]
    (hv : (.inl v : V ⊕ Unit) ∈ C.supp)
    (hleaf : (.inr () : V ⊕ Unit) ∉ C.supp)
    (hset : IsSET ((pendantExtension J h).induce C.supp)) :
    ∃ t : V, (.inl t : V ⊕ Unit) ∈ C.supp ∧ t ≠ v := by
  let vC : C.supp := ⟨.inl v, hv⟩
  have hdegree : 2 ≤ ((pendantExtension J h).induce C.supp).degree vC :=
    hset.two_le_degree vC
  have hcard : 0 < (((pendantExtension J h).induce C.supp).neighborFinset vC).card := by
    rw [SimpleGraph.card_neighborFinset_eq_degree]
    omega
  obtain ⟨z, hz⟩ := Finset.card_pos.mp hcard
  cases hzval : z.val with
  | inl t =>
    have hzC : (.inl t : V ⊕ Unit) ∈ C.supp := by
      simpa [hzval] using z.property
    refine ⟨t, hzC, ?_⟩
    intro htv
    have hAdj : ((pendantExtension J h).induce C.supp).Adj vC z := by
      simpa using hz
    apply hAdj.ne
    apply Subtype.ext
    simp [vC, hzval, htv]
  | inr w =>
    cases w
    exact False.elim (hleaf (by simpa [hzval] using z.property))

/-- If an old vertex lies in a pendant component but the fresh leaf does not,
then the pendant attachment itself also lies outside that component. -/
theorem pendantExtension_attachment_not_mem_of_leaf_not_mem
    {J : SimpleGraph V} [DecidableRel J.Adj] (h : V)
    (C : (pendantExtension J h).ConnectedComponent)
    (hleaf : (.inr () : V ⊕ Unit) ∉ C.supp) :
    (.inl h : V ⊕ Unit) ∉ C.supp := by
  intro hh
  apply hleaf
  exact C.mem_supp_of_adj_mem_supp hh
    ((pendantExtension_adj_new J h (.inl h)).mpr rfl).symm

/-- Once a pendant-auxiliary component contains `x` and avoids the other
three deleted-edge endpoints, every original boundary edge is oriented from
`x` to `a`. -/
theorem twoEdgeCyclePuncture_pendant_component_crossing_is_xa
    (h x a b c u v : V)
    (C : (pendantExtension (twoEdgeCyclePuncture (G := G) x a b c) h).ConnectedComponent)
    (ha : (.inl a : V ⊕ Unit) ∉ C.supp)
    (hb : (.inl b : V ⊕ Unit) ∉ C.supp)
    (hc : (.inl c : V ⊕ Unit) ∉ C.supp)
    (hu : (.inl u : V ⊕ Unit) ∈ C.supp)
    (hv : (.inl v : V ⊕ Unit) ∉ C.supp) (huv : G.Adj u v) :
    u = x ∧ v = a := by
  have hdeleted : s(u, v) = s(x, a) ∨ s(u, v) = s(b, c) := by
    by_contra hnot
    push_neg at hnot
    have hfirst : (G.deleteEdges {s(x, a)}).Adj u v :=
      SimpleGraph.deleteEdges_adj.mpr ⟨huv, by simpa [hnot.1]⟩
    have hpuncture : (twoEdgeCyclePuncture (G := G) x a b c).Adj u v :=
      SimpleGraph.deleteEdges_adj.mpr ⟨hfirst, by simpa [hnot.2]⟩
    have hp : (pendantExtension (twoEdgeCyclePuncture (G := G) x a b c) h).Adj
        (.inl u) (.inl v) :=
      (pendantExtension_adj_old _ h u v).mpr hpuncture
    exact hv (C.mem_supp_of_adj_mem_supp hu hp)
  rcases hdeleted with hxa | hbc
  · rcases Sym2.eq_iff.mp hxa with hpair | hpair
    · exact ⟨hpair.1, hpair.2⟩
    · exact (ha (by simpa [hpair.1] using hu)).elim
  · rcases Sym2.eq_iff.mp hbc with hpair | hpair
    · exact (hb (by simpa [hpair.1] using hu)).elim
    · exact (hc (by simpa [hpair.1] using hu)).elim

/-- An x-side SET component in the two-edge pendant auxiliary makes `x` a
cut vertex of the original graph.  A path from the pendant attachment to a
second old SET vertex cannot enter the component after `x` is removed: every
crossing is forced to be the deleted edge `x-a`. -/
theorem twoEdgeCyclePuncture_pendant_x_side_set_forces_not_connected
    (h x a b c : V)
    (C : (pendantExtension (twoEdgeCyclePuncture (G := G) x a b c) h).ConnectedComponent)
    [DecidablePred (· ∈ C.supp)]
    (hhx : h ≠ x) (hxC : (.inl x : V ⊕ Unit) ∈ C.supp)
    (haC : (.inl a : V ⊕ Unit) ∉ C.supp)
    (hbC : (.inl b : V ⊕ Unit) ∉ C.supp)
    (hcC : (.inl c : V ⊕ Unit) ∉ C.supp)
    (hleaf : (.inr () : V ⊕ Unit) ∉ C.supp)
    (hset : IsSET ((pendantExtension (twoEdgeCyclePuncture (G := G) x a b c) h).induce C.supp)) :
    ¬ (G.induce {v | v ≠ x}).Connected := by
  have hhC : (.inl h : V ⊕ Unit) ∉ C.supp :=
    pendantExtension_attachment_not_mem_of_leaf_not_mem h C hleaf
  obtain ⟨t, htC, htx⟩ :=
    pendantExtension_set_component_exists_second_old_of_mem h x C hxC hleaf hset
  intro hconn
  have hreach : (G.induce {v | v ≠ x}).Reachable ⟨h, hhx⟩ ⟨t, htx⟩ :=
    hconn ⟨h, hhx⟩ ⟨t, htx⟩
  rw [SimpleGraph.reachable_iff_reflTransGen] at hreach
  have hnoenter : ∀ {u v : {v : V | v ≠ x}},
      (.inl u.val : V ⊕ Unit) ∉ C.supp →
      (.inl v.val : V ⊕ Unit) ∈ C.supp →
      (G.induce {v | v ≠ x}).Adj u v → False := by
    intro u v huC hvC huv
    obtain ⟨hvx, _⟩ := twoEdgeCyclePuncture_pendant_component_crossing_is_xa
      (G := G) h x a b c v.val u.val C haC hbC hcC hvC huC huv.symm
    exact v.property hvx
  have hstay : ∀ {v : {v : V | v ≠ x}},
      Relation.ReflTransGen (G.induce {v | v ≠ x}).Adj ⟨h, hhx⟩ v →
      (.inl v.val : V ⊕ Unit) ∉ C.supp := by
    intro v hv
    induction hv with
    | refl => exact hhC
    | tail _ huv ih => exact fun hvC => hnoenter ih hvC huv
  exact hstay hreach htC

/-- The component containing the fresh leaf of a pendant extension is not
SET when the old attachment is even: the leaf is odd and its unique neighbour
becomes odd as well, hence it has E-degree zero. -/
theorem pendantExtension_leaf_component_not_set
    {J : SimpleGraph V} [DecidableRel J.Adj] (h : V)
    (hhEven : Even (J.degree h))
    (C : (pendantExtension J h).ConnectedComponent)
    [DecidablePred (· ∈ C.supp)]
    (hleaf : (.inr () : V ⊕ Unit) ∈ C.supp) :
    ¬ IsSET ((pendantExtension J h).induce C.supp) := by
  have hodd : Odd ((pendantExtension J h).degree (.inr ())) :=
    pendantExtension_odd_new J h
  have hzero : eDegree (pendantExtension J h) (.inr ()) = 0 := by
    apply eDegree_eq_zero_of_no_even_neighbor
    intro w hw hwEven
    cases w with
    | inr w =>
      cases w
      simpa using (pendantExtension_adj_new J h (.inr ())).mp hw
    | inl v =>
      have hv : v = h := Sum.inl.inj
        ((pendantExtension_adj_new J h (.inl v)).mp hw)
      subst v
      exact (Nat.not_even_iff_odd.mpr
        ((pendantExtension_odd_attach_iff J h).mpr hhEven)) hwEven
  exact component_not_set_of_odd_eDegree_zero (G := pendantExtension J h) C
    (.inr ()) hleaf hodd hzero

/-- A component of the two-edge cycle puncture has no surviving edge to its
complement.  Therefore every original crossing edge is one of the two
deleted edges. -/
theorem twoEdgeCyclePuncture_component_crossing_is_deleted
    (x a b c u v : V)
    (C : (twoEdgeCyclePuncture (G := G) x a b c).ConnectedComponent)
    (hu : u ∈ C.supp) (hv : v ∉ C.supp) (huv : G.Adj u v) :
    s(u, v) = s(x, a) ∨ s(u, v) = s(b, c) := by
  by_contra hnot
  push_neg at hnot
  have hfirst : (G.deleteEdges {s(x, a)}).Adj u v :=
    SimpleGraph.deleteEdges_adj.mpr ⟨huv, by simpa [hnot.1]⟩
  have hpuncture : (twoEdgeCyclePuncture (G := G) x a b c).Adj u v :=
    SimpleGraph.deleteEdges_adj.mpr ⟨hfirst, by simpa [hnot.2]⟩
  exact hv (C.mem_supp_of_adj_mem_supp hu hpuncture)

/-- The pendant auxiliary has the same old-vertex crossing classification as
the puncture: a component boundary in the original graph must be one of the
two deleted edges. -/
theorem twoEdgeCyclePuncture_pendant_component_crossing_is_deleted
    (h x a b c u v : V)
    (C : (pendantExtension (twoEdgeCyclePuncture (G := G) x a b c) h).ConnectedComponent)
    (hu : (.inl u : V ⊕ Unit) ∈ C.supp)
    (hv : (.inl v : V ⊕ Unit) ∉ C.supp) (huv : G.Adj u v) :
    s(u, v) = s(x, a) ∨ s(u, v) = s(b, c) := by
  by_contra hnot
  push_neg at hnot
  have hfirst : (G.deleteEdges {s(x, a)}).Adj u v :=
    SimpleGraph.deleteEdges_adj.mpr ⟨huv, by simpa [hnot.1]⟩
  have hpuncture : (twoEdgeCyclePuncture (G := G) x a b c).Adj u v :=
    SimpleGraph.deleteEdges_adj.mpr ⟨hfirst, by simpa [hnot.2]⟩
  have hp : (pendantExtension (twoEdgeCyclePuncture (G := G) x a b c) h).Adj
      (.inl u) (.inl v) :=
    (pendantExtension_adj_old _ h u v).mpr hpuncture
  exact hv (C.mem_supp_of_adj_mem_supp hu hp)

/-- In a connected original graph, every pendant-auxiliary component that
does not contain the fresh leaf meets one of the endpoints of the two deleted
cycle edges.  This is the boundary reduction used after the middle-vertex SET
exclusion. -/
theorem twoEdgeCyclePuncture_pendant_component_meets_deleted_support
    (h x a b c : V) (C :
      (pendantExtension (twoEdgeCyclePuncture (G := G) x a b c) h).ConnectedComponent)
    (hconn : G.Connected) (hleaf : (.inr () : V ⊕ Unit) ∉ C.supp) :
    ∃ z : V, (.inl z : V ⊕ Unit) ∈ C.supp ∧
      (z = x ∨ z = a ∨ z = b ∨ z = c) := by
  by_contra hnone
  obtain ⟨w, hw⟩ := C.nonempty_supp
  obtain ⟨u, hu⟩ : ∃ u : V, (.inl u : V ⊕ Unit) ∈ C.supp := by
    cases w with
    | inl u => exact ⟨u, hw⟩
    | inr w => cases w; exact False.elim (hleaf hw)
  have hhC : (.inl h : V ⊕ Unit) ∉ C.supp := by
    intro hhC
    apply hleaf
    exact C.mem_supp_of_adj_mem_supp hhC
      ((pendantExtension_adj_new _ h (.inl h)).mpr rfl).symm
  have hclosed : ∀ r s : V, (.inl r : V ⊕ Unit) ∈ C.supp → G.Adj r s →
      (.inl s : V ⊕ Unit) ∈ C.supp := by
    intro r s hr hrs
    by_contra hs
    rcases twoEdgeCyclePuncture_pendant_component_crossing_is_deleted
      (G := G) h x a b c r s C hr hs hrs with hxa | hbc
    · apply hnone
      rcases Sym2.eq_iff.mp hxa with hpair | hpair
      · exact ⟨r, hr, Or.inl hpair.1⟩
      · exact ⟨r, hr, Or.inr (Or.inl hpair.1)⟩
    · apply hnone
      rcases Sym2.eq_iff.mp hbc with hpair | hpair
      · exact ⟨r, hr, Or.inr (Or.inr (Or.inl hpair.1))⟩
      · exact ⟨r, hr, Or.inr (Or.inr (Or.inr hpair.1))⟩
  have hreach : G.Reachable u h := hconn u h
  rw [SimpleGraph.reachable_iff_reflTransGen] at hreach
  have hpreserve : ∀ {v : V}, Relation.ReflTransGen G.Adj u v →
      (.inl u : V ⊕ Unit) ∈ C.supp → (.inl v : V ⊕ Unit) ∈ C.supp := by
    intro v hv hu
    induction hv with
    | refl => exact hu
    | tail _ huv ih => exact hclosed _ _ ih huv
  exact hhC (hpreserve hreach hu)

/-- In the long-cycle pendant auxiliary, every connected component containing
either of the two middle puncture vertices is not SET.  This discharges the
local part of the componentwise SET audit; components avoiding both middle
vertices still require the deleted-edge boundary analysis. -/
theorem twoEdgeCyclePuncture_pendant_middle_component_not_set
    (h x a b c : V) (hxa : G.Adj x a) (habAdj : G.Adj a b) (hbc : G.Adj b c)
    (hxb : x ≠ b) (hxc : x ≠ c) (hab : a ≠ b) (hac : a ≠ c)
    (hhx : h ≠ x) (hha : h ≠ a) (hhb : h ≠ b) (hhc : h ≠ c)
    (hhEven : Even (G.degree h)) (hxEven : Even (G.degree x))
    (haEven : Even (G.degree a)) (hbEven : Even (G.degree b))
    (hcEven : Even (G.degree c))
    (haDeg : eDegree G a = 2) (hbDeg : eDegree G b = 2)
    (C : (pendantExtension (twoEdgeCyclePuncture (G := G) x a b c) h).ConnectedComponent)
    [DecidablePred (· ∈ C.supp)]
    (hmid : (.inl a : V ⊕ Unit) ∈ C.supp ∨ (.inl b : V ⊕ Unit) ∈ C.supp) :
    ¬ IsSET ((pendantExtension (twoEdgeCyclePuncture (G := G) x a b c) h).induce C.supp) := by
  let J : SimpleGraph V := twoEdgeCyclePuncture (G := G) x a b c
  have hhJ : Even (J.degree h) := by
    dsimp [J]
    rw [twoEdgeCyclePuncture_degree_away (G := G) x a b c h hhx hha hhb hhc]
    exact hhEven
  obtain ⟨_, haOdd, hbOdd, _⟩ :=
    twoEdgeCyclePuncture_odd_profile (G := G) x a b c hxa hbc hxb hxc hab hac
      hxEven haEven hbEven hcEven
  obtain ⟨haZero, hbZero⟩ :=
    twoEdgeCyclePuncture_middle_eDegree_zero (G := G) x a b c hxa habAdj hbc
      hxb hxc hab hac hxEven haEven hbEven hcEven haDeg hbDeg
  rcases hmid with haC | hbC
  · have haOddP : Odd ((pendantExtension J h).degree (.inl a)) :=
      (pendantExtension_odd_old_ne J h a hha.symm).mpr haOdd
    have haZeroP : eDegree (pendantExtension J h) (.inl a) = 0 :=
      pendantExtension_eDegree_zero_old_ne h a hha.symm hhJ haZero
    exact component_not_set_of_odd_eDegree_zero (G := pendantExtension J h) C
      (.inl a) haC haOddP haZeroP
  · have hbOddP : Odd ((pendantExtension J h).degree (.inl b)) :=
      (pendantExtension_odd_old_ne J h b hhb.symm).mpr hbOdd
    have hbZeroP : eDegree (pendantExtension J h) (.inl b) = 0 :=
      pendantExtension_eDegree_zero_old_ne h b hhb.symm hhJ hbZero
    exact component_not_set_of_odd_eDegree_zero (G := pendantExtension J h) C
      (.inl b) hbC hbOddP hbZeroP

/-- Under the long-cycle local degree data, a SET component of the pendant
auxiliary can meet the two-edge deleted support only at the exceptional hub
`x`.  The fresh leaf, both middle vertices, and the final vertex are each
already excluded by local odd E-degree witnesses. -/
theorem twoEdgeCyclePuncture_pendant_set_component_contains_x
    (h x a b c : V) (hxa : G.Adj x a) (habAdj : G.Adj a b) (hbc : G.Adj b c)
    (hxb : x ≠ b) (hxc : x ≠ c) (hab : a ≠ b) (hac : a ≠ c)
    (hhx : h ≠ x) (hha : h ≠ a) (hhb : h ≠ b) (hhc : h ≠ c)
    (hhEven : Even (G.degree h)) (hxEven : Even (G.degree x))
    (haEven : Even (G.degree a)) (hbEven : Even (G.degree b))
    (hcEven : Even (G.degree c))
    (haDeg : eDegree G a = 2) (hbDeg : eDegree G b = 2)
    (hcDeg : eDegree G c = 2) (hconn : G.Connected)
    (C : (pendantExtension (twoEdgeCyclePuncture (G := G) x a b c) h).ConnectedComponent)
    [DecidablePred (· ∈ C.supp)]
    (hset : IsSET ((pendantExtension (twoEdgeCyclePuncture (G := G) x a b c) h).induce C.supp)) :
    (.inl x : V ⊕ Unit) ∈ C.supp := by
  let J : SimpleGraph V := twoEdgeCyclePuncture (G := G) x a b c
  have hhJ : Even (J.degree h) := by
    dsimp [J]
    rw [twoEdgeCyclePuncture_degree_away (G := G) x a b c h hhx hha hhb hhc]
    exact hhEven
  have hleaf : (.inr () : V ⊕ Unit) ∉ C.supp := by
    intro hleaf
    exact (pendantExtension_leaf_component_not_set h hhJ C hleaf) hset
  obtain ⟨z, hzC, hz⟩ :=
    twoEdgeCyclePuncture_pendant_component_meets_deleted_support (G := G) h x a b c C hconn hleaf
  rcases hz with hx | ha | hb | hc
  · simpa [hx] using hzC
  · exact False.elim
      ((twoEdgeCyclePuncture_pendant_middle_component_not_set (G := G)
        h x a b c hxa habAdj hbc hxb hxc hab hac hhx hha hhb hhc
        hhEven hxEven haEven hbEven hcEven haDeg hbDeg C
          (Or.inl (by simpa [ha] using hzC))) hset)
  · exact False.elim
      ((twoEdgeCyclePuncture_pendant_middle_component_not_set (G := G)
        h x a b c hxa habAdj hbc hxb hxc hab hac hhx hha hhb hhc
        hhEven hxEven haEven hbEven hcEven haDeg hbDeg C
          (Or.inr (by simpa [hb] using hzC))) hset)
  · exact False.elim
      ((twoEdgeCyclePuncture_pendant_end_component_not_set (G := G)
        h x a b c hxa hbc hxb hxc hab hac hhx hha hhb hhc hhEven hxEven
        haEven hbEven hcEven hcDeg C (by simpa [hc] using hzC)) hset)

/-- Under the bare minimal-counterexample and literal degree-two cycle data,
no component of the long-cycle pendant auxiliary is SET.  The leaf and the
three non-hub deleted-edge endpoints have intrinsic odd/E-degree witnesses;
the sole possible x-side component contradicts the already established
non-cutness of the exceptional hub. -/
theorem twoEdgeCyclePuncture_pendant_all_components_not_set
    (h x a b c : V) (H : BareMinimalCounterexample G h x)
    (hxa : G.Adj x a) (habAdj : G.Adj a b) (hbc : G.Adj b c)
    (hxb : x ≠ b) (hxc : x ≠ c) (hab : a ≠ b) (hac : a ≠ c)
    (hha : h ≠ a) (hhb : h ≠ b) (hhc : h ≠ c)
    (haEven : Even (G.degree a)) (hbEven : Even (G.degree b))
    (hcEven : Even (G.degree c))
    (haDeg : eDegree G a = 2) (hbDeg : eDegree G b = 2)
    (hcDeg : eDegree G c = 2)
    (C : (pendantExtension (twoEdgeCyclePuncture (G := G) x a b c) h).ConnectedComponent)
    [DecidablePred (· ∈ C.supp)] :
    ¬ IsSET ((pendantExtension (twoEdgeCyclePuncture (G := G) x a b c) h).induce C.supp) := by
  rcases H.counterexample.1 with ⟨hconn, hhx, _, hhEven, hxEven, _, _⟩
  intro hset
  have hhJ : Even ((twoEdgeCyclePuncture (G := G) x a b c).degree h) := by
    rw [twoEdgeCyclePuncture_degree_away (G := G) x a b c h hhx hha hhb hhc]
    exact hhEven
  have hleaf : (.inr () : V ⊕ Unit) ∉ C.supp := by
    intro hleaf
    exact (pendantExtension_leaf_component_not_set h hhJ C hleaf) hset
  have haC : (.inl a : V ⊕ Unit) ∉ C.supp := by
    intro haC
    exact (twoEdgeCyclePuncture_pendant_middle_component_not_set (G := G)
      h x a b c hxa habAdj hbc hxb hxc hab hac hhx hha hhb hhc
      hhEven hxEven haEven hbEven hcEven haDeg hbDeg C (Or.inl haC)) hset
  have hbC : (.inl b : V ⊕ Unit) ∉ C.supp := by
    intro hbC
    exact (twoEdgeCyclePuncture_pendant_middle_component_not_set (G := G)
      h x a b c hxa habAdj hbc hxb hxc hab hac hhx hha hhb hhc
      hhEven hxEven haEven hbEven hcEven haDeg hbDeg C (Or.inr hbC)) hset
  have hcC : (.inl c : V ⊕ Unit) ∉ C.supp := by
    intro hcC
    exact (twoEdgeCyclePuncture_pendant_end_component_not_set (G := G)
      h x a b c hxa hbc hxb hxc hab hac hhx hha hhb hhc hhEven hxEven
      haEven hbEven hcEven hcDeg C hcC) hset
  have hxC := twoEdgeCyclePuncture_pendant_set_component_contains_x (G := G)
    h x a b c hxa habAdj hbc hxb hxc hab hac hhx hha hhb hhc
    hhEven hxEven haEven hbEven hcEven haDeg hbDeg hcDeg hconn C hset
  exact twoEdgeCyclePuncture_pendant_x_side_set_forces_not_connected (G := G)
    h x a b c C hhx hxC haC hbC hcC hleaf hset
      (bare_exception_noncut G h x H)

omit [DecidableRel G.Adj] in
/-- The long-cycle pendant auxiliary has the published floor budget once its
local subcubic cap and componentwise SET exclusion are established.  This
packages only the universal component assembly; the two hypotheses are the
remaining graph-specific obligations in the bare windmill reduction. -/
theorem twoEdgeCyclePuncture_pendant_floor_of_component_nonSET
    (h x a b c : V)
    (hcap : ∀ v, Even ((pendantExtension
        (twoEdgeCyclePuncture (G := G) x a b c) h).degree v) →
      eDegree (pendantExtension (twoEdgeCyclePuncture (G := G) x a b c) h) v ≤ 3)
    (hnot : ∀ (C : (pendantExtension
        (twoEdgeCyclePuncture (G := G) x a b c) h).ConnectedComponent)
      [DecidablePred (· ∈ C.supp)],
      ¬ IsSET ((pendantExtension (twoEdgeCyclePuncture (G := G) x a b c) h).induce C.supp)) :
    HasPathBudget (pendantExtension (twoEdgeCyclePuncture (G := G) x a b c) h)
      (Fintype.card (V ⊕ Unit) / 2) := by
  apply floor_of_components
  intro C
  classical
  apply (floor_or_set ((pendantExtension
    (twoEdgeCyclePuncture (G := G) x a b c) h).induce C.supp)
    C.connected_toSimpleGraph ?_).resolve_right
  · exact hnot C
  · have hclosed : ∀ v ∈ C.supp,
        (pendantExtension (twoEdgeCyclePuncture (G := G) x a b c) h).neighborSet v ⊆ C.supp := by
      intro v hv w hw
      exact C.mem_supp_of_adj_mem_supp hv hw
    exact even_degree_cap_induce_of_closed
      (pendantExtension (twoEdgeCyclePuncture (G := G) x a b c) h) C.supp hclosed 3 hcap

/-- The literal long-cycle pendant auxiliary has the ambient floor budget in
a bare minimal counterexample.  This is the exact componentwise application
of the published floor-or-SET input, with no remaining SET alternative. -/
theorem twoEdgeCyclePuncture_pendant_floor_of_bare_long_cycle
    (h x a b c : V) (H : BareMinimalCounterexample G h x)
    (hxa : G.Adj x a) (habAdj : G.Adj a b) (hbc : G.Adj b c)
    (hxb : x ≠ b) (hxc : x ≠ c) (hab : a ≠ b) (hac : a ≠ c)
    (hha : h ≠ a) (hhb : h ≠ b) (hhc : h ≠ c)
    (haEven : Even (G.degree a)) (hbEven : Even (G.degree b))
    (hcEven : Even (G.degree c))
    (haDeg : eDegree G a = 2) (hbDeg : eDegree G b = 2)
    (hcDeg : eDegree G c = 2) :
    HasPathBudget (pendantExtension (twoEdgeCyclePuncture (G := G) x a b c) h)
      (Fintype.card (V ⊕ Unit) / 2) := by
  apply twoEdgeCyclePuncture_pendant_floor_of_component_nonSET
  · exact twoEdgeCyclePuncture_pendant_cap_of_bare_counterexample (G := G)
      h x a b c H hxa hbc hxb hxc hab hac hha hhb hhc haEven hbEven hcEven
  · intro C _
    exact twoEdgeCyclePuncture_pendant_all_components_not_set (G := G)
      h x a b c H hxa habAdj hbc hxb hxc hab hac hha hhb hhc
      haEven hbEven hcEven haDeg hbDeg hcDeg C

/-- The long-cycle puncture is restored at unchanged path count once the two
strict Fan inequalities have been established on the actual intermediate
decomposition.  The theorem deliberately retains those inequalities as
premises: their proof is the component-budget part of the windmill argument,
not local path bookkeeping. -/
theorem Decomposition.restore_twoEdgeCyclePuncture
    (x a b c : V) (hxa : G.Adj x a) (hbc : G.Adj b c)
    (hxb : x ≠ b) (hab : a ≠ b)
    (D : Decomposition (twoEdgeCyclePuncture (G := G) x a b c))
    (hbcStrict : #{v ∈ (twoEdgeCyclePuncture (G := G) x a b c).neighborFinset b |
        D.endpointCount v = 0} < D.endpointCount c)
    (hxaStrict : ∀ E : Decomposition
        ((twoEdgeCyclePuncture (G := G) x a b c) ⊔ SimpleGraph.edge b c),
        E.size = D.size →
        (∀ w, E.endpointCount w + (if c = w then 1 else 0) =
          D.endpointCount w + if b = w then 1 else 0) →
        #{v ∈ ((twoEdgeCyclePuncture (G := G) x a b c) ⊔
            SimpleGraph.edge b c).neighborFinset a | E.endpointCount v = 0} <
          E.endpointCount x) :
    ∃ E : Decomposition G, E.size = D.size ∧
      ∀ t, t ≠ x → t ≠ a → t ≠ b → t ≠ c →
        E.endpointCount t = D.endpointCount t := by
  classical
  have hbc₁ : (G.deleteEdges {s(x, a)}).Adj b c := by
    apply adj_delete_edge_of_ne G x a b c hbc
    intro he
    rw [Sym2.eq_iff] at he
    rcases he with ⟨hbx, _⟩ | ⟨hba, _⟩
    · exact hxb hbx.symm
    · exact hab hba.symm
  have hrestoreBC :
      (twoEdgeCyclePuncture (G := G) x a b c) ⊔ SimpleGraph.edge b c =
        G.deleteEdges {s(x, a)} := by
    exact delete_edge_sup_edge (G.deleteEdges {s(x, a)}) b c hbc₁
  have hbcMissing : ¬ (twoEdgeCyclePuncture (G := G) x a b c).Adj b c := by
    intro h
    obtain ⟨_, hne⟩ := SimpleGraph.deleteEdges_adj.mp h
    exact hne rfl
  obtain ⟨E₁, hE₁size, hE₁ends⟩ :=
    D.single_edge_addibility b c hbc.ne hbcMissing hbcStrict
  have hxaMissing : ¬ ((twoEdgeCyclePuncture (G := G) x a b c) ⊔
      SimpleGraph.edge b c).Adj a x := by
    rw [hrestoreBC]
    intro h
    obtain ⟨_, hne⟩ := SimpleGraph.deleteEdges_adj.mp h
    apply hne
    simp
  obtain ⟨E₂, hE₂size, hE₂ends⟩ :=
    E₁.single_edge_addibility a x hxa.ne.symm hxaMissing
      (hxaStrict E₁ hE₁size hE₁ends)
  have hrestoreAll :
      ((twoEdgeCyclePuncture (G := G) x a b c) ⊔ SimpleGraph.edge b c) ⊔
        SimpleGraph.edge a x = G := by
    rw [hrestoreBC, SimpleGraph.edge_comm a x]
    exact delete_edge_sup_edge G x a hxa
  have castSize {L M : SimpleGraph V} (e : L = M) (P : Decomposition L) :
      (e ▸ P).size = P.size := by
    subst M
    rfl
  have castEnds {L M : SimpleGraph V} (e : L = M) (P : Decomposition L) (v : V) :
      (e ▸ P).endpointCount v = P.endpointCount v := by
    subst M
    rfl
  have hcast : (hrestoreAll ▸ E₂).size = E₂.size := castSize hrestoreAll E₂
  refine ⟨hrestoreAll ▸ E₂, hcast.trans (hE₂size.trans hE₁size), ?_⟩
  intro t htx hta htb htc
  have hE₁t : E₁.endpointCount t = D.endpointCount t := by
    have ht := hE₁ends t
    simp [htc, htc.symm, htb, htb.symm] at ht
    exact ht
  have hE₂t : E₂.endpointCount t = E₁.endpointCount t := by
    have ht := hE₂ends t
    simp [htx, htx.symm, hta, hta.symm] at ht
    exact ht
  rw [castEnds hrestoreAll E₂ t, hE₂t, hE₁t]

/-- The two separated edges of a degree-two four-vertex even cycle path can
be restored at unchanged path count.  This packages the two strict Fan
conditions from the local parity and degree ledger; the remaining consumer
task is solely to obtain the puncture decomposition by trimming the pendant
edge from the checked auxiliary budget. -/
theorem Decomposition.restore_twoEdgeCyclePuncture_of_local_ledger
    (x a b c : V) (hxa : G.Adj x a) (habAdj : G.Adj a b) (hbc : G.Adj b c)
    (hxb : x ≠ b) (hxc : x ≠ c) (hab : a ≠ b) (hac : a ≠ c)
    (hxEven : Even (G.degree x)) (haEven : Even (G.degree a))
    (hbEven : Even (G.degree b)) (hcEven : Even (G.degree c))
    (haDeg : eDegree G a = 2) (hbDeg : eDegree G b = 2)
    (D : Decomposition (twoEdgeCyclePuncture (G := G) x a b c)) :
    ∃ E : Decomposition G, E.size = D.size ∧
      ∀ t, t ≠ x → t ≠ a → t ≠ b → t ≠ c →
        E.endpointCount t = D.endpointCount t := by
  obtain ⟨hxOdd, _, _, hcOdd⟩ :=
    twoEdgeCyclePuncture_odd_profile (G := G) x a b c hxa hbc hxb hxc hab hac
      hxEven haEven hbEven hcEven
  obtain ⟨haZero, hbZero⟩ :=
    twoEdgeCyclePuncture_middle_eDegree_zero (G := G) x a b c hxa habAdj hbc
      hxb hxc hab hac hxEven haEven hbEven hcEven haDeg hbDeg
  obtain ⟨E, hEsize, hEpreserve⟩ := Decomposition.restore_twoEdgeCyclePuncture
    x a b c hxa hbc hxb hab D
    (twoEdgeCyclePuncture_first_restoration_strict (G := G) x a b c D hbZero hcOdd)
    (by
      intro E _ hends
      exact twoEdgeCyclePuncture_second_restoration_strict (G := G) x a b c D E hends
        haZero hxOdd hxa habAdj hbc hxb hxc hab hac hxEven hbEven hcEven haDeg)
  exact ⟨E, hEsize, hEpreserve⟩

/-- A pendant auxiliary budget returns to its old graph without increasing the
path count.  This is the budget transport needed by the long-cycle puncture;
the endpoint detail of the pendant return is not needed here. -/
theorem pendantExtension_hasPathBudget_returns
    (J : SimpleGraph V) [DecidableRel J.Adj] (h : V) (k : ℕ) :
    HasPathBudget (pendantExtension J h) k → HasPathBudget J k := by
  rintro ⟨D, hDsize⟩
  obtain ⟨E, hEsize, _, _⟩ := D.return_pendant J h
  exact ⟨E, hEsize.trans hDsize⟩

/-- The checked pendant auxiliary budget and the local degree-two ledger
produce a path budget for the original graph.  Thus a long hub cycle cannot
survive in a bare minimal counterexample once the supplied auxiliary budget is
at the ambient floor. -/
theorem twoEdgeCyclePuncture_hasPathBudget_of_local_ledger_and_pendant_budget
    (x a b c h : V) (k : ℕ)
    (hbudget : HasPathBudget
      (pendantExtension (twoEdgeCyclePuncture (G := G) x a b c) h) k)
    (hxa : G.Adj x a) (habAdj : G.Adj a b) (hbc : G.Adj b c)
    (hxb : x ≠ b) (hxc : x ≠ c) (hab : a ≠ b) (hac : a ≠ c)
    (hxEven : Even (G.degree x)) (haEven : Even (G.degree a))
    (hbEven : Even (G.degree b)) (hcEven : Even (G.degree c))
    (haDeg : eDegree G a = 2) (hbDeg : eDegree G b = 2) :
    HasPathBudget G k := by
  obtain ⟨D, hDsize⟩ := pendantExtension_hasPathBudget_returns
    (twoEdgeCyclePuncture (G := G) x a b c) h k hbudget
  obtain ⟨E, hEsize, _⟩ := Decomposition.restore_twoEdgeCyclePuncture_of_local_ledger
    x a b c hxa habAdj hbc hxb hxc hab hac hxEven haEven hbEven hcEven haDeg hbDeg D
  exact ⟨E, hEsize.le.trans hDsize⟩

/-- The long-cycle pendant auxiliary gives the full bare endpoint conclusion
when its floor budget is available.  Returning the pendant exposes the
positive even prescribed vertex `h`; both cycle-edge restorations preserve
that endpoint reserve because `h` is disjoint from their four endpoints. -/
theorem twoEdgeCyclePuncture_bareConclusion_of_local_ledger_and_pendant_budget
    (h x a b c : V)
    (hbudget : HasPathBudget
      (pendantExtension (twoEdgeCyclePuncture (G := G) x a b c) h)
        (Fintype.card (V ⊕ Unit) / 2))
    (hxa : G.Adj x a) (habAdj : G.Adj a b) (hbc : G.Adj b c)
    (hxb : x ≠ b) (hxc : x ≠ c) (hab : a ≠ b) (hac : a ≠ c)
    (hxEven : Even (G.degree x)) (haEven : Even (G.degree a))
    (hbEven : Even (G.degree b)) (hcEven : Even (G.degree c))
    (haDeg : eDegree G a = 2) (hbDeg : eDegree G b = 2)
    (hpositive : 0 < G.degree h) (hhEven : Even (G.degree h))
    (hhx : h ≠ x) (hha : h ≠ a) (hhb : h ≠ b) (hhc : h ≠ c) :
    BareConclusion G h := by
  let J : SimpleGraph V := twoEdgeCyclePuncture (G := G) x a b c
  have hhJdegree : J.degree h = G.degree h := by
    dsimp [J]
    exact twoEdgeCyclePuncture_degree_away (G := G) x a b c h hhx hha hhb hhc
  obtain ⟨D₀, hD₀size⟩ := hbudget
  obtain ⟨D, hDsize, hDh, _⟩ := D₀.return_pendant_even_exposes J h (by
    rw [hhJdegree]
    exact hpositive) (by
    rw [hhJdegree]
    exact hhEven)
  obtain ⟨E, hEsize, hEpreserve⟩ :=
    Decomposition.restore_twoEdgeCyclePuncture_of_local_ledger
      x a b c hxa habAdj hbc hxb hxc hab hac hxEven haEven hbEven hcEven
      haDeg hbDeg D
  refine ⟨E, ?_, ?_⟩
  · simpa only [Fintype.card_sum, Fintype.card_unit, Nat.add_zero] using
      hEsize.le.trans (hDsize.trans hD₀size)
  · rw [hEpreserve h hhx hha hhb hhc]
    exact hDh

/-- A literal degree-two four-vertex segment of a long hub cycle is
incompatible with bare minimality as soon as its checked pendant auxiliary
has the ambient floor budget.  The remaining structural reduction need only
produce this segment and the auxiliary certificate. -/
theorem bare_minimal_no_twoEdgeCyclePuncture_of_pendant_floor
    (h x a b c : V) (H : BareMinimalCounterexample G h x)
    (hbudget : HasPathBudget
      (pendantExtension (twoEdgeCyclePuncture (G := G) x a b c) h)
        (Fintype.card (V ⊕ Unit) / 2))
    (hxa : G.Adj x a) (habAdj : G.Adj a b) (hbc : G.Adj b c)
    (hxb : x ≠ b) (hxc : x ≠ c) (hab : a ≠ b) (hac : a ≠ c)
    (haEven : Even (G.degree a)) (hbEven : Even (G.degree b))
    (hcEven : Even (G.degree c))
    (haDeg : eDegree G a = 2) (hbDeg : eDegree G b = 2)
    (hha : h ≠ a) (hhb : h ≠ b) (hhc : h ≠ c) : False := by
  rcases H.counterexample.1 with ⟨_, hhx, hhpositive, hhEven, hxEven, _, _⟩
  exact H.counterexample.2
    (twoEdgeCyclePuncture_bareConclusion_of_local_ledger_and_pendant_budget
      h x a b c hbudget hxa habAdj hbc hxb hxc hab hac hxEven haEven hbEven hcEven
      haDeg hbDeg hhpositive hhEven hhx hha hhb hhc)

/-- The local degree-two segment `x-a-b-c` cannot occur on a long hub cycle
in a bare minimal counterexample.  Its pendant auxiliary has the floor
budget by the complete componentwise SET audit, and the endpoint-preserving
restoration bridge then supplies the forbidden bare conclusion. -/
theorem bare_minimal_no_long_cycle_segment
    (h x a b c : V) (H : BareMinimalCounterexample G h x)
    (hxa : G.Adj x a) (habAdj : G.Adj a b) (hbc : G.Adj b c)
    (hxb : x ≠ b) (hxc : x ≠ c) (hab : a ≠ b) (hac : a ≠ c)
    (hha : h ≠ a) (hhb : h ≠ b) (hhc : h ≠ c)
    (haEven : Even (G.degree a)) (hbEven : Even (G.degree b))
    (hcEven : Even (G.degree c))
    (haDeg : eDegree G a = 2) (hbDeg : eDegree G b = 2)
    (hcDeg : eDegree G c = 2) : False := by
  exact bare_minimal_no_twoEdgeCyclePuncture_of_pendant_floor
    h x a b c H
    (twoEdgeCyclePuncture_pendant_floor_of_bare_long_cycle (G := G)
      h x a b c H hxa habAdj hbc hxb hxc hab hac hha hhb hhc
      haEven hbEven hcEven haDeg hbDeg hcDeg)
    hxa habAdj hbc hxb hxc hab hac haEven hbEven hcEven haDeg hbDeg hha hhb hhc

/-- A non-hub vertex in the even-subgraph component of the bare exception has
exactly two even neighbours.  Positivity comes from a nontrivial shortest
path in that component; degrees one and three were already excluded by the
two corridor reductions. -/
theorem bare_hub_private_eDegree_eq_two
    (h : V) (x z : evenVertices G) (H : BareMinimalCounterexample G h (x : V))
    (hreached : (evenSubgraph G).Reachable x z) (hzx : (z : V) ≠ x) :
    eDegree G (z : V) = 2 := by
  obtain ⟨p, hp, hdist⟩ := hreached.exists_path_of_dist
  have hlen : 0 < p.length := by
    by_contra hnot
    have hzero : p.length = 0 := Nat.eq_zero_of_not_pos hnot
    have heq : (z : V) = x := by
      calc
        (z : V) = (p.getVert p.length : V) := by simp
        _ = (p.getVert 0 : V) := by simp [hzero]
        _ = x := by simp
    exact hzx heq
  have hpredAdj : (evenSubgraph G).Adj (p.getVert (p.length - 1)) z := by
    simpa [Nat.sub_add_cancel (Nat.succ_le_iff.mpr hlen)] using
      p.adj_getVert_succ (i := p.length - 1) (by omega)
  have hpos : 0 < eDegree G (z : V) := by
    apply Finset.card_pos.mpr
    refine ⟨p.getVert (p.length - 1), ?_⟩
    exact (mem_evenNeighbors (G := G) (z : V) (p.getVert (p.length - 1))).mpr
      ⟨hpredAdj.symm, (p.getVert (p.length - 1)).property⟩
  rcases H.counterexample.1 with ⟨_, hhx, _, _, _, hbare, hcap⟩
  have hzh : (z : V) ≠ h := by
    intro heq
    subst h
    rw [hbare] at hpos
    omega
  have hle : eDegree G (z : V) ≤ 3 :=
    hcap (z : V) z.property hzh hzx
  have hne1 : eDegree G (z : V) ≠ 1 := by
    intro hd
    exact bare_hub_no_degree_one h x z H hreached hd
  have hne3 : eDegree G (z : V) ≠ 3 := by
    intro hd
    exact bare_hub_component_no_degree_three h x H ⟨z, hreached, hd⟩
  omega

set_option maxHeartbeats 800000 in
/-- Inside the bare hub's even-subgraph component, every hub spoke is
non-bridging.  The component-local degree-two theorem supplies the parity
hypothesis of `nonbridge_of_even_degree_off_hub`; no assertion is made about
unrelated ordinary components. -/
theorem bare_hub_spoke_nonbridge_in_component
    (h : V) (x a : evenVertices G) (H : BareMinimalCounterexample G h (x : V))
    (C : (evenSubgraph G).ConnectedComponent)
    (hxC : x ∈ C.supp) (haC : a ∈ C.supp)
    (hxa : (evenSubgraph G).Adj x a) :
    ¬ C.toSimpleGraph.IsBridge s(⟨x, hxC⟩, ⟨a, haC⟩) := by
  classical
  have hCxa : C.toSimpleGraph.Adj ⟨x, hxC⟩ ⟨a, haC⟩ :=
    (C.toSimpleGraph_adj hxC haC).mpr hxa
  apply nonbridge_of_even_degree_off_hub (K := C.toSimpleGraph)
    ⟨x, hxC⟩ ⟨a, haC⟩ hCxa
  intro z hzx
  let zF : evenVertices G := z.val
  have hzx' : (zF : V) ≠ (x : V) := by
    intro hEq
    apply hzx
    apply Subtype.ext
    apply Subtype.ext
    exact hEq
  have hreach : (evenSubgraph G).Reachable x zF :=
    C.reachable_of_mem_supp hxC z.property
  have hdeg := bare_hub_private_eDegree_eq_two h x zF H hreach hzx'
  have hclosed : ∀ v ∈ C.supp, (evenSubgraph G).neighborSet v ⊆ C.supp := by
    intro v hv w hw
    exact C.mem_supp_of_adj_mem_supp hv hw
  have hdegC : C.toSimpleGraph.degree z = (evenSubgraph G).degree zF := by
    have hd := SimpleGraph.degree_induce_of_neighborSet_subset (hclosed zF z.property)
    simp only [← SimpleGraph.ncard_neighborSet] at hd ⊢
    exact hd
  rw [hdegC, ← eDegree_eq_induced_degree, hdeg]
  exact ⟨1, rfl⟩

/-- A hub spoke in the bare component lies on a simple even-subgraph cycle
rooted at the hub.  The proof first works in the connected component and then
maps and rotates its cycle back into the ambient even subgraph. -/
theorem bare_hub_spoke_exists_cycle
    (h : V) (x a : evenVertices G) (H : BareMinimalCounterexample G h (x : V))
    (C : (evenSubgraph G).ConnectedComponent)
    (hxC : x ∈ C.supp) (haC : a ∈ C.supp)
    (hxa : (evenSubgraph G).Adj x a) :
    ∃ p : (evenSubgraph G).Walk x x, p.IsCycle ∧ p.toSubgraph.Adj x a := by
  classical
  letI : Fintype C := Fintype.ofFinite C
  letI : DecidableEq C := Classical.decEq C
  letI : DecidableRel C.toSimpleGraph.Adj := Classical.decRel _
  let xC : C := ⟨x, hxC⟩
  let aC : C := ⟨a, haC⟩
  have hCxa : C.toSimpleGraph.Adj xC aC :=
    (C.toSimpleGraph_adj hxC haC).mpr hxa
  have hnotBridge : ¬ C.toSimpleGraph.IsBridge s(xC, aC) :=
    bare_hub_spoke_nonbridge_in_component h x a H C hxC haC hxa
  obtain ⟨u, q, hqcycle, hqedge⟩ :=
    nonbridge_adj_exists_cycle xC aC hCxa hnotBridge
  have hxq : xC ∈ q.support := q.fst_mem_support_of_mem_edges hqedge
  let f : C.toSimpleGraph →g evenSubgraph G := C.toSimpleGraph_hom
  have hfinj : Function.Injective f := by
    intro s t hst
    exact Subtype.ext hst
  let r : (evenSubgraph G).Walk (f u) (f u) := q.map f
  have hrcycle : r.IsCycle := by
    dsimp [r]
    exact hqcycle.map hfinj
  have hxr : x ∈ r.support := by
    dsimp [r, f]
    rw [SimpleGraph.Walk.support_map]
    exact List.mem_map.mpr ⟨xC, hxq, rfl⟩
  let p : (evenSubgraph G).Walk x x := r.rotate x hxr
  have hpcycle : p.IsCycle := by
    dsimp [p]
    exact hrcycle.rotate hxr
  have hredge : s(x, a) ∈ r.edges := by
    dsimp [r, f]
    rw [SimpleGraph.Walk.edges_map]
    exact List.mem_map.mpr ⟨s(xC, aC), hqedge, rfl⟩
  have hpedge : s(x, a) ∈ p.edges := by
    dsimp [p]
    exact (r.rotate_edges x hxr).perm.mem_iff.mpr hredge
  exact ⟨p, hpcycle, SimpleGraph.Walk.adj_toSubgraph_iff_mem_edges.mpr hpedge⟩

/-- A private neighbour of the bare hub has one and only one further even
neighbour.  This is the local successor relation used to trace the hub cycles;
the statement intentionally does not yet identify the successor with another
hub neighbour. -/
theorem bare_hub_neighbor_even_successor
    (h : V) (x z : evenVertices G) (H : BareMinimalCounterexample G h (x : V))
    (hzx : (z : V) ≠ x) (hzxAdj : (evenSubgraph G).Adj x z) :
    ∃ w : V, w ≠ (x : V) ∧ G.Adj (z : V) w ∧ Even (G.degree w) ∧
      ∀ v, G.Adj (z : V) v → Even (G.degree v) → v = (x : V) ∨ v = w := by
  have hreached : (evenSubgraph G).Reachable x z := hzxAdj.reachable
  have hdeg := bare_hub_private_eDegree_eq_two h x z H hreached hzx
  have hxmem : (x : V) ∈ evenNeighbors G (z : V) :=
    (mem_evenNeighbors (G := G) (z : V) (x : V)).mpr ⟨hzxAdj.symm, x.property⟩
  have herase : ((evenNeighbors G (z : V)).erase (x : V)).card = 1 := by
    have hcard := Finset.card_erase_add_one hxmem
    change (evenNeighbors G (z : V)).card = 2 at hdeg
    omega
  obtain ⟨w, hwset⟩ := Finset.card_eq_one.mp herase
  have hwmem : w ∈ evenNeighbors G (z : V) := by
    apply Finset.mem_of_mem_erase
    rw [hwset]
    simp
  have hwne : w ≠ (x : V) := by
    apply Finset.ne_of_mem_erase
    rw [hwset]
    simp
  obtain ⟨hzw, hwEven⟩ := (mem_evenNeighbors (G := G) (z : V) w).mp hwmem
  refine ⟨w, hwne, hzw, hwEven, ?_⟩
  exact even_neighbors_pair_of_degree_two (z : V) (x : V) w hdeg hxmem hwmem hwne.symm

/-- A simple cycle through an even-subgraph vertex has a literal four-vertex
segment at that vertex once its length is at least four.  The conclusion is
stated in the ambient graph because it is consumed by the puncture and
restoration lemmas. -/
theorem even_cycle_four_vertex_segment
    (x : evenVertices G) (p : (evenSubgraph G).Walk x x) (hp : p.IsCycle)
    (hlen : 4 ≤ p.length) :
    ∃ a b c : evenVertices G,
      G.Adj (x : V) (a : V) ∧ G.Adj (a : V) (b : V) ∧ G.Adj (b : V) (c : V) ∧
        (x : V) ≠ (b : V) ∧ (x : V) ≠ (c : V) ∧
          (a : V) ≠ (b : V) ∧ (a : V) ≠ (c : V) := by
  refine ⟨p.getVert 1, p.getVert 2, p.getVert 3, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa using p.adj_getVert_succ (i := 0) (by omega)
  · simpa using p.adj_getVert_succ (i := 1) (by omega)
  · simpa using p.adj_getVert_succ (i := 2) (by omega)
  · intro hxb
    have hEq : p.getVert 2 = x := Subtype.ext hxb.symm
    have hends := (hp.getVert_endpoint_iff (i := 2) (by omega)).mp hEq
    omega
  · intro hxc
    have hEq : p.getVert 3 = x := Subtype.ext hxc.symm
    have hends := (hp.getVert_endpoint_iff (i := 3) (by omega)).mp hEq
    omega
  · intro hab
    have hEq : p.getVert 1 = p.getVert 2 := Subtype.ext hab
    have hind := hp.getVert_injOn (by simp; omega) (by simp; omega) hEq
    omega
  · intro hac
    have hEq : p.getVert 1 = p.getVert 3 := Subtype.ext hac
    have hind := hp.getVert_injOn (by simp; omega) (by simp; omega) hEq
    omega

/-- In a bare minimal counterexample, the even-subgraph component through the
bare hub contains no simple cycle of length at least four.  A four-vertex
segment from such a cycle has E-degree two at each private vertex, and is
therefore excluded by the checked two-edge puncture restoration. -/
theorem bare_minimal_no_long_even_cycle_at_hub
    (h : V) (x : evenVertices G) (H : BareMinimalCounterexample G h (x : V))
    (p : (evenSubgraph G).Walk x x) (hp : p.IsCycle) (hlen : 4 ≤ p.length) :
    False := by
  obtain ⟨a, b, c, hxa, hab, hbc, hxb, hxc, habne, hac⟩ :=
    even_cycle_four_vertex_segment (G := G) x p hp hlen
  have hxaF : (evenSubgraph G).Adj x a := hxa
  have habF : (evenSubgraph G).Adj a b := hab
  have hbcF : (evenSubgraph G).Adj b c := hbc
  have hra : (evenSubgraph G).Reachable x a := hxaF.reachable
  have hrb : (evenSubgraph G).Reachable x b := hxaF.reachable.trans habF.reachable
  have hrc : (evenSubgraph G).Reachable x c :=
    hxaF.reachable.trans (habF.reachable.trans hbcF.reachable)
  have hax : (a : V) ≠ x := by
    exact hxa.ne.symm
  have haDeg := bare_hub_private_eDegree_eq_two h x a H hra hax
  have hbDeg := bare_hub_private_eDegree_eq_two h x b H hrb hxb.symm
  have hcDeg := bare_hub_private_eDegree_eq_two h x c H hrc hxc.symm
  rcases H.counterexample.1 with ⟨_, _, _, _, _, hbare, _⟩
  have hha : h ≠ (a : V) := by
    intro hha
    subst h
    omega
  have hhb : h ≠ (b : V) := by
    intro hhb
    subst h
    omega
  have hhc : h ≠ (c : V) := by
    intro hhc
    subst h
    omega
  exact bare_minimal_no_long_cycle_segment h (x : V) (a : V) (b : V) (c : V) H
    hxa hab hbc hxb hxc habne hac hha hhb hhc a.property b.property c.property
    haDeg hbDeg hcDeg

/-- Every simple even-subgraph cycle through the bare hub is a triangle in a
bare minimal counterexample.  This is the cycle-level normal form consumed by
the remaining finite successor-orbit argument. -/
theorem bare_minimal_even_cycle_at_hub_length_eq_three
    (h : V) (x : evenVertices G) (H : BareMinimalCounterexample G h (x : V))
    (p : (evenSubgraph G).Walk x x) (hp : p.IsCycle) :
    p.length = 3 := by
  have hthree : 3 ≤ p.length := hp.three_le_length
  by_contra hne
  have hlong : 4 ≤ p.length := by omega
  exact bare_minimal_no_long_even_cycle_at_hub h x H p hp hlong

/-- Once a cycle through the bare hub contains a specified hub spoke, it can
be oriented along that spoke.  The triangle-only cycle normal form then gives
the mate of the spoke and all three petal edges.  This separates the local
cycle calculation from the remaining proof that every hub spoke is
non-bridging. -/
theorem bare_minimal_spoke_cycle_triangle
    (h : V) (x a : evenVertices G) (H : BareMinimalCounterexample G h (x : V))
    (p : (evenSubgraph G).Walk x x) (hp : p.IsCycle)
    (hxa : p.toSubgraph.Adj x a) :
    ∃ b : evenVertices G,
      (evenSubgraph G).Adj x a ∧ (evenSubgraph G).Adj a b ∧
        (evenSubgraph G).Adj b x ∧ a ≠ b ∧ b ≠ x := by
  obtain ⟨q, hqcycle, hqsnd, _⟩ := hp.exists_isCycle_snd_verts_eq hxa
  have hlen : q.length = 3 := bare_minimal_even_cycle_at_hub_length_eq_three h x H q hqcycle
  have hq1 : q.getVert 1 = a := by
    simpa [SimpleGraph.Walk.snd] using hqsnd
  have hq3 : q.getVert 3 = x := by
    simpa [hlen] using (show q.getVert q.length = x by simp)
  refine ⟨q.getVert 2, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [hq1] using q.adj_getVert_succ (i := 0) (by omega)
  · simpa [hq1] using q.adj_getVert_succ (i := 1) (by omega)
  · simpa [hq3] using q.adj_getVert_succ (i := 2) (by omega)
  · intro hab
    have hEq : q.getVert 1 = q.getVert 2 := hq1.trans hab
    have hind := hqcycle.getVert_injOn (by simp; omega) (by simp; omega) hEq
    omega
  · intro hbx
    have hEq : q.getVert 2 = x := hbx
    have hends := (hqcycle.getVert_endpoint_iff (i := 2) (by omega)).mp hEq
    omega

/-- Every spoke of the bare hub's even component belongs to a literal triangle
petal.  This is the component-level form of the preceding cycle calculation:
the non-bridge argument supplies the cycle, and the long-cycle exclusion turns
it into a triangle. -/
theorem bare_hub_spoke_triangle_in_component
    (h : V) (x a : evenVertices G) (H : BareMinimalCounterexample G h (x : V))
    (C : (evenSubgraph G).ConnectedComponent)
    (hxC : x ∈ C.supp) (haC : a ∈ C.supp)
    (hxa : (evenSubgraph G).Adj x a) :
    ∃ b : evenVertices G,
      (evenSubgraph G).Adj x a ∧ (evenSubgraph G).Adj a b ∧
        (evenSubgraph G).Adj b x ∧ a ≠ b ∧ b ≠ x := by
  obtain ⟨p, hp, hpSpoke⟩ :=
    bare_hub_spoke_exists_cycle h x a H C hxC haC hxa
  exact bare_minimal_spoke_cycle_triangle h x a H p hp hpSpoke

/-- The mate of a hub spoke is unique.  Indeed the private endpoint has
E-degree two, and its two even neighbours are already the hub and the mate.
This is the local non-overlap certificate for triangle petals. -/
theorem bare_hub_spoke_triangle_mate_unique
    (h : V) (x a b c : evenVertices G) (H : BareMinimalCounterexample G h (x : V))
    (hxa : (evenSubgraph G).Adj x a)
    (hab : (evenSubgraph G).Adj a b) (hbx : (evenSubgraph G).Adj b x)
    (hac : (evenSubgraph G).Adj a c) (hcx : (evenSubgraph G).Adj c x) : b = c := by
  have hax : (a : V) ≠ (x : V) := by
    intro hax
    exact hxa.ne (Subtype.ext hax.symm)
  have haDeg := bare_hub_private_eDegree_eq_two h x a H hxa.reachable hax
  have haxmem : (x : V) ∈ evenNeighbors G (a : V) :=
    (mem_evenNeighbors (G := G) (a : V) (x : V)).mpr ⟨hxa.symm, x.property⟩
  have habmem : (b : V) ∈ evenNeighbors G (a : V) :=
    (mem_evenNeighbors (G := G) (a : V) (b : V)).mpr ⟨hab, b.property⟩
  have hxb : (x : V) ≠ (b : V) := by
    intro hxb
    exact hbx.ne (Subtype.ext hxb.symm)
  rcases even_neighbors_pair_of_degree_two (a : V) (x : V) (b : V)
      haDeg haxmem habmem hxb (c : V) hac c.property with hcx' | hcb
  · exact (hcx.ne (Subtype.ext hcx')).elim
  · exact Subtype.ext hcb.symm

/-- Every non-hub vertex in the bare hub's even component is itself a hub
neighbour.  A shortest component path that began `x-a-b` would be shortened
by the triangle petal on `xa`, whose mate is forced to be `b`. -/
theorem bare_hub_component_nonhub_adjacent_to_hub
    (h : V) (x z : evenVertices G) (H : BareMinimalCounterexample G h (x : V))
    (C : (evenSubgraph G).ConnectedComponent) (hxC : x ∈ C.supp)
    (hreached : (evenSubgraph G).Reachable x z) (hzx : (z : V) ≠ (x : V)) :
    (evenSubgraph G).Adj x z := by
  classical
  by_contra hxz
  obtain ⟨p, hp, hdist⟩ := hreached.exists_path_of_dist
  have hlen : 2 ≤ p.length := by
    by_contra hnot
    have hle : p.length ≤ 1 := by omega
    have hcases : p.length = 0 ∨ p.length = 1 := by omega
    rcases hcases with hzero | hone
    · have heq : (z : V) = (x : V) := by
        calc
          (z : V) = (p.getVert p.length : V) := by simp
          _ = (p.getVert 0 : V) := by simp [hzero]
          _ = (x : V) := by simp
      exact hzx heq
    · have hpath : (evenSubgraph G).Adj x z := by
        have hp1 : p.getVert 1 = z := by
          rw [← hone]
          simp
        simpa only [SimpleGraph.Walk.getVert_zero, hp1] using
          p.adj_getVert_succ (i := 0) (by omega)
      exact hxz hpath
  let a : evenVertices G := p.getVert 1
  have hxa : (evenSubgraph G).Adj x a := by
    dsimp [a]
    simpa using p.adj_getVert_succ (i := 0) (by omega)
  have haC : a ∈ C.supp := C.mem_supp_of_adj_mem_supp hxC hxa
  obtain ⟨b, _, hab, hbx, _, _⟩ :=
    bare_hub_spoke_triangle_in_component h x a H C hxC haC hxa
  have hax : (a : V) ≠ (x : V) := by
    intro hax
    exact hxa.ne (Subtype.ext hax.symm)
  have haDeg := bare_hub_private_eDegree_eq_two h x a H hxa.reachable hax
  have haxmem : (x : V) ∈ evenNeighbors G (a : V) :=
    (mem_evenNeighbors (G := G) (a : V) (x : V)).mpr ⟨hxa.symm, x.property⟩
  have habmem : (b : V) ∈ evenNeighbors G (a : V) :=
    (mem_evenNeighbors (G := G) (a : V) (b : V)).mpr ⟨hab, b.property⟩
  have hxb : (x : V) ≠ (b : V) := by
    intro hxb
    exact hbx.ne (Subtype.ext hxb.symm)
  have hap2 : (evenSubgraph G).Adj a (p.getVert 2) := by
    dsimp [a]
    simpa using p.adj_getVert_succ (i := 1) (by omega)
  have hp2ne : p.getVert 2 ≠ x := by
    intro heq
    have hEq : p.getVert 2 = p.getVert 0 := by simpa using heq
    have hind := hp.getVert_injOn (by simp; omega) (by simp) hEq
    omega
  have hp2b : p.getVert 2 = b := by
    rcases even_neighbors_pair_of_degree_two (a : V) (x : V) (b : V)
        haDeg haxmem habmem hxb (p.getVert 2 : V) hap2 (p.getVert 2).property with hp2x | hp2b
    · exact (hp2ne (Subtype.ext hp2x)).elim
    · exact Subtype.ext hp2b
  have hshortcut : (evenSubgraph G).Adj x (p.getVert 2) := by
    simpa [hp2b] using hbx.symm
  let q : (evenSubgraph G).Walk x z := SimpleGraph.Walk.cons hshortcut (p.drop 2)
  have hqLen : q.length = 1 + (p.length - 2) := by
    simp [q, Nat.add_comm]
  have hdistLe : (evenSubgraph G).dist x z ≤ q.length := SimpleGraph.dist_le q
  rw [← hdist, hqLen] at hdistLe
  omega

/-- The bare hub component is exactly the hub together with its neighbours;
each private vertex has a unique private mate.  Thus its private edges form
disjoint pairs, and each pair together with the hub forms a whole triangle. -/
theorem bare_windmill
    (h : V) (x : evenVertices G) (H : BareMinimalCounterexample G h (x : V))
    (C : (evenSubgraph G).ConnectedComponent) (hxC : x ∈ C.supp) :
    (∀ a, a ∈ C.supp ↔ a = x ∨ (evenSubgraph G).Adj x a) ∧
    (∀ a, (evenSubgraph G).Adj x a →
      ∃! b, (evenSubgraph G).Adj a b ∧ (evenSubgraph G).Adj b x) := by
  constructor
  · intro a
    constructor
    · intro haC
      by_cases hax : a = x
      · exact Or.inl hax
      · right
        apply bare_hub_component_nonhub_adjacent_to_hub h x a H C hxC
          (C.reachable_of_mem_supp hxC haC)
        intro heq
        exact hax (Subtype.ext heq)
    · rintro (rfl | hxa)
      · exact hxC
      · exact C.mem_supp_of_adj_mem_supp hxC hxa
  · intro a hxa
    have haC := C.mem_supp_of_adj_mem_supp hxC hxa
    obtain ⟨b, _, hab, hbx, _, _⟩ :=
      bare_hub_spoke_triangle_in_component h x a H C hxC haC hxa
    refine ⟨b, ⟨hab, hbx⟩, ?_⟩
    intro c hc
    exact (bare_hub_spoke_triangle_mate_unique h x a b c H
      hxa hab hbx hc.1 hc.2).symm

/-- The finite hub-neighbour type admits a fixed-point-free mate involution.
Its two-element orbits are precisely the private pairs of the petals. -/
theorem bare_windmill_mate_involution
    (h : V) (x : evenVertices G) (H : BareMinimalCounterexample G h (x : V))
    (C : (evenSubgraph G).ConnectedComponent) (hxC : x ∈ C.supp) :
    ∃ f : {a : evenVertices G // (evenSubgraph G).Adj x a} →
        {a : evenVertices G // (evenSubgraph G).Adj x a},
      Function.Involutive f ∧
      (∀ a, f a ≠ a) ∧
      (∀ a, (evenSubgraph G).Adj a.val (f a).val) ∧
      (∀ a b, (evenSubgraph G).Adj a.val b.val ↔ f a = b) := by
  classical
  let N := {a : evenVertices G // (evenSubgraph G).Adj x a}
  have hex : ∀ a : N, ∃ b : N, (evenSubgraph G).Adj a.val b.val := by
    intro a
    obtain ⟨b, hb, _⟩ := (bare_windmill h x H C hxC).2 a.val a.property
    exact ⟨⟨b, hb.2.symm⟩, hb.1⟩
  choose f hf using hex
  refine ⟨f, ?_, ?_, hf, ?_⟩
  · intro a
    apply Subtype.ext
    exact (bare_hub_spoke_triangle_mate_unique h x (f a).val a.val (f (f a)).val H
      (f a).property (hf a).symm a.property.symm
      (hf (f a)) (f (f a)).property.symm).symm
  · intro a heq
    have hadj := hf a
    rw [heq] at hadj
    exact hadj.ne rfl
  · intro a b
    constructor
    · intro hab
      apply Subtype.ext
      exact bare_hub_spoke_triangle_mate_unique h x a.val (f a).val b.val H
        a.property (hf a) (f a).property.symm hab b.property.symm
    · intro heq
      simpa only [heq] using hf a

/-- Choose one index for each two-element orbit of a finite fixed-point-free
involution. Each element belongs to exactly one indexed pair. -/
theorem finite_involution_pair_indices {N : Type*} [Fintype N]
    (f : N → N) (hinv : Function.Involutive f) (hfree : ∀ a, f a ≠ a) :
    ∃ R : Finset N, ∀ a, ∃! r, r ∈ R ∧ (a = r ∨ a = f r) := by
  classical
  let rank := Fintype.equivFin N
  let R := Finset.univ.filter fun a => rank a < rank (f a)
  have hmem : ∀ r, r ∈ R ↔ rank r < rank (f r) := by
    intro r
    simp [R]
  have hneq : ∀ a, rank a ≠ rank (f a) := by
    intro a heq
    exact hfree a (rank.injective heq).symm
  refine ⟨R, ?_⟩
  intro a
  have hex : ∃ r, r ∈ R ∧ (a = r ∨ a = f r) := by
    rcases lt_or_gt_of_ne (hneq a) with hlt | hgt
    · exact ⟨a, (hmem a).mpr hlt, Or.inl rfl⟩
    · refine ⟨f a, (hmem (f a)).mpr ?_, Or.inr (hinv a).symm⟩
      simpa only [hinv a] using hgt
  obtain ⟨r, hr, har⟩ := hex
  refine ⟨r, ⟨hr, har⟩, ?_⟩
  rintro s ⟨hs, has⟩
  have hrlt := (hmem r).mp hr
  have hslt := (hmem s).mp hs
  rcases har with har | har <;> rcases has with has | has
  · exact has.symm.trans har
  · have hrs : r = f s := har.symm.trans has
    rw [hrs, hinv s] at hrlt
    exact (lt_asymm hrlt hslt).elim
  · have hsr : s = f r := has.symm.trans har
    rw [hsr, hinv r] at hslt
    exact (lt_asymm hrlt hslt).elim
  · exact hinv.injective (has.symm.trans har)

/-- The hub's private vertices have a finite, non-overlapping petal index.
The index covers every private vertex once, and the mate relation describes
all private edges, not just the edges selected in a triangle witness. -/
theorem bare_windmill_indexed_petals
    (h : V) (x : evenVertices G) (H : BareMinimalCounterexample G h (x : V))
    (C : (evenSubgraph G).ConnectedComponent) (hxC : x ∈ C.supp) :
    ∃ (f : {a : evenVertices G // (evenSubgraph G).Adj x a} →
          {a : evenVertices G // (evenSubgraph G).Adj x a})
      (R : Finset {a : evenVertices G // (evenSubgraph G).Adj x a}),
      Function.Involutive f ∧ (∀ a, f a ≠ a) ∧
      (∀ a, ∃! r, r ∈ R ∧ (a = r ∨ a = f r)) ∧
      (∀ a b, (evenSubgraph G).Adj a.val b.val ↔ f a = b) ∧
      (∀ a, a ∈ C.supp ↔ a = x ∨ (evenSubgraph G).Adj x a) := by
  classical
  obtain ⟨f, hinv, hfree, _, hedge⟩ := bare_windmill_mate_involution h x H C hxC
  obtain ⟨R, hR⟩ := finite_involution_pair_indices f hinv hfree
  exact ⟨f, R, hinv, hfree, hR, hedge, (bare_windmill h x H C hxC).1⟩

end Gallai.TwoException
