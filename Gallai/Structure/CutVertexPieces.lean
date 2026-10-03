/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.Structure.OneVertexSeparation
public import Mathlib.Data.Set.Card

@[expose] public section

/-! # Actual connected pieces from a disconnected vertex deletion

Reachability after deletion determines one side. Both sides retain the
separator and at least one other vertex. Their induced graphs cover every
original edge and are connected; no connected-piece hypothesis is supplied.
-/

namespace Gallai

variable {V : Type*} (G : SimpleGraph V)

/-- An induced spanning graph retains precisely edges with both ends in its set. -/
theorem spanning_induce_adj_iff (S : Set V) (a b : V) :
    (G.induce S).spanningCoe.Adj a b ↔ G.Adj a b ∧ a ∈ S ∧ b ∈ S := by
  constructor
  · intro h
    obtain ⟨u, v, huv, rfl, rfl⟩ :=
      (SimpleGraph.map_adj (Function.Embedding.subtype _) (G.induce S) a b).mp h
    exact ⟨huv, u.property, v.property⟩
  · rintro ⟨hab, ha, hb⟩
    exact (SimpleGraph.map_adj (Function.Embedding.subtype _) (G.induce S) a b).mpr
      ⟨⟨a, ha⟩, ⟨b, hb⟩, hab, rfl, rfl⟩

/-- In a disconnected graph, the connected component of any chosen vertex
misses some vertex. This pins a cut-piece construction at a designated
surviving vertex instead of relying on arbitrary disconnectedness witnesses. -/
theorem exists_not_reachable_of_not_connected (a : V) (hdisc : ¬ G.Connected) :
    ∃ b : V, ¬ G.Reachable a b := by
  classical
  by_contra h
  push Not at h
  apply hdisc
  exact G.connected_iff_exists_forall_reachable.mpr ⟨a, h⟩

/-- The connected component selected after deleting `z` remains connected
when regarded as the corresponding induced graph of the original graph.
This makes explicit the component choice used in hub-cut arguments: the
selected side is not merely one member of an arbitrary binary separation. -/
theorem induced_component_after_delete_connected (z a : V) (ha : a ≠ z) :
    (G.induce {v | v ≠ z ∧ ∃ hv : v ≠ z,
      (G.induce {q | q ≠ z}).Reachable ⟨a, ha⟩ ⟨v, hv⟩}).Connected := by
  classical
  let K : SimpleGraph {q : V | q ≠ z} := G.induce {q | q ≠ z}
  let aK : {q : V | q ≠ z} := ⟨a, ha⟩
  let C : K.ConnectedComponent := K.connectedComponentMk aK
  let U : Set V := {v | v ≠ z ∧ ∃ hv : v ≠ z,
    K.Reachable aK ⟨v, hv⟩}
  let f : (K.induce C.supp) →g (G.induce U) :=
    { toFun := fun q => ⟨q.val.val, by
        constructor
        · exact q.val.property
        · refine ⟨q.val.property, ?_⟩
          apply SimpleGraph.ConnectedComponent.exact
          have hq := (SimpleGraph.ConnectedComponent.mem_supp_iff C q.val).mp q.property
          simpa [C] using hq.symm
        ⟩
      map_rel' := by
        intro p q hpq
        change G.Adj p.val.val q.val.val
        simpa [K] using hpq }
  have hsurj : Function.Surjective f := by
    intro u
    rcases u.property with ⟨huz, hv, hur⟩
    let uK : {q : V | q ≠ z} := ⟨u.val, huz⟩
    have huC : uK ∈ C.supp := by
      rw [SimpleGraph.ConnectedComponent.mem_supp_iff]
      simpa [C, uK] using (SimpleGraph.ConnectedComponent.sound hur).symm
    let uC : {q : {q : V | q ≠ z} | q ∈ C.supp} := ⟨uK, huC⟩
    refine ⟨uC, ?_⟩
    apply Subtype.ext
    rfl
  have hc : (K.induce C.supp).Connected :=
    SimpleGraph.ConnectedComponent.connected_toSimpleGraph C
  have hout := hc.map f hsurj
  simpa [K, aK, C, U] using hout

/-- Two vertices separated by deletion of z produce a nontrivial connected
two-piece decomposition of the original connected graph. -/
theorem cut_vertex_pieces (hconn : G.Connected) (z a b : V)
    (ha : a ≠ z) (hb : b ≠ z)
    (hn : ¬ (G.induce {v | v ≠ z}).Reachable ⟨a, ha⟩ ⟨b, hb⟩) :
    ∃ S T : Set V, S ∪ T = Set.univ ∧ S ∩ T = {z} ∧
      a ∈ S ∧ b ∈ T ∧
      (G.induce S).spanningCoe ⊔ (G.induce T).spanningCoe = G ∧
      (G.induce S).Connected ∧ (G.induce T).Connected := by
  classical
  let K := G.induce {v | v ≠ z}
  let S : Set V := {v | v = z ∨ ∃ hv : v ≠ z, K.Reachable ⟨a, ha⟩ ⟨v, hv⟩}
  let T : Set V := {v | v = z ∨ v ∉ S}
  have hzS : z ∈ S := Or.inl rfl
  have hzT : z ∈ T := Or.inl rfl
  have haS : a ∈ S := Or.inr ⟨ha, SimpleGraph.Reachable.refl _⟩
  have hbS : b ∉ S := by
    rintro (h | ⟨hv, hr⟩)
    · exact hb h
    · exact hn hr
  have hbT : b ∈ T := Or.inr hbS
  have hinterVertex (v : V) (hs : v ∈ S) (ht : v ∈ T) : v = z := by
    rcases ht with h | h
    · exact h
    · exact (h hs).elim
  have hcover : S ∪ T = Set.univ := by
    ext v
    simp only [Set.mem_union, Set.mem_univ, iff_true]
    by_cases h : v ∈ S
    · exact Or.inl h
    · exact Or.inr (Or.inr h)
  have hinter : S ∩ T = {z} := by
    ext v
    constructor
    · exact fun h => hinterVertex v h.1 h.2
    · rintro rfl
      exact ⟨hzS, hzT⟩
  have hclosed (u : V) (hu : u ∈ S) (huz : u ≠ z)
      (v : V) (huv : G.Adj u v) : v ∈ S := by
    by_cases hvz : v = z
    · exact Or.inl hvz
    obtain ⟨huz', hr⟩ := hu.resolve_left huz
    exact Or.inr ⟨hvz, hr.trans
      (show K.Adj ⟨u, huz'⟩ ⟨v, hvz⟩ from huv).reachable⟩
  have hclosedT (u : V) (hu : u ∈ T) (huz : u ≠ z)
      (v : V) (huv : G.Adj u v) : v ∈ T := by
    by_cases hvz : v = z
    · exact Or.inl hvz
    refine Or.inr ?_
    intro hv
    exact (hu.resolve_left huz) (hclosed v hv hvz u huv.symm)
  have hgraph : (G.induce S).spanningCoe ⊔ (G.induce T).spanningCoe = G := by
    apply le_antisymm
    · exact sup_le (G.spanningCoe_induce_le S) (G.spanningCoe_induce_le T)
    · intro u v huv
      by_cases huz : u = z
      · subst u
        by_cases hv : v ∈ S
        · exact Or.inl ((spanning_induce_adj_iff G S z v).mpr ⟨huv, hzS, hv⟩)
        · exact Or.inr ((spanning_induce_adj_iff G T z v).mpr
            ⟨huv, hzT, Or.inr hv⟩)
      · by_cases hu : u ∈ S
        · exact Or.inl ((spanning_induce_adj_iff G S u v).mpr
            ⟨huv, hu, hclosed u hu huz v huv⟩)
        · have huT : u ∈ T := Or.inr hu
          exact Or.inr ((spanning_induce_adj_iff G T u v).mpr
            ⟨huv, huT, hclosedT u huT huz v huv⟩)
  have connected_piece (U W : Set V) (hzU : z ∈ U)
      (hmeet : ∀ v, v ∈ U → v ∈ W → v = z)
      (heq : (G.induce W).spanningCoe ⊔ (G.induce U).spanningCoe = G) :
      (G.induce U).Connected := by
    have hc : ((G.induce W).spanningCoe ⊔ (G.induce U).spanningCoe).Connected :=
      heq.symm ▸ hconn
    have h := connected_right_of_one_vertex_separation
      (G.induce W).spanningCoe (G.induce U).spanningCoe U z hc hzU
      (fun v w hvw => ((spanning_induce_adj_iff G U v w).mp hvw).2.1)
      (fun v w hvw hv => hmeet v hv ((spanning_induce_adj_iff G W v w).mp hvw).2.1)
    simpa only [SimpleGraph.induce_spanningCoe] using h
  exact ⟨S, T, hcover, hinter, haS, hbT, hgraph,
    connected_piece S T hzS hinterVertex ((sup_comm _ _).trans hgraph),
    connected_piece T S hzT (fun v ht hs => hinterVertex v hs ht) hgraph⟩

/-- The reachability-selected version of `cut_vertex_pieces`.  In addition to
the ordinary two-piece data, it records that the side containing `a` remains
connected after the separator is removed.  This is the exact orientation used
when a source proof chooses a hub-containing piece `G₁` with `G₁ - z`
connected. -/
theorem cut_vertex_pieces_with_selected_core (hconn : G.Connected) (z a b : V)
    (ha : a ≠ z) (hb : b ≠ z)
    (hn : ¬ (G.induce {v | v ≠ z}).Reachable ⟨a, ha⟩ ⟨b, hb⟩) :
    ∃ S T : Set V, S ∪ T = Set.univ ∧ S ∩ T = {z} ∧
      a ∈ S ∧ b ∈ T ∧
      (G.induce S).spanningCoe ⊔ (G.induce T).spanningCoe = G ∧
      (G.induce S).Connected ∧ (G.induce T).Connected ∧
      (G.induce {v | v ∈ S ∧ v ≠ z}).Connected := by
  classical
  let K := G.induce {v | v ≠ z}
  let S : Set V := {v | v = z ∨ ∃ hv : v ≠ z, K.Reachable ⟨a, ha⟩ ⟨v, hv⟩}
  let T : Set V := {v | v = z ∨ v ∉ S}
  have hzS : z ∈ S := Or.inl rfl
  have hzT : z ∈ T := Or.inl rfl
  have haS : a ∈ S := Or.inr ⟨ha, SimpleGraph.Reachable.refl _⟩
  have hbS : b ∉ S := by
    rintro (h | ⟨hv, hr⟩)
    · exact hb h
    · exact hn hr
  have hbT : b ∈ T := Or.inr hbS
  have hinterVertex (v : V) (hs : v ∈ S) (ht : v ∈ T) : v = z := by
    rcases ht with h | h
    · exact h
    · exact (h hs).elim
  have hcover : S ∪ T = Set.univ := by
    ext v
    simp only [Set.mem_union, Set.mem_univ, iff_true]
    by_cases h : v ∈ S
    · exact Or.inl h
    · exact Or.inr (Or.inr h)
  have hinter : S ∩ T = {z} := by
    ext v
    constructor
    · exact fun h => hinterVertex v h.1 h.2
    · rintro rfl
      exact ⟨hzS, hzT⟩
  have hclosed (u : V) (hu : u ∈ S) (huz : u ≠ z)
      (v : V) (huv : G.Adj u v) : v ∈ S := by
    by_cases hvz : v = z
    · exact Or.inl hvz
    obtain ⟨huz', hr⟩ := hu.resolve_left huz
    exact Or.inr ⟨hvz, hr.trans
      (show K.Adj ⟨u, huz'⟩ ⟨v, hvz⟩ from huv).reachable⟩
  have hclosedT (u : V) (hu : u ∈ T) (huz : u ≠ z)
      (v : V) (huv : G.Adj u v) : v ∈ T := by
    by_cases hvz : v = z
    · exact Or.inl hvz
    refine Or.inr ?_
    intro hv
    exact (hu.resolve_left huz) (hclosed v hv hvz u huv.symm)
  have hgraph : (G.induce S).spanningCoe ⊔ (G.induce T).spanningCoe = G := by
    apply le_antisymm
    · exact sup_le (G.spanningCoe_induce_le S) (G.spanningCoe_induce_le T)
    · intro u v huv
      by_cases huz : u = z
      · subst u
        by_cases hv : v ∈ S
        · exact Or.inl ((spanning_induce_adj_iff G S z v).mpr ⟨huv, hzS, hv⟩)
        · exact Or.inr ((spanning_induce_adj_iff G T z v).mpr
            ⟨huv, hzT, Or.inr hv⟩)
      · by_cases hu : u ∈ S
        · exact Or.inl ((spanning_induce_adj_iff G S u v).mpr
            ⟨huv, hu, hclosed u hu huz v huv⟩)
        · have huT : u ∈ T := Or.inr hu
          exact Or.inr ((spanning_induce_adj_iff G T u v).mpr
            ⟨huv, huT, hclosedT u huT huz v huv⟩)
  have connected_piece (U W : Set V) (hzU : z ∈ U)
      (hmeet : ∀ v, v ∈ U → v ∈ W → v = z)
      (heq : (G.induce W).spanningCoe ⊔ (G.induce U).spanningCoe = G) :
      (G.induce U).Connected := by
    have hc : ((G.induce W).spanningCoe ⊔ (G.induce U).spanningCoe).Connected :=
      heq.symm ▸ hconn
    have h := connected_right_of_one_vertex_separation
      (G.induce W).spanningCoe (G.induce U).spanningCoe U z hc hzU
      (fun v w hvw => ((spanning_induce_adj_iff G U v w).mp hvw).2.1)
      (fun v w hvw hv => hmeet v hv ((spanning_induce_adj_iff G W v w).mp hvw).2.1)
    simpa only [SimpleGraph.induce_spanningCoe] using h
  have hcore : (G.induce {v | v ∈ S ∧ v ≠ z}).Connected := by
    have hset : {v | v ∈ S ∧ v ≠ z} =
        {v | v ≠ z ∧ ∃ hv : v ≠ z,
          (G.induce {q | q ≠ z}).Reachable ⟨a, ha⟩ ⟨v, hv⟩} := by
      ext v
      simp only [Set.mem_ofPred_eq, S, K]
      constructor
      · rintro ⟨h | ⟨hv, hr⟩, hvz⟩
        · exact (hvz h).elim
        · exact ⟨hvz, ⟨hv, hr⟩⟩
      · rintro ⟨hvz, hv, hr⟩
        exact ⟨Or.inr ⟨hv, hr⟩, hvz⟩
    rw [hset]
    exact induced_component_after_delete_connected G z a ha
  exact ⟨S, T, hcover, hinter, haS, hbT, hgraph,
    connected_piece S T hzS hinterVertex ((sup_comm _ _).trans hgraph),
    connected_piece T S hzT (fun v ht hs => hinterVertex v hs ht) hgraph, hcore⟩

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- A nontrivial connected induced piece with one edge is precisely that edge.
Choosing a distinguished vertex `x` in the piece identifies its unique
neighbour `w`, and every vertex of the piece is one of `x,w`.  This is the
structural classification needed when a source cut argument reaches a
one-edge opposite piece. -/
theorem connected_induced_one_edge_eq (T : Set V) [DecidablePred (· ∈ T)]
    (x : V) (hxT : x ∈ T) (hother : ∃ b ∈ T, b ≠ x)
    (hconn : (G.induce T).Connected)
    (hedge : (G.induce T).edgeFinset.card = 1) :
    ∃ w : V, w ≠ x ∧ G.Adj x w ∧ T = {x, w} := by
  classical
  let K : SimpleGraph T := G.induce T
  obtain ⟨b, hbT, hbx⟩ := hother
  letI : Nontrivial T := ⟨⟨x, hxT⟩, ⟨b, hbT⟩,
    fun h => hbx (congrArg Subtype.val h).symm⟩
  have hxdeg : 0 < K.degree ⟨x, hxT⟩ :=
    hconn.preconnected.degree_pos_of_nontrivial ⟨x, hxT⟩
  obtain ⟨wT, hxwK⟩ := (K.degree_pos_iff_exists_adj ⟨x, hxT⟩).mp hxdeg
  have hxw : G.Adj x wT.val := by
    simpa [K] using hxwK
  have hwx : wT.val ≠ x := hxw.ne.symm
  obtain ⟨e, he⟩ := Finset.card_eq_one.mp hedge
  have hxwE : s(⟨x, hxT⟩, wT) ∈ K.edgeFinset :=
    SimpleGraph.mem_edgeFinset.mpr hxwK
  rw [he] at hxwE
  have hxwEq : s(⟨x, hxT⟩, wT) = e := by simpa using hxwE
  refine ⟨wT.val, hwx, hxw, ?_⟩
  ext v
  constructor
  · intro hvT
    let vT : T := ⟨v, hvT⟩
    have hvdeg : 0 < K.degree vT :=
      hconn.preconnected.degree_pos_of_nontrivial vT
    obtain ⟨rT, hvrK⟩ := (K.degree_pos_iff_exists_adj vT).mp hvdeg
    have hvrE : s(vT, rT) ∈ K.edgeFinset :=
      SimpleGraph.mem_edgeFinset.mpr hvrK
    rw [he] at hvrE
    have hvrEqE : s(vT, rT) = e := by simpa using hvrE
    have hvrEq : s(vT, rT) = s(⟨x, hxT⟩, wT) :=
      hvrEqE.trans hxwEq.symm
    rcases Sym2.eq_iff.mp hvrEq with h | h
    · exact Or.inl (congrArg Subtype.val h.1)
    · exact Or.inr (congrArg Subtype.val h.1)
  · intro hv
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
    rcases hv with rfl | rfl
    · exact hxT
    · exact wT.property

/-- Each actual cut piece is strictly smaller in edges when the opposite
side contains a vertex other than the separator. -/
theorem cut_piece_edge_count_lt (S T : Set V)
    [DecidablePred (· ∈ S)] [DecidablePred (· ∈ T)]
    (z : V) (hconn : G.Connected) (hzT : z ∈ T)
    (hmeet : ∀ v, v ∈ S → v ∈ T → v = z)
    (hgraph : (G.induce S).spanningCoe ⊔ (G.induce T).spanningCoe = G)
    (hother : ∃ b ∈ T, b ≠ z) :
    (G.induce S).edgeFinset.card < G.edgeFinset.card := by
  classical
  let L := (G.induce S).spanningCoe
  let R := (G.induce T).spanningCoe
  have hc : (L ⊔ R).Connected := hgraph.symm ▸ hconn
  have hl (a b : V) (h : L.Adj a b) : a ∈ S :=
    ((spanning_induce_adj_iff G S a b).mp h).2.1
  have hr (a b : V) (h : R.Adj a b) : a ∈ T :=
    ((spanning_induce_adj_iff G T a b).mp h).2.1
  obtain ⟨w, hw⟩ := joint_neighbor_of_one_vertex_separation L R T z hc hzT hr
    (fun a b h ha => hmeet a (hl a b h) ha) hother
  have hlt := right_edge_count_lt_of_one_vertex_separation R L S z hl
    (fun a b h ha => hmeet a ha (hr a b h)) ⟨z, w, hw⟩
  have heq : R ⊔ L = G := (sup_comm _ _).trans hgraph
  have hLS : L.induce S = G.induce S := SimpleGraph.induce_spanningCoe
  simp only [SimpleGraph.edgeFinset, ← Set.ncard_eq_toFinset_card'] at hlt ⊢
  rw [hLS, heq] at hlt
  exact hlt

/-- A genuine vertex on the opposite side of a one-vertex cut makes the
chosen induced-side vertex type strictly smaller than the ambient type.  This
is the vertex-order input for relative induction on a cut piece. -/
theorem cut_piece_card_lt (S T : Set V)
    [DecidablePred (· ∈ S)] [DecidablePred (· ∈ T)]
    (z b : V) (hinter : S ∩ T = {z}) (hbT : b ∈ T) (hbz : b ≠ z) :
    Fintype.card S < Fintype.card V := by
  apply Fintype.card_subtype_lt
  intro hbS
  have hmem : b ∈ S ∩ T := ⟨hbS, hbT⟩
  have : b = z := by simpa only [hinter, Set.mem_singleton_iff] using hmem
  exact hbz this

/-- The correct FHZ arithmetic: two ceiling budgets and one saved path
fit the ceiling budget of a union sharing one vertex. -/
theorem ceiling_one_vertex_budget (a b n : ℕ) (hn : n + 1 = a + b) :
    (a + 1) / 2 + (b + 1) / 2 - 1 ≤ (n + 1) / 2 := by omega

end Gallai
