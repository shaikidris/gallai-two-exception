/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.BareOrdinaryDegreeThree
public import Gallai.TwoException.BareWindmill
public import Gallai.TwoException.OrdinaryCycleContacts

@[expose] public section

/-! # Ordinary cycle reduction in the bare two-exception kernel -/

namespace Gallai.TwoException

universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- After degree-one and degree-three elimination, every vertex in an
ordinary even-subgraph component has E-degree zero or two. -/
theorem bare_ordinary_degree_zero_or_two
    (z w : evenVertices G) (h : V)
    (H : BareMinimalCounterexample G h (z : V))
    (C : (evenSubgraph G).ConnectedComponent)
    (hz : z ∉ C.supp) (hw : w ∈ C.supp) :
    eDegree G (w : V) = 0 ∨ eDegree G (w : V) = 2 := by
  have hwz : (w : V) ≠ (z : V) := by
    intro heq
    exact hz (by simpa only [show w = z from Subtype.ext heq] using hw)
  have hcap : eDegree G (w : V) ≤ 3 := by
    by_cases hwh : (w : V) = h
    · rw [hwh, H.counterexample.1.2.2.2.2.2.1]; omega
    · exact H.counterexample.1.2.2.2.2.2.2 (w : V) w.property hwh hwz
  have hne1 := bare_ordinary_no_degree_one z w h H C hz hw
  have hne3 := bare_ordinary_no_degree_three z w h H C hz hw
  omega

/-- Consecutive arc partitions cannot both constrain a distinguished
puncture component to a singleton cycle contact in a bare counterexample.
The component and removed-edge endpoint set are literal graph data. -/
theorem bare_consecutive_contact_partitions_false
    (z h a b c : V) (H : BareCounterexample G h z)
    (J : SimpleGraph V) (C : J.ConnectedComponent) (A : Set V)
    (hh : h ∈ C.supp) (hz : z ∉ C.supp)
    (hab : a ≠ b) (hac : a ≠ c)
    (haEven : Even (G.degree a)) (hbEven : Even (G.degree b))
    (hah : a ≠ h) (haz : a ≠ z) (hbh : b ≠ h) (hbz : b ≠ z)
    (hremoved : ∀ u v, G.Adj u v → ¬ J.Adj u v → u ∈ A)
    (hne : (C.supp ∩ A).Nonempty)
    (hfirst : C.supp ∩ A ⊆ {a, b})
    (hnext : C.supp ∩ A ⊆ {b, c} ∨ Disjoint (C.supp ∩ A) {b, c}) :
    False := by
  have hsingle := consecutive_arc_contact_singleton (C.supp ∩ A) a b c
    hab hac hne hfirst hnext
  rcases hsingle with hsa | hsb
  · apply bare_even_separator_separating_hubs_false G a h z H hah haz haEven
    apply puncture_singleton_contact_not_reachable C A a h z hh hz hah.symm haz.symm
      hremoved
    intro u hu hA
    have hm : u ∈ C.supp ∩ A := ⟨hu, hA⟩
    rw [hsa] at hm
    exact hm
  · apply bare_even_separator_separating_hubs_false G b h z H hbh hbz hbEven
    apply puncture_singleton_contact_not_reachable C A b h z hh hz hbh.symm hbz.symm
      hremoved
    intro u hu hA
    have hm : u ∈ C.supp ∩ A := ⟨hu, hA⟩
    rw [hsb] at hm
    exact hm

/-- The complementary arc of the cycle x-a-b-c...x survives deletion of
xa and bc. Edge-trail uniqueness proves both removed edges are absent. -/
theorem two_edge_cycle_complementary_arc
    (x a b c : V) (hxa : G.Adj x a) (hab : G.Adj a b) (hbc : G.Adj b c)
    (q : G.Walk c x)
    (hp : (SimpleGraph.Walk.cons hxa
      (SimpleGraph.Walk.cons hab (SimpleGraph.Walk.cons hbc q))).IsTrail) :
    ∃ r : (twoEdgeCyclePuncture (G := G) x a b c).Walk c x,
      r.support = q.support := by
  classical
  have hnd : (s(x, a) :: s(a, b) :: s(b, c) :: q.edges).Nodup := hp.edges_nodup
  have hxaN : s(x, a) ∉ q.edges := by
    intro he
    exact (List.nodup_cons.mp hnd).1
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ he))
  have hbcN : s(b, c) ∉ q.edges :=
    (List.nodup_cons.mp (List.nodup_cons.mp (List.nodup_cons.mp hnd).2).2).1
  have hkeep : ∀ e, e ∈ q.edges →
      e ∈ (twoEdgeCyclePuncture (G := G) x a b c).edgeSet := by
    intro e he
    simp only [twoEdgeCyclePuncture, SimpleGraph.edgeSet_deleteEdges,
      Set.mem_sdiff, Set.mem_singleton_iff]
    exact ⟨⟨q.edges_subset_edgeSet he, fun heq => hxaN (heq ▸ he)⟩,
      fun heq => hbcN (heq ▸ he)⟩
  exact ⟨q.transfer _ hkeep, q.support_transfer hkeep⟩

/-- The two-vertex arc a-b survives the same two boundary-edge deletions. -/
theorem two_edge_cycle_inner_arc
    (x a b c : V) (hab : G.Adj a b) (hxb : x ≠ b) (hac : a ≠ c) :
    ∃ p : (twoEdgeCyclePuncture (G := G) x a b c).Walk a b,
      p.support = [a, b] := by
  have habP : (twoEdgeCyclePuncture (G := G) x a b c).Adj a b := by
    apply SimpleGraph.deleteEdges_adj.mpr
    refine ⟨SimpleGraph.deleteEdges_adj.mpr ⟨hab, ?_⟩, ?_⟩
    · intro heq
      rcases Sym2.eq_iff.mp heq with ⟨hax, hba⟩ | ⟨_, hbx⟩
      · exact hab.ne hba.symm
      · exact hxb hbx.symm
    · intro heq
      rcases Sym2.eq_iff.mp heq with ⟨hab', _⟩ | ⟨hac', _⟩
      · exact hab.ne hab'
      · exact hac hac'
  exact ⟨habP.toWalk, rfl⟩

/-- The two surviving walks cover the full original cycle support. The
construction works for any edge-trail cycle, including length four. -/
theorem two_edge_cycle_arc_support_cover
    (x a b c : V) (hxa : G.Adj x a) (hab : G.Adj a b) (hbc : G.Adj b c)
    (hxb : x ≠ b) (hac : a ≠ c) (q : G.Walk c x)
    (hp : (SimpleGraph.Walk.cons hxa
      (SimpleGraph.Walk.cons hab (SimpleGraph.Walk.cons hbc q))).IsTrail) :
    ∃ p : (twoEdgeCyclePuncture (G := G) x a b c).Walk a b,
    ∃ r : (twoEdgeCyclePuncture (G := G) x a b c).Walk c x,
      p.support = [a, b] ∧ r.support = q.support ∧
      ∀ v, v ∈ (SimpleGraph.Walk.cons hxa
        (SimpleGraph.Walk.cons hab (SimpleGraph.Walk.cons hbc q))).support ↔
          v ∈ p.support ∨ v ∈ r.support := by
  obtain ⟨p, hpS⟩ := two_edge_cycle_inner_arc x a b c hab hxb hac
  obtain ⟨r, hrS⟩ := two_edge_cycle_complementary_arc x a b c hxa hab hbc q hp
  refine ⟨p, r, hpS, hrS, ?_⟩
  intro v
  rw [hpS, hrS]
  simp only [SimpleGraph.Walk.support_cons, List.mem_cons, List.not_mem_nil, or_false]
  have hx : x ∈ q.support := q.end_mem_support
  constructor
  · rintro (rfl | rfl | rfl | hv)
    · exact Or.inr hx
    · exact Or.inl (Or.inl rfl)
    · exact Or.inl (Or.inr rfl)
    · exact Or.inr hv
  · rintro ((rfl | rfl) | hv)
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr hv))

/-- A failed literal two-edge cycle puncture forces each finer component's
cycle contacts onto one of its two surviving arcs. -/
theorem two_edge_cycle_contacts_partition
    (x a b c : V) (hxa : G.Adj x a) (hab : G.Adj a b) (hbc : G.Adj b c)
    (hxb : x ≠ b) (hac : a ≠ c) (q : G.Walk c x)
    (hp : (SimpleGraph.Walk.cons hxa
      (SimpleGraph.Walk.cons hab (SimpleGraph.Walk.cons hbc q))).IsTrail)
    (J : SimpleGraph V) (hle : J ≤ twoEdgeCyclePuncture (G := G) x a b c)
    (h z : V) (hnot : ¬ (twoEdgeCyclePuncture (G := G) x a b c).Reachable h z)
    (hh : ((J.connectedComponentMk h).supp ∩
      {v | v ∈ (SimpleGraph.Walk.cons hxa
        (SimpleGraph.Walk.cons hab (SimpleGraph.Walk.cons hbc q))).support}).Nonempty)
    (hz : ((J.connectedComponentMk z).supp ∩
      {v | v ∈ (SimpleGraph.Walk.cons hxa
        (SimpleGraph.Walk.cons hab (SimpleGraph.Walk.cons hbc q))).support}).Nonempty)
    (C : J.ConnectedComponent) :
    C.supp ∩ {v | v ∈ (SimpleGraph.Walk.cons hxa
      (SimpleGraph.Walk.cons hab (SimpleGraph.Walk.cons hbc q))).support} ⊆ {a, b} ∨
      Disjoint (C.supp ∩ {v | v ∈ (SimpleGraph.Walk.cons hxa
        (SimpleGraph.Walk.cons hab (SimpleGraph.Walk.cons hbc q))).support}) {a, b} := by
  obtain ⟨p, r, hpS, hrS, hcover⟩ :=
    two_edge_cycle_arc_support_cover x a b c hxa hab hbc hxb hac q hp
  have hset : {v | v ∈ (SimpleGraph.Walk.cons hxa
      (SimpleGraph.Walk.cons hab (SimpleGraph.Walk.cons hbc q))).support} =
      {v | v ∈ p.support ∨ v ∈ r.support} := Set.ext hcover
  have hpSet : {v | v ∈ p.support} = ({a, b} : Set V) := by
    ext v
    rw [hpS]
    simp
  rw [hset] at hh hz ⊢
  rw [← hpSet]
  exact puncture_contacts_respect_arc_walks hle p r h z hnot hh hz C

/-- Deleting every edge of a nonempty walk in a connected graph gives
every remaining component a contact on the actual walk support. -/
theorem full_cycle_puncture_contacts_nonempty
    (hconn : G.Connected) {a b : V} (p : G.Walk a b)
    (hne : p.edges ≠ []) (C : (G.deleteEdges p.edgeSet).ConnectedComponent) :
    (C.supp ∩ {v | v ∈ p.support}).Nonempty := by
  have hlt : G.deleteEdges p.edgeSet < G := by
    refine lt_of_le_of_ne (G.deleteEdges_le _) ?_
    intro heq
    obtain ⟨e, he⟩ := List.exists_mem_of_ne_nil p.edges hne
    have hG : e ∈ G.edgeSet := p.edges_subset_edgeSet he
    have hdel : e ∈ (G.deleteEdges p.edgeSet).edgeSet := by
      rw [heq]
      exact hG
    have hn : e ∉ p.edgeSet := (SimpleGraph.edgeSet_deleteEdges _ ▸ hdel).2
    exact hn he
  apply puncture_component_contacts_nonempty hconn hlt
    {v | v ∈ p.support} ?_ C
  intro u v huv hn
  have he : s(u, v) ∈ p.edgeSet := by
    by_contra he
    exact hn (SimpleGraph.deleteEdges_adj.mpr ⟨huv, he⟩)
  exact p.fst_mem_support_of_mem_edges he

/-- The full cycle deletion is a spanning subgraph of the two-edge
puncture: both boundary edges belong to the deleted cycle edge set. -/
theorem full_cycle_puncture_le_two_edge
    (x a b c : V) (hxa : G.Adj x a) (hab : G.Adj a b) (hbc : G.Adj b c)
    (q : G.Walk c x) :
    G.deleteEdges (SimpleGraph.Walk.cons hxa
      (SimpleGraph.Walk.cons hab (SimpleGraph.Walk.cons hbc q))).edgeSet ≤
        twoEdgeCyclePuncture (G := G) x a b c := by
  intro u v huv
  obtain ⟨huvG, hn⟩ := SimpleGraph.deleteEdges_adj.mp huv
  apply SimpleGraph.deleteEdges_adj.mpr
  refine ⟨SimpleGraph.deleteEdges_adj.mpr ⟨huvG, ?_⟩, ?_⟩
  · intro he
    apply hn
    have heq : s(u, v) = s(x, a) := he
    rw [heq]
    simp [SimpleGraph.Walk.mem_edgeSet, SimpleGraph.Walk.edges_cons]
  · intro he
    apply hn
    have heq : s(u, v) = s(b, c) := he
    rw [heq]
    simp [SimpleGraph.Walk.mem_edgeSet, SimpleGraph.Walk.edges_cons]

/-- The full-cycle contact partition follows from connectedness and an
actual failed two-edge puncture, without supplied inclusion or contacts. -/
theorem full_cycle_failed_puncture_partition
    (hconn : G.Connected) (x a b c : V)
    (hxa : G.Adj x a) (hab : G.Adj a b) (hbc : G.Adj b c)
    (hxb : x ≠ b) (hac : a ≠ c) (q : G.Walk c x)
    (hp : (SimpleGraph.Walk.cons hxa
      (SimpleGraph.Walk.cons hab (SimpleGraph.Walk.cons hbc q))).IsTrail)
    (h z : V) (hnot : ¬ (twoEdgeCyclePuncture (G := G) x a b c).Reachable h z)
    (C : (G.deleteEdges (SimpleGraph.Walk.cons hxa
      (SimpleGraph.Walk.cons hab (SimpleGraph.Walk.cons hbc q))).edgeSet).ConnectedComponent) :
    C.supp ∩ {v | v ∈ (SimpleGraph.Walk.cons hxa
      (SimpleGraph.Walk.cons hab (SimpleGraph.Walk.cons hbc q))).support} ⊆ {a, b} ∨
      Disjoint (C.supp ∩ {v | v ∈ (SimpleGraph.Walk.cons hxa
        (SimpleGraph.Walk.cons hab (SimpleGraph.Walk.cons hbc q))).support}) {a, b} := by
  let p := SimpleGraph.Walk.cons hxa
    (SimpleGraph.Walk.cons hab (SimpleGraph.Walk.cons hbc q))
  have hne : p.edges ≠ [] := by simp [p]
  exact two_edge_cycle_contacts_partition x a b c hxa hab hbc hxb hac q hp
    (G.deleteEdges p.edgeSet)
    (full_cycle_puncture_le_two_edge x a b c hxa hab hbc q) h z hnot
    (full_cycle_puncture_contacts_nonempty hconn p hne _)
    (full_cycle_puncture_contacts_nonempty hconn p hne _) C

/-- A singleton ordinary-even contact cannot separate the designated
vertices, regardless of which designated vertex lies in the component. -/
theorem bare_singleton_contact_either_side_false
    (z h a : V) (H : BareCounterexample G h z)
    (J : SimpleGraph V) (C : J.ConnectedComponent) (A : Set V)
    (hside : (h ∈ C.supp ∧ z ∉ C.supp) ∨ (z ∈ C.supp ∧ h ∉ C.supp))
    (haEven : Even (G.degree a)) (hah : a ≠ h) (haz : a ≠ z)
    (hremoved : ∀ u v, G.Adj u v → ¬ J.Adj u v → u ∈ A)
    (hcontact : C.supp ∩ A = {a}) : False := by
  apply bare_even_separator_separating_hubs_false G a h z H hah haz haEven
  have hsingle : ∀ u, u ∈ C.supp → u ∈ A → u = a := by
    intro u hu hA
    have hm : u ∈ C.supp ∩ A := ⟨hu, hA⟩
    rw [hcontact] at hm
    exact hm
  rcases hside with ⟨hh, hz⟩ | ⟨hz, hh⟩
  · exact puncture_singleton_contact_not_reachable C A a h z hh hz
      hah.symm haz.symm hremoved hsingle
  · intro hr
    exact puncture_singleton_contact_not_reachable C A a z h hz hh
      haz.symm hah.symm hremoved hsingle hr.symm

/-- Consecutive arc partitions contradict bare minimality on either
designated side of the failed puncture. -/
theorem bare_consecutive_contact_either_side_false
    (z h a b c : V) (H : BareCounterexample G h z)
    (J : SimpleGraph V) (C : J.ConnectedComponent) (A : Set V)
    (hside : (h ∈ C.supp ∧ z ∉ C.supp) ∨ (z ∈ C.supp ∧ h ∉ C.supp))
    (hab : a ≠ b) (hac : a ≠ c)
    (haEven : Even (G.degree a)) (hbEven : Even (G.degree b))
    (hah : a ≠ h) (haz : a ≠ z) (hbh : b ≠ h) (hbz : b ≠ z)
    (hremoved : ∀ u v, G.Adj u v → ¬ J.Adj u v → u ∈ A)
    (hne : (C.supp ∩ A).Nonempty) (hfirst : C.supp ∩ A ⊆ {a, b})
    (hnext : C.supp ∩ A ⊆ {b, c} ∨ Disjoint (C.supp ∩ A) {b, c}) :
    False := by
  rcases consecutive_arc_contact_singleton (C.supp ∩ A) a b c
      hab hac hne hfirst hnext with ha | hb
  · exact bare_singleton_contact_either_side_false z h a H J C A
      hside haEven hah haz hremoved ha
  · exact bare_singleton_contact_either_side_false z h b H J C A
      hside hbEven hbh hbz hremoved hb

/-- Moving the initial cycle edge to the end keeps the full deletion
unchanged and exposes the next consecutive boundary choice. -/
theorem cycle_shift_first_edge_set
    (x a : V) (hxa : G.Adj x a) (q : G.Walk a x) :
    (q.append hxa.toWalk).edgeSet = (SimpleGraph.Walk.cons hxa q).edgeSet := by
  ext e
  simp only [SimpleGraph.Walk.mem_edgeSet, SimpleGraph.Walk.edges_append,
    SimpleGraph.Walk.edges_cons, SimpleGraph.Walk.edges_nil,
    List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
  exact or_comm

/-- The consecutive edge shift preserves the actual contact vertex set. -/
theorem cycle_shift_first_edge_support
    (x a : V) (hxa : G.Adj x a) (q : G.Walk a x) :
    {v | v ∈ (q.append hxa.toWalk).support} =
      {v | v ∈ (SimpleGraph.Walk.cons hxa q).support} := by
  ext v
  simp only [SimpleGraph.Walk.mem_support_append_iff,
    SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil,
    List.mem_cons, List.not_mem_nil, or_false]
  have hx : x ∈ q.support := q.end_mem_support
  have ha : a ∈ q.support := q.start_mem_support
  constructor
  · rintro (hv | rfl | rfl)
    · exact Or.inr hv
    · exact Or.inl rfl
    · exact Or.inr ha
  · rintro (rfl | hv)
    · exact Or.inl hx
    · exact Or.inl hv

/-- A failed literal puncture puts one designated full-deletion component
on the inner arc. Both contacts and the graph inclusion are constructed. -/
theorem full_cycle_failed_designated_inner
    (hconn : G.Connected) (x a b c : V)
    (hxa : G.Adj x a) (hab : G.Adj a b) (hbc : G.Adj b c)
    (hxb : x ≠ b) (hac : a ≠ c) (q : G.Walk c x)
    (hp : (SimpleGraph.Walk.cons hxa
      (SimpleGraph.Walk.cons hab (SimpleGraph.Walk.cons hbc q))).IsTrail)
    (h z : V) (hnot : ¬ (twoEdgeCyclePuncture (G := G) x a b c).Reachable h z) :
    let J := G.deleteEdges (SimpleGraph.Walk.cons hxa
      (SimpleGraph.Walk.cons hab (SimpleGraph.Walk.cons hbc q))).edgeSet
    let A := {v | v ∈ (SimpleGraph.Walk.cons hxa
      (SimpleGraph.Walk.cons hab (SimpleGraph.Walk.cons hbc q))).support}
    (J.connectedComponentMk h).supp ∩ A ⊆ {a, b} ∨
      (J.connectedComponentMk z).supp ∩ A ⊆ {a, b} := by
  dsimp only
  let w := SimpleGraph.Walk.cons hxa
    (SimpleGraph.Walk.cons hab (SimpleGraph.Walk.cons hbc q))
  have hne : w.edges ≠ [] := by simp [w]
  have hle := full_cycle_puncture_le_two_edge x a b c hxa hab hbc q
  apply separated_designated_component_on_inner_arc hle
    {v | v ∈ w.support} {a, b} h z hnot
    (full_cycle_puncture_contacts_nonempty hconn w hne _)
    (full_cycle_puncture_contacts_nonempty hconn w hne _)
  · intro C
    exact full_cycle_failed_puncture_partition hconn x a b c hxa hab hbc
      hxb hac q hp h z hnot C
  · intro u hu v hv huA hvA
    obtain ⟨p, r, hpS, hrS, hcover⟩ :=
      two_edge_cycle_arc_support_cover x a b c hxa hab hbc hxb hac q hp
    have huR : u ∈ r.support := by
      rcases (hcover u).mp hu with huP | huR
      · exact (huA (by simpa [hpS] using huP)).elim
      · exact huR
    have hvR : v ∈ r.support := by
      rcases (hcover v).mp hv with hvP | hvR
      · exact (hvA (by simpa [hpS] using hvP)).elim
      · exact hvR
    exact arc_walk_support_reachable r huR hvR

/-- Two consecutive boundary choices cannot both separate the designated
vertices. This is the graph-level good-puncture selection for a displayed
four-vertex segment of an ordinary cycle. -/
theorem bare_consecutive_cycle_puncture_good
    (h z x a b c d : V) (H : BareCounterexample G h z)
    (hconn : G.Connected) (hxa : G.Adj x a) (hab : G.Adj a b)
    (hbc : G.Adj b c) (hcd : G.Adj c d) (r : G.Walk d x)
    (hp : (SimpleGraph.Walk.cons hxa (SimpleGraph.Walk.cons hab
      (SimpleGraph.Walk.cons hbc (SimpleGraph.Walk.cons hcd r)))).IsTrail)
    (hxb : x ≠ b) (hac : a ≠ c) (hbd : b ≠ d) (habN : a ≠ b)
    (haEven : Even (G.degree a)) (hbEven : Even (G.degree b))
    (hah : a ≠ h) (haz : a ≠ z) (hbh : b ≠ h) (hbz : b ≠ z) :
    (twoEdgeCyclePuncture (G := G) x a b c).Reachable h z ∨
      (twoEdgeCyclePuncture (G := G) a b c d).Reachable h z := by
  classical
  by_contra hn
  have hn1 : ¬ (twoEdgeCyclePuncture (G := G) x a b c).Reachable h z :=
    fun hr => hn (Or.inl hr)
  have hn2 : ¬ (twoEdgeCyclePuncture (G := G) a b c d).Reachable h z :=
    fun hr => hn (Or.inr hr)
  let q := SimpleGraph.Walk.cons hcd r
  let t := SimpleGraph.Walk.cons hab (SimpleGraph.Walk.cons hbc q)
  let w := SimpleGraph.Walk.cons hxa t
  let q' := r.append hxa.toWalk
  let w' := SimpleGraph.Walk.cons hab
    (SimpleGraph.Walk.cons hbc (SimpleGraph.Walk.cons hcd q'))
  have hp' : w'.IsTrail := by
    simpa [w', q', t, q] using cycle_shift_first_edge_isTrail x a hxa t hp
  have heq : w'.edgeSet = w.edgeSet := by
    simpa [w', q', t, q, w] using cycle_shift_first_edge_set x a hxa t
  have hseq : {v | v ∈ w'.support} = {v | v ∈ w.support} := by
    simpa [w', q', t, q, w] using cycle_shift_first_edge_support x a hxa t
  let J := G.deleteEdges w.edgeSet
  let A := {v | v ∈ w.support}
  have hle : J ≤ twoEdgeCyclePuncture (G := G) x a b c :=
    full_cycle_puncture_le_two_edge x a b c hxa hab hbc q
  have hne : w.edges ≠ [] := by simp [w]
  have hremoved : ∀ u v, G.Adj u v → ¬ J.Adj u v → u ∈ A := by
    intro u v huv hnv
    have he : s(u, v) ∈ w.edgeSet := by
      by_contra he
      exact hnv (SimpleGraph.deleteEdges_adj.mpr ⟨huv, he⟩)
    exact w.fst_mem_support_of_mem_edges he
  have hnext : ∀ C : J.ConnectedComponent,
      C.supp ∩ A ⊆ {b, c} ∨ Disjoint (C.supp ∩ A) {b, c} := by
    intro C
    have ht := full_cycle_failed_puncture_partition hconn a b c d hab hbc hcd
      hac hbd q' hp' h z hn2
    rw [heq, hseq] at ht
    exact ht C
  rcases full_cycle_failed_designated_inner hconn x a b c hxa hab hbc hxb hac
      q hp h z hn1 with hh | hz
  · have hzs : z ∉ (J.connectedComponentMk h).supp := by
      intro hzC
      exact hn1 (((J.connectedComponentMk h).reachable_of_mem_supp
        (show h ∈ _ from rfl) hzC).mono hle)
    exact bare_consecutive_contact_either_side_false z h a b c H J
      (J.connectedComponentMk h) A (Or.inl ⟨rfl, hzs⟩) habN hac
      haEven hbEven hah haz hbh hbz hremoved
      (full_cycle_puncture_contacts_nonempty hconn w hne _) hh (hnext _)
  · have hhs : h ∉ (J.connectedComponentMk z).supp := by
      intro hhC
      exact hn1 (((J.connectedComponentMk z).reachable_of_mem_supp
        hhC (show z ∈ _ from rfl)).mono hle)
    exact bare_consecutive_contact_either_side_false z h a b c H J
      (J.connectedComponentMk z) A (Or.inr ⟨rfl, hhs⟩) habN hac
      haEven hbEven hah haz hbh hbz hremoved
      (full_cycle_puncture_contacts_nonempty hconn w hne _) hz (hnext _)

/-- An actual long ordinary cycle supplies two consecutive choices, one
of which keeps the designated vertices together. The segment is extracted
from the walk rather than assumed. -/
theorem bare_long_ordinary_cycle_good_choice
    (h z x : V) (H : BareCounterexample G h z) (hconn : G.Connected)
    (p : G.Walk x x) (hp : p.IsCycle) (hlen : 4 ≤ p.length)
    (heven : ∀ v ∈ p.support, Even (G.degree v))
    (havoid : ∀ v ∈ p.support, v ≠ h ∧ v ≠ z) :
    ∃ a b c d, G.Adj x a ∧ G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧
      ((twoEdgeCyclePuncture (G := G) x a b c).Reachable h z ∨
        (twoEdgeCyclePuncture (G := G) a b c d).Reachable h z) := by
  obtain ⟨a, b, c, d, hxa, hab, hbc, hcd, r, heq⟩ :=
    closed_walk_four_edge_decomposition p hlen
  subst p
  obtain ⟨hxb, hac, hbd⟩ := cycle_four_edge_segment_guards x a b c d
    hxa hab hbc hcd r hp
  have haS : a ∈ (SimpleGraph.Walk.cons hxa (SimpleGraph.Walk.cons hab
      (SimpleGraph.Walk.cons hbc (SimpleGraph.Walk.cons hcd r)))).support := by simp
  have hbS : b ∈ (SimpleGraph.Walk.cons hxa (SimpleGraph.Walk.cons hab
      (SimpleGraph.Walk.cons hbc (SimpleGraph.Walk.cons hcd r)))).support := by simp
  exact ⟨a, b, c, d, hxa, hab, hbc, hcd,
    bare_consecutive_cycle_puncture_good h z x a b c d H hconn hxa hab hbc hcd r
      hp.isTrail hxb hac hbd hab.ne (heven a haS) (heven b hbS)
      (havoid a haS).1 (havoid a haS).2 (havoid b hbS).1 (havoid b hbS).2⟩

/-- An ordinary degree-two vertex has at most one surviving even neighbour
when one of its original even neighbours has been flipped to odd. This
applies uniformly to all four boundary vertices of the cycle puncture. -/
theorem ordinary_puncture_eDegree_le_one
    (P : SimpleGraph V) [DecidableRel P.Adj] (hle : P ≤ G)
    (hkeep : ∀ v, Even (P.degree v) → Even (G.degree v))
    (v w : V) (hvw : G.Adj v w) (hwEven : Even (G.degree w))
    (hwOdd : Odd (P.degree w)) (hvDeg : eDegree G v = 2) :
    eDegree P v ≤ 1 := by
  classical
  have hwmem : w ∈ evenNeighbors G v := (mem_evenNeighbors v w).mpr ⟨hvw, hwEven⟩
  have herase : ((evenNeighbors G v).erase w).card = 1 := by
    have hc := Finset.card_erase_add_one hwmem
    change (evenNeighbors G v).card = 2 at hvDeg
    omega
  have hsub : evenNeighbors P v ⊆ (evenNeighbors G v).erase w := by
    intro u hu
    obtain ⟨hvu, huEven⟩ := (mem_evenNeighbors (G := P) v u).mp hu
    apply Finset.mem_erase.mpr
    refine ⟨?_, (mem_evenNeighbors v u).mpr ⟨hle hvu, hkeep u huEven⟩⟩
    intro heq
    subst u
    exact (Nat.not_even_iff_odd.mpr hwOdd) huEven
  exact (Finset.card_le_card hsub).trans_eq herase

/-- Any component touching a flipped ordinary cycle vertex is non-SET:
that vertex is odd and has at most one even neighbour in the puncture. -/
theorem ordinary_cycle_contact_component_not_set
    (x a b c : V) (hxa : G.Adj x a) (hbc : G.Adj b c)
    (hxb : x ≠ b) (hxc : x ≠ c) (hab : a ≠ b) (hac : a ≠ c)
    (hxEven : Even (G.degree x)) (haEven : Even (G.degree a))
    (hbEven : Even (G.degree b)) (hcEven : Even (G.degree c))
    (hxDeg : eDegree G x = 2) (haDeg : eDegree G a = 2)
    (hbDeg : eDegree G b = 2) (hcDeg : eDegree G c = 2)
    (B : (twoEdgeCyclePuncture (G := G) x a b c).ConnectedComponent)
    (hcontact : ∃ v ∈ B.supp, v = x ∨ v = a ∨ v = b ∨ v = c) :
    ¬ IsSET ((twoEdgeCyclePuncture (G := G) x a b c).induce B.supp) := by
  classical
  let P := twoEdgeCyclePuncture (G := G) x a b c
  have hle : P ≤ G := twoEdgeCyclePuncture_le x a b c
  have hkeep := twoEdgeCyclePuncture_even_preserved x a b c hxa hbc
    hxb hxc hab hac hxEven haEven hbEven hcEven
  obtain ⟨hxOdd, haOdd, hbOdd, hcOdd⟩ := twoEdgeCyclePuncture_odd_profile
    x a b c hxa hbc hxb hxc hab hac hxEven haEven hbEven hcEven
  obtain ⟨v, hvB, hv⟩ := hcontact
  rcases hv with hv | hv | hv | hv
  · subst v
    exact component_not_set_of_odd_eDegree_le_one B x hvB hxOdd
      (ordinary_puncture_eDegree_le_one P hle hkeep x a hxa haEven haOdd hxDeg)
  · subst v
    exact component_not_set_of_odd_eDegree_le_one B a hvB haOdd
      (ordinary_puncture_eDegree_le_one P hle hkeep a x hxa.symm hxEven hxOdd haDeg)
  · subst v
    exact component_not_set_of_odd_eDegree_le_one B b hvB hbOdd
      (ordinary_puncture_eDegree_le_one P hle hkeep b c hbc hcEven hcOdd hbDeg)
  · subst v
    exact component_not_set_of_odd_eDegree_le_one B c hvB hcOdd
      (ordinary_puncture_eDegree_le_one P hle hkeep c b hbc.symm hbEven hbOdd hcDeg)

end Gallai.TwoException
