/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.ContactPunctureCap

@[expose] public section

/-! # Boundary witnesses for contact punctures -/
namespace Gallai.TwoException
open scoped Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G J : SimpleGraph V} [DecidableRel G.Adj] [DecidableRel J.Adj]

noncomputable local instance witnessStarAdj (u : V) (B : Finset V) :
    DecidableRel (starPuncture G u B).Adj := fun _ _ => Classical.propDecidable _
noncomputable local instance witnessDeleteAdj (u x q : V) (B : Finset V) :
    DecidableRel ((starPuncture G u B).deleteEdges {s(x,q)}).Adj :=
  fun _ _ => Classical.propDecidable _

/-- Making the hub odd removes one of each private vertex's two possible
even neighbours. This bound does not require the private vertex itself to
remain even. -/
theorem private_eDegree_le_one_of_odd_hub
    (hsub : J ≤ G)
    (hkeep : ∀ t, Even (J.degree t) → Even (G.degree t))
    (x p : V) (hxEven : Even (G.degree x)) (hxOdd : Odd (J.degree x))
    (hpx : G.Adj p x) (hp : eDegree G p = 2) :
    eDegree J p ≤ 1 := by
  have hxmem : x ∈ evenNeighbors G p :=
    (mem_evenNeighbors (G := G) p x).mpr ⟨hpx, hxEven⟩
  have hcard : #((evenNeighbors G p).erase x) = 1 := by
    have hc := Finset.card_erase_add_one hxmem
    change #(evenNeighbors G p) = 2 at hp
    omega
  have hsubset : evenNeighbors J p ⊆ (evenNeighbors G p).erase x := by
    intro t ht
    obtain ⟨hpt, htEven⟩ := (mem_evenNeighbors (G := J) p t).mp ht
    refine Finset.mem_erase.mpr ⟨?_,
      (mem_evenNeighbors (G := G) p t).mpr ⟨hsub hpt, hkeep t htEven⟩⟩
    intro he
    subst t
    exact (Nat.not_even_iff_odd.mpr hxOdd) htEven
  exact (Finset.card_le_card hsubset).trans_eq hcard

/-- A newly even contact centre does not spoil the retained-private witness
when that private is not currently adjacent to it. -/
theorem private_eDegree_le_one_of_odd_hub_except_centre
    (u x p : V)
    (hsub : J ≤ G)
    (hprofile : ∀ t, Even (J.degree t) → Even (G.degree t) ∨ t = u)
    (hxEven : Even (G.degree x)) (hxOdd : Odd (J.degree x))
    (hpx : G.Adj p x) (hp : eDegree G p = 2) (hpu : ¬ J.Adj p u) :
    eDegree J p ≤ 1 := by
  have hxmem : x ∈ evenNeighbors G p :=
    (mem_evenNeighbors (G := G) p x).mpr ⟨hpx,hxEven⟩
  have hcard : #((evenNeighbors G p).erase x) = 1 := by
    have hc := Finset.card_erase_add_one hxmem
    change #(evenNeighbors G p) = 2 at hp
    omega
  have hsubset : evenNeighbors J p ⊆ (evenNeighbors G p).erase x := by
    intro t ht
    obtain ⟨hpt,htEven⟩ := (mem_evenNeighbors (G := J) p t).mp ht
    have htOriginal : Even (G.degree t) := by
      rcases hprofile t htEven with he | htu
      · exact he
      · rw [htu] at hpt
        exact False.elim (hpu hpt)
    refine Finset.mem_erase.mpr ⟨?_,
      (mem_evenNeighbors (G := G) p t).mpr ⟨hsub hpt,htOriginal⟩⟩
    intro he
    subst t
    exact (Nat.not_even_iff_odd.mpr hxOdd) htEven
  exact (Finset.card_le_card hsubset).trans_eq hcard

/-- The bare prescribed isolate cannot acquire an even neighbour in a
puncture that introduces no new even vertices. -/
theorem bare_isolate_puncture_eDegree_zero
    (hsub : J ≤ G)
    (hkeep : ∀ t, Even (J.degree t) → Even (G.degree t))
    (h : V) (hzero : eDegree G h = 0) : eDegree J h = 0 := by
  have hm := eDegree_le_of_subgraph_of_even_preservation hsub hkeep h
  omega

/-- A selected even contact leaf becomes odd after its star edge is
deleted, provided the subsequent spoke deletion is away from that leaf. -/
theorem contact_spoke_puncture_leaf_odd
    (u x q t : V) (B : Finset V) (htB : t ∈ B) (hut : G.Adj u t)
    (htEven : Even (G.degree t)) (htx : t ≠ x) (htq : t ≠ q) :
    Odd (((starPuncture G u B).deleteEdges {s(x,q)}).degree t) := by
  classical
  have hd := starPuncture_degree_leaf (G := G) u B t htB hut
  have ha := degree_delete_edge_of_ne (starPuncture G u B) x q t htx htq
  simp only [← SimpleGraph.ncard_neighborSet] at hd ha htEven ⊢
  rw [ha]
  rw [Nat.even_iff] at htEven
  rw [Nat.odd_iff]
  omega

/-- Odd boundary privates select the floor budget in their actual
component once the puncture's hub is odd and no new even vertex appears. -/
theorem contact_private_component_floor
    (hsub : J ≤ G)
    (hkeep : ∀ t, Even (J.degree t) → Even (G.degree t))
    (hcap : ∀ t, Even (J.degree t) → eDegree J t ≤ 3)
    (C : J.ConnectedComponent) (x p : V) (hpC : p ∈ C.supp)
    (hxEven : Even (G.degree x)) (hxOdd : Odd (J.degree x))
    (hpx : G.Adj p x) (hp : eDegree G p = 2) (hpOdd : Odd (J.degree p)) :
    HasPathBudget (J.induce C.supp) (Fintype.card C.supp / 2) :=
  contact_puncture_component_floor hcap C p hpC hpOdd
    (private_eDegree_le_one_of_odd_hub hsub hkeep x p hxEven hxOdd hpx hp)

/-- Parity and hub witnesses are derived on the literal star/spoke puncture,
not postulated on an arbitrary subgraph. -/
theorem contact_spoke_puncture_profile
    (u x q : V) (B : Finset V) (hu : u ∉ B)
    (hadj : ∀ t ∈ B, G.Adj u t)
    (huOdd : Odd (G.degree u)) (hB : Even #B)
    (hleaves : ∀ t ∈ B, Even (G.degree t))
    (hxu : x ≠ u) (hqu : q ≠ u) (hxB : x ∉ B) (hqB : q ∉ B)
    (hxq : G.Adj x q) (hxEven : Even (G.degree x)) (hqEven : Even (G.degree q)) :
    (∀ t, Even (((starPuncture G u B).deleteEdges {s(x,q)}).degree t) →
      Even (G.degree t)) ∧
    Odd (((starPuncture G u B).deleteEdges {s(x,q)}).degree x) ∧
    Odd (((starPuncture G u B).deleteEdges {s(x,q)}).degree q) := by
  classical
  let Q := starPuncture G u B
  let K := Q.deleteEdges {s(x,q)}
  letI : DecidableRel Q.Adj := witnessStarAdj u B
  letI : DecidableRel K.Adj := witnessDeleteAdj u x q B
  change (∀ t, Even (K.degree t) → Even (G.degree t)) ∧
    Odd (K.degree x) ∧ Odd (K.degree q)
  have hQkeep := even_star_at_odd_center_even_preserved (G := G)
    u B hu hadj huOdd hB hleaves
  have hxd : Q.degree x = G.degree x :=
    starPuncture_degree_other (G := G) u B x hxu hxB
  have hqd : Q.degree q = G.degree q :=
    starPuncture_degree_other (G := G) u B q hqu hqB
  have hxQ : Even (Q.degree x) := hxd ▸ hxEven
  have hqQ : Even (Q.degree q) := hqd ▸ hqEven
  have hxqQ : Q.Adj x q := by
    change G.Adj x q ∧ ¬ (B.sup (SimpleGraph.edge u)).Adj x q
    exact ⟨hxq, fun ha => hqu ((star_sup_adj_off_center u B x q hxu).mp ha).2⟩
  refine ⟨?_, ?_, ?_⟩
  · intro t ht
    apply hQkeep t
    have hp := even_edge_deletion_even_preserved (G := Q) x q hxqQ hxQ hqQ t
    simp only [← SimpleGraph.ncard_neighborSet] at hp ht ⊢
    exact hp ht
  · have hd := degree_delete_edge_add_one Q x q hxqQ
    dsimp only [K]
    simp only [← SimpleGraph.ncard_neighborSet] at hd hxQ ⊢
    rw [Nat.even_iff] at hxQ
    rw [Nat.odd_iff]
    omega
  · have hd := degree_delete_edge_add_one_other Q x q hxqQ
    dsimp only [K]
    simp only [← SimpleGraph.ncard_neighborSet] at hd hqQ ⊢
    rw [Nat.even_iff] at hqQ
    rw [Nat.odd_iff]
    omega

/-- Components containing a deleted contact leaf have a floor budget when
the leaf is either the bare prescribed isolate or a windmill private. All
puncture parity and degree-cap premises are derived from the deletion data. -/
theorem bare_contact_spoke_leaf_component_floor
    (h x : V) (H : BareMinimalCounterexample G h x)
    (u v q : V) (S : Finset V)
    (hu : u ∉ S) (hv : v ∉ S) (huv : u ≠ v)
    (huOdd : Odd (G.degree u)) (hvEven : Even (G.degree v))
    (hodd : Odd #S) (huvAdj : G.Adj u v)
    (hadj : ∀ t ∈ S, G.Adj u t) (heven : ∀ t ∈ S, Even (G.degree t))
    (hxu : x ≠ u) (hxv : x ≠ v) (hxS : x ∉ S)
    (hqu : q ≠ u) (hqv : q ≠ v) (hqS : q ∉ S)
    (hxq : G.Adj x q) (hqEven : Even (G.degree q))
    (C : ((starPuncture G u (insert v S)).deleteEdges {s(x,q)}).ConnectedComponent)
    (t : V) (htC : t ∈ C.supp) (ht : t ∈ insert v S)
    (htype : t = h ∨ (G.Adj t x ∧ eDegree G t = 2)) :
    HasPathBudget (((starPuncture G u (insert v S)).deleteEdges {s(x,q)}).induce C.supp)
      (Fintype.card C.supp / 2) := by
  classical
  rcases H.counterexample.1 with ⟨_, _, _, _, hxEven, hhzero, _⟩
  have hxuB : x ∉ insert v S := by simp [hxv, hxS]
  have hquB : q ∉ insert v S := by simp [hqv, hqS]
  have huB : u ∉ insert v S := by simp [huv, hu]
  have hB : Even #(insert v S) := by
    rw [Finset.card_insert_of_notMem hv]
    rw [Nat.odd_iff] at hodd
    rw [Nat.even_iff]
    omega
  have hBAdj : ∀ w ∈ insert v S, G.Adj u w := by
    intro w hw
    rcases Finset.mem_insert.mp hw with rfl | hw
    · exact huvAdj
    · exact hadj w hw
  have hBEven : ∀ w ∈ insert v S, Even (G.degree w) := by
    intro w hw
    rcases Finset.mem_insert.mp hw with rfl | hw
    · exact hvEven
    · exact heven w hw
  have hprof := contact_spoke_puncture_profile u x q (insert v S) huB hBAdj
    huOdd hB hBEven hxu hqu hxuB hquB hxq hxEven hqEven
  have hsub : (starPuncture G u (insert v S)).deleteEdges {s(x,q)} ≤ G :=
    fun _ _ ha => ha.1.1
  have htOdd := contact_spoke_puncture_leaf_odd u x q t (insert v S)
    ht (hBAdj t ht) (hBEven t ht)
    (fun he => hxuB (he ▸ ht)) (fun he => hquB (he ▸ ht))
  have hcap := bare_contact_spoke_puncture_cap h x H u v q S hu hv huv
    huOdd hvEven hodd huvAdj hadj heven hxu hxv hxS hqu hqv hqS hxq hqEven
  apply contact_puncture_component_floor hcap C t htC htOdd
  rcases htype with rfl | ⟨htx, htdeg⟩
  · have hz := bare_isolate_puncture_eDegree_zero hsub hprof.1 t hhzero
    omega
  · exact private_eDegree_le_one_of_odd_hub hsub hprof.1 x t hxEven hprof.2.1 htx htdeg

/-- A low-E-degree boundary witness excludes SET independently of its
own parity, covering both touched and untouched windmill privates. -/
theorem contact_component_floor_of_eDegree_le_one
    (hcap : ∀ t, Even (J.degree t) → eDegree J t ≤ 3)
    (C : J.ConnectedComponent) (p : V) (hpC : p ∈ C.supp)
    (hp : eDegree J p ≤ 1) :
    HasPathBudget (J.induce C.supp) (Fintype.card C.supp / 2) := by
  rcases floor_or_set_component C hcap with hf | hs
  · exact hf
  · have hclosed : ∀ u ∈ C.supp, J.neighborSet u ⊆ C.supp := by
      intro u hu w huw
      exact C.mem_supp_of_adj_mem_supp hu huw
    have hpCdeg : eDegree (J.induce C.supp) ⟨p, hpC⟩ ≤ 1 := by
      rw [eDegree_induce_of_closed J C.supp hclosed]
      exact hp
    rcases hs.eDegree_two_or_three ⟨p, hpC⟩ with hd | hd <;> omega

/-- Any component containing a windmill private has a floor budget after
the hub is made odd; no endpoint or parity condition on that private is
needed. -/
theorem contact_private_component_floor_without_parity
    (hsub : J ≤ G)
    (hkeep : ∀ t, Even (J.degree t) → Even (G.degree t))
    (hcap : ∀ t, Even (J.degree t) → eDegree J t ≤ 3)
    (C : J.ConnectedComponent) (x p : V) (hpC : p ∈ C.supp)
    (hxEven : Even (G.degree x)) (hxOdd : Odd (J.degree x))
    (hpx : G.Adj p x) (hp : eDegree G p = 2) :
    HasPathBudget (J.induce C.supp) (Fintype.card C.supp / 2) :=
  contact_component_floor_of_eDegree_le_one hcap C p hpC
    (private_eDegree_le_one_of_odd_hub hsub hkeep x p hxEven hxOdd hpx hp)

/-- Deleting every original even neighbour of the contact centre leaves
it with E-degree zero when the puncture introduces no new even vertices. -/
theorem contact_puncture_center_eDegree_zero
    (u : V) (B : Finset V) (hu : u ∉ B)
    (hsub : J ≤ starPuncture G u B)
    (hkeep : ∀ t, Even (J.degree t) → Even (G.degree t))
    (hcontacts : ∀ t, G.Adj u t → Even (G.degree t) → t ∈ B) :
    eDegree J u = 0 := by
  apply eDegree_eq_zero_of_no_even_neighbor
  intro t hut ht
  have ha := hsub hut
  have htB := hcontacts t ha.1 (hkeep t ht)
  exact ha.2 ((star_sup_adj_center u B hu t).mpr htB)

/-- Every component of a star/spoke puncture of a connected graph meets
the deleted-edge support. This uses connectivity of the original graph,
not a connectedness assumption on the puncture. -/
theorem contact_spoke_component_meets_boundary
    (hconn : G.Connected) (u x q : V) (B : Finset V)
    (C : ((starPuncture G u B).deleteEdges {s(x,q)}).ConnectedComponent) :
    ∃ t ∈ C.supp, t = u ∨ t = x ∨ t = q ∨ t ∈ B := by
  classical
  by_contra hnone
  have havoid : ∀ t ∈ C.supp, t ≠ u ∧ t ≠ x ∧ t ≠ q ∧ t ∉ B := by
    intro t ht
    exact ⟨fun he => hnone ⟨t, ht, Or.inl he⟩,
      fun he => hnone ⟨t, ht, Or.inr (Or.inl he)⟩,
      fun he => hnone ⟨t, ht, Or.inr (Or.inr (Or.inl he))⟩,
      fun hb => hnone ⟨t, ht, Or.inr (Or.inr (Or.inr hb))⟩⟩
  have hclosed : ∀ r s, r ∈ C.supp → G.Adj r s → s ∈ C.supp := by
    intro r s hr hrs
    have hav := havoid r hr
    have hstar : (starPuncture G u B).Adj r s := by
      refine ⟨hrs, ?_⟩
      intro hs
      exact hav.2.2.2 ((star_sup_adj_off_center u B r s hav.1).mp hs).1
    have hpuncture : ((starPuncture G u B).deleteEdges {s(x,q)}).Adj r s := by
      apply SimpleGraph.deleteEdges_adj.mpr
      refine ⟨hstar, ?_⟩
      intro he
      have heq : s(r,s) = s(x,q) := by simpa using he
      rcases Sym2.eq_iff.mp heq with heq | heq
      · exact hav.2.1 heq.1
      · exact hav.2.2.1 heq.1
    exact C.mem_supp_of_adj_mem_supp hr hpuncture
  obtain ⟨w, hw⟩ := C.nonempty_supp
  have hreach : G.Reachable w u := hconn w u
  rw [SimpleGraph.reachable_iff_reflTransGen] at hreach
  have hpreserve : ∀ {v : V}, Relation.ReflTransGen G.Adj w v →
      w ∈ C.supp → v ∈ C.supp := by
    intro v hv hw
    induction hv with
    | refl => exact hw
    | tail _ hab ih => exact hclosed _ _ ih hab
  exact (havoid u (hpreserve hreach hw)).1 rfl

end Gallai.TwoException
