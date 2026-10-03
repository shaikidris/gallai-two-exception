/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.EarlyCanonicalPrivateContactResidual
public import Gallai.TwoException.EarlyCanonicalHubOnly
public import Mathlib.Combinatorics.SimpleGraph.Metric

@[expose] public section

/-! # Ambient corridors between the windmill and exterior even vertices -/
namespace Gallai.TwoException

variable {V : Type*} {G : SimpleGraph V}

/-- Choose a globally shortest ambient path between two nonempty sets.
Minimality compares both endpoints, not merely walks between a fixed pair. -/
theorem exists_shortest_set_corridor
    (A B : Set V) (hconn : G.Connected) (hA : A.Nonempty) (hB : B.Nonempty) :
    ∃ a ∈ A, ∃ b ∈ B, ∃ p : G.Walk a b, p.IsPath ∧
      ∀ c ∈ A, ∀ d ∈ B, ∀ q : G.Walk c d, p.length ≤ q.length := by
  classical
  have hex : ∃ n : ℕ, ∃ a ∈ A, ∃ b ∈ B, ∃ p : G.Walk a b, p.length = n := by
    obtain ⟨a,ha⟩ := hA
    obtain ⟨b,hb⟩ := hB
    obtain ⟨p,_⟩ := hconn.exists_isPath a b
    exact ⟨p.length,a,ha,b,hb,p,rfl⟩
  obtain ⟨a,ha,b,hb,p,hp⟩ := Nat.find_spec hex
  have hmin : ∀ c ∈ A, ∀ d ∈ B, ∀ q : G.Walk c d, p.length ≤ q.length := by
    intro c hc d hd q
    rw [hp]
    exact Nat.find_min' hex ⟨c,hc,d,hd,q,rfl⟩
  have hdist : p.length = G.dist a b := by
    obtain ⟨q,hq⟩ := hconn.exists_walk_length_eq_dist a b
    exact le_antisymm (hq ▸ hmin a ha b hb q) (SimpleGraph.dist_le p)
  exact ⟨a,ha,b,hb,p,p.isPath_of_length_eq_dist hdist,hmin⟩

/-- Proper internal vertices of a set-minimal corridor belong to neither
endpoint set. A suffix or prefix would otherwise be a shorter corridor. -/
theorem shortest_set_corridor_internal_separation
    (A B : Set V) {a b : V} (p : G.Walk a b)
    (ha : a ∈ A) (hb : b ∈ B)
    (hmin : ∀ c ∈ A, ∀ d ∈ B, ∀ q : G.Walk c d, p.length ≤ q.length)
    (i : ℕ) (hi : 0 < i) (hilast : i < p.length) :
    p.getVert i ∉ A ∧ p.getVert i ∉ B := by
  constructor
  · intro hAi
    have hh := hmin (p.getVert i) hAi b hb (p.drop i)
    rw [SimpleGraph.Walk.drop_length] at hh
    omega
  · intro hBi
    have hh := hmin a ha (p.getVert i) hBi (p.take i)
    rw [SimpleGraph.Walk.take_length, min_eq_left (Nat.le_of_lt hilast)] at hh
    omega

/-- Beyond the first corridor edge no vertex can have a neighbour in the
initial set. This is the separation guard for reserved-edge restoration. -/
theorem shortest_set_corridor_no_initial_contact
    (A B : Set V) {a b : V} (p : G.Walk a b) (hb : b ∈ B)
    (hmin : ∀ c ∈ A, ∀ d ∈ B, ∀ q : G.Walk c d, p.length ≤ q.length)
    (i : ℕ) (hi : 1 < i) (hile : i ≤ p.length) :
    ∀ c ∈ A, ¬ G.Adj c (p.getVert i) := by
  intro c hc hadj
  have hh := hmin c hc b hb (hadj.toWalk.append (p.drop i))
  rw [SimpleGraph.Walk.length_append, SimpleGraph.Adj.length_toWalk,
    SimpleGraph.Walk.drop_length] at hh
  omega

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- Every positive ordinary-component contact is excluded at an odd
windmill contact centre, including the singleton three-contact triangle.
The canonical private-contact and hub-only schedules cover all possibilities. -/
theorem bare_windmill_ordinary_contact_impossible
    (h u : V) (x : evenVertices G) (H : BareMinimalCounterexample G h (x : V))
    (C : (evenSubgraph G).ConnectedComponent) (hxC : x ∈ C.supp)
    (huOdd : Odd (G.degree u))
    (hcontact : G.Adj u x ∨
      ∃ a : {a : evenVertices G // (evenSubgraph G).Adj x a}, G.Adj u a.val.val)
    (hordinary : (earlyOrdinaryContactComponents G h x u).Nonempty) : False := by
  classical
  by_cases hp : (windmillContacts x u).Nonempty
  · have hz := (bare_canonical_private_contact_residual h u x H C hxC huOdd hp).1
    rw [hz] at hordinary
    simpa using hordinary
  · have hempty := Finset.not_nonempty_iff_eq_empty.mp hp
    have hux : G.Adj u x := by
      rcases hcontact with hx | ⟨a,ha⟩
      · exact hx
      · exact False.elim (hp ⟨a,Finset.mem_filter.mpr ⟨Finset.mem_univ _,ha⟩⟩)
    exact bare_canonical_hub_only_impossible h u x H huOdd hux hempty hordinary

/-- The zero-ordinary-component residual also covers hub-only contacts.
Hence every odd vertex meeting the hub component has only windmill even
neighbours, including when its private contact set is empty. -/
theorem bare_windmill_contact_even_neighbors
    (h u : V) (x : evenVertices G) (H : BareMinimalCounterexample G h (x : V))
    (C : (evenSubgraph G).ConnectedComponent) (hxC : x ∈ C.supp)
    (huOdd : Odd (G.degree u))
    (hcontact : G.Adj u x ∨
      ∃ a : {a : evenVertices G // (evenSubgraph G).Adj x a}, G.Adj u a.val.val) :
    ∀ t, G.Adj u t → Even (G.degree t) →
      t = (x : V) ∨ t ∈ windmillPrivateSet x (windmillContacts x u) := by
  classical
  by_cases hp : (windmillContacts x u).Nonempty
  · exact bare_canonical_private_contact_even_neighbors h u x H C hxC huOdd hp
  have hempty : windmillContacts x u = ∅ := Finset.not_nonempty_iff_eq_empty.mp hp
  have hux : G.Adj u x := by
    rcases hcontact with hx | ⟨a,ha⟩
    · exact hx
    · exact False.elim (hp ⟨a,Finset.mem_filter.mpr ⟨Finset.mem_univ _,ha⟩⟩)
  have hzero : earlyOrdinaryContactComponents G h x u = ∅ := by
    by_contra hn
    exact bare_windmill_ordinary_contact_impossible h u x H C hxC huOdd hcontact
      (Finset.nonempty_iff_ne_empty.mpr hn)
  have huh : ¬ G.Adj u h := by
    intro hh
    exact bare_canonical_protected_zero_impossible h u x H C hxC huOdd hh hcontact hzero
  obtain ⟨_,_,hcontacts,_,hclasses⟩ := bare_early_canonical_contact_guards h u x H
  intro t hut ht
  rcases hcontacts t hut ht with hx | hh | hs
  · exact Or.inl hx
  · exact False.elim (huh (hh ▸ hut))
  · rcases hclasses ⟨t,ht⟩ hs with hw | ho
    · exact Or.inr hw
    · rw [hzero] at ho
      simp at ho

/-- The bare kernel has a shortest ambient corridor from its hub component
to an exterior even vertex. All proper internal vertices are originally odd,
and no vertex beyond the first step contacts the initial even component. -/
theorem bare_exists_shortest_odd_corridor
    (h : V) (x : evenVertices G) (H : BareMinimalCounterexample G h (x : V))
    (C : (evenSubgraph G).ConnectedComponent) (hxC : x ∈ C.supp) :
    ∃ a ∈ Subtype.val '' C.supp,
      ∃ b ∈ evenVertices G \ (Subtype.val '' C.supp), ∃ p : G.Walk a b,
        p.IsPath ∧ 3 ≤ p.length ∧
        (∀ i, 0 < i → i < p.length → Odd (G.degree (p.getVert i))) ∧
        (∀ i, 1 < i → i ≤ p.length →
          ∀ c ∈ Subtype.val '' C.supp, ¬ G.Adj c (p.getVert i)) ∧
        (∀ c ∈ Subtype.val '' C.supp,
          ∀ d ∈ evenVertices G \ (Subtype.val '' C.supp),
          ∀ q : G.Walk c d, p.length ≤ q.length) := by
  classical
  obtain ⟨hconn,hhx,_,hhEven,_,hhzero,_⟩ := H.counterexample.1
  let A : Set V := Subtype.val '' C.supp
  let B : Set V := evenVertices G \ A
  have hhA : h ∉ A := by
    rintro ⟨z,hz,hzh⟩
    have hzx : (z : V) ≠ (x : V) := by simpa [hzh] using hhx
    have hax := bare_hub_component_nonhub_adjacent_to_hub h x z H C hxC
      (C.reachable_of_mem_supp hxC hz) hzx
    have hmem : (x : V) ∈ evenNeighbors G h := by
      exact (mem_evenNeighbors h x).mpr ⟨by simpa [hzh] using hax.symm, x.property⟩
    have hpos : 0 < eDegree G h := Finset.card_pos.mpr ⟨x,hmem⟩
    omega
  have hA : A.Nonempty := ⟨x,x,hxC,rfl⟩
  have hB : B.Nonempty := ⟨h,hhEven,hhA⟩
  obtain ⟨a,ha,b,hb,p,hpath,hmin⟩ := exists_shortest_set_corridor A B hconn hA hB
  have hab : a ≠ b := by
    intro heq
    exact hb.2 (heq ▸ ha)
  have hnadj : ¬ G.Adj a b := by
    intro hadj
    obtain ⟨a',ha',haa⟩ := ha
    have hinside : (⟨b,hb.1⟩ : evenVertices G) ∈ C.supp := by
      apply C.mem_supp_of_adj_mem_supp ha'
      change G.Adj (a' : V) b
      simpa [haa] using hadj
    exact hb.2 ⟨⟨b,hb.1⟩,hinside,rfl⟩
  have hlen : 2 ≤ p.length := by
    have hdist := hconn.one_lt_dist_of_ne_of_not_adj hab hnadj
    have hle := SimpleGraph.dist_le p
    omega
  have hlen3 : 3 ≤ p.length := by
    by_contra hn
    have heq : p.length = 2 := by omega
    have huOdd : Odd (G.degree (p.getVert 1)) := by
      obtain ⟨hiA,hiB⟩ := shortest_set_corridor_internal_separation A B p ha hb hmin
        1 (by omega) (by omega)
      apply Nat.not_even_iff_odd.mp
      intro he
      exact hiB ⟨he,hiA⟩
    have hau : G.Adj a (p.getVert 1) := by
      simpa using p.adj_getVert_succ (i := 0) (by omega)
    have hcontact : G.Adj (p.getVert 1) x ∨
        ∃ z : {z : evenVertices G // (evenSubgraph G).Adj x z},
          G.Adj (p.getVert 1) z.val.val := by
      by_cases hax : a = (x : V)
      · exact Or.inl (by simpa [hax] using hau.symm)
      · obtain ⟨a',ha',haa⟩ := ha
        have ha'x : (a' : V) ≠ (x : V) := by simpa [haa] using hax
        have hxa := bare_hub_component_nonhub_adjacent_to_hub h x a' H C hxC
          (C.reachable_of_mem_supp hxC ha') ha'x
        exact Or.inr ⟨⟨a',hxa⟩,by simpa [haa] using hau.symm⟩
    have hlast : p.getVert 2 = b := by rw [← heq]; simp
    have hub : G.Adj (p.getVert 1) b := by
      simpa only [hlast] using p.adj_getVert_succ (i := 1) (by omega)
    rcases bare_windmill_contact_even_neighbors h (p.getVert 1) x H C hxC
      huOdd hcontact b hub hb.1 with hbx | hw
    · apply hb.2
      rw [hbx]
      exact ⟨x,hxC,rfl⟩
    · obtain ⟨z,_,hzb⟩ := (mem_windmillPrivateSet x _ b).mp hw
      exact hb.2 ⟨z.val,C.mem_supp_of_adj_mem_supp hxC z.property,hzb⟩
  refine ⟨a,ha,b,hb,p,hpath,hlen3,?_,?_,hmin⟩
  · intro i hi hilast
    obtain ⟨hiA,hiB⟩ := shortest_set_corridor_internal_separation A B p ha hb hmin
      i hi hilast
    apply Nat.not_even_iff_odd.mp
    intro he
    exact hiB ⟨he,hiA⟩
  · exact shortest_set_corridor_no_initial_contact A B p hb hmin

/-- Select the actual reserved odd edge for the remaining bare endgame.
Its first endpoint contacts the windmill, while its second endpoint has no
neighbour anywhere in that even component. Both avoid the prescribed vertex. -/
theorem bare_exists_reserved_odd_edge
    (h : V) (x : evenVertices G) (H : BareMinimalCounterexample G h (x : V))
    (C : (evenSubgraph G).ConnectedComponent) (hxC : x ∈ C.supp) :
    ∃ u v : V, Odd (G.degree u) ∧ Odd (G.degree v) ∧ G.Adj u v ∧
      (G.Adj u x ∨
        ∃ z : {z : evenVertices G // (evenSubgraph G).Adj x z}, G.Adj u z.val.val) ∧
      (∀ t, G.Adj u t → Even (G.degree t) →
        t = (x : V) ∨ t ∈ windmillPrivateSet x (windmillContacts x u)) ∧
      (∀ t ∈ Subtype.val '' C.supp, ¬ G.Adj v t) ∧ u ≠ h ∧ v ≠ h := by
  classical
  obtain ⟨a,ha,b,_,p,_,hlen,hodd,hsep,_⟩ :=
    bare_exists_shortest_odd_corridor h x H C hxC
  have huOdd := hodd 1 (by omega) (by omega)
  have hvOdd := hodd 2 (by omega) (by omega)
  have hau : G.Adj a (p.getVert 1) := by
    simpa using p.adj_getVert_succ (i := 0) (by omega)
  have hcontact : G.Adj (p.getVert 1) x ∨
      ∃ z : {z : evenVertices G // (evenSubgraph G).Adj x z},
        G.Adj (p.getVert 1) z.val.val := by
    by_cases hax : a = (x : V)
    · exact Or.inl (by simpa [hax] using hau.symm)
    · obtain ⟨a',ha',haa⟩ := ha
      have ha'x : (a' : V) ≠ (x : V) := by simpa [haa] using hax
      have hxa := bare_hub_component_nonhub_adjacent_to_hub h x a' H C hxC
        (C.reachable_of_mem_supp hxC ha') ha'x
      exact Or.inr ⟨⟨a',hxa⟩,by simpa [haa] using hau.symm⟩
  have hhEven : Even (G.degree h) := H.counterexample.1.2.2.2.1
  refine ⟨p.getVert 1,p.getVert 2,huOdd,hvOdd,?_,hcontact,?_,?_,?_,?_⟩
  · exact p.adj_getVert_succ (i := 1) (by omega)
  · exact bare_windmill_contact_even_neighbors h (p.getVert 1) x H C hxC huOdd hcontact
  · intro t ht hvt
    exact hsep 2 (by omega) (by omega) t ht hvt.symm
  · intro heq
    exact (Nat.not_even_iff_odd.mpr huOdd) (heq ▸ hhEven)
  · intro heq
    exact (Nat.not_even_iff_odd.mpr hvOdd) (heq ▸ hhEven)

end Gallai.TwoException
