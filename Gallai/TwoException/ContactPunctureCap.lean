/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.WindmillContactE1
public import Gallai.TwoException.SimultaneousBridge

@[expose] public section

/-! # Even-vertex control for contact punctures -/
namespace Gallai.TwoException
open scoped Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable local instance contactCapStarAdj (u : V) (B : Finset V) :
    DecidableRel (starPuncture G u B).Adj := fun _ _ => Classical.propDecidable _
noncomputable local instance contactCapDeleteAdj (u x q : V) (B : Finset V) :
    DecidableRel ((starPuncture G u B).deleteEdges {s(x,q)}).Adj :=
  fun _ _ => Classical.propDecidable _

/-- Removing an even number of edges from an odd centre to even leaves
cannot introduce a new even vertex. -/
theorem even_star_at_odd_center_even_preserved
    (u : V) (B : Finset V) (hu : u ∉ B)
    (hadj : ∀ t ∈ B, G.Adj u t)
    (huOdd : Odd (G.degree u)) (hB : Even #B)
    (hleaves : ∀ t ∈ B, Even (G.degree t)) :
    ∀ t, Even ((starPuncture G u B).degree t) → Even (G.degree t) := by
  intro t ht
  by_cases htu : t = u
  · subst t
    have hd := starPuncture_degree_center (G := G) u B hu
      (fun t ht => (G.mem_neighborFinset u t).mpr (hadj t ht))
    simp only [← SimpleGraph.ncard_neighborSet] at hd ht huOdd
    rw [Nat.even_iff] at ht hB
    rw [Nat.odd_iff] at huOdd
    omega
  · by_cases htB : t ∈ B
    · have hd := starPuncture_degree_leaf (G := G) u B t htB (hadj t htB)
      have he := hleaves t htB
      simp only [← SimpleGraph.ncard_neighborSet] at hd ht he
      rw [Nat.even_iff] at ht he
      omega
    · rwa [starPuncture_degree_other (G := G) u B t htu htB] at ht

/-- An existing even--even edge deletion introduces no new even vertex. -/
theorem even_edge_deletion_even_preserved
    (x q : V) (hxq : G.Adj x q)
    (hxEven : Even (G.degree x)) (hqEven : Even (G.degree q)) :
    ∀ t, Even ((G.deleteEdges {s(x,q)}).degree t) → Even (G.degree t) := by
  intro t ht
  by_cases htx : t = x
  · subst t
    have hd := degree_delete_edge_add_one G x q hxq
    simp only [← SimpleGraph.ncard_neighborSet] at hd ht hxEven
    rw [Nat.even_iff] at ht hxEven
    omega
  · by_cases htq : t = q
    · subst t
      have hd := degree_delete_edge_add_one_other G x q hxq
      simp only [← SimpleGraph.ncard_neighborSet] at hd ht hqEven
      rw [Nat.even_iff] at ht hqEven
      omega
    · rwa [degree_delete_edge_of_ne G x q t htx htq] at ht

/-- A single-spoke contact puncture with an even reserved endpoint has
no even hub left. Bare minimality therefore gives its global subcubic cap. -/
theorem bare_contact_spoke_puncture_cap
    (h x : V) (H : BareMinimalCounterexample G h x)
    (u v q : V) (S : Finset V)
    (hu : u ∉ S) (hv : v ∉ S) (huv : u ≠ v)
    (huOdd : Odd (G.degree u)) (hvEven : Even (G.degree v))
    (hodd : Odd #S) (huvAdj : G.Adj u v)
    (hadj : ∀ t ∈ S, G.Adj u t) (heven : ∀ t ∈ S, Even (G.degree t))
    (hxu : x ≠ u) (hxv : x ≠ v) (hxS : x ∉ S)
    (hqu : q ≠ u) (hqv : q ≠ v) (hqS : q ∉ S)
    (hxq : G.Adj x q) (hqEven : Even (G.degree q)) :
    ∀ t, Even (((starPuncture G u (insert v S)).deleteEdges {s(x,q)}).degree t) →
      eDegree ((starPuncture G u (insert v S)).deleteEdges {s(x,q)}) t ≤ 3 := by
  classical
  let Q := starPuncture G u (insert v S)
  let J := Q.deleteEdges {s(x,q)}
  letI : DecidableRel Q.Adj := contactCapStarAdj u (insert v S)
  letI : DecidableRel J.Adj := contactCapDeleteAdj u x q (insert v S)
  change ∀ t, Even (J.degree t) → eDegree J t ≤ 3
  have huI : u ∉ insert v S := by simp [huv, hu]
  have hI : Even #(insert v S) := by
    rw [Finset.card_insert_of_notMem hv]
    rw [Nat.odd_iff] at hodd
    rw [Nat.even_iff]
    omega
  have hQkeep : ∀ t, Even (Q.degree t) → Even (G.degree t) :=
    even_star_at_odd_center_even_preserved u (insert v S) huI
      (fun t ht => by
        rcases Finset.mem_insert.mp ht with rfl | ht
        · exact huvAdj
        · exact hadj t ht)
      huOdd hI (fun t ht => by
        rcases Finset.mem_insert.mp ht with rfl | ht
        · exact hvEven
        · exact heven t ht)
  rcases H.counterexample.1 with ⟨_, _, _, _, hxEven, hhbare, hcap⟩
  have hxd : Q.degree x = G.degree x :=
    starPuncture_degree_other (G := G) u (insert v S) x hxu (by simp [hxv, hxS])
  have hqd : Q.degree q = G.degree q :=
    starPuncture_degree_other (G := G) u (insert v S) q hqu (by simp [hqv, hqS])
  have hxQ : Even (Q.degree x) := hxd ▸ hxEven
  have hqQ : Even (Q.degree q) := hqd ▸ hqEven
  have hxqQ : Q.Adj x q := by
    change G.Adj x q ∧ ¬ ((insert v S).sup (SimpleGraph.edge u)).Adj x q
    exact ⟨hxq, fun ha => hqu ((star_sup_adj_off_center u (insert v S) x q hxu).mp ha).2⟩
  have hkeep : ∀ t, Even (J.degree t) → Even (G.degree t) := by
    intro t ht
    apply hQkeep t
    have hp := even_edge_deletion_even_preserved (G := Q) x q hxqQ hxQ hqQ t
    simp only [← SimpleGraph.ncard_neighborSet] at hp ht ⊢
    exact hp ht
  have hsub : J ≤ G := fun _ _ ha => ha.1.1
  have hmono := eDegree_le_of_subgraph_of_even_preservation hsub hkeep
  intro t ht
  have htx : t ≠ x := by
    intro heq
    subst t
    have hd := degree_delete_edge_add_one Q x q hxqQ
    dsimp only [J] at ht
    simp only [← SimpleGraph.ncard_neighborSet] at hd ht hxQ
    rw [Nat.even_iff] at ht hxQ
    omega
  by_cases hth : t = h
  · subst t
    have hm := hmono h
    rw [hhbare] at hm
    omega
  · exact (hmono t).trans (hcap t (hkeep t ht) hth htx)

/-- The literal E1 puncture whose reserved endpoint is the prescribed
isolate has a subcubic even subgraph. The mate is selected by the E1 rule. -/
theorem bare_windmill_E1_protected_puncture_cap
    (h : V) (x : evenVertices G) (H : BareMinimalCounterexample G h (x : V))
    (u : V)
    (f : {a : evenVertices G // (evenSubgraph G).Adj x a} →
      {a : evenVertices G // (evenSubgraph G).Adj x a})
    (P : Finset {a : evenVertices G // (evenSubgraph G).Adj x a})
    (hfree : ∀ a, f a ≠ a)
    (hindex : ∀ a, ∃! r, r ∈ P ∧ (a = r ∨ a = f r))
    (ho : Odd #(singleContactPetals f P (windmillContacts x u)))
    (p : {a : evenVertices G // (evenSubgraph G).Adj x a})
    (hnq : f p ∉ windmillContacts x u)
    (huOdd : Odd (G.degree u)) (huh : G.Adj u h) :
    ∀ t, Even (((starPuncture G u (insert h (ambientWindmillContacts x u))).deleteEdges
      {s((x : V),(f p).val.val)}).degree t) →
      eDegree ((starPuncture G u (insert h (ambientWindmillContacts x u))).deleteEdges
        {s((x : V),(f p).val.val)}) t ≤ 3 := by
  classical
  let S := ambientWindmillContacts x u
  have hcap := bare_windmillPrivateSet_leaf_guards h x H (windmillContacts x u)
  have hstar := windmillPrivateSet_contact_guards x u (windmillContacts x u)
    (fun a ha => (Finset.mem_filter.mp ha).2)
  rcases H.counterexample.1 with ⟨_, hhx, _, hhEven, _, hhbare, _⟩
  have hhS : h ∉ S := by
    intro hh
    have hd := (hcap h hh).2
    rw [hhbare] at hd
    omega
  have hodd : Odd #S :=
    (windmill_contact_row_parities x f hfree P (windmillContacts x u) hindex).1 ho
  have hxu : (x : V) ≠ u := by
    intro he
    exact (Nat.not_even_iff_odd.mpr huOdd) (he ▸ x.property)
  have hqu : (f p).val.val ≠ u := by
    intro he
    exact (Nat.not_even_iff_odd.mpr huOdd) (he ▸ (f p).val.property)
  have hqh : (f p).val.val ≠ h := by
    intro he
    have hd := bare_windmillPrivateSet_leaf_guards h x H ({f p} : Finset _)
      (f p).val.val ((mem_windmillPrivateSet x {f p} (f p).val.val).mpr
        ⟨f p, by simp, rfl⟩)
    rw [he, hhbare] at hd
    omega
  have hqS : (f p).val.val ∉ S := by
    intro hq
    obtain ⟨a, ha, he⟩ := (mem_windmillPrivateSet x (windmillContacts x u) (f p).val.val).mp hq
    have hae : a = f p := Subtype.ext (Subtype.ext he)
    exact hnq (hae ▸ ha)
  exact bare_contact_spoke_puncture_cap h x H u h (f p).val.val S
    hstar.1 hhS huh.ne huOdd hhEven hodd huh hstar.2
    (fun t ht => (hcap t ht).1) hxu hhx.symm
    (hub_not_mem_windmillPrivateSet x (windmillContacts x u))
    hqu hqh hqS (f p).property (f p).val.property

/-- The published floor-or-SET input applies to every actual component
of the protected-endpoint E1 puncture. Non-SET witnesses are still needed
to choose the floor alternative. -/
theorem bare_windmill_E1_protected_puncture_floor_or_set
    (h : V) (x : evenVertices G) (H : BareMinimalCounterexample G h (x : V))
    (u : V)
    (f : {a : evenVertices G // (evenSubgraph G).Adj x a} →
      {a : evenVertices G // (evenSubgraph G).Adj x a})
    (P : Finset {a : evenVertices G // (evenSubgraph G).Adj x a})
    (hfree : ∀ a, f a ≠ a)
    (hindex : ∀ a, ∃! r, r ∈ P ∧ (a = r ∨ a = f r))
    (ho : Odd #(singleContactPetals f P (windmillContacts x u)))
    (p : {a : evenVertices G // (evenSubgraph G).Adj x a})
    (hnq : f p ∉ windmillContacts x u)
    (huOdd : Odd (G.degree u)) (huh : G.Adj u h)
    (C : ((starPuncture G u (insert h (ambientWindmillContacts x u))).deleteEdges
      {s((x : V),(f p).val.val)}).ConnectedComponent) :
    HasPathBudget (((starPuncture G u (insert h (ambientWindmillContacts x u))).deleteEdges
      {s((x : V),(f p).val.val)}).induce C.supp) (Fintype.card C.supp / 2) ∨
    IsSET (((starPuncture G u (insert h (ambientWindmillContacts x u))).deleteEdges
      {s((x : V),(f p).val.val)}).induce C.supp) := by
  apply floor_or_set_component C
  exact bare_windmill_E1_protected_puncture_cap h x H u f P hfree hindex ho p hnq huOdd huh

/-- An odd boundary vertex with at most one even neighbour selects the floor
alternative for its actual puncture component. -/
theorem contact_puncture_component_floor
    {J : SimpleGraph V} [DecidableRel J.Adj]
    (hcap : ∀ t, Even (J.degree t) → eDegree J t ≤ 3)
    (C : J.ConnectedComponent)
    (v : V) (hv : v ∈ C.supp) (hodd : Odd (J.degree v))
    (hle : eDegree J v ≤ 1) :
    HasPathBudget (J.induce C.supp) (Fintype.card C.supp / 2) := by
  rcases floor_or_set_component C hcap with hfloor | hset
  · exact hfloor
  · exact (component_not_set_of_odd_eDegree_le_one C v hv hodd hle hset).elim

end Gallai.TwoException
