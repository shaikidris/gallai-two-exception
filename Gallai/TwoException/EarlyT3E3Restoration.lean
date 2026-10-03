/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.ContactE3
public import Gallai.TwoException.ContactPunctureCap
public import Gallai.TwoException.ContactStarAssembly
public import Gallai.TwoException.EarlyT3MateRestoration

@[expose] public section

/-! # E3 contact restoration followed by the T3 opposite mate -/
namespace Gallai.TwoException
open scoped Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
noncomputable local instance t3E3Star (u a b c : V) (S : Finset V) :
    DecidableRel (starPuncture (G.deleteEdges {s(b,c)}) u (insert a S)).Adj :=
  fun _ _ => Classical.propDecidable _

/-- E3 restores the contact star and reserved edge before the T3 mate.
All retained-neighbour guards are derived from original contacts and triangle
support; only the auxiliary decomposition and its protected reserve remain. -/
theorem restore_t3_E3
    (Z : (evenSubgraph G).ConnectedComponent) (a b c : evenVertices G)
    (hsupp : Z.supp = {a,b,c}) (hab : G.Adj a b) (hbc : G.Adj b c) (hca : G.Adj c a)
    (u h x : V) (S : Finset V) (hu : u ∉ S) (haS : (a : V) ∉ S)
    (hua : G.Adj u a) (huOdd : Odd (G.degree u)) (hodd : Odd #S)
    (hbu : (b : V) ≠ u) (hcu : (c : V) ≠ u)
    (hbS : (b : V) ∉ S) (hcS : (c : V) ∉ S)
    (hadj : ∀ t ∈ S, G.Adj u t) (heven : ∀ t ∈ S, Even (G.degree t))
    (hxS : x ∈ S) (hcap : ∀ t ∈ S, t ≠ x → eDegree G t ≤ 2)
    (hseparate : ∀ t ∈ S, ¬ G.Adj a t)
    (hcontacts : ∀ t, G.Adj u t → Even (G.degree t) →
      t ∈ insert (a : V) S ∨ t = (b : V) ∨ t = (c : V) ∨ t = h)
    (hhu : h ≠ u) (hha : h ≠ (a : V)) (hhb : h ≠ (b : V)) (hhc : h ≠ (c : V))
    (hhS : h ∉ S)
    (D : Decomposition (starPuncture (G.deleteEdges {s((b : V),(c : V))}) u
      (insert (a : V) S))) (hh : 2 ≤ D.endpointCount h) :
    ∃ E : Decomposition G, E.size = D.size ∧ 2 ≤ E.endpointCount h := by
  classical
  let Q := G.deleteEdges {s((b : V),(c : V))}
  have hkeep := even_edge_deletion_even_preserved (G := G) b c hbc b.property c.property
  have hsub : Q ≤ G := fun _ _ ht => ht.1
  have hmono := eDegree_le_of_subgraph_of_even_preservation hsub hkeep
  have hdU := degree_delete_edge_of_ne G b c u hbu.symm hcu.symm
  have huQ : Odd (Q.degree u) := by
    simp only [← SimpleGraph.ncard_neighborSet] at hdU huOdd ⊢
    change Odd (Q.neighborSet u).ncard
    rw [hdU]; exact huOdd
  have hadjQ : ∀ t ∈ insert (a : V) S, Q.Adj u t := by
    intro t ht
    have hut : G.Adj u t := by
      rcases Finset.mem_insert.mp ht with ht | ht
      · exact ht ▸ hua
      · exact hadj t ht
    refine ⟨hut,?_⟩
    intro he
    rw [SimpleGraph.fromEdgeSet_adj] at he
    have he := Set.mem_singleton_iff.mp he.1
    rw [Sym2.eq_iff] at he
    rcases he with he | he
    · exact hbu he.1.symm
    · exact hcu he.1.symm
  have hevenQ : ∀ t ∈ insert (a : V) S, Even (Q.degree t) := by
    intro t ht
    have htb : t ≠ (b : V) := by
      rcases Finset.mem_insert.mp ht with ht | ht
      · exact fun he => hab.ne (ht.symm.trans he)
      · exact fun he => hbS (he ▸ ht)
    have htc : t ≠ (c : V) := by
      rcases Finset.mem_insert.mp ht with ht | ht
      · exact fun he => hca.ne (he.symm.trans ht)
      · exact fun he => hcS (he ▸ ht)
    have hd := degree_delete_edge_of_ne G b c t htb htc
    have he : Even (G.degree t) := by
      rcases Finset.mem_insert.mp ht with ht | ht
      · exact ht ▸ a.property
      · exact heven t ht
    simp only [← SimpleGraph.ncard_neighborSet] at hd he ⊢
    change Even (Q.neighborSet t).ncard
    rw [hd]; exact he
  have haOdd := contact_star_leaf_odd (G := Q) u a (insert (a : V) S)
    (by simp) (hadjQ a (by simp)) (hevenQ a (by simp))
  have hretained : ∀ t, Q.Adj u t → t ∉ S →
      Odd (Q.degree t) ∨ 0 < D.endpointCount t := by
    intro t hut htS
    by_cases htOdd : Odd (Q.degree t)
    · exact Or.inl htOdd
    have heQ := (Nat.even_or_odd _).resolve_right htOdd
    have heG := hkeep t heQ
    rcases hcontacts t hut.1 heG with ht | ht | ht | ht
    · rcases Finset.mem_insert.mp ht with ht | ht
      · exact Or.inr (ht ▸ D.endpointCount_pos_of_odd_degree a haOdd)
      · exact False.elim (htS ht)
    · subst t
      have hd := degree_delete_edge_add_one G b c hbc
      have he : Even (G.degree b) := b.property
      simp only [← SimpleGraph.ncard_neighborSet] at hd he heQ
      change Even ((G.deleteEdges {s((b : V),(c : V))}).neighborSet b).ncard at heQ
      rw [Nat.even_iff] at he heQ
      omega
    · subst t
      have hd := degree_delete_edge_add_one_other G b c hbc
      have he : Even (G.degree c) := c.property
      simp only [← SimpleGraph.ncard_neighborSet] at hd he heQ
      change Even ((G.deleteEdges {s((b : V),(c : V))}).neighborSet c).ncard at heQ
      rw [Nat.even_iff] at he heQ
      omega
    · exact Or.inr (ht ▸ (by omega : 0 < D.endpointCount h))
  have hvpositive : ∀ t, (starPuncture Q u (insert (a : V) S)).Adj a t →
      0 < D.endpointCount t := by
    intro t hat
    apply D.endpointCount_pos_of_odd_degree t
    by_contra hn
    have he := (Nat.even_or_odd _).resolve_right hn
    have hprofile := even_star_at_odd_center_even_preserved u (insert (a : V) S)
      (by simp [hua.ne,hu]) hadjQ huQ
      (by
        rw [Finset.card_insert_of_notMem haS, Nat.even_iff]
        have ho := hodd
        rw [Nat.odd_iff] at ho
        omega)
      hevenQ
    have heG := hkeep t (hprofile t he)
    rcases triangle_component_even_neighbors Z b a c (by rw [hsupp]; ext w; simp; tauto)
      t hat.1.1 heG with ht | ht
    · subst t
      have hd := degree_delete_edge_add_one G b c hbc
      have hb : Even (G.degree b) := b.property
      have heQ := hprofile b he
      simp only [← SimpleGraph.ncard_neighborSet] at hd hb heQ
      change Even ((G.deleteEdges {s((b : V),(c : V))}).neighborSet b).ncard at heQ
      rw [Nat.even_iff] at hb heQ
      omega
    · subst t
      have hd := degree_delete_edge_add_one_other G b c hbc
      have hc : Even (G.degree c) := c.property
      have heQ := hprofile c he
      simp only [← SimpleGraph.ncard_neighborSet] at hd hc heQ
      change Even ((G.deleteEdges {s((b : V),(c : V))}).neighborSet c).ncard at heQ
      rw [Nat.even_iff] at hc heQ
      omega
  obtain ⟨F,hsize,_,haF,hpres⟩ := restore_contact_E3_with_retained_reserves
    (R := Q) u a x S hu haS hua.ne huQ hodd (hadjQ a (by simp))
    (fun t ht => hadjQ t (Finset.mem_insert_of_mem ht))
    (fun t ht => hevenQ t (Finset.mem_insert_of_mem ht)) hxS
    (fun t ht htx => (hmono t).trans (hcap t ht htx))
    (fun t ht hadj => hseparate t ht hadj.1) D hretained hvpositive
  obtain ⟨E,hs,_,hpresE⟩ := restore_t3_opposite_mate Z a b c hsupp hbc F (by omega)
  refine ⟨E,hs.trans hsize,?_⟩
  rw [hpresE h hhb hhc,hpres h hhu hha hhS]
  exact hh

end Gallai.TwoException
