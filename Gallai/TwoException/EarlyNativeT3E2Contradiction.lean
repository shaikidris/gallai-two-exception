/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.EarlyT3RetainedSpokeBudget
public import Gallai.TwoException.EarlyT3E2Restoration
public import Gallai.TwoException.EarlyT3E2Restoration
public import Gallai.TwoException.EarlyT3TwoMatePositivity

@[expose] public section

/-! # Native non-hub T3/E1 contradiction -/
namespace Gallai.TwoException
open scoped Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
noncomputable local instance nativeT3E2Graph (Q : SimpleGraph V) :
    DecidableRel Q.Adj := fun _ _ => Classical.propDecidable _

/-- Original single-spoke and singleton-triangle labels supply the budget
and both neighbour guards, closing the retained-recipient E2 row without callbacks. -/
theorem bare_native_t3_E2_impossible
    (h u : V) (x : evenVertices G) (H : BareMinimalCounterexample G h (x : V))
    (S privates : Finset V) (Z : (evenSubgraph G).ConnectedComponent)
    (a b c : evenVertices G) (hsupp : Z.supp = {a,b,c}) (hxZ : x ∉ Z.supp)
    (hab : G.Adj a b) (hbc : G.Adj b c) (hca : G.Adj c a)
    (p q : V) (hpS : p ∈ S) (hqS : q ∉ S) (hxS : (x : V) ∉ S)
    (hqu : q ≠ u) (hqEven : Even (G.degree q))
    (hxu : (x : V) ≠ u) (hpx : p ≠ (x : V)) (hpqne : p ≠ q)
    (hxq : G.Adj x q) (hxp : G.Adj x p) (hpq : G.Adj p q)
    (hpdegree : eDegree G p = 2)
    (hpair : ∀ t, G.Adj q t → Even (G.degree t) → t = (x : V) ∨ t = p)
    (hu : u ∉ S) (haS : (a : V) ∉ S) (hua : G.Adj u a)
    (huOdd : Odd (G.degree u)) (hodd : Odd #S)
    (hadj : ∀ t ∈ S, G.Adj u t) (hleaves : ∀ t ∈ S, Even (G.degree t))
    (hcap : ∀ t ∈ S, eDegree G t ≤ 2)
    (hbS : (b : V) ∉ S) (hcS : (c : V) ∉ S)
    (hbu : (b : V) ≠ u) (hcu : (c : V) ≠ u)
    (hcontacts : ∀ t, G.Adj u t → Even (G.degree t) →
      t ∈ S ∨ t = (a : V) ∨ t = (b : V) ∨ t = (c : V) ∨ t = q ∨ t = h)
    (hS : ∀ t ∈ S, t ∈ privates)
    (hprivates : ∀ t ∈ privates, G.Adj t x ∧ eDegree G t = 2)
    (hprivateContacts : ∀ t ∈ privates, G.Adj t u → t ∈ S ∨ t = q)
    (haq : ¬ G.Adj a q) (hax : ¬ G.Adj a x)
    (hux : ¬ G.Adj u x)
    (hhu : h ≠ u) (hha : h ≠ (a : V)) (hhS : h ∉ S)
    (hhx : h ≠ (x : V)) (hhq : h ≠ q)
    (hhb : h ≠ (b : V)) (hhc : h ≠ (c : V)) : False := by
  classical
  let B := insert (a : V) S
  let Q := G.deleteEdges {s((b : V),(c : V))}
  have hxa : (x : V) ≠ (a : V) := by
    intro he
    exact hxZ (Subtype.val_injective he.symm ▸ (by rw [hsupp]; simp : a ∈ Z.supp))
  have hqa' : q ≠ (a : V) := by
    intro he
    exact hax (he ▸ hxq.symm)
  have hadjB : ∀ t ∈ B, G.Adj u t := by
    intro t ht
    rcases Finset.mem_insert.mp ht with ht | ht
    · exact ht ▸ hua
    · exact hadj t ht
  have hevenB : ∀ t ∈ B, Even (G.degree t) := by
    intro t ht
    rcases Finset.mem_insert.mp ht with ht | ht
    · exact ht ▸ a.property
    · exact hleaves t ht
  have hout := bare_t3_retained_spoke_auxiliary_endpoint h u x H B privates Z a b c
    hsupp hxZ p q (Finset.mem_insert_of_mem hpS) (by simp [B,hqa',hqS])
    (by simp [B,hxa,hxS]) hqu hqEven hxu hpx hpqne hxq hxp hpq hpdegree hpair
    hadjB hevenB (by simp [B]) (by simp [B,hab.ne.symm,hbS])
    (by simp [B,hca.ne,hcS]) hbu hcu hbc
    (by
      intro t ht he
      rcases hcontacts t ht he with ht | ht | ht | ht | ht | ht
      · exact Or.inl (Finset.mem_insert_of_mem ht)
      · exact Or.inl (Finset.mem_insert.mpr (Or.inl ht))
      · exact Or.inr (Or.inl ht)
      · exact Or.inr (Or.inr (Or.inl ht))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ht))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ht)))))
    (by
      intro t ht
      rcases Finset.mem_insert.mp ht with ht | ht
      · exact Or.inr ht
      · exact Or.inl (hS t ht))
    hprivates (by
      intro t ht htu
      rcases hprivateContacts t ht htu with ht | ht
      · exact Or.inl (Finset.mem_insert_of_mem ht)
      · exact Or.inr ht)
    hhu (by simp [B,hha,hhS]) hhx hhq hhb hhc
  have hgraph : ((starPuncture G u B).deleteEdges {s((x : V),q)}).deleteEdges
      {s((b : V),(c : V))} = (starPuncture Q u B).deleteEdges {s((x : V),q)} := by
    ext v w
    simp only [Q,SimpleGraph.deleteEdges_adj,SimpleGraph.sdiff_adj]
    tauto
  rw [hgraph] at hout
  obtain ⟨D,hs,hh⟩ := hout
  have hkeep := even_edge_deletion_even_preserved (G := G) b c hbc b.property c.property
  have hmono := eDegree_le_of_subgraph_of_even_preservation
    (show Q ≤ G from fun _ _ ht => ht.1) hkeep
  have hdegree : ∀ t, t ≠ (b : V) → t ≠ (c : V) → Q.degree t = G.degree t := by
    intro t htb htc
    have hd := degree_delete_edge_of_ne G b c t htb htc
    simp only [← SimpleGraph.ncard_neighborSet] at hd ⊢
    exact hd
  have hxb : (x : V) ≠ (b : V) := by
    intro he
    exact hxZ (Subtype.val_injective he.symm ▸ (by rw [hsupp]; simp : b ∈ Z.supp))
  have hxc : (x : V) ≠ (c : V) := by
    intro he
    exact hxZ (Subtype.val_injective he.symm ▸ (by rw [hsupp]; simp : c ∈ Z.supp))
  have hqb : q ≠ (b : V) := by
    intro he
    have hbZ : b ∈ Z.supp := by rw [hsupp]; simp
    have hbx : (evenSubgraph G).Adj b x := by
      change G.Adj (b : V) x
      exact he ▸ hxq.symm
    exact hxZ (Z.mem_supp_of_adj_mem_supp hbZ hbx)
  have hqc : q ≠ (c : V) := by
    intro he
    have hcZ : c ∈ Z.supp := by rw [hsupp]; simp
    have hcx : (evenSubgraph G).Adj c x := by
      change G.Adj (c : V) x
      exact he ▸ hxq.symm
    exact hxZ (Z.mem_supp_of_adj_mem_supp hcZ hcx)
  have hadjQ : ∀ t, G.Adj u t → Q.Adj u t := by
    intro t hut
    refine ⟨hut,?_⟩
    intro he
    rw [SimpleGraph.fromEdgeSet_adj] at he
    have he := Set.mem_singleton_iff.mp he.1
    rw [Sym2.eq_iff] at he
    rcases he with he | he
    · exact hbu he.1.symm
    · exact hcu he.1.symm
  have hseparate : ∀ t ∈ S, ¬ Q.Adj a t := by
    intro t ht hat
    rcases triangle_component_even_neighbors Z b a c
      (by rw [hsupp]; ext w; simp; tauto) t hat.1 (hleaves t ht) with htB | htC
    · exact hbS (htB ▸ ht)
    · exact hcS (htC ▸ ht)
  have hxqQ : Q.Adj x q := by
    refine ⟨hxq,?_⟩
    intro he
    rw [SimpleGraph.fromEdgeSet_adj] at he
    have he := Set.mem_singleton_iff.mp he.1
    rw [Sym2.eq_iff] at he
    rcases he with he | he
    · exact hxb he.1
    · exact hxc he.1
  have hcomm : starPuncture Q u B = (starPuncture G u B).deleteEdges {s((b : V),(c : V))} := by
    ext v w
    simp only [Q,SimpleGraph.deleteEdges_adj,SimpleGraph.sdiff_adj]
    tauto
  have hpositive : ∀ D : Decomposition ((starPuncture Q u B).deleteEdges {s((x : V),q)}),
      ∀ t, (starPuncture Q u B).Adj a t → 0 < D.endpointCount t := by
    rw [hcomm]
    intro D
    exact t3_two_mate_reserved_positive Z a b c hsupp u B hadjB hevenB
      (by simp [B]) hbu hcu (by simp [B,hab.ne.symm,hbS])
      (by simp [B,hca.ne,hcS]) hbc x q hax haq D
  obtain ⟨E,he,hhE⟩ := restore_t3_E2 Z a b c hsupp hbc u x p q h S hu haS hua.ne
    (by rw [hdegree u hbu.symm hcu.symm]; exact huOdd) hodd (hadjQ a hua)
    (fun t ht => hadjQ t (hadj t ht))
    (by
      intro t ht
      rw [hdegree t (fun he => hbS (he ▸ ht)) (fun he => hcS (he ▸ ht))]
      exact hleaves t ht)
    hpS (fun t ht _ => (hmono t).trans (hcap t ht)) hseparate
    hxu hxa hxS hqu hqa' hqS hxqQ
    (by rw [hdegree x hxb hxc]; exact x.property)
    (by rw [hdegree q hqb hqc]; exact hqEven)
    (fun ht => haq ht.1.symm)
    (fun t ht he => hpair t ht.1 (hkeep t he)) (fun ht => hax ht.1)
    (fun ht => hux ht.1) hhu hha hhx hhq hhS hhb hhc D hh
    (t3_E2_retained_guard a b c hbc u x q h S hab.ne hca.ne.symm hua.ne.symm hua
      hqa'.symm hxa.symm hbu hcu (by
        intro t ht he
        rcases hcontacts t ht he with ht | ht | ht | ht | ht | ht
        · exact Or.inl ht
        · exact Or.inr (Or.inl ht)
        · exact Or.inr (Or.inr (Or.inr (Or.inl ht)))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ht))))
        · exact Or.inr (Or.inr (Or.inl ht))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ht))))) D hh)
    (hpositive D)
  apply H.counterexample.2
  exact ⟨E,by rw [he]; exact hs,hhE⟩

end Gallai.TwoException
