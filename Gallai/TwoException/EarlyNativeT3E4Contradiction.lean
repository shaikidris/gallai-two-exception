/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.EarlyT3E4Budget
public import Gallai.TwoException.EarlyT3E4Restoration
public import Gallai.TwoException.EarlyT3E4Retained
public import Gallai.TwoException.EarlyT3TwoMatePositivity

@[expose] public section

/-! # Native T3/E4 minimum-counterexample contradiction -/
namespace Gallai.TwoException
open scoped Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
noncomputable local instance nativeT3E4Graph (Q : SimpleGraph V) :
    DecidableRel Q.Adj := fun _ _ => Classical.propDecidable _

/-- Original two-mate labels construct a budgeted auxiliary and derive
both neighbour reserves before E4 and final T3 restoration. -/
theorem bare_native_t3_E4_impossible
    (h u : V) (x : evenVertices G) (H : BareMinimalCounterexample G h (x : V))
    (S privates : Finset V) (Z : (evenSubgraph G).ConnectedComponent)
    (a b c : evenVertices G) (hsupp : Z.supp = {a,b,c})
    (hab : G.Adj a b) (hbc : G.Adj b c) (hca : G.Adj c a)
    (p q : V) (hpq : G.Adj p q) (hpEven : Even (G.degree p))
    (hqEven : Even (G.degree q)) (hpPriv : p ∈ privates) (hqPriv : q ∈ privates)
    (hu : u ∉ S) (haS : (a : V) ∉ S) (hua : G.Adj u a)
    (huOdd : Odd (G.degree u)) (hodd : Odd #S)
    (hadj : ∀ t ∈ S, G.Adj u t) (hleaves : ∀ t ∈ S, Even (G.degree t))
    (hxS : (x : V) ∈ S) (hcap : ∀ t ∈ S, t ≠ (x : V) → eDegree G t ≤ 2)
    (havoid : ∀ e ∈ [(p,q),((b : V),(c : V))],
      e.1 ≠ u ∧ e.2 ≠ u ∧ e.1 ∉ insert (a : V) S ∧ e.2 ∉ insert (a : V) S)
    (hdis : p ≠ (b : V) ∧ p ≠ (c : V) ∧ q ≠ (b : V) ∧ q ≠ (c : V))
    (hcontacts : ∀ t, G.Adj u t → Even (G.degree t) →
      t ∈ S ∨ t = (a : V) ∨ t = p ∨ t = (b : V) ∨ t = (c : V) ∨ t = h)
    (hS : ∀ t ∈ S, t = (x : V) ∨ t ∈ privates)
    (hprivateCentre : u ∉ privates)
    (hprivates : ∀ t ∈ privates, G.Adj t x ∧ eDegree G t = 2)
    (hpair : ∀ t, G.Adj p t → Even (G.degree t) → t = (x : V) ∨ t = q)
    (hap : ¬ G.Adj a p) (haq : ¬ G.Adj a q) (huq : ¬ G.Adj u q)
    (hhu : h ≠ u) (hha : h ≠ (a : V)) (hhS : h ∉ S)
    (hhp : h ≠ p) (hhq : h ≠ q) (hhb : h ≠ (b : V)) (hhc : h ≠ (c : V)) : False := by
  classical
  let B := insert (a : V) S
  let Q := G.deleteEdges {s((b : V),(c : V))}
  have hpA := havoid (p,q) (by simp)
  have hbA := havoid ((b : V),(c : V)) (by simp)
  have hpS : p ∉ S := fun ht => hpA.2.2.1 (Finset.mem_insert_of_mem ht)
  have hqS : q ∉ S := fun ht => hpA.2.2.2 (Finset.mem_insert_of_mem ht)
  have hbS : (b : V) ∉ S := fun ht => hbA.2.2.1 (Finset.mem_insert_of_mem ht)
  have hcS : (c : V) ∉ S := fun ht => hbA.2.2.2 (Finset.mem_insert_of_mem ht)
  have hpa : p ≠ (a : V) := fun he => hpA.2.2.1 (Finset.mem_insert.mpr (Or.inl he))
  have hqa : q ≠ (a : V) := fun he => hpA.2.2.2 (Finset.mem_insert.mpr (Or.inl he))
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
  have hEvenB : Even #B := by
    change Even #(insert (a : V) S)
    rw [Finset.card_insert_of_notMem haS,Nat.even_iff]
    have ho := hodd
    rw [Nat.odd_iff] at ho
    omega
  have hcontactsB : ∀ t, G.Adj u t → Even (G.degree t) →
      t ∈ B ∨ (∃ e ∈ [(p,q),((b : V),(c : V))], t = e.1 ∨ t = e.2) ∨ t = h := by
    intro t ht he
    rcases hcontacts t ht he with ht | ht | ht | ht | ht | ht
    · exact Or.inl (Finset.mem_insert_of_mem ht)
    · exact Or.inl (Finset.mem_insert.mpr (Or.inl ht))
    · exact Or.inr (Or.inl ⟨(p,q),by simp,Or.inl ht⟩)
    · exact Or.inr (Or.inl ⟨((b : V),(c : V)),by simp,Or.inl ht⟩)
    · exact Or.inr (Or.inl ⟨((b : V),(c : V)),by simp,Or.inr ht⟩)
    · exact Or.inr (Or.inr ht)
  have hout := bare_t3_E4_auxiliary_endpoint h u x H B privates Z a b c hsupp
    p q hpq hbc hpEven hqEven hpPriv hqPriv (Finset.mem_insert_of_mem hxS)
    (by simp [B]) huOdd hEvenB hadjB hevenB havoid hdis hcontactsB
    (by
      intro t ht
      rcases Finset.mem_insert.mp ht with ht | ht
      · exact Or.inr (Or.inr ht)
      · rcases hS t ht with ht | ht
        · exact Or.inl ht
        · exact Or.inr (Or.inl ht))
    hprivateCentre hprivates hhu (by simp [B,hha,hhS]) hhp hhq hhb hhc
  rw [t3_E4_auxiliary_eq] at hout
  obtain ⟨D,hs,hh⟩ := hout
  have hkeep := even_edge_deletion_even_preserved (G := G) b c hbc b.property c.property
  have hmono := eDegree_le_of_subgraph_of_even_preservation
    (show Q ≤ G from fun _ _ ht => ht.1) hkeep
  have hadjQ : ∀ t, G.Adj u t → Q.Adj u t := by
    intro t hut
    refine ⟨hut,?_⟩
    intro he
    rw [SimpleGraph.fromEdgeSet_adj] at he
    have he := Set.mem_singleton_iff.mp he.1
    rw [Sym2.eq_iff] at he
    rcases he with he | he
    · exact hbA.1 he.1.symm
    · exact hbA.2.1 he.1.symm
  have hdegree : ∀ t, t ≠ (b : V) → t ≠ (c : V) → Q.degree t = G.degree t := by
    intro t htb htc
    have hd := degree_delete_edge_of_ne G b c t htb htc
    simp only [← SimpleGraph.ncard_neighborSet] at hd ⊢
    exact hd
  have huOddQ : Odd (Q.degree u) := by rw [hdegree u hbA.1.symm hbA.2.1.symm]; exact huOdd
  have hevenQ : ∀ t ∈ S, Even (Q.degree t) := by
    intro t ht
    rw [hdegree t (fun he => hbS (he ▸ ht)) (fun he => hcS (he ▸ ht))]
    exact hleaves t ht
  have hseparate : ∀ t ∈ S, ¬ Q.Adj a t := by
    intro t ht hat
    rcases triangle_component_even_neighbors Z b a c
      (by rw [hsupp]; ext w; simp; tauto) t hat.1 (hleaves t ht) with htB | htC
    · exact hbS (htB ▸ ht)
    · exact hcS (htC ▸ ht)
  have hcomm : starPuncture Q u B = (starPuncture G u B).deleteEdges {s((b : V),(c : V))} := by
    ext v w
    simp only [Q,SimpleGraph.deleteEdges_adj,SimpleGraph.sdiff_adj]
    tauto
  have hpositive : ∀ D : Decomposition ((starPuncture Q u B).deleteEdges {s(q,p)}),
      ∀ t, (starPuncture Q u B).Adj a t → 0 < D.endpointCount t := by
    rw [hcomm]
    intro D
    exact t3_two_mate_reserved_positive Z a b c hsupp u B hadjB hevenB
      (by simp [B]) hbA.1 hbA.2.1 hbA.2.2.1 hbA.2.2.2 hbc q p haq hap D
  have hqpQ : Q.Adj q p := by
    refine ⟨hpq.symm,?_⟩
    intro he
    rw [SimpleGraph.fromEdgeSet_adj] at he
    have he := Set.mem_singleton_iff.mp he.1
    rw [Sym2.eq_iff] at he
    rcases he with he | he
    · exact hdis.2.2.1 he.1
    · exact hdis.2.2.2 he.1
  obtain ⟨E,he,hhE⟩ := restore_t3_E4 Z a b c hsupp hbc u x p q h S hu haS hua.ne
    huOddQ hodd (hadjQ a hua) (fun t ht => hadjQ t (hadj t ht)) hevenQ hxS
    (fun t ht htx => (hmono t).trans (hcap t ht htx)) hseparate
    hpA.2.1 hqa hqS hpA.1 hpa hpS hqpQ
    (by rw [hdegree q hdis.2.2.1 hdis.2.2.2]; exact hqEven)
    (by rw [hdegree p hdis.1 hdis.2.1]; exact hpEven)
    (fun ht => hap ht.1.symm) (fun t ht he => hpair t ht.1 (hkeep t he))
    (fun ht => haq ht.1) (fun ht => huq ht.1) hhu hha hhq hhp hhS hhb hhc D hh
    (t3_E4_retained_guard a b c hbc u p q h S hab.ne hca.ne.symm hua.ne.symm hua
      hpa.symm hqa.symm hbA.1 hbA.2.1 hcontacts D hh) (hpositive D)
  apply H.counterexample.2
  exact ⟨E,by rw [he]; exact hs,hhE⟩

end Gallai.TwoException
