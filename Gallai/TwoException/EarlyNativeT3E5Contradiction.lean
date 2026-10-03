/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.EarlyT3E5Budget
public import Gallai.TwoException.EarlyT3E5Restoration
public import Gallai.TwoException.EarlyT3E5Positivity
public import Gallai.TwoException.EarlyT3E5Retained

@[expose] public section

/-! # Native singleton-triangle E5 contradiction -/
namespace Gallai.TwoException
open scoped Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
noncomputable local instance nativeT3E5Graph (Q : SimpleGraph V) :
    DecidableRel Q.Adj := fun _ _ => Classical.propDecidable _

/-- Original E5 labels supply the auxiliary budget and both graph-derived
neighbour guards; no auxiliary decomposition or restoration callback is assumed. -/
theorem bare_native_t3_E5_impossible
    (h u : V) (x : evenVertices G) (H : BareMinimalCounterexample G h (x : V))
    (S privates : Finset V) (Z : (evenSubgraph G).ConnectedComponent)
    (a b c : evenVertices G) (hsupp : Z.supp = {a,b,c}) (hxZ : x ∉ Z.supp)
    (hab : G.Adj a b) (hbc : G.Adj b c) (hca : G.Adj c a)
    (r s p q : V) (hrS : r ∈ S) (hsS : s ∉ S) (hpS : p ∉ S) (hqS : q ∉ S)
    (hxS : (x : V) ∉ S) (hxu : (x : V) ≠ u)
    (hrx : r ≠ (x : V)) (hrs : r ≠ s)
    (hxs : G.Adj x s) (hxr : G.Adj x r) (hrsAdj : G.Adj r s)
    (hrdegree : eDegree G r = 2)
    (hsEven : Even (G.degree s)) (hpEven : Even (G.degree p)) (hqEven : Even (G.degree q))
    (hpPriv : p ∈ privates) (hqPriv : q ∈ privates)
    (hpq : G.Adj p q) (hps : p ≠ s) (hqs : q ≠ s)
    (hpairP : ∀ t, G.Adj p t → Even (G.degree t) → t = (x : V) ∨ t = q)
    (hpairS : ∀ t, G.Adj s t → Even (G.degree t) → t = (x : V) ∨ t = r)
    (hu : u ∉ S) (haS : (a : V) ∉ S) (hua : G.Adj u a)
    (huOdd : Odd (G.degree u)) (hodd : Odd #S)
    (hadj : ∀ t ∈ S, G.Adj u t) (hleaves : ∀ t ∈ S, Even (G.degree t))
    (hcap : ∀ t ∈ S, eDegree G t ≤ 2)
    (hbS : (b : V) ∉ S) (hcS : (c : V) ∉ S)
    (hcontacts : ∀ t, G.Adj u t → Even (G.degree t) →
      t ∈ S ∨ t = (a : V) ∨ t = p ∨ t = (b : V) ∨ t = (c : V) ∨ t = h)
    (hS : ∀ t ∈ S, t ∈ privates)
    (hprivates : ∀ t ∈ privates, G.Adj t x ∧ eDegree G t = 2)
    (hax : ¬ G.Adj a x) (has : ¬ G.Adj a s)
    (hap : ¬ G.Adj a p) (haq : ¬ G.Adj a q)
    (hus : ¬ G.Adj u s) (huq : ¬ G.Adj u q) (hux : ¬ G.Adj u x)
    (hhu : h ≠ u) (hha : h ≠ (a : V)) (hhS : h ∉ S)
    (hhx : h ≠ (x : V)) (hhs : h ≠ s) (hhp : h ≠ p) (hhq : h ≠ q)
    (hhb : h ≠ (b : V)) (hhc : h ≠ (c : V)) : False := by
  classical
  let B := insert (a : V) S
  let Q := G.deleteEdges {s((b : V),(c : V))}
  have hnotU : ∀ t, Even (G.degree t) → t ≠ u := by
    intro t he ht
    exact (Nat.not_even_iff_odd.mpr huOdd) (ht ▸ he)
  have hbu := hnotU b b.property
  have hcu := hnotU c c.property
  have hsu := hnotU s hsEven
  have hpu := hnotU p hpEven
  have hqu := hnotU q hqEven
  have hprivateX : G.Adj x p ∧ G.Adj x q :=
    ⟨(hprivates p hpPriv).1.symm,(hprivates q hqPriv).1.symm⟩
  have houtside : ∀ t, G.Adj x t → t ≠ (a : V) ∧ t ≠ (b : V) ∧ t ≠ (c : V) := by
    intro t ht
    have hnot : ∀ v : evenVertices G, v ∈ Z.supp → t ≠ v := by
      intro v hv he
      have hvx : (evenSubgraph G).Adj v x := by
        change G.Adj (v : V) x
        exact he ▸ ht.symm
      exact hxZ (Z.mem_supp_of_adj_mem_supp hv hvx)
    exact ⟨hnot a (by rw [hsupp]; simp),hnot b (by rw [hsupp]; simp),
      hnot c (by rw [hsupp]; simp)⟩
  have hxa : (x : V) ≠ (a : V) := fun he => hxZ
    (Subtype.val_injective he.symm ▸ (by rw [hsupp]; simp : a ∈ Z.supp))
  have hxb : (x : V) ≠ (b : V) := fun he => hxZ
    (Subtype.val_injective he.symm ▸ (by rw [hsupp]; simp : b ∈ Z.supp))
  have hxc : (x : V) ≠ (c : V) := fun he => hxZ
    (Subtype.val_injective he.symm ▸ (by rw [hsupp]; simp : c ∈ Z.supp))
  have hsa := (houtside s hxs).1
  have hsb := (houtside s hxs).2.1
  have hsc := (houtside s hxs).2.2
  have hpa := (houtside p hprivateX.1).1
  have hpb := (houtside p hprivateX.1).2.1
  have hpc := (houtside p hprivateX.1).2.2
  have hqa := (houtside q hprivateX.2).1
  have hqb := (houtside q hprivateX.2).2.1
  have hqc := (houtside q hprivateX.2).2.2
  have hpx := hprivateX.1.ne.symm
  have hqx := hprivateX.2.ne.symm
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
    rw [Finset.card_insert_of_notMem haS,Nat.even_iff]
    rw [Nat.odd_iff] at hodd
    omega
  have hout := bare_t3_E5_auxiliary_endpoint h u x H B privates Z a b c hsupp hxZ
    r s p q (Finset.mem_insert_of_mem hrS) (by simp [B,hsa,hsS]) (by simp [B,hxa,hxS])
    hsu hsEven hxu hrx hrs hxs hxr hrsAdj hrdegree hpairS hpq hpEven hqEven
    hpPriv hqPriv (by simp [B]) hbc huOdd hEvenB hadjB hevenB
    (by
      intro e he
      simp only [List.mem_cons,List.not_mem_nil,or_false] at he
      rcases he with he | he
      · subst e; exact ⟨hpu,hqu,by simp [B,hpa,hpS],by simp [B,hqa,hqS],hpx,hqx,hps,hqs⟩
      · subst e; exact ⟨hbu,hcu,by simp [B,hab.ne.symm,hbS],by simp [B,hca.ne,hcS],
          hxb.symm,hxc.symm,hsb.symm,hsc.symm⟩)
    ⟨hpb,hpc,hqb,hqc⟩
    (by
      intro t ht he
      rcases hcontacts t ht he with ht | ht | ht | ht | ht | ht
      · exact Or.inl (Finset.mem_insert_of_mem ht)
      · exact Or.inl (Finset.mem_insert.mpr (Or.inl ht))
      · exact Or.inr (Or.inl ⟨(p,q),by simp,Or.inl ht⟩)
      · exact Or.inr (Or.inl ⟨((b : V),(c : V)),by simp,Or.inl ht⟩)
      · exact Or.inr (Or.inl ⟨((b : V),(c : V)),by simp,Or.inr ht⟩)
      · exact Or.inr (Or.inr (Or.inr ht)))
    (by
      intro t ht
      rcases Finset.mem_insert.mp ht with ht | ht
      · exact Or.inr ht
      · exact Or.inl (hS t ht))
    hprivates hhu (by simp [B,hha,hhS]) hhx hhs hhp hhq hhb hhc
  rw [t3_E5_auxiliary_eq] at hout
  obtain ⟨D,hs,hh⟩ := hout
  have hkeep := even_edge_deletion_even_preserved (G := G) b c hbc b.property c.property
  have hmono := eDegree_le_of_subgraph_of_even_preservation
    (show Q ≤ G from fun _ _ ht => ht.1) hkeep
  have hdegree : ∀ t, t ≠ (b : V) → t ≠ (c : V) → Q.degree t = G.degree t := by
    intro t htb htc
    have hd := degree_delete_edge_of_ne G b c t htb htc
    simp only [← SimpleGraph.ncard_neighborSet] at hd ⊢
    exact hd
  have hadjQ : ∀ v w, v ≠ (b : V) → v ≠ (c : V) → G.Adj v w → Q.Adj v w := by
    intro v w hvb hvc hvw
    refine ⟨hvw,?_⟩
    intro he
    rw [SimpleGraph.fromEdgeSet_adj] at he
    have he := Set.mem_singleton_iff.mp he.1
    rw [Sym2.eq_iff] at he
    rcases he with he | he
    · exact hvb he.1
    · exact hvc he.1
  have hsep : ∀ t ∈ S, ¬ Q.Adj a t := by
    intro t ht hat
    rcases triangle_component_even_neighbors Z b a c
      (by rw [hsupp]; ext w; simp; tauto) t hat.1 (hleaves t ht) with htB | htC
    · exact hbS (htB ▸ ht)
    · exact hcS (htC ▸ ht)
  have hpositive : ∀ D : Decomposition (((starPuncture Q u B).deleteEdges
      {s((x : V),s)}).deleteEdges {s(q,p)}),
      ∀ t, (starPuncture Q u B).Adj a t → 0 < D.endpointCount t := by
    have hcomm : starPuncture Q u B = (starPuncture G u B).deleteEdges {s((b : V),(c : V))} := by
      ext v w
      simp only [Q,SimpleGraph.deleteEdges_adj,SimpleGraph.sdiff_adj]
      tauto
    rw [hcomm]
    intro D
    exact t3_E5_reserved_positive Z a b c hsupp u B hadjB hevenB (by simp [B])
      hbu hcu (by simp [B,hab.ne.symm,hbS]) (by simp [B,hca.ne,hcS])
      hbc x s p q hax has hap haq D
  obtain ⟨E,he,hhE⟩ := restore_t3_E5 Z a b c hsupp hbc u x s p q r h S hu haS hua.ne
    (by rw [hdegree u hbu.symm hcu.symm]; exact huOdd) hodd (hadjQ u a hbu.symm hcu.symm hua)
    (fun t ht => hadjQ u t hbu.symm hcu.symm (hadj t ht))
    (by intro t ht; rw [hdegree t (fun he => hbS (he ▸ ht)) (fun he => hcS (he ▸ ht))]; exact hleaves t ht)
    hrS (fun t ht _ => (hmono t).trans (hcap t ht)) hsep hxu hxa hxS hsu
    (hadjQ x s hxb hxc hxs) (by rw [hdegree x hxb hxc]; exact x.property)
    (by rw [hdegree s hsb hsc]; exact hsEven) (fun ht => hap ht.1.symm)
    (fun t ht he => hpairP t ht.1 (hkeep t he)) hpu hpa hpS hpx hps
    hqu hqa hqS hqx hqs (hadjQ q p hqb hqc hpq.symm)
    (by rw [hdegree p hpb hpc]; exact hpEven) (by rw [hdegree q hqb hqc]; exact hqEven)
    (fun ht => hus ht.1.symm) (fun ht => has ht.1.symm)
    (fun t ht he => hpairS t ht.1 (hkeep t he)) (fun ht => hax ht.1)
    (fun ht => haq ht.1) (fun ht => hux ht.1) (fun ht => huq ht.1)
    hhu hha hhS hhx hhs hhp hhq hhb hhc D hh
    (t3_E5_retained_guard a b c hbc u x s p q h S hab.ne hca.ne.symm hua.ne.symm hua
      hpa.symm hqa.symm hbu hcu hcontacts hxa.symm hsa.symm D hh) (hpositive D)
  exact H.counterexample.2 ⟨E,by rw [he]; exact hs,hhE⟩

end Gallai.TwoException
