/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.EarlyNativeDoublePreparation
public import Gallai.TwoException.EarlyAllDoubleRestoration
public import Gallai.TwoException.EarlyMixedMateGuards

@[expose] public section

/-! # Native all-double early minimum-counterexample contradiction -/
namespace Gallai.TwoException
open scoped Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
noncomputable local instance nativeAllDoubleComponents : DecidableEq (evenSubgraph G).ConnectedComponent :=
  Classical.decEq _

/-- Native mixed packets with an even deletion star and at least two ordinary
components exclude the sole-single early branch. The auxiliary decomposition
and all endpoint reserves are constructed rather than assumed. -/
theorem bare_native_early_all_double_impossible
    (h u : V) (x : evenVertices G) (H : BareMinimalCounterexample G h (x : V))
    (f : {a : evenVertices G // (evenSubgraph G).Adj x a} →
      {a : evenVertices G // (evenSubgraph G).Adj x a})
    (hinv : Function.Involutive f)
    (hedge : ∀ a b, (evenSubgraph G).Adj a.val b.val ↔ f a = b)
    (P C : Finset {a : evenVertices G // (evenSubgraph G).Adj x a})
    (hindex : ∀ a, ∃! r, r ∈ P ∧ (a = r ∨ a = f r))
    (p : {a : evenVertices G // (evenSubgraph G).Adj x a})
    (hpC : p ∈ C) (hfpC : f p ∈ C)
    (hsingle : singleContactPetals f P C = ∅)
    (K L privates : Finset V) (O : List (V × V))
    (hK : K = windmillPrivateSet x C)
    (F special : Finset (evenSubgraph G).ConnectedComponent)
    (S : Finset (evenVertices G))
    (Q : (evenSubgraph G).ConnectedComponent → Finset (evenVertices G))
    (mates : (evenSubgraph G).ConnectedComponent → List (evenVertices G × evenVertices G))
    (hL : L = (F.biUnion Q).image Subtype.val)
    (hadj : ∀ t ∈ K ∪ L, G.Adj u t)
    (hB : ∀ t ∈ K ∪ L, t ∈ privates ∨
      ∃ Z ∈ F, ∃ v : evenVertices G, v ∈ Z.supp ∧ (v : V) = t)
    (hprivates : ∀ t ∈ privates, G.Adj t x ∧ eDegree G t = 2)
    (hprivateContacts : ∀ t ∈ privates, G.Adj t u → t ∈ K ∪ L)
    (huOdd : Odd (G.degree u))
    (hMdef : (O ++ []) = ((F \ special).toList.flatMap mates).map
      (fun e => ((e.1 : V),(e.2 : V))))
    (hxComponents : ∀ Z ∈ F, ∀ t : evenVertices G, t ∈ Z.supp → (t : V) ≠ x)
    (hfull : ∀ Z ∈ special, Q Z = ordinaryComponentPacket G S Z)
    (hregularCoverage : ∀ Z ∈ F, Z ∉ special → ∀ t ∈ Z.supp,
      t ∈ Q Z ∨ ∃ e ∈ mates Z, t = e.1 ∨ t = e.2)
    (hlen : ∀ Z ∈ F, Z ∉ special → (mates Z).length ≤ 1)
    (hmateData : ∀ Z ∈ F, Z ∉ special → ∀ e ∈ mates Z,
      G.Adj e.1 e.2 ∧ e.1 ∈ Z.supp ∧ e.2 ∈ Z.supp ∧
      e.1 ∉ Q Z ∧ e.2 ∉ Q Z)
    (hspecial : ∀ Z ∈ special, ∃ a b c : evenVertices G,
      Z.supp = {a,b,c} ∧ G.Adj a b ∧ G.Adj b c ∧ G.Adj c a ∧
      ordinaryComponentPacket G S Z = {a,b} ∧ c ∉ S ∧ ¬ G.Adj c u)
    (hhu : h ≠ u) (hhB : h ∉ K ∪ L) (hhx : h ≠ x) (hhq : h ≠ (f p).val.val)
    (hhM : ∀ e ∈ (O ++ []), h ≠ e.1 ∧ h ≠ e.2)
    (hEvenB : Even #(K ∪ L))
    (hpacket : ∀ e ∈ O, ∃ (Z : (evenSubgraph G).ConnectedComponent)
      (a b c : evenVertices G), e = ((b : V),(c : V)) ∧
      Z.supp = {a,b,c} ∧ (a : V) ∈ K ∪ L)
    (hcover : ∀ t, G.Adj u t → Even (G.degree t) →
      t ∈ K ∪ L ∨ t = h ∨ ∃ e ∈ O, t = e.1)
    (hsupp : ∀ Z ∈ F, ∀ t ∈ Q Z, t ∈ Z.supp)
    (hN : 2 ≤ #F) (hepsilon : #special ≤ 1)
    (hregular : ∀ Z ∈ F, Z ∉ special →
      (∃ a : evenVertices G, (Q Z).image Subtype.val = {(a : V)} ∧
        ∀ t, G.Adj a t → ¬ Even (G.degree t)) ∨
      (∃ a b c : evenVertices G, Z.supp = {a,b,c} ∧
        (Q Z).image Subtype.val = {(a : V)} ∧ ∃ e ∈ O, e.1 = (b : V)) ∨
      (∃ a b c : evenVertices G, Z.supp = {a,b,c} ∧
        G.Adj a b ∧ G.Adj b c ∧ G.Adj c a ∧
      (Q Z).image Subtype.val = {(a : V),(b : V),(c : V)})) : False := by
  classical
  have hleaves : ∀ t ∈ K ∪ L, Even (G.degree t) := by
    intro t ht
    rcases Finset.mem_union.mp ht with hk | hl
    · rw [hK] at hk
      obtain ⟨a,ha,rfl⟩ := (mem_windmillPrivateSet x C _).mp hk
      exact a.val.property
    · rw [hL] at hl
      obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hl
      exact a.property
  have hdisKL : Disjoint K L := by
    apply Finset.disjoint_left.mpr
    intro t hk hl
    rw [hK] at hk
    obtain ⟨a,ha,hat⟩ := (mem_windmillPrivateSet x C _).mp hk
    rw [hL] at hl
    obtain ⟨b,hb,hbt⟩ := Finset.mem_image.mp hl
    obtain ⟨Z,hZ,hbQ⟩ := Finset.mem_biUnion.mp hb
    have hbZ := hsupp Z hZ b hbQ
    have hba : b = a.val := Subtype.ext (hbt.trans hat.symm)
    have haZ : a.val ∈ Z.supp := hba ▸ hbZ
    have hxZ := Z.mem_supp_of_adj_mem_supp haZ a.property.symm
    exact hxComponents Z hZ x hxZ rfl
  have hpB : p.val.val ∈ K ∪ L := by
    apply Finset.mem_union_left
    rw [hK]
    exact (mem_windmillPrivateSet x C _).mpr ⟨p,hpC,rfl⟩
  have hxL : (x : V) ∉ L := by
    rw [hL]
    intro ht
    obtain ⟨t,ht,he⟩ := Finset.mem_image.mp ht
    obtain ⟨Z,hZ,htQ⟩ := Finset.mem_biUnion.mp ht
    exact hxComponents Z hZ t (hsupp Z hZ t htQ) he
  have hxB : (x : V) ∉ K ∪ L := by
    intro ht
    rcases Finset.mem_union.mp ht with hk | hl
    · rw [hK] at hk
      exact hub_not_mem_windmillPrivateSet x C hk
    · exact hxL hl
  have hqB : (f p).val.val ∈ K ∪ L := by
    apply Finset.mem_union_left
    rw [hK]
    exact (mem_windmillPrivateSet x C _).mpr ⟨f p,hfpC,rfl⟩
  have hxu : (x : V) ≠ u := by
    intro he
    exact (Nat.not_even_iff_odd.mpr huOdd) (he ▸ x.property)
  have hqu : (f p).val.val ≠ u := by
    intro he
    exact (Nat.not_even_iff_odd.mpr huOdd) (he ▸ (f p).val.property)
  have hpx : p.val.val ≠ (x : V) := by
    intro he
    exact p.property.ne (Subtype.ext he.symm)
  have hxq : G.Adj x (f p).val.val := (f p).property
  have hxp : G.Adj x p.val.val := p.property
  have hpq : G.Adj p.val.val (f p).val.val := (hedge p (f p)).mpr rfl
  have hpqne : p.val.val ≠ (f p).val.val := hpq.ne
  have hpdegree : eDegree G p.val.val = 2 :=
    bare_hub_private_eDegree_eq_two h x p.val H p.property.reachable hpx
  have hpair : ∀ t, G.Adj (f p).val.val t → Even (G.degree t) →
      t = (x : V) ∨ t = p.val.val := by
    simpa only [hinv p] using bare_windmill_private_even_neighbors h x H f hedge (f p)
  have hmixed := early_mixed_mate_guards u huOdd x (f p).val hxq C
    F special Q mates hsupp
    (fun Z hZ hxZ => hxComponents Z hZ x hxZ rfl) hlen hmateData
  have hdis : (O ++ []).Pairwise (fun (e g : V × V) =>
      e.1 ≠ g.1 ∧ e.1 ≠ g.2 ∧ e.2 ≠ g.1 ∧ e.2 ≠ g.2) := by
    rw [hMdef]
    exact hmixed.1
  have hedges : ∀ e ∈ (O ++ []), G.Adj e.1 e.2 ∧
      Even (G.degree e.1) ∧ Even (G.degree e.2) := by
    intro e he
    rw [hMdef] at he
    exact (hmixed.2 e he).1
  have havoid : ∀ e ∈ (O ++ []),
      e.1 ≠ u ∧ e.2 ≠ u ∧ e.1 ∉ K ∪ L ∧ e.2 ∉ K ∪ L ∧
      e.1 ≠ (x : V) ∧ e.2 ≠ (x : V) ∧
      e.1 ≠ (f p).val.val ∧ e.2 ≠ (f p).val.val := by
    intro e he
    rw [hMdef] at he
    simpa only [hK,hL] using (hmixed.2 e he).2
  have hmates : ∀ Z ∈ F, Z ∉ special → ∀ e ∈ mates Z,
      e.1 ∈ Z.supp ∧ e.2 ∈ Z.supp := by
    intro Z hZ hn e he
    have hd := hmateData Z hZ hn e he
    exact ⟨hd.2.1,hd.2.2.1⟩
  have hcontacts : ∀ t, G.Adj u t → Even (G.degree t) →
      t ∈ K ∪ L ∨ (∃ e ∈ (O ++ []), t = e.1 ∨ t = e.2) ∨
      t = (x : V) ∨ t = h := by
    intro t ht he
    rcases hcover t ht he with hb | hh | ⟨e,he,hte⟩
    · exact Or.inl hb
    · exact Or.inr (Or.inr (Or.inr hh))
    · exact Or.inr (Or.inl ⟨e,List.mem_append_left [] he,Or.inl hte⟩)
  have hselected : ∀ Z ∈ F, ∀ t ∈ Q Z, (t : V) ∈ K ∪ L := by
    intro Z hZ t ht
    apply Finset.mem_union_right
    rw [hL]
    exact Finset.mem_image.mpr ⟨t,Finset.mem_biUnion.mpr ⟨Z,hZ,ht⟩,rfl⟩
  have hM : ∀ e ∈ (O ++ []), ∀ t, t = e.1 ∨ t = e.2 → t ∈ privates ∨
      ∃ Z ∈ F, ∃ v : evenVertices G, v ∈ Z.supp ∧ (v : V) = t := by
    intro e he t ht
    rw [hMdef] at he
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp he
    obtain ⟨Z,hZ,haZ⟩ := List.mem_flatMap.mp ha
    obtain ⟨hZF,hZS⟩ := Finset.mem_sdiff.mp (Finset.mem_toList.mp hZ)
    have hs := hmates Z hZF hZS a haZ
    apply Or.inr
    rcases ht with ht | ht
    · exact ⟨Z,hZF,a.1,hs.1,ht.symm⟩
    · exact ⟨Z,hZF,a.2,hs.2,ht.symm⟩
  obtain ⟨D,hs,hh,hu,_,hrec⟩ :=
    bare_native_early_double_spoke_preparation h u x p.val.val (f p).val.val H
      (K ∪ L) privates O F hadj hleaves hpB hqB hxB hqu
      hxu hpx hpqne hxq hxp hpq hpdegree hpair hdis havoid hedges hcontacts
      hB hM hprivates hprivateContacts huOdd S special Q mates hMdef
      hxComponents hselected hfull hregularCoverage hmates hspecial
      hhu hhB hhx hhq hhM hEvenB hpacket
  have hregularD : ∀ Z ∈ F, Z ∉ special →
      (∃ a : evenVertices G, (Q Z).image Subtype.val = {(a : V)} ∧
        ∀ t, G.Adj a t → ¬ Even (G.degree t)) ∨
      (∃ a b c : evenVertices G, Z.supp = {a,b,c} ∧
        (Q Z).image Subtype.val = {(a : V)} ∧ 2 ≤ D.endpointCount b) ∨
      (∃ a b c : evenVertices G, Z.supp = {a,b,c} ∧
        G.Adj a b ∧ G.Adj b c ∧ G.Adj c a ∧
        (Q Z).image Subtype.val = {(a : V),(b : V),(c : V)}) := by
    intro Z hZ hn
    rcases hregular Z hZ hn with hi | ht | ht
    · exact Or.inl hi
    · obtain ⟨a,b,c,hc,ha,e,he,hb⟩ := ht
      exact Or.inr (Or.inl ⟨a,b,c,hc,ha,hb ▸ hrec e he⟩)
    · exact Or.inr (Or.inr ht)
  have hspecialD : ∀ Z ∈ F, Z ∈ special →
      ∃ a b c : evenVertices G, Z.supp = {a,b,c} ∧ G.Adj a b ∧
        (Q Z).image Subtype.val = {(a : V),(b : V)} := by
    intro Z _ hz
    obtain ⟨a,b,c,hc,hab,_,_,hp,_,_⟩ := hspecial Z hz
    refine ⟨a,b,c,hc,hab,?_⟩
    rw [hfull Z hz,hp]
    simp
  obtain ⟨E,he,_,hkeep⟩ :=
    bare_prepared_early_all_double_restoration h x H f hedge P C hindex
      p hpC hsingle u K L O hK F special Q hL hdisKL hxB hadj hleaves
      hcover hsupp D (by omega) hrec (Or.inl hu) hN (by omega)
      hregularD hspecialD
  apply H.counterexample.2
  refine ⟨E,?_,?_⟩
  · rw [he]; exact hs
  · rw [hkeep h hhu hhB]; exact hh

end Gallai.TwoException
