/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.EarlySelectedHubFamily
public import Gallai.TwoException.EarlyNativeOddHubContradiction
public import Gallai.TwoException.OrdinaryOddStarRecipients
public import Gallai.TwoException.EarlyMixedMateGuards
public import Gallai.TwoException.EarlyMixedComponentCoverage
public import Gallai.TwoException.WindmillContactE1

@[expose] public section

/-! # Selected odd-star hub branch -/
namespace Gallai.TwoException
open scoped Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
noncomputable local instance selectedOddHubContradictionComponents :
    DecidableEq (evenSubgraph G).ConnectedComponent := Classical.decEq _

/-- Actual contact data select the mixed packets and contradict bare
minimality in the all-double, even ordinary-count regime. No packet
family, puncture decomposition, endpoint reserve or mate callback is supplied
by the caller. -/
theorem bare_selected_early_odd_hub_impossible
    (h u : V) (x : evenVertices G) (H : BareMinimalCounterexample G h (x : V))
    (f : {a : evenVertices G // (evenSubgraph G).Adj x a} →
      {a : evenVertices G // (evenSubgraph G).Adj x a})
    (hinv : Function.Involutive f)
    (hedge : ∀ a b, (evenSubgraph G).Adj a.val b.val ↔ f a = b)
    (P : Finset {a : evenVertices G // (evenSubgraph G).Adj x a})
    (hindex : ∀ a, ∃! r, r ∈ P ∧ (a = r ∨ a = f r))
    (p : {a : evenVertices G // (evenSubgraph G).Adj x a})
    (hpC : p ∈ windmillContacts x u)
    (hnoSingle : singleContactPetals f P (windmillContacts x u) = ∅)
    (S : Finset (evenVertices G)) (F : Finset (evenSubgraph G).ConnectedComponent)
    (hF : F ⊆ S.image (evenSubgraph G).connectedComponentMk)
    (hx : ∀ Z ∈ F, x ∉ Z.supp)
    (hclass : ∀ t, G.Adj u t → ∀ ht : Even (G.degree t),
      t = (x : V) ∨ t = h ∨ (⟨t,ht⟩ : evenVertices G) ∈ S)
    (hS : ∀ t ∈ S, G.Adj u t ∧ (t : V) ≠ h)
    (hcoverS : ∀ t ∈ S, (t : V) ∈ windmillPrivateSet x (windmillContacts x u) ∨
      (evenSubgraph G).connectedComponentMk t ∈ F)
    (huOdd : Odd (G.degree u)) (hux : G.Adj u x)
    (hN : 2 ≤ #F)
    (hFeven : Even #F)
    (hnoT2 : F.filter (fun Z => #(ordinaryComponentPacket G S Z) = 2) = ∅) : False := by
  classical
  let C := windmillContacts x u
  let K := insert (x : V) (windmillPrivateSet x C)
  let privates := windmillPrivateSet x (Finset.univ : Finset _)
  let special : Finset (evenSubgraph G).ConnectedComponent := ∅
  have hspecial : ∀ Z ∈ special, ∃ a b c : evenVertices G,
      Z.supp = {a,b,c} ∧ G.Adj a b ∧ G.Adj b c ∧ G.Adj c a ∧
      ordinaryComponentPacket G S Z = {a,b} ∧ c ∉ S ∧ ¬ G.Adj c u := by
    simp [special]
  obtain ⟨Q,mates,hQ,hregular,hfull,hg⟩ :=
    bare_early_oriented_mixed_family h u x H S F special hF hx
      (by simp [special]) hspecial
  have hglobal := And.intro hg.2 (fun t ht htouch =>
    early_mixed_recipient_coverage_at S F special Q mates hfull
      (fun Z hZ hn => (hregular Z hZ hn).1)
      (fun Z hZ hn e he => ((hregular Z hZ hn).2.1 e he).2.2.2.2.2.1)
      t ht htouch)
  have hsingle : ∀ r ∈ singleContactPetals f P C,
      ∀ a ∈ C ∩ ({r,f r} : Finset _), a = p := by
    intro r hr
    change r ∈ singleContactPetals f P (windmillContacts x u) at hr
    rw [hnoSingle] at hr
    exact False.elim (Finset.notMem_empty r hr)
  let L := (F.biUnion Q).image Subtype.val
  let O := ((F \ special).toList.flatMap mates).map
    (fun e => ((e.1 : V),(e.2 : V)))
  rcases H.counterexample.1 with ⟨_,hhx,_,hhEven,_,hhzero,_⟩
  have hnot : ∀ t, Even (G.degree t) → ¬ G.Adj h t := by
    intro t ht hadj
    have hempty : evenNeighbors G h = ∅ := Finset.card_eq_zero.mp hhzero
    have hm := (mem_evenNeighbors (G := G) h t).mpr ⟨hadj,ht⟩
    simpa [hempty] using hm
  have hsupp : ∀ Z ∈ F, ∀ t ∈ Q Z, t ∈ Z.supp :=
    fun Z hZ => (hQ Z hZ).2.2
  have hadj : ∀ t ∈ K ∪ L, G.Adj u t := by
    intro t ht
    rcases Finset.mem_union.mp ht with ht | ht
    · rcases Finset.mem_insert.mp ht with ht | ht
      · exact ht ▸ hux
      · obtain ⟨a,ha,rfl⟩ := (mem_windmillPrivateSet x C _).mp ht
        exact (Finset.mem_filter.mp ha).2
    · obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp ht
      obtain ⟨Z,hZ,haQ⟩ := Finset.mem_biUnion.mp ha
      have haS := (Finset.mem_filter.mp ((hQ Z hZ).2.1 haQ)).1
      exact (hS a haS).1
  have hB : ∀ t ∈ K ∪ L, t = (x : V) ∨ t ∈ privates ∨
      ∃ Z ∈ F, ∃ v : evenVertices G, v ∈ Z.supp ∧ (v : V) = t := by
    intro t ht
    rcases Finset.mem_union.mp ht with ht | ht
    · rcases Finset.mem_insert.mp ht with ht | ht
      · exact Or.inl ht
      · obtain ⟨a,ha,rfl⟩ := (mem_windmillPrivateSet x C _).mp ht
        exact Or.inr (Or.inl ((mem_windmillPrivateSet x _ _).mpr
          ⟨a,Finset.mem_univ a,rfl⟩))
    · obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp ht
      obtain ⟨Z,hZ,haQ⟩ := Finset.mem_biUnion.mp ha
      exact Or.inr (Or.inr ⟨Z,hZ,a,hsupp Z hZ a haQ,rfl⟩)
  have hprivates : ∀ t ∈ privates, G.Adj t x ∧ eDegree G t = 2 := by
    intro t ht
    obtain ⟨a,ha,rfl⟩ := (mem_windmillPrivateSet x _ _).mp ht
    exact ⟨a.property.symm,
      (bare_windmillPrivateSet_leaf_guards h x H Finset.univ a.val.val
        ((mem_windmillPrivateSet x _ _).mpr ⟨a,ha,rfl⟩)).2⟩
  have hprivateContacts : ∀ t ∈ privates, G.Adj t u → t ∈ K ∪ L := by
    intro t ht htu
    obtain ⟨a,ha,rfl⟩ := (mem_windmillPrivateSet x _ _).mp ht
    apply Finset.mem_union_left
    apply Finset.mem_insert_of_mem
    exact (mem_windmillPrivateSet x C _).mpr
      ⟨a,Finset.mem_filter.mpr ⟨Finset.mem_univ a,htu.symm⟩,rfl⟩
  have hhu : h ≠ u := by
    intro he
    exact (Nat.not_even_iff_odd.mpr huOdd) (he ▸ hhEven)
  have hhB : h ∉ K ∪ L := by
    intro ht
    rcases Finset.mem_union.mp ht with ht | ht
    · rcases Finset.mem_insert.mp ht with ht | ht
      · exact hhx ht
      · obtain ⟨a,ha,he⟩ := (mem_windmillPrivateSet x C h).mp ht
        exact hnot x x.property (he ▸ a.property.symm)
    · obtain ⟨a,ha,he⟩ := Finset.mem_image.mp ht
      obtain ⟨Z,hZ,haQ⟩ := Finset.mem_biUnion.mp ha
      exact (hS a (Finset.mem_filter.mp ((hQ Z hZ).2.1 haQ)).1).2 he
  have hhq : h ≠ (f p).val.val := by
    intro he
    exact hnot x x.property (he.symm ▸ (f p).property.symm)
  have hhM : ∀ e ∈ O ++ [], h ≠ e.1 ∧ h ≠ e.2 := by
    intro e he
    have heO : e ∈ O := by simpa only [List.append_nil] using he
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp heO
    obtain ⟨Z,hZ,haZ⟩ := List.mem_flatMap.mp ha
    obtain ⟨hZF,hZS⟩ := Finset.mem_sdiff.mp (Finset.mem_toList.mp hZ)
    have hd := (hregular Z hZF hZS).2.1 a haZ
    constructor
    · intro heq
      exact hnot a.2 a.2.property (heq.symm ▸ hd.1)
    · intro heq
      exact hnot a.1 a.1.property (heq.symm ▸ hd.1.symm)
  have hpacket : ∀ e ∈ O, ∃ (Z : (evenSubgraph G).ConnectedComponent)
      (a b c : evenVertices G), e = ((b : V),(c : V)) ∧
      Z.supp = {a,b,c} ∧ (a : V) ∈ K ∪ L := by
    intro e he
    obtain ⟨Z,a,b,c,heq,hZ,ha⟩ := early_mixed_flattened_labels F special Q mates
      (fun Z hZ hn e he => by
        obtain ⟨a,hs,ha,_,_⟩ := ((hregular Z hZ hn).2.1 e he).2.2.2.2.2.2
        exact ⟨a,hs,ha⟩) e he
    exact ⟨Z,a,b,c,heq,hZ,Finset.mem_union_right _ ha⟩
  have hcover : ∀ t, G.Adj u t → Even (G.degree t) →
      t ∈ K ∪ L ∨ t = h ∨ ∃ e ∈ O, t = e.1 := by
    intro t ht he
    rcases hclass t ht he with hx | hh | htS
    · exact Or.inl (Finset.mem_union_left _ (Finset.mem_insert.mpr (Or.inl hx)))
    · exact Or.inr (Or.inl hh)
    · rcases hcoverS ⟨t,he⟩ htS with hk | hf
      · exact Or.inl (Finset.mem_union_left _ (Finset.mem_insert_of_mem hk))
      · rcases hglobal.2 ⟨t,he⟩ htS hf with hl | hr
        · exact Or.inl (Finset.mem_union_right _ hl)
        · exact Or.inr (Or.inr hr)
  have hselected : ∀ Z ∈ F, ∀ t ∈ Q Z, (t : V) ∈ K ∪ L := by
    intro Z hZ t ht
    exact Finset.mem_union_right _ (Finset.mem_image.mpr
      ⟨t,Finset.mem_biUnion.mpr ⟨Z,hZ,ht⟩,rfl⟩)
  obtain ⟨hdis,hguards⟩ := early_mixed_mate_guards u huOdd x (f p).val
    (f p).property C F special Q mates hsupp hx
    (fun Z hZ hn => (hregular Z hZ hn).2.2.1)
    (fun Z hZ hn e he => by
      have hd := (hregular Z hZ hn).2.1 e he
      exact ⟨hd.1,hd.2.1,hd.2.2.1,hd.2.2.2.1,hd.2.2.2.2.1⟩)
  have havoid : ∀ e ∈ O, e.1 ≠ u ∧ e.2 ≠ u ∧
      e.1 ∉ K ∪ L ∧ e.2 ∉ K ∪ L := by
    intro e he
    obtain ⟨hed,hu1,hu2,hb1,hb2,hx1,hx2,hq1,hq2⟩ := hguards e he
    refine ⟨hu1,hu2,?_,?_⟩
    · intro ht
      rcases Finset.mem_union.mp ht with ht | ht
      · rcases Finset.mem_insert.mp ht with ht | ht
        · exact hx1 ht
        · exact hb1 (Finset.mem_union_left _ ht)
      · exact hb1 (Finset.mem_union_right _ ht)
    · intro ht
      rcases Finset.mem_union.mp ht with ht | ht
      · rcases Finset.mem_insert.mp ht with ht | ht
        · exact hx2 ht
        · exact hb2 (Finset.mem_union_left _ ht)
      · exact hb2 (Finset.mem_union_right _ ht)
  have hM : ∀ e ∈ O, ∀ t, t = e.1 ∨ t = e.2 →
      ∃ Z ∈ F, ∃ v : evenVertices G, v ∈ Z.supp ∧ (v : V) = t := by
    intro e he t ht
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp he
    obtain ⟨Z,hZ,haZ⟩ := List.mem_flatMap.mp ha
    obtain ⟨hZF,hZS⟩ := Finset.mem_sdiff.mp (Finset.mem_toList.mp hZ)
    have hd := (hregular Z hZF hZS).2.1 a haZ
    rcases ht with ht | ht
    · exact ⟨Z,hZF,a.1,hd.2.1,ht.symm⟩
    · exact ⟨Z,hZF,a.2,hd.2.2.1,ht.symm⟩
  obtain ⟨_,hordinary⟩ := early_mixed_auxiliary_component_guards u huOdd x
    (f p).val (f p).property (K ∪ L) S F special Q mates O rfl hx hselected
    hfull (fun Z hZ hn => (hregular Z hZ hn).1)
    (fun Z hZ hn e he =>
      ⟨((hregular Z hZ hn).2.1 e he).2.1,
        ((hregular Z hZ hn).2.1 e he).2.2.1⟩) hspecial
  have hnonempty : privates.Nonempty :=
    ⟨p.val.val,(mem_windmillPrivateSet x _ _).mpr ⟨p,Finset.mem_univ p,rfl⟩⟩
  have huPriv : u ∉ privates := by
    intro ht
    obtain ⟨a,ha,he⟩ := (mem_windmillPrivateSet x _ _).mp ht
    exact (Nat.not_even_iff_odd.mpr huOdd) (he.symm ▸ a.val.property)
  have hleaves : ∀ t ∈ K ∪ L, Even (G.degree t) := by
    intro t ht
    rcases hB t ht with ht | ht | ⟨Z,hZ,v,hv,ht⟩
    · exact ht ▸ x.property
    · obtain ⟨a,ha,he⟩ := (mem_windmillPrivateSet x _ _).mp ht
      exact he ▸ a.val.property
    · exact ht ▸ v.property
  have hdisKL : Disjoint K L := by
    apply Finset.disjoint_left.mpr
    intro t htK htL
    obtain ⟨b,hb,hbt⟩ := Finset.mem_image.mp htL
    obtain ⟨Z,hZ,hbQ⟩ := Finset.mem_biUnion.mp hb
    have hbZ := hsupp Z hZ b hbQ
    rcases Finset.mem_insert.mp htK with ht | ht
    · have hbx : b = x := Subtype.ext (hbt.trans ht)
      exact hx Z hZ (hbx ▸ hbZ)
    · obtain ⟨a,ha,hat⟩ := (mem_windmillPrivateSet x C _).mp ht
      have hba : b = a.val := Subtype.ext (hbt.trans hat.symm)
      exact hx Z hZ (Z.mem_supp_of_adj_mem_supp (hba ▸ hbZ) a.property.symm)
  have hcountL := early_mixed_spokes_count S F special Q
    (by simp [special]) hsupp
    (fun Z hZ hn => (hregular Z hZ hn).2.2.2)
    (by simp [special])
  have hfree : ∀ a, f a ≠ a := by
    intro a he
    exact (evenSubgraph G).irrefl ((hedge a a).mpr he)
  have hcardC := indexed_petal_contact_card f hfree P C hindex
  change #C = #(singleContactPetals f P C) + 2 * #(doubleContactPetals f P C) at hcardC
  have hCzero : singleContactPetals f P C = ∅ := hnoSingle
  rw [hCzero,Finset.card_empty,Nat.zero_add] at hcardC
  have hcardK : #K = 1 + #C := by
    simp only [K,Finset.card_insert_of_notMem (hub_not_mem_windmillPrivateSet x C),
      windmillPrivateSet_card]
    omega
  have hOddB : Odd #(K ∪ L) := by
    rw [Finset.card_union_of_disjoint hdisKL,hcardK]
    change Odd (1 + #C + #((F.biUnion Q).image Subtype.val))
    rw [hcountL]
    have he := hFeven
    rw [Nat.even_iff] at he
    simp only [special,Finset.card_empty,Nat.add_zero]
    rw [Nat.odd_iff]
    omega
  have hnotS : ∀ Z ∈ F, ∀ e ∈ mates Z, e.1 ∉ S := by
    apply ordinary_odd_star_recipients_noncontact S F special Q mates
      (fun Z hZ => (hQ Z hZ).2.1)
      (fun Z hZ e he => by
        have hd := (hregular Z hZ (by simp [special])).2.1 e he
        obtain ⟨a,hs,ha,hab,hca⟩ := hd.2.2.2.2.2.2
        exact ⟨hd.2.2.2.1,a,hs,ha,hab,hd.1,hca⟩)
      (fun Z hZ e he => ((hregular Z hZ (by simp [special])).2.1 e he).2.2.2.2.2.1)
      (fun Z hZ hs => hfull Z hs) #(K ∪ L) hOddB
    intro hn
    simpa only [hnoT2,special,Finset.sdiff_self,Finset.not_nonempty_empty] using hn
  have hnoncontact : ∀ e ∈ O, ¬ G.Adj e.1 u := by
    intro e he
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp he
    obtain ⟨Z,hZ,haZ⟩ := List.mem_flatMap.mp ha
    obtain ⟨hZF,hZS⟩ := Finset.mem_sdiff.mp (Finset.mem_toList.mp hZ)
    have hd := (hregular Z hZF hZS).2.1 a haZ
    exact bare_ordinary_noncontact_recipient_nonadjacent h u x a.1 a.2 H S Z
      (hx Z hZF) hd.2.1 hd.1 (hnotS Z hZF a haZ) hclass
  apply bare_native_early_odd_hub_impossible h u x H K L privates O F
    (Finset.mem_union_left _ (Finset.mem_insert_self _ _)) hadj hleaves hdis havoid
    (fun e he => (hguards e he).1)
    (fun t ht he => by
      rcases hcover t ht he with hb | hh | ⟨e,he,ht⟩
      · exact Or.inl hb
      · exact Or.inr (Or.inr hh)
      · exact Or.inr (Or.inl ⟨e,he,Or.inl ht⟩))
    hB hM hnonempty huPriv hprivates hprivateContacts hordinary hhu hhB
    (by simpa only [List.append_nil] using hhM) hOddB hnoncontact hpacket
    f hedge P C hindex p hpC hsingle rfl special Q rfl hdisKL hcover hsupp hN rfl
    hglobal.1
    (fun Z hZ hs => by
      obtain ⟨a,b,c,hc,hab,hbc,hca,hp,hcs,hcu⟩ := hspecial Z hs
      refine ⟨a,b,c,hc,hab,?_⟩
      rw [hfull Z hs,hp]
      simp)

end Gallai.TwoException
