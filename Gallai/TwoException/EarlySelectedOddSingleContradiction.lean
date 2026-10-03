/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.EarlySelectedMixedFamily
public import Gallai.TwoException.EarlyNativeOddStarContradiction
public import Gallai.TwoException.EarlyNoTwoContactRecipient
public import Gallai.TwoException.WindmillContactE1

@[expose] public section

/-! # Selected odd-star sole-single branch without packet certificates -/
namespace Gallai.TwoException
open scoped Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
noncomputable local instance selectedOddSingleComponents :
    DecidableEq (evenSubgraph G).ConnectedComponent := Classical.decEq _

/-- Original contacts select ordinary packets and contradict bare minimality
in the odd-baseline, no-two-contact regime. The recipient avoidance, packet
family and auxiliary decomposition are constructed. -/
theorem bare_selected_early_odd_star_sole_single_impossible
    (h u : V) (x : evenVertices G) (H : BareMinimalCounterexample G h (x : V))
    (f : {a : evenVertices G // (evenSubgraph G).Adj x a} →
      {a : evenVertices G // (evenSubgraph G).Adj x a})
    (hinv : Function.Involutive f)
    (hedge : ∀ a b, (evenSubgraph G).Adj a.val b.val ↔ f a = b)
    (P : Finset {a : evenVertices G // (evenSubgraph G).Adj x a})
    (hindex : ∀ a, ∃! r, r ∈ P ∧ (a = r ∨ a = f r))
    (p : {a : evenVertices G // (evenSubgraph G).Adj x a})
    (hpC : p ∈ windmillContacts x u) (hfpC : f p ∉ windmillContacts x u)
    (hsingle : ∀ r ∈ singleContactPetals f P (windmillContacts x u),
      ∀ a ∈ windmillContacts x u ∩ ({r,f r} : Finset _), a = p)
    (S : Finset (evenVertices G)) (F : Finset (evenSubgraph G).ConnectedComponent)
    (hF : F ⊆ S.image (evenSubgraph G).connectedComponentMk)
    (hx : ∀ Z ∈ F, x ∉ Z.supp)
    (hclass : ∀ t, G.Adj u t → ∀ ht : Even (G.degree t),
      t = (x : V) ∨ t = h ∨ (⟨t,ht⟩ : evenVertices G) ∈ S)
    (hS : ∀ t ∈ S, G.Adj u t ∧ (t : V) ≠ h)
    (hcoverS : ∀ t ∈ S, (t : V) ∈ windmillPrivateSet x (windmillContacts x u) ∨
      (evenSubgraph G).connectedComponentMk t ∈ F)
    (huOdd : Odd (G.degree u)) (hux : ¬ G.Adj u x)
    (hN : 2 ≤ #F)
    (hCodd : Odd #(windmillContacts x u)) (hFeven : Even #F)
    (hnoT2 : ∀ Z ∈ F, #(ordinaryComponentPacket G S Z) ≠ 2) : False := by
  classical
  let C := windmillContacts x u
  let K := windmillPrivateSet x C
  let privates := windmillPrivateSet x (Finset.univ : Finset _)
  let special : Finset (evenSubgraph G).ConnectedComponent := ∅
  have hspecial : ∀ Z ∈ special, ∃ a b c : evenVertices G,
      Z.supp = {a,b,c} ∧ G.Adj a b ∧ G.Adj b c ∧ G.Adj c a ∧
      ordinaryComponentPacket G S Z = {a,b} ∧ c ∉ S ∧ ¬ G.Adj c u := by
    simp [special]
  obtain ⟨Q,mates,hQ,hregular,hfull,hrawGlobal⟩ :=
    bare_early_oriented_mixed_family h u x H S F special hF hx
      (by simp [special]) hspecial
  have hcoverage := early_mixed_recipient_coverage_at S F special Q mates hfull
    (fun Z hZ hn => (hregular Z hZ hn).1)
    (fun Z hZ hn e he => (hregular Z hZ hn).2.1 e he |>.2.2.2.2.2.1)
  have hglobal := And.intro hrawGlobal.2 hcoverage
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
  have hdisKL : Disjoint K L := by
    apply Finset.disjoint_left.mpr
    intro t htK htL
    obtain ⟨a,ha,hat⟩ := (mem_windmillPrivateSet x C _).mp htK
    obtain ⟨b,hb,hbt⟩ := Finset.mem_image.mp htL
    obtain ⟨Z,hZ,hbQ⟩ := Finset.mem_biUnion.mp hb
    have hba : b = a.val := Subtype.ext (hbt.trans hat.symm)
    have haZ : a.val ∈ Z.supp := hba ▸ hsupp Z hZ b hbQ
    exact hx Z hZ (Z.mem_supp_of_adj_mem_supp haZ a.property.symm)
  have hcount := early_mixed_spokes_count S F special Q
    (by simp [special]) hsupp
    (fun Z hZ hn => (hregular Z hZ hn).2.2.2)
    (by simp [special])
  have hodd : Odd #(K ∪ L) := by
    rw [Finset.card_union_of_disjoint hdisKL]
    change Odd (#K + #((F.biUnion Q).image Subtype.val))
    rw [hcount]
    simp only [special,Finset.card_empty,Nat.add_zero]
    have hKcard : #K = #C := windmillPrivateSet_card x C
    rw [hKcard,Nat.odd_iff]
    rw [Nat.odd_iff] at hCodd
    rw [Nat.even_iff] at hFeven
    change #C % 2 = 1 at hCodd
    omega
  have hadj : ∀ t ∈ K ∪ L, G.Adj u t := by
    intro t ht
    rcases Finset.mem_union.mp ht with ht | ht
    · obtain ⟨a,ha,rfl⟩ := (mem_windmillPrivateSet x C _).mp ht
      exact (Finset.mem_filter.mp ha).2
    · obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp ht
      obtain ⟨Z,hZ,haQ⟩ := Finset.mem_biUnion.mp ha
      have haS := (Finset.mem_filter.mp ((hQ Z hZ).2.1 haQ)).1
      exact (hS a haS).1
  have hB : ∀ t ∈ K ∪ L, t ∈ privates ∨
      ∃ Z ∈ F, ∃ v : evenVertices G, v ∈ Z.supp ∧ (v : V) = t := by
    intro t ht
    rcases Finset.mem_union.mp ht with ht | ht
    · obtain ⟨a,ha,rfl⟩ := (mem_windmillPrivateSet x C _).mp ht
      exact Or.inl ((mem_windmillPrivateSet x _ _).mpr ⟨a,Finset.mem_univ a,rfl⟩)
    · obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp ht
      obtain ⟨Z,hZ,haQ⟩ := Finset.mem_biUnion.mp ha
      exact Or.inr ⟨Z,hZ,a,hsupp Z hZ a haQ,rfl⟩
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
    exact (mem_windmillPrivateSet x C _).mpr
      ⟨a,Finset.mem_filter.mpr ⟨Finset.mem_univ a,htu.symm⟩,rfl⟩
  have hhu : h ≠ u := by
    intro he
    exact (Nat.not_even_iff_odd.mpr huOdd) (he ▸ hhEven)
  have hhB : h ∉ K ∪ L := by
    intro ht
    rcases Finset.mem_union.mp ht with ht | ht
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
    · exact False.elim (hux (hx ▸ ht))
    · exact Or.inr (Or.inl hh)
    · rcases hcoverS ⟨t,he⟩ htS with hk | hf
      · exact Or.inl (Finset.mem_union_left _ hk)
      · rcases hglobal.2 ⟨t,he⟩ htS hf with hl | hr
        · exact Or.inl (Finset.mem_union_right _ hl)
        · exact Or.inr (Or.inr hr)
  have hnoncontact : ∀ e ∈ O, ¬ G.Adj e.1 u := by
    have hn := early_no_two_contact_family_noncontact u x h S F Q mates
      (fun Z hZ => (hQ Z hZ).2.1) hnoT2
      (fun Z hZ e he => by
        have hd := (hregular Z hZ (by simp [special])).2.1 e he
        obtain ⟨a,ha,hqa,_,_⟩ := hd.2.2.2.2.2.2
        exact ⟨hd.2.2.2.1,hd.2.2.2.2.2.1,a,ha,hqa⟩)
      hclass
      (fun Z hZ e he => by
        have hd := (hregular Z hZ (by simp [special])).2.1 e he
        refine ⟨?_,?_⟩
        · intro heq
          exact hx Z hZ (Subtype.val_injective heq ▸ hd.2.1)
        · intro heq
          exact hnot e.2 e.2.property (heq ▸ hd.1))
    simpa only [O,special,Finset.sdiff_empty] using hn
  apply bare_native_early_odd_star_sole_single_impossible h u x H f hinv hedge P C hindex
    p hpC hfpC hsingle K L privates O rfl F special S Q mates rfl hadj hB
    hprivates hprivateContacts huOdd (by simp only [O,List.append_nil])
    (fun Z hZ t ht he => hx Z hZ (Subtype.val_injective he ▸ ht)) hfull
    (fun Z hZ hn => (hregular Z hZ hn).1)
    (fun Z hZ hn => (hregular Z hZ hn).2.2.1)
    (fun Z hZ hn e he => by
      have hd := (hregular Z hZ hn).2.1 e he
      exact ⟨hd.1,hd.2.1,hd.2.2.1,hd.2.2.2.1,hd.2.2.2.2.1⟩)
    hspecial hhu hhB hhx hhq hhM hodd hnoncontact
    (by intro hadj; exact hfpC (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hadj.symm⟩))
    hpacket hcover hsupp hN rfl hglobal.1

end Gallai.TwoException
