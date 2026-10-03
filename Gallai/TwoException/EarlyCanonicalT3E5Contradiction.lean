/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.EarlyCanonicalT3TwoSingleSelection
public import Gallai.TwoException.EarlyNativeT3E5Contradiction

@[expose] public section

/-! # Canonical non-hub two-single-petal singleton-triangle branch -/
namespace Gallai.TwoException
open scoped Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The canonical non-hub singleton-triangle row with even private-contact
cardinality and two disjoint single petals is impossible. Every native schedule guard is derived here. -/
theorem bare_canonical_t3_nonhub_selected_singles_impossible
    (h u : V) (x : evenVertices G) (H : BareMinimalCounterexample G h (x : V))
    (huOdd : Odd (G.degree u)) (hux : ¬ G.Adj u x)
    (ho : Even #(windmillContacts x u))
    (Z : (evenSubgraph G).ConnectedComponent)
    (hF : earlyOrdinaryContactComponents G h x u = {Z})
    (hthree : #(ordinaryComponentPacket G (earlyOriginalContacts G h x u) Z) = 3)
    (f : {a : evenVertices G // (evenSubgraph G).Adj x a} →
      {a : evenVertices G // (evenSubgraph G).Adj x a})
    (hinv : Function.Involutive f)
    (hedge : ∀ a b, (evenSubgraph G).Adj a.val b.val ↔ f a = b)
    (p r : {a : evenVertices G // (evenSubgraph G).Adj x a})
    (hpC : p ∈ windmillContacts x u) (hqC : f p ∉ windmillContacts x u)
    (hrC : r ∈ windmillContacts x u) (hsC : f r ∉ windmillContacts x u)
    (hdis : Disjoint ({p,f p} : Finset _) {r,f r}) : False := by
  classical
  have hpq : G.Adj p.val.val (f p).val.val := (hedge p (f p)).mpr rfl
  let q := f p
  let s := f r
  let A := windmillContacts x u
  let S := (windmillPrivateSet x A).erase p.val.val
  have hpSet : p.val.val ∈ windmillPrivateSet x A :=
    (mem_windmillPrivateSet x A _).mpr ⟨p,hpC,rfl⟩
  have hoddS : Odd #S := by
    have hc := Finset.card_erase_add_one hpSet
    rw [windmillPrivateSet_card] at hc
    rw [Nat.even_iff] at ho
    rw [Nat.odd_iff]
    change #((windmillPrivateSet x A).erase p.val.val) % 2 = 1
    change #A % 2 = 0 at ho
    omega
  let privates := windmillPrivateSet x (Finset.univ : Finset _)
  obtain ⟨_,houtside,hclass,_,hcover⟩ := bare_early_canonical_contact_guards h u x H
  have hZ : Z ∈ earlyOrdinaryContactComponents G h x u := by rw [hF]; simp
  have hxZ := houtside Z hZ
  obtain ⟨a,b,c,hsupp,hab,hbc,hca,hua,hub,huc,hah,hbh,hch⟩ :=
    bare_canonical_t3_labels h u x H Z hZ hthree
  have hprivateGuard : ∀ t ∈ privates, G.Adj t x ∧ eDegree G t = 2 := by
    intro t ht
    obtain ⟨v,hv,rfl⟩ := (mem_windmillPrivateSet x _ _).mp ht
    exact ⟨v.property.symm,
      (bare_windmillPrivateSet_leaf_guards h x H Finset.univ v.val.val
        ((mem_windmillPrivateSet x _ _).mpr ⟨v,hv,rfl⟩)).2⟩
  have hS : ∀ t ∈ S, t ∈ privates := by
    intro t ht
    obtain ⟨v,_,rfl⟩ := (mem_windmillPrivateSet x A _).mp (Finset.mem_of_mem_erase ht)
    exact (mem_windmillPrivateSet x _ _).mpr ⟨v,Finset.mem_univ _,rfl⟩
  have hpPriv : p.val.val ∈ privates :=
    (mem_windmillPrivateSet x _ _).mpr ⟨p,Finset.mem_univ _,rfl⟩
  have hqPriv : q.val.val ∈ privates :=
    (mem_windmillPrivateSet x _ _).mpr ⟨q,Finset.mem_univ _,rfl⟩
  have hnotPriv : ∀ t : evenVertices G, t ∈ Z.supp → (t : V) ∉ privates := by
    intro t ht hp
    obtain ⟨v,_,hv⟩ := (mem_windmillPrivateSet x _ _).mp hp
    have hvt : v.val = t := Subtype.val_injective hv
    exact hxZ (Z.mem_supp_of_adj_mem_supp ht (hvt ▸ v.property.symm))
  have hnotX : ∀ t : evenVertices G, t ∈ Z.supp → (t : V) ≠ x := by
    intro t ht he
    exact hxZ (Subtype.val_injective he ▸ ht)
  have haZ : a ∈ Z.supp := by rw [hsupp]; simp
  have hbZ : b ∈ Z.supp := by rw [hsupp]; simp
  have hcZ : c ∈ Z.supp := by rw [hsupp]; simp
  have hadjS : ∀ t ∈ S, G.Adj u t := by
    intro t ht
    obtain ⟨v,hv,rfl⟩ := (mem_windmillPrivateSet x A _).mp (Finset.mem_of_mem_erase ht)
    exact (Finset.mem_filter.mp hv).2
  have hevenS : ∀ t ∈ S, Even (G.degree t) := by
    intro t ht
    exact (bare_windmillPrivateSet_leaf_guards h x H Finset.univ t (hS t ht)).1
  have hnotContact : ∀ v : {a : evenVertices G // (evenSubgraph G).Adj x a},
      v ∉ A → v.val.val ∉ S := by
    intro v hv ht
    obtain ⟨w,hw,he⟩ := (mem_windmillPrivateSet x A _).mp (Finset.mem_of_mem_erase ht)
    have hwv : w = v := Subtype.ext (Subtype.ext he)
    exact hv (hwv ▸ hw)
  have hqS : q.val.val ∉ S := hnotContact q hqC
  have hsS : s.val.val ∉ S := hnotContact s hsC
  have hpS : p.val.val ∉ S := by simp [S]
  have hcross : p.val.val ≠ r.val.val ∧ p.val.val ≠ s.val.val ∧
      q.val.val ≠ r.val.val ∧ q.val.val ≠ s.val.val := by
    have hd := Finset.disjoint_left.mp hdis
    have hn : ∀ v ∈ ({p,q} : Finset _), ∀ w ∈ ({r,s} : Finset _),
        v.val.val ≠ w.val.val := by
      intro v hv w hw he
      have hvw : v = w := Subtype.ext (Subtype.ext he)
      exact hd hv (hvw.symm ▸ hw)
    exact ⟨hn p (by simp) r (by simp),hn p (by simp) s (by simp),
      hn q (by simp) r (by simp),hn q (by simp) s (by simp)⟩
  have hrS : r.val.val ∈ S := Finset.mem_erase.mpr
    ⟨hcross.1.symm,(mem_windmillPrivateSet x A _).mpr ⟨r,hrC,rfl⟩⟩
  have hrPriv : r.val.val ∈ privates :=
    (mem_windmillPrivateSet x _ _).mpr ⟨r,Finset.mem_univ _,rfl⟩
  have hsPriv : s.val.val ∈ privates :=
    (mem_windmillPrivateSet x _ _).mpr ⟨s,Finset.mem_univ _,rfl⟩
  have hpairP : ∀ t, G.Adj p.val.val t → Even (G.degree t) →
      t = (x : V) ∨ t = q.val.val :=
    bare_windmill_private_even_neighbors h x H f hedge p
  have hpairS : ∀ t, G.Adj s.val.val t → Even (G.degree t) →
      t = (x : V) ∨ t = r.val.val := by
    intro t ht he
    have hp := bare_windmill_private_even_neighbors h x H f hedge s t ht he
    have hfr : f s = r := hinv r
    simpa only [hfr] using hp
  have havoidA : ∀ v : {a : evenVertices G // (evenSubgraph G).Adj x a},
      ¬ G.Adj a v.val.val := by
    intro v ht
    have hp := bare_windmill_private_even_neighbors h x H f hedge v a ht.symm a.property
    rcases hp with ht | ht
    · exact hnotX a haZ ht
    · exact hnotPriv a haZ (ht.symm ▸
        ((mem_windmillPrivateSet x _ _).mpr ⟨f v,Finset.mem_univ _,rfl⟩))
  have hax : ¬ G.Adj a x := by
    intro ht
    have ht' : (evenSubgraph G).Adj a x := ht
    exact hxZ (Z.mem_supp_of_adj_mem_supp haZ ht')
  have hcontacts : ∀ t, G.Adj u t → Even (G.degree t) →
      t ∈ S ∨ t = (a : V) ∨ t = p.val.val ∨ t = (b : V) ∨ t = (c : V) ∨ t = h := by
    intro t hut he
    rcases hclass t hut he with ht | ht | ht
    · exact False.elim (hux (ht ▸ hut))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ht))))
    · rcases hcover ⟨t,he⟩ ht with hp | hz
      · by_cases htp : t = p.val.val
        · exact Or.inr (Or.inr (Or.inl htp))
        · exact Or.inl (Finset.mem_erase.mpr ⟨htp,hp⟩)
      · rw [hF,Finset.mem_singleton] at hz
        have htZ : (⟨t,he⟩ : evenVertices G) ∈ Z.supp :=
          (SimpleGraph.ConnectedComponent.mem_supp_iff Z _).mpr hz
        rw [hsupp] at htZ
        rcases htZ with ht | ht | ht
        · exact Or.inr (Or.inl (congrArg Subtype.val ht))
        · exact Or.inr (Or.inr (Or.inr (Or.inl (congrArg Subtype.val ht))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (congrArg Subtype.val ht)))))
  rcases H.counterexample.1 with ⟨_,hhx,_,hhEven,_,hhzero,_⟩
  have hnot : ∀ t, Even (G.degree t) → ¬ G.Adj h t := by
    intro t ht hadj
    have hempty : evenNeighbors G h = ∅ := Finset.card_eq_zero.mp hhzero
    have hm := (mem_evenNeighbors (G := G) h t).mpr ⟨hadj,ht⟩
    simpa [hempty] using hm
  apply bare_native_t3_E5_impossible h u x H S privates Z a b c hsupp hxZ hab hbc hca
    r.val.val s.val.val p.val.val q.val.val hrS hsS hpS hqS
    (fun ht => hub_not_mem_windmillPrivateSet x A (Finset.mem_of_mem_erase ht))
  · intro he
    exact (Nat.not_even_iff_odd.mpr huOdd) (he ▸ x.property)
  · exact fun he => r.property.ne (Subtype.val_injective he).symm
  · have hrsAdj : G.Adj r.val.val s.val.val := (hedge r (f r)).mpr rfl
    exact hrsAdj.ne
  · exact s.property
  · exact r.property
  · exact (hedge r (f r)).mpr rfl
  · exact (hprivateGuard r.val.val hrPriv).2
  · exact s.val.property
  · exact p.val.property
  · exact q.val.property
  · exact hpPriv
  · exact hqPriv
  · exact hpq
  · exact hcross.2.1
  · exact hcross.2.2.2
  · exact hpairP
  · exact hpairS
  · exact fun ht => G.irrefl (hadjS u ht)
  · exact fun ht => hnotPriv a haZ (hS a ht)
  · exact hua
  · exact huOdd
  · exact hoddS
  · exact hadjS
  · exact hevenS
  · exact fun t ht => (hprivateGuard t (hS t ht)).2.le
  · exact fun ht => hnotPriv b hbZ (hS b ht)
  · exact fun ht => hnotPriv c hcZ (hS c ht)
  · exact hcontacts
  · exact hS
  · exact hprivateGuard
  · exact hax
  · exact havoidA s
  · exact havoidA p
  · exact havoidA q
  · intro ht
    exact hsC (Finset.mem_filter.mpr ⟨Finset.mem_univ _,ht⟩)
  · intro ht
    exact hqC (Finset.mem_filter.mpr ⟨Finset.mem_univ _,ht⟩)
  · exact hux
  · intro he
    exact (Nat.not_even_iff_odd.mpr huOdd) (he ▸ hhEven)
  · exact hah.symm
  · exact fun ht => hnot x x.property (hprivateGuard h (hS h ht)).1
  · exact hhx
  · exact fun he => hnot x x.property (he.symm ▸ s.property.symm)
  · exact fun he => hnot x x.property (he.symm ▸ p.property.symm)
  · exact fun he => hnot x x.property (he.symm ▸ q.property.symm)
  · exact hbh.symm
  · exact hch.symm

end Gallai.TwoException
