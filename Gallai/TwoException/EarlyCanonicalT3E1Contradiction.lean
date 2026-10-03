/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.EarlyCanonicalOddSingleSelection
public import Gallai.TwoException.EarlyNativeT3E1Contradiction

@[expose] public section

/-! # Canonical non-hub odd-contact singleton-triangle branch -/
namespace Gallai.TwoException
open scoped Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The canonical non-hub singleton-triangle row with odd private-contact
cardinality is impossible. Every native schedule guard is derived here. -/
theorem bare_canonical_t3_nonhub_odd_impossible
    (h u : V) (x : evenVertices G) (H : BareMinimalCounterexample G h (x : V))
    (huOdd : Odd (G.degree u)) (hux : ¬ G.Adj u x)
    (ho : Odd #(windmillContacts x u))
    (Z : (evenSubgraph G).ConnectedComponent)
    (hF : earlyOrdinaryContactComponents G h x u = {Z})
    (hthree : #(ordinaryComponentPacket G (earlyOriginalContacts G h x u) Z) = 3)
    (f : {a : evenVertices G // (evenSubgraph G).Adj x a} →
      {a : evenVertices G // (evenSubgraph G).Adj x a})
    (hinv : Function.Involutive f)
    (hedge : ∀ a b, (evenSubgraph G).Adj a.val b.val ↔ f a = b)
    (P : Finset {a : evenVertices G // (evenSubgraph G).Adj x a})
    (hindex : ∀ a, ∃! r, r ∈ P ∧ (a = r ∨ a = f r)) : False := by
  classical
  obtain ⟨p,hpC,hqC,hpq,huq,hoddS⟩ :=
    odd_private_contacts_single_selection u x f hinv hedge P hindex ho
  let q := f p
  let A := windmillContacts x u
  let S := windmillPrivateSet x A
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
    obtain ⟨v,_,rfl⟩ := (mem_windmillPrivateSet x A _).mp ht
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
    obtain ⟨v,hv,rfl⟩ := (mem_windmillPrivateSet x A _).mp ht
    exact (Finset.mem_filter.mp hv).2
  have hevenS : ∀ t ∈ S, Even (G.degree t) := by
    intro t ht
    exact (bare_windmillPrivateSet_leaf_guards h x H Finset.univ t (hS t ht)).1
  have hqS : q.val.val ∉ S := by
    intro ht
    obtain ⟨v,hv,he⟩ := (mem_windmillPrivateSet x A _).mp ht
    have hvq : v = q := Subtype.ext (Subtype.ext he)
    apply hqC
    change q ∈ A
    exact hvq ▸ hv
  have hpair : ∀ t, G.Adj q.val.val t → Even (G.degree t) →
      t = (x : V) ∨ t = p.val.val := by
    intro t ht he
    have hp := bare_windmill_private_even_neighbors h x H f hedge q t ht he
    have hfp : f q = p := hinv p
    simpa only [hfp] using hp
  have haq : ¬ G.Adj a q.val.val := by
    intro hadj
    rcases hpair a hadj.symm a.property with ht | ht
    · exact hnotX a haZ ht
    · exact hnotPriv a haZ (ht.symm ▸ hpPriv)
  have hax : ¬ G.Adj a x := by
    intro ht
    have ht' : (evenSubgraph G).Adj a x := ht
    exact hxZ (Z.mem_supp_of_adj_mem_supp haZ ht')
  have hcontacts : ∀ t, G.Adj u t → Even (G.degree t) →
      t ∈ S ∨ t = (a : V) ∨ t = (b : V) ∨ t = (c : V) ∨ t = h := by
    intro t hut he
    rcases hclass t hut he with ht | ht | ht
    · exact False.elim (hux (ht ▸ hut))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ht)))
    · rcases hcover ⟨t,he⟩ ht with hp | hz
      · exact Or.inl hp
      · rw [hF,Finset.mem_singleton] at hz
        have htZ : (⟨t,he⟩ : evenVertices G) ∈ Z.supp :=
          (SimpleGraph.ConnectedComponent.mem_supp_iff Z _).mpr hz
        rw [hsupp] at htZ
        rcases htZ with ht | ht | ht
        · exact Or.inr (Or.inl (congrArg Subtype.val ht))
        · exact Or.inr (Or.inr (Or.inl (congrArg Subtype.val ht)))
        · exact Or.inr (Or.inr (Or.inr (Or.inl (congrArg Subtype.val ht))))
  rcases H.counterexample.1 with ⟨_,hhx,_,hhEven,_,hhzero,_⟩
  have hnot : ∀ t, Even (G.degree t) → ¬ G.Adj h t := by
    intro t ht hadj
    have hempty : evenNeighbors G h = ∅ := Finset.card_eq_zero.mp hhzero
    have hm := (mem_evenNeighbors (G := G) h t).mpr ⟨hadj,ht⟩
    simpa [hempty] using hm
  apply bare_native_t3_E1_impossible h u x H S privates Z a b c hsupp hxZ hab hbc hca
    p.val.val q.val.val ((mem_windmillPrivateSet x A _).mpr ⟨p,hpC,rfl⟩) hqS
    (hub_not_mem_windmillPrivateSet x A)
  · intro he
    exact (Nat.not_even_iff_odd.mpr huOdd) (he ▸ q.val.property)
  · exact q.val.property
  · intro he
    exact (Nat.not_even_iff_odd.mpr huOdd) (he ▸ x.property)
  · intro he
    exact p.property.ne (Subtype.val_injective he).symm
  · exact hpq.ne
  · change G.Adj (x : V) q.val.val
    exact q.property
  · change G.Adj (x : V) p.val.val
    exact p.property
  · exact hpq
  · exact (hprivateGuard p.val.val hpPriv).2
  · exact hpair
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
  · exact hub.ne.symm
  · exact huc.ne.symm
  · exact hcontacts
  · exact hS
  · exact hprivateGuard
  · intro t ht htu
    obtain ⟨v,_,rfl⟩ := (mem_windmillPrivateSet x _ _).mp ht
    exact (mem_windmillPrivateSet x A _).mpr
      ⟨v,Finset.mem_filter.mpr ⟨Finset.mem_univ _,htu.symm⟩,rfl⟩
  · exact haq
  · exact hax
  · exact huq
  · exact hux
  · intro he
    exact (Nat.not_even_iff_odd.mpr huOdd) (he ▸ hhEven)
  · exact hah.symm
  · exact fun ht => hnot x x.property (hprivateGuard h (hS h ht)).1
  · exact hhx
  · exact fun he => hnot x x.property (he.symm ▸ q.property.symm)
  · exact hbh.symm
  · exact hch.symm

end Gallai.TwoException
