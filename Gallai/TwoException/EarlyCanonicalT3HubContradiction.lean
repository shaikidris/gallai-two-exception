/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.EarlyCanonicalT3SingleSelection
public import Gallai.TwoException.EarlyNativeT3E4Contradiction

@[expose] public section

/-! # Complete canonical singleton-T3 hub-contact branch -/
namespace Gallai.TwoException
open scoped Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Canonical singleton-T3 contacts meeting the hub and a private are
impossible, with no private-contact parity restriction. -/
theorem bare_canonical_t3_hub_impossible
    (h u : V) (x : evenVertices G) (H : BareMinimalCounterexample G h (x : V))
    (huOdd : Odd (G.degree u)) (hux : G.Adj u x)
    (hp : (windmillContacts x u).Nonempty)
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
  obtain ⟨p,hpC,hqC,hpq,huq,hoddS⟩ := bare_canonical_t3_hub_single_selection
    h u x H huOdd hux hp Z hF hthree f hinv hedge P hindex
  let q := f p
  let A := windmillContacts x u
  let privates := windmillPrivateSet x (Finset.univ : Finset _)
  let S := insert (x : V) ((windmillPrivateSet x A).erase p.val.val)
  obtain ⟨hfamily,houtside,hclass,hOriginal,hcover⟩ := bare_early_canonical_contact_guards h u x H
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
  have hpPriv : p.val.val ∈ privates := (mem_windmillPrivateSet x _ _).mpr
    ⟨p,Finset.mem_univ _,rfl⟩
  have hqPriv : q.val.val ∈ privates := (mem_windmillPrivateSet x _ _).mpr
    ⟨q,Finset.mem_univ _,rfl⟩
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
  have hS : ∀ t ∈ S, t = (x : V) ∨ t ∈ privates := by
    intro t ht
    rcases Finset.mem_insert.mp ht with ht | ht
    · exact Or.inl ht
    · obtain ⟨v,hv,rfl⟩ := (mem_windmillPrivateSet x A _).mp (Finset.mem_of_mem_erase ht)
      exact Or.inr ((mem_windmillPrivateSet x _ _).mpr ⟨v,Finset.mem_univ _,rfl⟩)
  have hnotS : ∀ t : evenVertices G, t ∈ Z.supp → (t : V) ∉ S := by
    intro t ht hs
    rcases hS t hs with hx | hp
    · exact hnotX t ht hx
    · exact hnotPriv t ht hp
  have haS := hnotS a haZ
  have hbS := hnotS b hbZ
  have hcS := hnotS c hcZ
  have hadjS : ∀ t ∈ S, G.Adj u t := by
    intro t ht
    rcases Finset.mem_insert.mp ht with ht | ht
    · exact ht ▸ hux
    · obtain ⟨v,hv,rfl⟩ := (mem_windmillPrivateSet x A _).mp (Finset.mem_of_mem_erase ht)
      exact (Finset.mem_filter.mp hv).2
  have hevenS : ∀ t ∈ S, Even (G.degree t) := by
    intro t ht
    rcases hS t ht with ht | ht
    · exact ht ▸ x.property
    · exact (bare_windmillPrivateSet_leaf_guards h x H Finset.univ t ht).1
  have hpS : p.val.val ∉ S := by
    intro ht
    rcases Finset.mem_insert.mp ht with ht | ht
    · exact p.property.ne (Subtype.val_injective ht).symm
    · exact (Finset.mem_erase.mp ht).1 rfl
  have hqS : q.val.val ∉ S := by
    intro ht
    rcases Finset.mem_insert.mp ht with ht | ht
    · exact q.property.ne (Subtype.val_injective ht).symm
    · obtain ⟨v,hv,he⟩ := (mem_windmillPrivateSet x A _).mp (Finset.mem_of_mem_erase ht)
      have hvq : v = q := Subtype.ext (Subtype.ext he)
      apply hqC
      change q ∈ A
      exact hvq ▸ hv
  have hpa : p.val.val ≠ (a : V) := fun he => hnotPriv a haZ (he ▸ hpPriv)
  have hqa : q.val.val ≠ (a : V) := fun he => hnotPriv a haZ (he ▸ hqPriv)
  have hdis : p.val.val ≠ (b : V) ∧ p.val.val ≠ (c : V) ∧
      q.val.val ≠ (b : V) ∧ q.val.val ≠ (c : V) :=
    ⟨fun he => hnotPriv b hbZ (he ▸ hpPriv),fun he => hnotPriv c hcZ (he ▸ hpPriv),
      fun he => hnotPriv b hbZ (he ▸ hqPriv),fun he => hnotPriv c hcZ (he ▸ hqPriv)⟩
  have hpu : p.val.val ≠ u := by
    intro he
    have hpEven : Even (G.degree p.val.val) := p.val.property
    exact (Nat.not_even_iff_odd.mpr huOdd) (he ▸ hpEven)
  have hqu : q.val.val ≠ u := by
    intro he
    have hqEven : Even (G.degree q.val.val) := q.val.property
    exact (Nat.not_even_iff_odd.mpr huOdd) (he ▸ hqEven)
  have hpair : ∀ t, G.Adj p.val.val t → Even (G.degree t) →
      t = (x : V) ∨ t = q.val.val :=
    bare_windmill_private_even_neighbors h x H f hedge p
  have hap : ¬ G.Adj a p.val.val := by
    intro hadj
    rcases hpair a hadj.symm a.property with ht | ht
    · exact hnotX a haZ ht
    · exact hnotPriv a haZ (ht.symm ▸ hqPriv)
  have haq : ¬ G.Adj a q.val.val := by
    intro hadj
    have hqaPair := bare_windmill_private_even_neighbors h x H f hedge q a hadj.symm a.property
    rcases hqaPair with ht | ht
    · exact hnotX a haZ ht
    · have hfp : f q = p := hinv p
      have ht' : (a : V) = p.val.val := by simpa only [hfp] using ht
      exact hnotPriv a haZ (ht'.symm ▸ hpPriv)
  have hcontacts : ∀ t, G.Adj u t → Even (G.degree t) →
      t ∈ S ∨ t = (a : V) ∨ t = p.val.val ∨ t = (b : V) ∨ t = (c : V) ∨ t = h := by
    intro t hut he
    rcases hclass t hut he with ht | ht | ht
    · exact Or.inl (Finset.mem_insert.mpr (Or.inl ht))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ht))))
    · rcases hcover ⟨t,he⟩ ht with hp | hz
      · by_cases htp : t = p.val.val
        · exact Or.inr (Or.inr (Or.inl htp))
        · exact Or.inl (Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨htp,hp⟩))
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
  apply bare_native_t3_E4_impossible h u x H S privates Z a b c hsupp hab hbc hca
    p.val.val q.val.val hpq p.val.property q.val.property hpPriv hqPriv
    (fun ht => G.irrefl (hadjS u ht)) haS hua huOdd hoddS hadjS hevenS (by simp [S])
  · intro t ht htx
    rcases hS t ht with hx | hp
    · exact False.elim (htx hx)
    · exact (hprivateGuard t hp).2.le
  · intro e he
    simp only [List.mem_cons,List.not_mem_nil,or_false] at he
    rcases he with he | he
    · subst e; exact ⟨hpu,hqu,by simp [hpa,hpS],by simp [hqa,hqS]⟩
    · subst e; exact ⟨hub.ne.symm,huc.ne.symm,by simp [hab.ne.symm,hbS],by simp [hca.ne,hcS]⟩
  · exact hdis
  · exact hcontacts
  · exact hS
  · intro ht
    obtain ⟨v,_,he⟩ := (mem_windmillPrivateSet x _ _).mp ht
    have heven : Even (G.degree u) := he ▸ v.val.property
    exact (Nat.not_even_iff_odd.mpr huOdd) heven
  · exact hprivateGuard
  · exact hpair
  · exact hap
  · exact haq
  · exact huq
  · intro he
    exact (Nat.not_even_iff_odd.mpr huOdd) (he ▸ hhEven)
  · exact hah.symm
  · intro ht
    rcases hS h ht with hx | hp
    · exact hhx hx
    · exact hnot x x.property (hprivateGuard h hp).1
  · intro he
    exact hnot x x.property (he.symm ▸ p.property.symm)
  · intro he
    exact hnot x x.property (he.symm ▸ q.property.symm)
  · exact hbh.symm
  · exact hch.symm

end Gallai.TwoException
