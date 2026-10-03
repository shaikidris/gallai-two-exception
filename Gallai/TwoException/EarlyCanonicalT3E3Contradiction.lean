/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.EarlyNativeT3E3Contradiction
public import Gallai.TwoException.EarlyCanonicalT3Labels

@[expose] public section

/-! # Canonical hub-contact T3 with even private contact count -/
namespace Gallai.TwoException
open scoped Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Canonical singleton-T3 contacts with the hub present and even private
contact count supply the native E3 contradiction. No packet-selection or
auxiliary-decomposition certificate is required. -/
theorem bare_canonical_t3_even_hub_impossible
    (h u : V) (x : evenVertices G) (H : BareMinimalCounterexample G h (x : V))
    (huOdd : Odd (G.degree u)) (hux : G.Adj u x)
    (hp : (windmillContacts x u).Nonempty)
    (hevenC : Even #(windmillContacts x u))
    (Z : (evenSubgraph G).ConnectedComponent)
    (hF : earlyOrdinaryContactComponents G h x u = {Z})
    (hthree : #(ordinaryComponentPacket G (earlyOriginalContacts G h x u) Z) = 3) :
    False := by
  classical
  obtain ⟨hfamily,houtside,hclass,hS,hcover⟩ := bare_early_canonical_contact_guards h u x H
  have hZ : Z ∈ earlyOrdinaryContactComponents G h x u := by rw [hF]; simp
  have hxZ := houtside Z hZ
  obtain ⟨a,b,c,hsupp,hab,hbc,hca,hua,hub,huc,hah,hbh,hch⟩ :=
    bare_canonical_t3_labels h u x H Z hZ hthree
  let C := windmillContacts x u
  let K := insert (x : V) (windmillPrivateSet x C)
  let privates := windmillPrivateSet x (Finset.univ : Finset _)
  rcases H.counterexample.1 with ⟨_,hhx,_,hhEven,_,hhzero,_⟩
  have hnot : ∀ t, Even (G.degree t) → ¬ G.Adj h t := by
    intro t ht hadj
    have hempty : evenNeighbors G h = ∅ := Finset.card_eq_zero.mp hhzero
    have hm := (mem_evenNeighbors (G := G) h t).mpr ⟨hadj,ht⟩
    simpa [hempty] using hm
  have hxPrivate : (x : V) ∉ windmillPrivateSet x C := by
    intro ht
    obtain ⟨t,_,he⟩ := (mem_windmillPrivateSet x C _).mp ht
    have hxt : G.Adj x t.val.val := t.property
    have hloop : G.Adj x x := by simpa only [he] using hxt
    exact G.irrefl hloop
  have hoddK : Odd #K := by
    change Odd #(insert (x : V) (windmillPrivateSet x C))
    rw [Finset.card_insert_of_notMem hxPrivate,windmillPrivateSet_card,Nat.odd_iff]
    change Even #C at hevenC
    rw [Nat.even_iff] at hevenC
    omega
  have hprivateGuard : ∀ t ∈ privates, G.Adj t x ∧ eDegree G t = 2 := by
    intro t ht
    obtain ⟨v,hv,rfl⟩ := (mem_windmillPrivateSet x _ _).mp ht
    exact ⟨v.property.symm,
      (bare_windmillPrivateSet_leaf_guards h x H Finset.univ v.val.val
        ((mem_windmillPrivateSet x _ _).mpr ⟨v,hv,rfl⟩)).2⟩
  have hK : ∀ t ∈ K, t = (x : V) ∨ t ∈ privates := by
    intro t ht
    rcases Finset.mem_insert.mp ht with ht | ht
    · exact Or.inl ht
    · obtain ⟨v,hv,rfl⟩ := (mem_windmillPrivateSet x C _).mp ht
      exact Or.inr ((mem_windmillPrivateSet x _ _).mpr ⟨v,Finset.mem_univ _,rfl⟩)
  have hadjK : ∀ t ∈ K, G.Adj u t := by
    intro t ht
    rcases Finset.mem_insert.mp ht with ht | ht
    · exact ht ▸ hux
    · obtain ⟨v,hv,rfl⟩ := (mem_windmillPrivateSet x C _).mp ht
      exact (Finset.mem_filter.mp hv).2
  have hevenK : ∀ t ∈ K, Even (G.degree t) := by
    intro t ht
    rcases Finset.mem_insert.mp ht with ht | ht
    · exact ht ▸ x.property
    · obtain ⟨v,_,rfl⟩ := (mem_windmillPrivateSet x C _).mp ht
      exact v.val.property
  have hnotK : ∀ t : evenVertices G, t ∈ Z.supp → (t : V) ∉ K := by
    intro t ht htk
    rcases hK t htk with htX | htP
    · exact hxZ (Subtype.val_injective htX ▸ ht)
    · obtain ⟨v,_,hv⟩ := (mem_windmillPrivateSet x _ _).mp htP
      have hvt : v.val = t := Subtype.val_injective hv
      exact hxZ (Z.mem_supp_of_adj_mem_supp ht (hvt ▸ v.property.symm))
  have haK := hnotK a (by rw [hsupp]; simp)
  have hbK := hnotK b (by rw [hsupp]; simp)
  have hcK := hnotK c (by rw [hsupp]; simp)
  have hcontacts : ∀ t, G.Adj u t → Even (G.degree t) →
      t ∈ insert (a : V) K ∨ t = (b : V) ∨ t = (c : V) ∨ t = h := by
    intro t hut he
    rcases hclass t hut he with ht | ht | ht
    · exact Or.inl (Finset.mem_insert_of_mem (Finset.mem_insert.mpr (Or.inl ht)))
    · exact Or.inr (Or.inr (Or.inr ht))
    · rcases hcover ⟨t,he⟩ ht with hp | hz
      · exact Or.inl (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hp))
      · rw [hF,Finset.mem_singleton] at hz
        have htZ : (⟨t,he⟩ : evenVertices G) ∈ Z.supp :=
          (SimpleGraph.ConnectedComponent.mem_supp_iff Z _).mpr hz
        rw [hsupp] at htZ
        rcases htZ with ht | ht | ht
        · exact Or.inl (Finset.mem_insert.mpr (Or.inl (congrArg Subtype.val ht)))
        · exact Or.inr (Or.inl (congrArg Subtype.val ht))
        · exact Or.inr (Or.inr (Or.inl (congrArg Subtype.val ht)))
  apply bare_native_t3_E3_impossible h u x H K privates Z a b c hsupp hab hbc hca
    (by intro ht; exact G.irrefl (hadjK u ht)) haK hua huOdd hoddK
    hub.ne.symm huc.ne.symm hbK hcK hadjK hevenK (by simp [K]) hcontacts hK
  · obtain ⟨v,hv⟩ := hp
    exact ⟨v.val.val,(mem_windmillPrivateSet x _ _).mpr ⟨v,Finset.mem_univ _,rfl⟩⟩
  · intro ht
    obtain ⟨v,_,hv⟩ := (mem_windmillPrivateSet x _ _).mp ht
    have he : Even (G.degree u) := hv ▸ v.val.property
    exact (Nat.not_even_iff_odd.mpr huOdd) he
  · exact hprivateGuard
  · intro t ht htu
    obtain ⟨v,_,rfl⟩ := (mem_windmillPrivateSet x _ _).mp ht
    exact Finset.mem_insert_of_mem ((mem_windmillPrivateSet x C _).mpr
      ⟨v,Finset.mem_filter.mpr ⟨Finset.mem_univ _,htu.symm⟩,rfl⟩)
  · intro he
    exact (Nat.not_even_iff_odd.mpr huOdd) (he ▸ hhEven)
  · exact hah.symm
  · exact hbh.symm
  · exact hch.symm
  · intro ht
    rcases hK h ht with ht | ht
    · exact hhx ht
    · exact hnot x x.property (hprivateGuard h ht).1

/-- Any remaining canonical singleton-T3 hub contact has odd private
contact count. This is a necessary residual condition, not an existence
claim for such a counterexample. -/
theorem bare_canonical_t3_hub_contacts_odd
    (h u : V) (x : evenVertices G) (H : BareMinimalCounterexample G h (x : V))
    (huOdd : Odd (G.degree u)) (hux : G.Adj u x)
    (hp : (windmillContacts x u).Nonempty)
    (Z : (evenSubgraph G).ConnectedComponent)
    (hF : earlyOrdinaryContactComponents G h x u = {Z})
    (hthree : #(ordinaryComponentPacket G (earlyOriginalContacts G h x u) Z) = 3) :
    Odd #(windmillContacts x u) := by
  apply Nat.not_even_iff_odd.mp
  intro he
  exact bare_canonical_t3_even_hub_impossible h u x H huOdd hux hp he Z hF hthree

end Gallai.TwoException
