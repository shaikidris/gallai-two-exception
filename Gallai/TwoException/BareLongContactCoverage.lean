/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.BareLongE12Restore
public import Gallai.TwoException.BareLongE4Restore
public import Gallai.TwoException.BareLongE5Restore
public import Gallai.TwoException.WindmillContactSelection

@[expose] public section

/-! # Exhaustive native long-contact reconstruction -/
namespace Gallai.TwoException
open scoped Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Extract the actual windmill contact packet and dispatch all five rows.
The second ordinary preparation and every auxiliary decomposition are
constructed by the row consumers, rather than supplied by the caller. -/
theorem bare_long_contact_endpoint
    (h u v : V) (x : evenVertices G) (H : BareMinimalCounterexample G h (x : V))
    (C : (evenSubgraph G).ConnectedComponent) (hxC : x ∈ C.supp)
    (huOdd : Odd (G.degree u)) (hvOdd : Odd (G.degree v)) (huv : G.Adj u v)
    (hsep : ∀ t ∈ Subtype.val '' C.supp, ¬ G.Adj v t)
    (hcontact : G.Adj u x ∨
      ∃ a : {a : evenVertices G // (evenSubgraph G).Adj x a}, G.Adj u a.val.val)
    (hcontacts : ∀ t, G.Adj u t → Even (G.degree t) →
      t = (x : V) ∨ t ∈ ambientWindmillContacts x u) :
    ∃ E : Decomposition G, E.size ≤ (Fintype.card V + 1) / 2 ∧
      2 ≤ E.endpointCount h := by
  classical
  obtain ⟨f,P,hinv,hfree,hindex,hedge,hcases⟩ :=
    bare_windmill_contact_preparation_cases h x H C hxC u hcontact
  change ContactPreparationCases f P (windmillContacts x u) (G.Adj u x) at hcases
  let A := windmillContacts x u
  let B := ambientWindmillContacts x u
  have hmem : ∀ a ∈ A, a.val.val ∈ B := by
    intro a ha
    exact (mem_windmillPrivateSet x A a.val.val).mpr ⟨a,ha,rfl⟩
  have hnot : ∀ a, a ∉ A → a.val.val ∉ B := by
    intro a ha hb
    obtain ⟨b,hb,heq⟩ := (mem_windmillPrivateSet x A a.val.val).mp hb
    have hba : b = a := Subtype.ext (Subtype.ext heq)
    exact ha (hba ▸ hb)
  have hprivateC : ∀ a : {a : evenVertices G // (evenSubgraph G).Adj x a},
      a.val ∈ C.supp := fun a => C.mem_supp_of_adj_mem_supp hxC a.property
  have hBC : ∀ t ∈ B, G.Adj u t ∧ t ∈ Subtype.val '' C.supp := by
    intro t ht
    obtain ⟨a,ha,rfl⟩ := (mem_windmillPrivateSet x A t).mp ht
    exact ⟨(Finset.mem_filter.mp ha).2,⟨a.val,hprivateC a,rfl⟩⟩
  have hxB : (x : V) ∉ B := hub_not_mem_windmillPrivateSet x A
  have hhB : h ∉ B := by
    intro hh
    have hd := (bare_windmillPrivateSet_leaf_guards h x H A h hh).2
    have hz := H.counterexample.1.2.2.2.2.2.1
    omega
  have hhx : h ≠ (x : V) := H.counterexample.1.2.1
  have hneX : ∀ a : {a : evenVertices G // (evenSubgraph G).Adj x a},
      a.val.val ≠ (x : V) := by
    intro a he
    exact a.property.ne (Subtype.ext he.symm)
  have hneMate : ∀ a, a.val.val ≠ (f a).val.val := by
    intro a he
    have hae : a = f a := Subtype.ext (Subtype.ext he)
    exact hfree a hae.symm
  have hpair := bare_windmill_private_even_neighbors h x H f hedge
  have hpar := windmill_contact_row_parities x f hfree P A hindex
  rcases hcases with ⟨hux,ho,hsingle⟩ | ⟨hux,he,hdouble⟩ | ⟨hux,he⟩ |
      ⟨hux,ho,hsingle⟩ | ⟨hux,he,_,htwo⟩
  · obtain ⟨r,hr⟩ := hsingle
    obtain ⟨p,_,hp,hq⟩ := single_contact_orientation f hinv P A r hr
    apply bare_long_E12_endpoint h u v x (f p).val H C hxC (hprivateC (f p))
      huOdd hvOdd huv hsep B hxB (hnot (f p) hq) hhB (hpar.1 ho) hBC
      (f p).property
    · intro t hut htEven
      rcases hcontacts t hut htEven with ht | ht
      · exact Or.inr (Or.inl ht)
      · exact Or.inl ht
    · exact hmem p hp
    · exact hux
    · intro t ht htEven
      simpa only [hinv p] using hpair (f p) t ht htEven
  · obtain ⟨p,hp⟩ := hdouble
    obtain ⟨hpA,hqA⟩ := (Finset.mem_filter.mp hp).2
    let S := B.erase (f p).val.val
    have hpB := hmem p hpA
    have hqB := hmem (f p) hqA
    apply bare_long_E12_endpoint h u v x (f p).val H C hxC (hprivateC (f p))
      huOdd hvOdd huv hsep S (fun ht => hxB (Finset.mem_of_mem_erase ht))
      (Finset.notMem_erase _ _) (fun ht => hhB (Finset.mem_of_mem_erase ht))
      (hpar.2.1 he _ hqB) (fun t ht => hBC t (Finset.mem_of_mem_erase ht))
      (f p).property
    · intro t hut htEven
      rcases hcontacts t hut htEven with ht | ht
      · exact Or.inr (Or.inl ht)
      · by_cases htq : t = (f p).val.val
        · exact Or.inr (Or.inr htq)
        · exact Or.inl (Finset.mem_erase.mpr ⟨htq,ht⟩)
    · exact Finset.mem_erase.mpr ⟨hneMate p,hpB⟩
    · exact hux
    · intro t ht htEven
      simpa only [hinv p] using hpair (f p) t ht htEven
  · let S := insert (x : V) B
    apply bare_long_E3_endpoint h u v x H C hxC huOdd hvOdd huv hsep S
      (Finset.mem_insert_self _ _) (by simp [S,hhx,hhB]) (hpar.2.2.1 he)
    · intro t ht
      rcases Finset.mem_insert.mp ht with rfl | ht
      · exact ⟨hux,⟨x,hxC,rfl⟩⟩
      · exact hBC t ht
    · intro t hut htEven
      rcases hcontacts t hut htEven with ht | ht
      · exact Finset.mem_insert.mpr (Or.inl ht)
      · exact Finset.mem_insert_of_mem ht
  · obtain ⟨r,hr⟩ := hsingle
    obtain ⟨p,_,hp,hq⟩ := single_contact_orientation f hinv P A r hr
    let S := insert (x : V) (B.erase p.val.val)
    have hpB := hmem p hp
    have hpS : p.val.val ∉ S := by simp [S,hneX p]
    have hqS : (f p).val.val ∉ S := by
      simp only [S,Finset.mem_insert,not_or]
      exact ⟨hneX (f p),fun ht => hnot (f p) hq (Finset.mem_of_mem_erase ht)⟩
    apply bare_long_E4_endpoint h u v x p.val (f p).val H C hxC (hprivateC p)
      (hprivateC (f p)) huOdd hvOdd huv hsep S (Finset.mem_insert_self _ _)
      hpS hqS (by simp [S,hhx,hhB]) (hpar.2.2.2 ho _ hpB)
    · intro t ht
      rcases Finset.mem_insert.mp ht with rfl | ht
      · exact ⟨hux,⟨x,hxC,rfl⟩⟩
      · exact hBC t (Finset.mem_of_mem_erase ht)
    · exact ((hedge p (f p)).mpr rfl).symm
    · intro t hut htEven
      rcases hcontacts t hut htEven with ht | ht
      · exact Or.inl (Finset.mem_insert.mpr (Or.inl ht))
      · by_cases htp : t = p.val.val
        · exact Or.inr (Or.inr htp)
        · exact Or.inl (Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨htp,ht⟩))
    · intro ha
      exact hq (Finset.mem_filter.mpr ⟨Finset.mem_univ _,ha⟩)
    · exact hpair p
  · obtain ⟨p,r,hp,hq,hr,hs,hdis⟩ := two_single_contact_petals f hinv P A hindex htwo
    let S := B.erase p.val.val
    have hcross : ∀ a ∈ ({p,f p} : Finset _), ∀ b ∈ ({r,f r} : Finset _),
        a.val.val ≠ b.val.val := by
      intro a ha b hb heq
      have hab : a = b := Subtype.ext (Subtype.ext heq)
      exact (Finset.disjoint_left.mp hdis) ha (hab.symm ▸ hb)
    have hrp : r.val.val ≠ p.val.val := by
      intro heq
      exact hcross p (by simp) r (by simp) heq.symm
    apply bare_long_E5_endpoint h u v x (f r).val p.val (f p).val H C hxC
      (hprivateC (f r)) (hprivateC p) (hprivateC (f p)) huOdd hvOdd huv hsep S
      (fun ht => hxB (Finset.mem_of_mem_erase ht))
      (fun ht => hnot (f r) hs (Finset.mem_of_mem_erase ht))
      (Finset.notMem_erase _ _) (fun ht => hnot (f p) hq (Finset.mem_of_mem_erase ht))
      (fun ht => hhB (Finset.mem_of_mem_erase ht)) (hpar.2.1 he _ (hmem p hp))
      (fun t ht => hBC t (Finset.mem_of_mem_erase ht)) (f r).property
      ((hedge p (f p)).mpr rfl).symm (hneX p)
      (hcross p (by simp) (f r) (by simp)) (hneX (f p))
      (hcross (f p) (by simp) (f r) (by simp))
    · intro t hut htEven
      rcases hcontacts t hut htEven with ht | ht
      · exact Or.inr (Or.inl ht)
      · by_cases htp : t = p.val.val
        · exact Or.inr (Or.inr (Or.inr (Or.inr htp)))
        · exact Or.inl (Finset.mem_erase.mpr ⟨htp,ht⟩)
    · exact hux
    · intro ha
      exact hq (Finset.mem_filter.mpr ⟨Finset.mem_univ _,ha⟩)
    · intro ha
      exact hs (Finset.mem_filter.mpr ⟨Finset.mem_univ _,ha.symm⟩)
    · exact hpair p
    · exact Finset.mem_erase.mpr ⟨hrp,hmem r hr⟩
    · intro t ht htEven
      simpa only [hinv r] using hpair (f r) t ht htEven

end Gallai.TwoException
