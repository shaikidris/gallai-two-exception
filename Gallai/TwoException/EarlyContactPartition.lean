/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.WindmillContactSets

@[expose] public section

/-! # Complete double and single contact coverage for early payment -/
namespace Gallai.TwoException
open scoped Finset
variable {N : Type*} [DecidableEq N]

/-- Each contact belongs to an indexed double or single contact petal.
No petal with zero contacts contributes to the contact universe. -/
theorem indexed_contact_double_or_single
    (f : N → N) (P C : Finset N)
    (hindex : ∀ a, ∃! r, r ∈ P ∧ (a = r ∨ a = f r))
    (a : N) (ha : a ∈ C) :
    (∃ r ∈ doubleContactPetals f P C, a = r ∨ a = f r) ∨
      (∃ r ∈ singleContactPetals f P C, a = r ∨ a = f r) := by
  obtain ⟨r,⟨hr,har⟩,_⟩ := hindex a
  by_cases hb : r ∈ C ∧ f r ∈ C
  · exact Or.inl ⟨r,Finset.mem_filter.mpr ⟨hr,hb⟩,har⟩
  · refine Or.inr ⟨r,Finset.mem_filter.mpr ⟨hr,?_⟩,har⟩
    rcases har with rfl | rfl
    · exact Or.inl ⟨ha,fun hf => hb ⟨ha,hf⟩⟩
    · exact Or.inr ⟨fun hc => hb ⟨hc,ha⟩,ha⟩

/-- Exact contact coverage by complete double petals and the contact
parts of single petals. This identity excludes an unaccounted remainder
when local gains are summed. -/
theorem indexed_early_contact_partition
    (f : N → N) (P C : Finset N)
    (hindex : ∀ a, ∃! r, r ∈ P ∧ (a = r ∨ a = f r)) :
    C = (doubleContactPetals f P C).biUnion (fun r => {r,f r}) ∪
      (singleContactPetals f P C).biUnion (fun r => C ∩ {r,f r}) := by
  ext a
  constructor
  · intro ha
    rcases indexed_contact_double_or_single f P C hindex a ha with
      ⟨r,hr,har⟩ | ⟨r,hr,har⟩
    · exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr
        ⟨r,hr,by simpa using har⟩)
    · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
        ⟨r,hr,Finset.mem_inter.mpr ⟨ha,by simpa using har⟩⟩)
  · intro ha
    rcases Finset.mem_union.mp ha with ha | ha
    · obtain ⟨r,hr,har⟩ := Finset.mem_biUnion.mp ha
      have hc := (Finset.mem_filter.mp hr).2
      have har' : a = r ∨ a = f r := by simpa using har
      rcases har' with rfl | rfl
      · exact hc.1
      · exact hc.2
    · obtain ⟨r,_,har⟩ := Finset.mem_biUnion.mp ha
      exact (Finset.mem_inter.mp har).1

/-- If every single-contact petal uses the same contact p, the entire
contact set is the double-family union together with that sole contact. -/
theorem indexed_early_sole_single_partition
    (f : N → N) (P C : Finset N)
    (hindex : ∀ a, ∃! r, r ∈ P ∧ (a = r ∨ a = f r))
    (p : N) (hp : p ∈ C)
    (hsingle : ∀ r ∈ singleContactPetals f P C,
      ∀ a ∈ C ∩ ({r,f r} : Finset N), a = p) :
    C = (doubleContactPetals f P C).biUnion (fun r => {r,f r}) ∪ {p} := by
  have heq := indexed_early_contact_partition f P C hindex
  ext a
  constructor
  · intro ha
    have ha' : a ∈ (doubleContactPetals f P C).biUnion (fun r => {r,f r}) ∪
        (singleContactPetals f P C).biUnion (fun r => C ∩ {r,f r}) := by
      rw [← heq]
      exact ha
    rcases Finset.mem_union.mp ha' with hd | hs
    · exact Finset.mem_union_left _ hd
    · obtain ⟨r,hr,har⟩ := Finset.mem_biUnion.mp hs
      exact Finset.mem_union_right _ (Finset.mem_singleton.mpr (hsingle r hr a har))
  · intro ha
    rcases Finset.mem_union.mp ha with hd | hp'
    · rw [heq]
      exact Finset.mem_union_left _ hd
    · exact (Finset.mem_singleton.mp hp') ▸ hp

/-- A single contact cannot occur in the double-family union. -/
theorem single_contact_avoids_double_union
    (f : N → N) (hinv : Function.Involutive f) (P C : Finset N)
    (p : N) (hfp : f p ∉ C) :
    p ∉ (doubleContactPetals f P C).biUnion (fun r => {r,f r}) := by
  intro hp
  obtain ⟨r,hr,hpr⟩ := Finset.mem_biUnion.mp hp
  have hc := (Finset.mem_filter.mp hr).2
  have hpr' : p = r ∨ p = f r := by simpa using hpr
  rcases hpr' with rfl | rfl
  · exact hfp hc.2
  · exact hfp (by simpa only [hinv r] using hc.1)

/-- Selecting the sole single contact adds one unit to the double-family
gain. Exact disjoint union counts justify the combined inequality. -/
theorem early_sole_single_union_gain
    (D A : Finset N) (p : N) (hpD : p ∉ D) (hpA : p ∈ A)
    (hgain : #(D \ A) ≤ #(D ∩ A)) :
    #((D ∪ {p}) \ A) + 1 ≤ #((D ∪ {p}) ∩ A) := by
  have hpend : (D ∪ {p}) \ A = D \ A := by
    ext a
    simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_singleton]
    constructor
    · rintro ⟨ha | rfl,hn⟩
      · exact ⟨ha,hn⟩
      · exact False.elim (hn hpA)
    · rintro ⟨ha,hn⟩
      exact ⟨Or.inl ha,hn⟩
  have hsel : (D ∪ {p}) ∩ A = insert p (D ∩ A) := by
    ext a
    simp only [Finset.mem_inter, Finset.mem_union, Finset.mem_singleton, Finset.mem_insert]
    constructor
    · rintro ⟨ha | rfl,hA⟩
      · exact Or.inr ⟨ha,hA⟩
      · exact Or.inl rfl
    · rintro (rfl | ⟨ha,hA⟩)
      · exact ⟨Or.inr rfl,hpA⟩
      · exact ⟨Or.inl ha,hA⟩
  rw [hpend,hsel,Finset.card_insert_of_notMem
    (fun ht => hpD (Finset.mem_inter.mp ht).1)]
  omega

section Ambient
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Embedding a union of indexed petals gives the corresponding ambient
two-vertex packet union, with no change of the carrier universe. -/
theorem windmillPrivateSet_pair_union
    (x : evenVertices G)
    (f : {a : evenVertices G // (evenSubgraph G).Adj x a} →
      {a : evenVertices G // (evenSubgraph G).Adj x a})
    (F : Finset {a : evenVertices G // (evenSubgraph G).Adj x a}) :
    windmillPrivateSet x (F.biUnion (fun r => {r,f r})) =
      F.biUnion (fun r => ({r.val.val,(f r).val.val} : Finset V)) := by
  ext t
  constructor
  · intro ht
    obtain ⟨a,ha,rfl⟩ := (mem_windmillPrivateSet x _ t).mp ht
    obtain ⟨r,hr,har⟩ := Finset.mem_biUnion.mp ha
    refine Finset.mem_biUnion.mpr ⟨r,hr,?_⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at har ⊢
    exact har.imp (congrArg (windmillPrivateEmbedding x))
      (congrArg (windmillPrivateEmbedding x))
  · intro ht
    obtain ⟨r,hr,htr⟩ := Finset.mem_biUnion.mp ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at htr
    rcases htr with rfl | rfl
    · exact (mem_windmillPrivateSet x _ _).mpr
        ⟨r,Finset.mem_biUnion.mpr ⟨r,hr,by simp⟩,rfl⟩
    · exact (mem_windmillPrivateSet x _ _).mpr
        ⟨f r,Finset.mem_biUnion.mpr ⟨r,hr,by simp⟩,rfl⟩

/-- The sole-single contact partition holds on the exact ambient leaf
set consumed by the early star-restoration theorem. -/
theorem ambient_early_sole_single_partition
    (x : evenVertices G)
    (f : {a : evenVertices G // (evenSubgraph G).Adj x a} →
      {a : evenVertices G // (evenSubgraph G).Adj x a})
    (P C : Finset {a : evenVertices G // (evenSubgraph G).Adj x a})
    (hindex : ∀ a, ∃! r, r ∈ P ∧ (a = r ∨ a = f r))
    (p : {a : evenVertices G // (evenSubgraph G).Adj x a}) (hp : p ∈ C)
    (hsingle : ∀ r ∈ singleContactPetals f P C,
      ∀ a ∈ C ∩ ({r,f r} : Finset _), a = p) :
    windmillPrivateSet x C = (doubleContactPetals f P C).biUnion
      (fun r => ({r.val.val,(f r).val.val} : Finset V)) ∪ {p.val.val} := by
  have heq := indexed_early_sole_single_partition f P C hindex p hp hsingle
  calc
    windmillPrivateSet x C = windmillPrivateSet x
        ((doubleContactPetals f P C).biUnion (fun r => {r,f r}) ∪ {p}) :=
      congrArg (windmillPrivateSet x) heq
    _ = windmillPrivateSet x ((doubleContactPetals f P C).biUnion
        (fun r => {r,f r})) ∪ {p.val.val} := by
      simp only [windmillPrivateSet, Finset.map_union, Finset.map_singleton]
      rfl
    _ = _ := by rw [windmillPrivateSet_pair_union]

end Ambient
end Gallai.TwoException
