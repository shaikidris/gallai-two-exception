/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.BareWindmill
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

@[expose] public section

/-! # Exact contact counting over indexed windmill petals -/
namespace Gallai.TwoException
open scoped Finset BigOperators

/-- Count actual selected private vertices, with singleton and double
contacts counted over the disjoint petal representatives. -/
theorem indexed_petal_contact_card
    {N : Type*} [Fintype N] [DecidableEq N]
    (f : N → N) (hfree : ∀ a, f a ≠ a) (P A : Finset N)
    (hindex : ∀ a, ∃! r, r ∈ P ∧ (a = r ∨ a = f r)) :
    #A = #{r ∈ P | (r ∈ A ∧ f r ∉ A) ∨ (r ∉ A ∧ f r ∈ A)} +
      2 * #{r ∈ P | r ∈ A ∧ f r ∈ A} := by
  classical
  let pieces : N → Finset N := fun r => ({r, f r} : Finset N).filter (· ∈ A)
  have hcover : P.biUnion pieces = A := by
    ext a
    constructor
    · intro ha
      obtain ⟨r, _, ha⟩ := Finset.mem_biUnion.mp ha
      exact (Finset.mem_filter.mp ha).2
    · intro ha
      obtain ⟨r, ⟨hr, har⟩, _⟩ := hindex a
      apply Finset.mem_biUnion.mpr
      refine ⟨r, hr, Finset.mem_filter.mpr ⟨?_, ha⟩⟩
      simpa only [Finset.mem_insert, Finset.mem_singleton] using har
  have hdisjoint : (P : Set N).PairwiseDisjoint pieces := by
    intro r hr s hs hrs
    apply Finset.disjoint_left.mpr
    intro a har has
    have har' : a = r ∨ a = f r := by
      simpa only [Finset.mem_insert, Finset.mem_singleton] using
        (Finset.mem_filter.mp har).1
    have has' : a = s ∨ a = f s := by
      simpa only [Finset.mem_insert, Finset.mem_singleton] using
        (Finset.mem_filter.mp has).1
    obtain ⟨t, _, huniq⟩ := hindex a
    exact hrs ((huniq r ⟨hr, har'⟩).trans (huniq s ⟨hs, has'⟩).symm)
  have hcount : ∀ r, #(pieces r) =
      (if (r ∈ A ∧ f r ∉ A) ∨ (r ∉ A ∧ f r ∈ A) then 1 else 0) +
      2 * (if r ∈ A ∧ f r ∈ A then 1 else 0) := by
    intro r
    have hrf : r ≠ f r := (hfree r).symm
    by_cases hr : r ∈ A <;> by_cases hf : f r ∈ A <;>
      simp [pieces, Finset.filter_insert, Finset.filter_singleton, hr, hf, hrf]
  calc
    #A = #(P.biUnion pieces) := congrArg Finset.card hcover.symm
    _ = ∑ r ∈ P, #(pieces r) := Finset.card_biUnion hdisjoint
    _ = _ := by
      simp_rw [hcount]
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      simp

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The contact count for an actual bare windmill. The selected vertices
are precisely the private vertices adjacent to the contact vertex `u`. -/
theorem bare_windmill_contact_card
    (h : V) (x : evenVertices G) (H : BareMinimalCounterexample G h (x : V))
    (C : (evenSubgraph G).ConnectedComponent) (hxC : x ∈ C.supp) (u : V) :
    let A : Finset {a : evenVertices G // (evenSubgraph G).Adj x a} :=
      Finset.univ.filter (fun a => G.Adj u a.val.val)
    ∃ (f : {a : evenVertices G // (evenSubgraph G).Adj x a} →
          {a : evenVertices G // (evenSubgraph G).Adj x a})
      (P : Finset {a : evenVertices G // (evenSubgraph G).Adj x a}),
      Function.Involutive f ∧ (∀ a, f a ≠ a) ∧
      (∀ a, ∃! r, r ∈ P ∧ (a = r ∨ a = f r)) ∧
      (∀ a b, (evenSubgraph G).Adj a.val b.val ↔ f a = b) ∧
      #A = #{r ∈ P | (r ∈ A ∧ f r ∉ A) ∨ (r ∉ A ∧ f r ∈ A)} +
        2 * #{r ∈ P | r ∈ A ∧ f r ∈ A} := by
  classical
  dsimp only
  obtain ⟨f, P, hinv, hfree, hindex, hedge, _⟩ :=
    bare_windmill_indexed_petals h x H C hxC
  exact ⟨f, P, hinv, hfree, hindex, hedge,
    indexed_petal_contact_card f hfree P _ hindex⟩

end Gallai.TwoException
