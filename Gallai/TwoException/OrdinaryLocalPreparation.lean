/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.OrdinaryContactShapes

@[expose] public section

/-! # Local regular preparation chosen from actual triangle contacts -/
namespace Gallai.TwoException
open scoped Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Delete all three spokes in T3; otherwise delete the chosen contact
spoke and its opposite mate. The deletion covers the whole even component
and never gives a mate endpoint a deleted spoke in the same packet. -/
theorem ordinary_triangle_regular_preparation
    (S : Finset (evenVertices G)) (C : (evenSubgraph G).ConnectedComponent)
    (a b c : evenVertices G) (hsupp : C.supp = {a,b,c})
    (hab : G.Adj a b) (hbc : G.Adj b c) (hca : G.Adj c a) (haS : a ∈ S) :
    ∃ P : Finset (evenVertices G), ∃ M : List (evenVertices G × evenVertices G),
      P ⊆ ordinaryComponentPacket G S C ∧
      (∀ t, t ∈ C.supp → t ∈ P ∨ ∃ e ∈ M, t = e.1 ∨ t = e.2) ∧
      (∀ e ∈ M, G.Adj e.1 e.2 ∧ e.1 ∈ C.supp ∧ e.2 ∈ C.supp ∧
        e.1 ∉ P ∧ e.2 ∉ P) ∧
      ((P = {a,b,c} ∧ M = [] ∧ b ∈ S ∧ c ∈ S) ∨
       (P = {a} ∧ M = [(b,c)] ∧ (b ∉ S ∨ c ∉ S))) := by
  classical
  have habN : a ≠ b := fun he => G.irrefl (congrArg Subtype.val he ▸ hab)
  have hacN : a ≠ c := fun he => G.irrefl (congrArg Subtype.val he ▸ hca.symm)
  by_cases hb : b ∈ S
  · by_cases hc : c ∈ S
    · refine ⟨{a,b,c}, [], ?_, ?_, by simp, Or.inl ⟨rfl,rfl,hb,hc⟩⟩
      · intro t ht
        have htC : t ∈ C.supp := by simpa [hsupp] using ht
        have htS : t ∈ S := by
          simp only [Finset.mem_insert, Finset.mem_singleton] at ht
          rcases ht with rfl | rfl | rfl <;> assumption
        exact Finset.mem_filter.mpr ⟨htS, htC⟩
      · intro t ht
        exact Or.inl (by simpa [hsupp] using ht)
    · refine ⟨{a}, [(b,c)], ?_, ?_, ?_, Or.inr ⟨rfl,rfl,Or.inr hc⟩⟩
      · intro t ht
        have he := Finset.mem_singleton.mp ht
        subst t
        exact Finset.mem_filter.mpr ⟨haS, by simp [hsupp]⟩
      · intro t ht
        simp only [hsupp, Set.mem_insert_iff, Set.mem_singleton_iff] at ht
        rcases ht with ht | ht | ht
        · exact Or.inl (Finset.mem_singleton.mpr ht)
        · exact Or.inr ⟨(b,c), by simp, Or.inl ht⟩
        · exact Or.inr ⟨(b,c), by simp, Or.inr ht⟩
      · intro e he
        have heq : e = (b,c) := by simpa using he
        subst e
        simpa [hsupp, habN, hacN, Ne.symm habN, Ne.symm hacN] using hbc
  · refine ⟨{a}, [(b,c)], ?_, ?_, ?_, Or.inr ⟨rfl,rfl,Or.inl hb⟩⟩
    · intro t ht
      have he := Finset.mem_singleton.mp ht
      subst t
      exact Finset.mem_filter.mpr ⟨haS, by simp [hsupp]⟩
    · intro t ht
      simp only [hsupp, Set.mem_insert_iff, Set.mem_singleton_iff] at ht
      rcases ht with ht | ht | ht
      · exact Or.inl (Finset.mem_singleton.mpr ht)
      · exact Or.inr ⟨(b,c), by simp, Or.inl ht⟩
      · exact Or.inr ⟨(b,c), by simp, Or.inr ht⟩
    · intro e he
      have heq : e = (b,c) := by simpa using he
      subst e
      simpa [hsupp, habN, hacN, Ne.symm habN, Ne.symm hacN] using hbc

/-- The actual contact count of a labelled triangle records which of
the other two vertices are contacts; the chosen vertex is always one. -/
theorem ordinary_triangle_contact_count
    (S : Finset (evenVertices G)) (C : (evenSubgraph G).ConnectedComponent)
    (a b c : evenVertices G) (hsupp : C.supp = {a,b,c})
    (hab : G.Adj a b) (hbc : G.Adj b c) (hca : G.Adj c a) (haS : a ∈ S) :
    #(ordinaryComponentPacket G S C) =
      1 + (if b ∈ S then 1 else 0) + (if c ∈ S then 1 else 0) := by
  classical
  have habN : a ≠ b := fun he => G.irrefl (congrArg Subtype.val he ▸ hab)
  have hacN : a ≠ c := fun he => G.irrefl (congrArg Subtype.val he ▸ hca.symm)
  have hbcN : b ≠ c := fun he => G.irrefl (congrArg Subtype.val he ▸ hbc)
  have heq : ordinaryComponentPacket G S C = ({a,b,c} : Finset _).filter (fun t => t ∈ S) := by
    ext t
    simp only [ordinaryComponentPacket, Finset.mem_filter, hsupp,
      Set.mem_insert_iff, Set.mem_singleton_iff, Finset.mem_insert, Finset.mem_singleton]
    aesop
  rw [heq]
  by_cases hb : b ∈ S <;> by_cases hc : c ∈ S <;>
    simp [Finset.filter_insert, Finset.filter_singleton, haS, hb, hc, habN, hacN, hbcN]

/-- A special T2 deletes exactly its two actual contact spokes. Its third
even vertex is not adjacent to the centre, as required by the isolated
even-vertex witness in the special auxiliary component budget. -/
theorem ordinary_triangle_special_preparation
    (u : V) (S : Finset (evenVertices G))
    (C : (evenSubgraph G).ConnectedComponent) (a b c : evenVertices G)
    (hsupp : C.supp = {a,b,c})
    (hab : G.Adj a b) (hbc : G.Adj b c) (hca : G.Adj c a)
    (hpacket : ordinaryComponentPacket G S C = {a,b})
    (hcontacts : ∀ t : evenVertices G, G.Adj u t → t ∈ S) :
    {a,b} ⊆ S ∧ c ∉ S ∧ ¬ G.Adj c u ∧ #({a,b} : Finset (evenVertices G)) = 2 := by
  classical
  have habN : a ≠ b := fun he => G.irrefl (congrArg Subtype.val he ▸ hab)
  have hcbN : c ≠ b := fun he => G.irrefl (congrArg Subtype.val he ▸ hbc.symm)
  have hcaN : c ≠ a := fun he => G.irrefl (congrArg Subtype.val he ▸ hca)
  have hsub : {a,b} ⊆ S := by
    rw [← hpacket]
    exact Finset.filter_subset _ _
  have hcS : c ∉ S := by
    intro hc
    have hcP : c ∈ ordinaryComponentPacket G S C :=
      Finset.mem_filter.mpr ⟨hc, by simp [hsupp]⟩
    rw [hpacket] at hcP
    simpa [hcaN, hcbN] using hcP
  refine ⟨hsub, hcS, ?_, by simp [habN]⟩
  exact fun hcu => hcS (hcontacts c hcu.symm)

end Gallai.TwoException
