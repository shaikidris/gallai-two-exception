/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.EarlyRetainedSpokeBudget

@[expose] public section

/-! # Singleton-T3 budget with a retained recipient contact -/
namespace Gallai.TwoException
open scoped Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
noncomputable local instance t3RetainedBudgetGraph (Q : SimpleGraph V) :
    DecidableRel Q.Adj := fun _ _ => Classical.propDecidable _

/-- A singleton ordinary triangle specializes the retained-spoke budget.
Its whole component is separated from both hub and unpaid private mate. -/
theorem bare_t3_retained_spoke_auxiliary_endpoint
    (h u : V) (x : evenVertices G) (H : BareMinimalCounterexample G h (x : V))
    (B privates : Finset V) (Z : (evenSubgraph G).ConnectedComponent)
    (a b c : evenVertices G) (hsupp : Z.supp = {a,b,c}) (hxZ : x ∉ Z.supp)
    (p q : V) (hpB : p ∈ B) (hqB : q ∉ B) (hxB : (x : V) ∉ B)
    (hqu : q ≠ u) (hqEven : Even (G.degree q))
    (hxu : (x : V) ≠ u) (hpx : p ≠ (x : V)) (hpqne : p ≠ q)
    (hxq : G.Adj x q) (hxp : G.Adj x p) (hpq : G.Adj p q)
    (hpdegree : eDegree G p = 2)
    (hpair : ∀ t, G.Adj q t → Even (G.degree t) → t = (x : V) ∨ t = p)
    (hadj : ∀ t ∈ B, G.Adj u t) (hleaves : ∀ t ∈ B, Even (G.degree t))
    (haB : (a : V) ∈ B) (hbB : (b : V) ∉ B) (hcB : (c : V) ∉ B)
    (hbu : (b : V) ≠ u) (hcu : (c : V) ≠ u) (hbc : G.Adj b c)
    (hcontacts : ∀ t, G.Adj u t → Even (G.degree t) →
      t ∈ B ∨ t = (b : V) ∨ t = (c : V) ∨ t = (x : V) ∨ t = q ∨ t = h)
    (hB : ∀ t ∈ B, t ∈ privates ∨ t = (a : V))
    (hprivates : ∀ t ∈ privates, G.Adj t x ∧ eDegree G t = 2)
    (hprivateContacts : ∀ t ∈ privates, G.Adj t u → t ∈ B ∨ t = q)
    (hhu : h ≠ u) (hhB : h ∉ B) (hhx : h ≠ (x : V)) (hhq : h ≠ q)
    (hhb : h ≠ (b : V)) (hhc : h ≠ (c : V)) :
    ∃ D : Decomposition (((starPuncture G u B).deleteEdges {s((x : V),q)}).deleteEdges
      {s((b : V),(c : V))}),
      D.size ≤ (Fintype.card V + 1) / 2 ∧ 2 ≤ D.endpointCount h := by
  classical
  have hseparated : ∀ t : evenVertices G, t ∈ Z.supp → (t : V) ≠ x ∧ (t : V) ≠ q := by
    intro t ht
    constructor
    · intro he
      exact hxZ (Subtype.val_injective he ▸ ht)
    · intro he
      have htq : t = (⟨q,hqEven⟩ : evenVertices G) := Subtype.val_injective he
      have hqx : (evenSubgraph G).Adj (⟨q,hqEven⟩ : evenVertices G) x := hxq.symm
      exact hxZ (Z.mem_supp_of_adj_mem_supp (htq ▸ ht) hqx)
  have hbZ : b ∈ Z.supp := by rw [hsupp]; simp
  have hcZ : c ∈ Z.supp := by rw [hsupp]; simp
  have hout := bare_early_retained_spoke_auxiliary_endpoint h u x p q H B privates
    [((b : V),(c : V))] {Z} hadj hleaves hpB hqB hxB hqu hqEven
    hxu hpx hpqne hxq hxp hpq hpdegree hpair (by simp)
    (by
      intro e he
      simp only [List.mem_singleton] at he
      subst e
      exact ⟨hbu,hcu,hbB,hcB,(hseparated b hbZ).1,(hseparated c hcZ).1,
        (hseparated b hbZ).2,(hseparated c hcZ).2⟩)
    (by intro e he; simp only [List.mem_singleton] at he; subst e; exact ⟨hbc,b.property,c.property⟩)
    (by
      intro t ht he
      rcases hcontacts t ht he with ht | ht | ht | ht | ht | ht
      · exact Or.inl ht
      · exact Or.inr (Or.inl ⟨((b : V),(c : V)),by simp,Or.inl ht⟩)
      · exact Or.inr (Or.inl ⟨((b : V),(c : V)),by simp,Or.inr ht⟩)
      · exact Or.inr (Or.inr (Or.inl ht))
      · exact Or.inr (Or.inr (Or.inr (Or.inl ht)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr ht))))
    (by
      intro t ht
      rcases hB t ht with ht | ht
      · exact Or.inl ht
      · exact Or.inr ⟨Z,by simp,a,by rw [hsupp]; simp,ht.symm⟩)
    (by
      intro e he t ht
      simp only [List.mem_singleton] at he
      subst e
      apply Or.inr
      rcases ht with ht | ht
      · exact ⟨Z,by simp,b,hbZ,ht.symm⟩
      · exact ⟨Z,by simp,c,hcZ,ht.symm⟩)
    hprivates hprivateContacts
    (by intro W hW; simp only [Finset.mem_singleton] at hW; subst W; exact hseparated)
    (by
      intro W hW
      simp only [Finset.mem_singleton] at hW
      subst W
      apply Or.inl
      intro t ht
      rw [hsupp] at ht
      rcases ht with ht | ht | ht
      · exact Or.inl (ht ▸ haB)
      · exact Or.inr ⟨((b : V),(c : V)),by simp,Or.inl (congrArg Subtype.val ht)⟩
      · exact Or.inr ⟨((b : V),(c : V)),by simp,Or.inr (congrArg Subtype.val ht)⟩)
    hhu hhB hhx hhq
    (by intro e he; simp only [List.mem_singleton] at he; subst e; exact ⟨hhb,hhc⟩)
  simpa only [ordinaryMatePuncture] using hout

end Gallai.TwoException
