/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.EarlyHubAuxiliaryBudget

@[expose] public section

/-! # Actual auxiliary ceiling for the hub-contact T3 puncture -/
namespace Gallai.TwoException
open scoped Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
noncomputable local instance t3HubBudgetComponents :
    DecidableEq (evenSubgraph G).ConnectedComponent := Classical.decEq _
noncomputable local instance t3HubBudgetAux (u b c : V) (B : Finset V) :
    DecidableRel ((starPuncture G u B).deleteEdges {s(b,c)}).Adj :=
  fun _ _ => Classical.propDecidable _

/-- The hub-contact T3 auxiliary has a native ceiling and prescribed reserve.
Only original star, windmill and triangle labels are inputs. -/
theorem bare_t3_hub_auxiliary_endpoint
    (h u : V) (x : evenVertices G) (H : BareMinimalCounterexample G h (x : V))
    (B privates : Finset V) (Z : (evenSubgraph G).ConnectedComponent)
    (a b c : evenVertices G) (hsupp : Z.supp = {a,b,c}) (hbc : G.Adj b c)
    (hxB : (x : V) ∈ B) (haB : (a : V) ∈ B)
    (hbB : (b : V) ∉ B) (hcB : (c : V) ∉ B)
    (hbu : (b : V) ≠ u) (hcu : (c : V) ≠ u)
    (hadj : ∀ t ∈ B, G.Adj u t) (hleaves : ∀ t ∈ B, Even (G.degree t))
    (hcontacts : ∀ t, G.Adj u t → Even (G.degree t) →
      t ∈ B ∨ t = (b : V) ∨ t = (c : V) ∨ t = h)
    (hB : ∀ t ∈ B, t = (x : V) ∨ t ∈ privates ∨ t = (a : V))
    (hprivateNonempty : privates.Nonempty) (hprivateCentre : u ∉ privates)
    (hprivates : ∀ t ∈ privates, G.Adj t x ∧ eDegree G t = 2)
    (hprivateContacts : ∀ t ∈ privates, G.Adj t u → t ∈ B)
    (hhu : h ≠ u) (hhB : h ∉ B) (hhb : h ≠ (b : V)) (hhc : h ≠ (c : V)) :
    ∃ D : Decomposition ((starPuncture G u B).deleteEdges {s((b : V),(c : V))}),
      D.size ≤ (Fintype.card V + 1) / 2 ∧ 2 ≤ D.endpointCount h := by
  classical
  have hout := bare_early_hub_auxiliary_endpoint h u x H B privates
    [((b : V),(c : V))] {Z} hxB hadj hleaves (by simp)
    (by intro e he; simp only [List.mem_singleton] at he; subst e; exact ⟨hbu,hcu,hbB,hcB⟩)
    (by intro e he; simp only [List.mem_singleton] at he; subst e; exact ⟨hbc,b.property,c.property⟩)
    (by
      intro t ht he
      rcases hcontacts t ht he with ht | ht | ht | ht
      · exact Or.inl ht
      · exact Or.inr (Or.inl ⟨((b : V),(c : V)),by simp,Or.inl ht⟩)
      · exact Or.inr (Or.inl ⟨((b : V),(c : V)),by simp,Or.inr ht⟩)
      · exact Or.inr (Or.inr ht))
    (by
      intro t ht
      rcases hB t ht with ht | ht | ht
      · exact Or.inl ht
      · exact Or.inr (Or.inl ht)
      · exact Or.inr (Or.inr ⟨Z,by simp,a,by rw [hsupp]; simp,ht.symm⟩))
    (by
      intro e he t ht
      simp only [List.mem_singleton] at he
      subst e
      rcases ht with ht | ht
      · exact ⟨Z,by simp,b,by rw [hsupp]; simp,ht.symm⟩
      · exact ⟨Z,by simp,c,by rw [hsupp]; simp,ht.symm⟩)
    hprivateNonempty hprivateCentre hprivates hprivateContacts
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
    hhu hhB
    (by intro e he; simp only [List.mem_singleton] at he; subst e; exact ⟨hhb,hhc⟩)
  simpa only [ordinaryMatePuncture] using hout

end Gallai.TwoException
