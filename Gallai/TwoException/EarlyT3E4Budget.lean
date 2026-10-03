/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.EarlyHubAuxiliaryBudget

@[expose] public section

/-! # Native two-mate auxiliary budget for the T3/E4 row -/
namespace Gallai.TwoException
open scoped Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The two-mate budget graph is exactly the E4 restoration graph with
the ordinary triangle mate kept absent. -/
theorem t3_E4_auxiliary_eq (u p q b c : V) (B : Finset V) :
    ordinaryMatePuncture (starPuncture G u B) [(p,q),(b,c)] =
      (starPuncture (G.deleteEdges {s(b,c)}) u B).deleteEdges {s(q,p)} := by
  have hsym : s(q,p) = s(p,q) := Sym2.eq_swap
  rw [hsym]
  ext v w
  simp only [ordinaryMatePuncture,SimpleGraph.deleteEdges_adj,SimpleGraph.sdiff_adj]
  tauto

/-- Delete the private mate and the ordinary triangle opposite mate after
an even star. Original odd centre parity supplies every exempt-private
reserve required by the component budget. -/
theorem bare_t3_E4_auxiliary_endpoint
    (h u : V) (x : evenVertices G) (H : BareMinimalCounterexample G h (x : V))
    (B privates : Finset V) (Z : (evenSubgraph G).ConnectedComponent)
    (a b c : evenVertices G) (hsupp : Z.supp = {a,b,c})
    (p q : V) (hpq : G.Adj p q) (hbc : G.Adj b c)
    (hpEven : Even (G.degree p)) (hqEven : Even (G.degree q))
    (hpPriv : p ∈ privates) (hqPriv : q ∈ privates)
    (hxB : (x : V) ∈ B) (haB : (a : V) ∈ B)
    (huOdd : Odd (G.degree u)) (hEvenB : Even #B)
    (hadj : ∀ t ∈ B, G.Adj u t) (hleaves : ∀ t ∈ B, Even (G.degree t))
    (havoid : ∀ e ∈ [(p,q),((b : V),(c : V))],
      e.1 ≠ u ∧ e.2 ≠ u ∧ e.1 ∉ B ∧ e.2 ∉ B)
    (hdis : p ≠ (b : V) ∧ p ≠ (c : V) ∧ q ≠ (b : V) ∧ q ≠ (c : V))
    (hcontacts : ∀ t, G.Adj u t → Even (G.degree t) →
      t ∈ B ∨ (∃ e ∈ [(p,q),((b : V),(c : V))], t = e.1 ∨ t = e.2) ∨ t = h)
    (hB : ∀ t ∈ B, t = (x : V) ∨ t ∈ privates ∨ t = (a : V))
    (hprivateCentre : u ∉ privates)
    (hprivates : ∀ t ∈ privates, G.Adj t x ∧ eDegree G t = 2)
    (hhu : h ≠ u) (hhB : h ∉ B)
    (hhp : h ≠ p) (hhq : h ≠ q) (hhb : h ≠ (b : V)) (hhc : h ≠ (c : V)) :
    ∃ D : Decomposition (ordinaryMatePuncture (starPuncture G u B)
      [(p,q),((b : V),(c : V))]),
      D.size ≤ (Fintype.card V + 1) / 2 ∧ 2 ≤ D.endpointCount h := by
  classical
  have hcentre := ordinary_star_mates_centre_odd u B
    [(p,q),((b : V),(c : V))] hadj huOdd hEvenB
    (fun e he => ⟨(havoid e he).1,(havoid e he).2.1⟩)
  apply bare_early_hub_auxiliary_endpoint_of_private_reserves h u x H B privates
    [(p,q),((b : V),(c : V))] {Z} hxB hadj hleaves
  · simpa [List.pairwise_cons] using hdis
  · exact havoid
  · intro e he
    simp only [List.mem_cons,List.not_mem_nil,or_false] at he
    rcases he with he | he
    · subst e; exact ⟨hpq,hpEven,hqEven⟩
    · subst e; exact ⟨hbc,b.property,c.property⟩
  · exact hcontacts
  · intro t ht
    rcases hB t ht with ht | ht | ht
    · exact Or.inl ht
    · exact Or.inr (Or.inl ht)
    · exact Or.inr (Or.inr ⟨Z,by simp,a,by rw [hsupp]; simp,ht.symm⟩)
  · intro e he t ht
    simp only [List.mem_cons,List.not_mem_nil,or_false] at he
    rcases he with he | he
    · subst e
      apply Or.inr
      rcases ht with ht | ht
      · exact ht ▸ hpPriv
      · exact ht ▸ hqPriv
    · subst e
      apply Or.inl
      rcases ht with ht | ht
      · exact ⟨Z,by simp,b,by rw [hsupp]; simp,ht.symm⟩
      · exact ⟨Z,by simp,c,by rw [hsupp]; simp,ht.symm⟩
  · exact ⟨p,hpPriv⟩
  · exact hprivateCentre
  · exact hprivates
  · intro t ht htu
    exact Or.inr hcentre
  · intro W hW
    simp only [Finset.mem_singleton] at hW
    subst W
    apply Or.inl
    intro t ht
    rw [hsupp] at ht
    rcases ht with ht | ht | ht
    · exact Or.inl (ht ▸ haB)
    · exact Or.inr ⟨((b : V),(c : V)),by simp,Or.inl (congrArg Subtype.val ht)⟩
    · exact Or.inr ⟨((b : V),(c : V)),by simp,Or.inr (congrArg Subtype.val ht)⟩
  · exact hhu
  · exact hhB
  · intro e he
    simp only [List.mem_cons,List.not_mem_nil,or_false] at he
    rcases he with he | he
    · subst e; exact ⟨hhp,hhq⟩
    · subst e; exact ⟨hhb,hhc⟩

end Gallai.TwoException
