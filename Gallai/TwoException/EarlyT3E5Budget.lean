/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.EarlyOddCentreSpokeBudget

@[expose] public section

/-! # Native spoke-and-two-mate budget for singleton T3/E5 -/
namespace Gallai.TwoException
open scoped Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
noncomputable local instance t3E5BudgetGraph (Q : SimpleGraph V) :
    DecidableRel Q.Adj := fun _ _ => Classical.propDecidable _

/-- The two-mate budget has exactly E5's restoration graph with the
opposite ordinary mate still absent. -/
theorem t3_E5_auxiliary_eq (u x s p q b c : V) (B : Finset V) :
    ordinaryMatePuncture ((starPuncture G u B).deleteEdges {s(x,s)})
      [(p,q),(b,c)] =
      ((starPuncture (G.deleteEdges {s(b,c)}) u B).deleteEdges {s(x,s)}).deleteEdges
        {s(q,p)} := by
  have hsym : s(q,p) = s(p,q) := Sym2.eq_swap
  rw [hsym]
  ext v w
  simp only [ordinaryMatePuncture,SimpleGraph.deleteEdges_adj,SimpleGraph.sdiff_adj]
  tauto

/-- The singleton ordinary triangle and two private petals supply the
protected budget on the actual E5 auxiliary. No component floors are inputs. -/
theorem bare_t3_E5_auxiliary_endpoint
    (h u : V) (x : evenVertices G) (H : BareMinimalCounterexample G h (x : V))
    (B privates : Finset V) (Z : (evenSubgraph G).ConnectedComponent)
    (a b c : evenVertices G) (hsupp : Z.supp = {a,b,c}) (hxZ : x ∉ Z.supp)
    (r s p q : V) (hrB : r ∈ B) (hsB : s ∉ B) (hxB : (x : V) ∉ B)
    (hsu : s ≠ u) (hsEven : Even (G.degree s))
    (hxu : (x : V) ≠ u) (hrx : r ≠ (x : V)) (hrs : r ≠ s)
    (hxs : G.Adj x s) (hxr : G.Adj x r) (hrsAdj : G.Adj r s)
    (hrdegree : eDegree G r = 2)
    (hpair : ∀ t, G.Adj s t → Even (G.degree t) → t = (x : V) ∨ t = r)
    (hpq : G.Adj p q) (hpEven : Even (G.degree p)) (hqEven : Even (G.degree q))
    (hpPriv : p ∈ privates) (hqPriv : q ∈ privates)
    (haB : (a : V) ∈ B) (hbc : G.Adj b c)
    (huOdd : Odd (G.degree u)) (hEvenB : Even #B)
    (hadj : ∀ t ∈ B, G.Adj u t) (hleaves : ∀ t ∈ B, Even (G.degree t))
    (havoid : ∀ e ∈ [(p,q),((b : V),(c : V))],
      e.1 ≠ u ∧ e.2 ≠ u ∧ e.1 ∉ B ∧ e.2 ∉ B ∧
      e.1 ≠ (x : V) ∧ e.2 ≠ (x : V) ∧ e.1 ≠ s ∧ e.2 ≠ s)
    (hdis : p ≠ (b : V) ∧ p ≠ (c : V) ∧ q ≠ (b : V) ∧ q ≠ (c : V))
    (hcontacts : ∀ t, G.Adj u t → Even (G.degree t) →
      t ∈ B ∨ (∃ e ∈ [(p,q),((b : V),(c : V))], t = e.1 ∨ t = e.2) ∨
      t = (x : V) ∨ t = h)
    (hB : ∀ t ∈ B, t ∈ privates ∨ t = (a : V))
    (hprivates : ∀ t ∈ privates, G.Adj t x ∧ eDegree G t = 2)
    (hhu : h ≠ u) (hhB : h ∉ B) (hhx : h ≠ (x : V)) (hhs : h ≠ s)
    (hhp : h ≠ p) (hhq : h ≠ q) (hhb : h ≠ (b : V)) (hhc : h ≠ (c : V)) :
    ∃ D : Decomposition (ordinaryMatePuncture
      ((starPuncture G u B).deleteEdges {s((x : V),s)}) [(p,q),((b : V),(c : V))]),
      D.size ≤ (Fintype.card V + 1) / 2 ∧ 2 ≤ D.endpointCount h := by
  classical
  apply bare_early_odd_centre_spoke_auxiliary_endpoint h u x r s H B privates
    [(p,q),((b : V),(c : V))] {Z} hadj hleaves hrB hsB hxB hsu hsEven
    hxu hrx hrs hxs hxr hrsAdj hrdegree hpair
  · simpa [List.pairwise_cons] using hdis
  · exact havoid
  · intro e he
    simp only [List.mem_cons,List.not_mem_nil,or_false] at he
    rcases he with he | he
    · subst e; exact ⟨hpq,hpEven,hqEven⟩
    · subst e; exact ⟨hbc,b.property,c.property⟩
  · exact hcontacts
  · intro t ht
    rcases hB t ht with ht | ht
    · exact Or.inl ht
    · exact Or.inr ⟨Z,by simp,a,by rw [hsupp]; simp,ht.symm⟩
  · intro e he t ht
    simp only [List.mem_cons,List.not_mem_nil,or_false] at he
    rcases he with he | he
    · subst e
      apply Or.inl
      rcases ht with ht | ht
      · exact ht ▸ hpPriv
      · exact ht ▸ hqPriv
    · subst e
      apply Or.inr
      rcases ht with ht | ht
      · exact ⟨Z,by simp,b,by rw [hsupp]; simp,ht.symm⟩
      · exact ⟨Z,by simp,c,by rw [hsupp]; simp,ht.symm⟩
  · exact hprivates
  · exact huOdd
  · exact hEvenB
  · intro W hW
    simp only [Finset.mem_singleton] at hW
    subst W
    intro t ht
    constructor
    · intro he
      exact hxZ (Subtype.val_injective he ▸ ht)
    · intro he
      have hts : t = (⟨s,hsEven⟩ : evenVertices G) := Subtype.val_injective he
      have hsx : (evenSubgraph G).Adj (⟨s,hsEven⟩ : evenVertices G) x := hxs.symm
      exact hxZ (Z.mem_supp_of_adj_mem_supp (hts ▸ ht) hsx)
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
  · exact hhx
  · exact hhs
  · intro e he
    simp only [List.mem_cons,List.not_mem_nil,or_false] at he
    rcases he with he | he
    · subst e; exact ⟨hhp,hhq⟩
    · subst e; exact ⟨hhb,hhc⟩

end Gallai.TwoException
