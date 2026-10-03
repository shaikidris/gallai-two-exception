/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.OrdinaryTightSlots

@[expose] public section

/-! # Graph-derived guards for ordinary packet tight failures -/
namespace Gallai.TwoException
open scoped Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G J : SimpleGraph V} [DecidableRel G.Adj] [DecidableRel J.Adj]
noncomputable local instance nativeHalfAdj (J : SimpleGraph V) (u : V) (A : Finset V) :
    DecidableRel (J ⊔ A.sup (SimpleGraph.edge u)).Adj :=
  fun _ _ => Classical.propDecidable _

/-- Outside the original triangle slots, every retained neighbour of a
pending contact is odd and hence has a positive endpoint. -/
theorem ordinary_pending_outside_slots_positive
    (D : Decomposition J) (u a b c : V) (hsub : J ≤ G)
    (hprofile : ∀ t, Even (J.degree t) → Even (G.degree t) ∨ t = u)
    (heven : ∀ t, G.Adj a t → Even (G.degree t) → t = b ∨ t = c)
    (hmissing : ¬ J.Adj a u) :
    ∀ t, J.Adj a t → t ≠ b → t ≠ c → 0 < D.endpointCount t := by
  intro t hat htb htc
  apply D.endpointCount_pos_of_odd_degree
  rcases Nat.even_or_odd (J.degree t) with ht | ht
  · rcases hprofile t ht with htOriginal | htu
    · rcases heven t (hsub hat) htOriginal with h | h
      · exact False.elim (htb h)
      · exact False.elim (htc h)
    · subst t
      exact False.elim (hmissing hat)
  · exact ht

/-- A special T2 cannot leave both contacts pending. If b is unselected,
its old positive endpoint persists, forcing a's passing count below two. -/
theorem ordinary_special_contacts_selected
    (D : Decomposition J) (u a b c : V) (S A : Finset V)
    (haS : a ∈ S) (hau : a ≠ u) (hbD : 0 < D.endpointCount b)
    (hmissing : ¬ J.Adj a u)
    (E : Decomposition (J ⊔ A.sup (SimpleGraph.edge u)))
    (hsub : (J ⊔ A.sup (SimpleGraph.edge u)) ≤ G)
    (hprofile : ∀ t, Even ((J ⊔ A.sup (SimpleGraph.edge u)).degree t) →
      Even (G.degree t) ∨ t = u)
    (heven : ∀ t, G.Adj a t → Even (G.degree t) → t = b ∨ t = c)
    (hvec : ∀ t, E.endpointCount t + (if t ∈ A then 1 else 0) =
      D.endpointCount t + if u = t then #A else 0)
    (htight : ∀ w ∈ S \ A, passingNeighborCount E w = 2) :
    a ∈ A ∨ b ∈ A := by
  classical
  by_cases haA : a ∈ A
  · exact Or.inl haA
  right
  by_contra hbA
  have hbE : 0 < E.endpointCount b := by
    have hv := hvec b
    simp only [hbA, ite_false, Nat.add_zero] at hv
    split_ifs at hv <;> omega
  have hmissingE : ¬ (J ⊔ A.sup (SimpleGraph.edge u)).Adj a u := by
    intro ha
    rcases ha with hj | hs
    · exact hmissing hj
    · exact haA ((star_sup_adj_off_center u A a u hau).mp hs).1
  have hone := ordinary_regular_pending_passing_le_one E u a b c hsub hprofile
    heven hmissingE hbE
  have htwo := htight a (Finset.mem_sdiff.mpr ⟨haS, haA⟩)
  omega

end Gallai.TwoException
