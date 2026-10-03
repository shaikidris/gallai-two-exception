/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.OrdinarySequentialRestoration

@[expose] public section

/-! # Regular ordinary packets cannot remain pending in a tight failure -/
namespace Gallai.TwoException
open scoped Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G J : SimpleGraph V} [DecidableRel G.Adj] [DecidableRel J.Adj]

/-- After mate restoration, a pending regular contact leaf has at most
one passing neighbour: the recipient is positive, the centre edge is still
absent, and only the other triangle vertex can be passing. -/
theorem ordinary_regular_pending_passing_le_one
    (D : Decomposition J) (u a b c : V) (hsub : J ≤ G)
    (hprofile : ∀ t, Even (J.degree t) → Even (G.degree t) ∨ t = u)
    (heven : ∀ t, G.Adj a t → Even (G.degree t) → t = b ∨ t = c)
    (hmissing : ¬ J.Adj a u) (hb : 0 < D.endpointCount b) :
    passingNeighborCount D a ≤ 1 := by
  classical
  have hs : {t ∈ J.neighborFinset a | D.endpointCount t = 0} ⊆ {c} := by
    intro t ht
    obtain ⟨htAdj, htZero⟩ := Finset.mem_filter.mp ht
    have hat : J.Adj a t := (J.mem_neighborFinset a t).mp htAdj
    have htEven : Even (J.degree t) := by
      rcases Nat.even_or_odd (J.degree t) with he | ho
      · exact he
      · have hp := D.endpointCount_pos_of_odd_degree t ho
        omega
    rcases hprofile t htEven with htOriginal | htu
    · rcases heven t (hsub hat) htOriginal with htb | htc
      · subst t
        omega
      · exact Finset.mem_singleton.mpr htc
    · subst t
      exact False.elim (hmissing hat)
  exact (Finset.card_le_card hs).trans (by simp)

/-- Consequently a regular packet's contact must be selected whenever
every pending leaf has the tight two-passing-neighbour failure profile. -/
theorem ordinary_regular_contact_selected
    (D : Decomposition J) (u a b c : V) (S A : Finset V) (ha : a ∈ S)
    (hsub : J ≤ G)
    (hprofile : ∀ t, Even (J.degree t) → Even (G.degree t) ∨ t = u)
    (heven : ∀ t, G.Adj a t → Even (G.degree t) → t = b ∨ t = c)
    (hmissing : ¬ J.Adj a u) (hb : 0 < D.endpointCount b)
    (htight : ∀ w ∈ S \ A, passingNeighborCount D w = 2) : a ∈ A := by
  by_contra hn
  have htwo := htight a (Finset.mem_sdiff.mpr ⟨ha, hn⟩)
  have hone := ordinary_regular_pending_passing_le_one D u a b c hsub hprofile
    heven hmissing hb
  omega

/-- A restored mate recipient cannot become passing under the half-star:
even if selected, it loses only one of its at least two endpoints. -/
theorem ordinary_recipient_positive_after_half_star
    (D : Decomposition J) (u b : V) (A : Finset V)
    (E : Decomposition (J ⊔ A.sup (SimpleGraph.edge u)))
    (hb : 2 ≤ D.endpointCount b)
    (hvec : ∀ t, E.endpointCount t + (if t ∈ A then 1 else 0) =
      D.endpointCount t + if u = t then #A else 0) :
    0 < E.endpointCount b := by
  have he := hvec b
  split_ifs at he <;> omega

end Gallai.TwoException
