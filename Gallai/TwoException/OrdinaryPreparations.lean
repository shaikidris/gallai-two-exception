/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.ContactHalfStar

@[expose] public section

/-! # Ordinary triangle preparation before the contact star

Restoring a deleted triangle mate does not require endpoints at the contact
centre. Both flipped mate vertices are odd; positivity at the recipient's
retained neighbours makes the mate restoration free.
-/
namespace Gallai.TwoException
open scoped Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Restore the mate in a T1 or regular T2 preparation before paying the
contact star. The recipient gains a second endpoint; the donor may become
passing. Endpoint counts outside the mate pair are unchanged. -/
theorem restore_ordinary_triangle_mate
    (D : Decomposition G) (b c : V) (hbc : b ≠ c)
    (hmissing : ¬ G.Adj b c)
    (hbOdd : Odd (G.degree b)) (hcOdd : Odd (G.degree c))
    (hpositive : ∀ t, G.Adj b t → 0 < D.endpointCount t) :
    ∃ E : Decomposition (G ⊔ SimpleGraph.edge b c), E.size = D.size ∧
      2 ≤ E.endpointCount b ∧
      ∀ t, E.endpointCount t + (if c = t then 1 else 0) =
        D.endpointCount t + if b = t then 1 else 0 := by
  classical
  have hzero : {t ∈ G.neighborFinset b | D.endpointCount t = 0} = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro t ht
    obtain ⟨ht, hz⟩ := Finset.mem_filter.mp ht
    have hp := hpositive t ((G.mem_neighborFinset b t).mp ht)
    omega
  have hstrict : #{t ∈ G.neighborFinset b | D.endpointCount t = 0} <
      D.endpointCount c := by
    rw [hzero, Finset.card_empty]
    exact D.endpointCount_pos_of_odd_degree c hcOdd
  obtain ⟨E, hs, hv⟩ := D.single_edge_addibility b c hbc hmissing hstrict
  refine ⟨E, hs, ?_, hv⟩
  have hp := D.endpointCount_pos_of_odd_degree b hbOdd
  have he := hv b
  simp only [Ne.symm hbc, ite_false, Nat.add_zero, ite_true] at he
  omega

/-- Derive the retained-neighbour positivity required by mate restoration
from a triangle's original even neighbourhood and the puncture parity
profile. In T1 the centre is not a neighbour; in regular T2 it is positive. -/
theorem restore_ordinary_triangle_mate_of_profile
    {J : SimpleGraph V} [DecidableRel J.Adj]
    (D : Decomposition J) (u a b c : V) (hsub : J ≤ G)
    (hbc : b ≠ c) (hmissing : ¬ J.Adj b c)
    (hbOdd : Odd (J.degree b)) (hcOdd : Odd (J.degree c))
    (haOdd : Odd (J.degree a))
    (heven : ∀ t, G.Adj b t → Even (G.degree t) → t = a ∨ t = c)
    (hprofile : ∀ t, Even (J.degree t) → Even (G.degree t) ∨ t = u)
    (hcentre : ¬ J.Adj b u ∨ 0 < D.endpointCount u) :
    ∃ E : Decomposition (J ⊔ SimpleGraph.edge b c), E.size = D.size ∧
      2 ≤ E.endpointCount b ∧
      ∀ t, E.endpointCount t + (if c = t then 1 else 0) =
        D.endpointCount t + if b = t then 1 else 0 := by
  apply restore_ordinary_triangle_mate D b c hbc hmissing hbOdd hcOdd
  intro t hbt
  by_cases htOdd : Odd (J.degree t)
  · exact D.endpointCount_pos_of_odd_degree t htOdd
  have htEven : Even (J.degree t) := (Nat.even_or_odd (J.degree t)).resolve_right htOdd
  rcases hprofile t htEven with htOriginal | htu
  · rcases heven t (hsub hbt) htOriginal with hta | htc
    · subst t
      exact D.endpointCount_pos_of_odd_degree a haOdd
    · subst t
      exact False.elim (hmissing hbt)
  · subst t
    rcases hcentre with hn | hp
    · exact False.elim (hn hbt)
    · exact hp

end Gallai.TwoException
