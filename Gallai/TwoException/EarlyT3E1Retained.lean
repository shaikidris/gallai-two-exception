/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.EarlyT3E4Retained

@[expose] public section

/-! # Original retained-neighbour classification for the T3/E1 row -/
namespace Gallai.TwoException
open scoped Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
noncomputable local instance t3E1RetainedGraph (Q : SimpleGraph V) :
    DecidableRel Q.Adj := fun _ _ => Classical.propDecidable _

/-- The unpaid mate is not a centre neighbour, so the two-mate parity
guard specializes to all retained centre neighbours in the E1 row. -/
theorem t3_E1_retained_guard
    (a b c : evenVertices G) (hbc : G.Adj b c)
    (u x q h : V) (S : Finset V)
    (hab : (a : V) ≠ (b : V)) (hac : (a : V) ≠ (c : V))
    (hau : (a : V) ≠ u) (hua : G.Adj u a)
    (haq : (a : V) ≠ q) (hax : (a : V) ≠ x)
    (hbu : (b : V) ≠ u) (hcu : (c : V) ≠ u)
    (huq : ¬ G.Adj u q)
    (hcontacts : ∀ t, G.Adj u t → Even (G.degree t) →
      t ∈ S ∨ t = (a : V) ∨ t = (b : V) ∨ t = (c : V) ∨ t = h)
    (D : Decomposition ((starPuncture (G.deleteEdges {s((b : V),(c : V))}) u
      (insert (a : V) S)).deleteEdges {s(x,q)}))
    (hh : 2 ≤ D.endpointCount h) :
    ∀ t, (G.deleteEdges {s((b : V),(c : V))}).Adj u t → t ∉ S →
      Odd ((G.deleteEdges {s((b : V),(c : V))}).degree t) ∨
      0 < D.endpointCount t := by
  have hr := t3_E4_retained_guard a b c hbc u q x h S hab hac hau hua haq hax
    hbu hcu (by
      intro t ht he
      rcases hcontacts t ht he with ht | ht | ht | ht | ht
      · exact Or.inl ht
      · exact Or.inr (Or.inl ht)
      · exact Or.inr (Or.inr (Or.inr (Or.inl ht)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ht))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ht))))) D hh
  intro t ht htS
  exact hr t ht htS (fun he => huq (he ▸ ht.1))

end Gallai.TwoException
