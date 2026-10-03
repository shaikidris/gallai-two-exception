/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.ContactPunctureWitness

@[expose] public section

/-! # Parity of ordinary triangle preparations -/
namespace Gallai.TwoException
open scoped Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
noncomputable local instance ordinaryStarAdj (u : V) (B : Finset V) :
    DecidableRel (starPuncture G u B).Adj := fun _ _ => Classical.propDecidable _
noncomputable local instance ordinaryMateAdj (u b c : V) (B : Finset V) :
    DecidableRel ((starPuncture G u B).deleteEdges {s(b,c)}).Adj :=
  fun _ _ => Classical.propDecidable _

/-- Any even-leaf contact star followed by deletion of a disjoint even
triangle mate flips both mate vertices. Only the centre can become newly
even; no parity restriction on the total contact count is needed. -/
theorem ordinary_triangle_puncture_profile
    (u b c : V) (B : Finset V)
    (hadj : ∀ t ∈ B, G.Adj u t)
    (hleaves : ∀ t ∈ B, Even (G.degree t))
    (hbu : b ≠ u) (hcu : c ≠ u) (hbB : b ∉ B) (hcB : c ∉ B)
    (hbc : G.Adj b c) (hbEven : Even (G.degree b)) (hcEven : Even (G.degree c)) :
    (∀ t, Even (((starPuncture G u B).deleteEdges {s(b,c)}).degree t) →
      Even (G.degree t) ∨ t = u) ∧
    Odd (((starPuncture G u B).deleteEdges {s(b,c)}).degree b) ∧
    Odd (((starPuncture G u B).deleteEdges {s(b,c)}).degree c) := by
  classical
  let Q := starPuncture G u B
  let K := Q.deleteEdges {s(b,c)}
  letI : DecidableRel Q.Adj := ordinaryStarAdj u B
  letI : DecidableRel K.Adj := ordinaryMateAdj u b c B
  change (∀ t, Even (K.degree t) → Even (G.degree t) ∨ t = u) ∧
    Odd (K.degree b) ∧ Odd (K.degree c)
  have hbd : Q.degree b = G.degree b := starPuncture_degree_other (G := G) u B b hbu hbB
  have hcd : Q.degree c = G.degree c := starPuncture_degree_other (G := G) u B c hcu hcB
  have hbQ : Even (Q.degree b) := hbd ▸ hbEven
  have hcQ : Even (Q.degree c) := hcd ▸ hcEven
  have hbcQ : Q.Adj b c := by
    exact ⟨hbc, fun ha => hcu ((star_sup_adj_off_center u B b c hbu).mp ha).2⟩
  refine ⟨?_, ?_, ?_⟩
  · intro t ht
    by_cases htu : t = u
    · exact Or.inr htu
    left
    have hp := even_edge_deletion_even_preserved (G := Q) b c hbcQ hbQ hcQ t
    simp only [← SimpleGraph.ncard_neighborSet] at hp ht
    have hQt := hp ht
    dsimp only [Q] at hQt
    by_cases htB : t ∈ B
    · have hd := starPuncture_degree_leaf (G := G) u B t htB (hadj t htB)
      have he := hleaves t htB
      simp only [← SimpleGraph.ncard_neighborSet] at hd hQt he
      rw [Nat.even_iff] at hQt he
      omega
    · have hd := starPuncture_degree_other (G := G) u B t htu htB
      simp only [← SimpleGraph.ncard_neighborSet] at hd ⊢
      rwa [hd] at hQt
  · have hd := degree_delete_edge_add_one Q b c hbcQ
    dsimp only [K]
    simp only [← SimpleGraph.ncard_neighborSet] at hd hbQ ⊢
    rw [Nat.even_iff] at hbQ
    rw [Nat.odd_iff]
    omega
  · have hd := degree_delete_edge_add_one_other Q b c hbcQ
    dsimp only [K]
    simp only [← SimpleGraph.ncard_neighborSet] at hd hcQ ⊢
    rw [Nat.even_iff] at hcQ
    rw [Nat.odd_iff]
    omega

end Gallai.TwoException
