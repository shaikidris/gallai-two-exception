/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.BareLongPreparationCap

@[expose] public section

/-! # Original parity in the joint two-star corridor puncture -/
namespace Gallai.TwoException
open scoped Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
noncomputable local instance jointProfileAdj (Q : SimpleGraph V) : DecidableRel Q.Adj :=
  fun _ _ => Classical.propDecidable _

/-- Ordinary star/mate preparation does not affect any originally odd
vertex other than its centre. No parity of that centre is assumed here. -/
theorem long_preparation_original_odd_unchanged
    (v w : V) (B : Finset V) (O : List (V × V))
    (hwOdd : Odd (G.degree w)) (hwv : w ≠ v)
    (hB : ∀ t ∈ B, Even (G.degree t))
    (hO : ∀ e ∈ O, Even (G.degree e.1) ∧ Even (G.degree e.2)) :
    (ordinaryMatePuncture (starPuncture G v B) O).degree w = G.degree w ∧
      ∀ t, (ordinaryMatePuncture (starPuncture G v B) O).Adj w t ↔ G.Adj w t := by
  classical
  have hn := Nat.not_even_iff_odd.mpr hwOdd
  apply long_ordinary_preparation_unchanged (G := G) v w B O hwv
  · exact fun ht => hn (hB w ht)
  · intro e he
    exact ⟨fun hh => hn (hh ▸ (hO e he).1),
      fun hh => hn (hh ▸ (hO e he).2)⟩

/-- All five windmill rows have this joint parity interface: an odd
windmill contact star, the reserved odd edge, and even-ended additional
deletions. Only v can become newly even relative to the original graph;
u stays odd and v loses exactly the reserved edge after its preparation. -/
theorem long_joint_original_parity_profile
    (u v : V) (B S : Finset V) (O N : List (V × V))
    (huOdd : Odd (G.degree u)) (hvOdd : Odd (G.degree v)) (huv : G.Adj u v)
    (hB : ∀ t ∈ B, Even (G.degree t))
    (hO : ∀ e ∈ O, Even (G.degree e.1) ∧ Even (G.degree e.2))
    (hS : ∀ t ∈ S, G.Adj u t ∧ Even (G.degree t)) (hSodd : Odd #S)
    (hN : ∀ e ∈ N, Even (G.degree e.1) ∧ Even (G.degree e.2)) :
    let Q := ordinaryMatePuncture (starPuncture G v B) O
    let J := ordinaryMatePuncture (starPuncture Q u (insert v S)) N
    (∀ t, Even (J.degree t) → Even (G.degree t) ∨ t = v) ∧
      Odd (J.degree u) ∧ J.degree v + 1 = Q.degree v := by
  classical
  let Q := ordinaryMatePuncture (starPuncture G v B) O
  let R := starPuncture Q u (insert v S)
  let J := ordinaryMatePuncture R N
  have hdu : Q.degree u = G.degree u := by
    exact (long_preparation_original_odd_unchanged v u B O huOdd huv.ne hB hO).1
  have hau : ∀ t, Q.Adj u t ↔ G.Adj u t :=
    (long_preparation_original_odd_unchanged v u B O huOdd huv.ne hB hO).2
  have huS : u ∉ S := fun ht => (Nat.not_even_iff_odd.mpr huOdd) (hS u ht).2
  have hvS : v ∉ S := fun ht => (Nat.not_even_iff_odd.mpr hvOdd) (hS v ht).2
  have huI : u ∉ insert v S := by simp [huv.ne,huS]
  have hadj : ∀ t ∈ insert v S, Q.Adj u t := by
    intro t ht
    rcases Finset.mem_insert.mp ht with htv | htS
    · subst t
      exact (hau v).mpr huv
    · exact (hau t).mpr (hS t htS).1
  have huN : ∀ e ∈ N, u ≠ e.1 ∧ u ≠ e.2 := by
    intro e he
    have hn := Nat.not_even_iff_odd.mpr huOdd
    exact ⟨fun hh => hn (hh ▸ (hN e he).1),fun hh => hn (hh ▸ (hN e he).2)⟩
  have hvN : ∀ e ∈ N, v ≠ e.1 ∧ v ≠ e.2 := by
    intro e he
    have hn := Nat.not_even_iff_odd.mpr hvOdd
    exact ⟨fun hh => hn (hh ▸ (hN e he).1),fun hh => hn (hh ▸ (hN e he).2)⟩
  have hcentre := starPuncture_degree_center (G := Q) u (insert v S) huI
    (fun t ht => (Q.mem_neighborFinset u t).mpr (hadj t ht))
  have hmateU := ordinaryMatePuncture_degree_of_avoids (G := R) N u huN
  have huJ : Odd (J.degree u) := by
    simp only [← SimpleGraph.ncard_neighborSet] at hdu hcentre hmateU huOdd ⊢
    rw [Finset.card_insert_of_notMem hvS] at hcentre
    rw [Nat.odd_iff] at huOdd hSodd ⊢
    dsimp only [Q,R,J] at hdu hcentre hmateU ⊢
    omega
  refine ⟨?_,huJ,?_⟩
  · intro t ht
    by_cases he : Even (G.degree t)
    · exact Or.inl he
    by_cases htv : t = v
    · exact Or.inr htv
    have htOdd := Nat.not_even_iff_odd.mp he
    by_cases htu : t = u
    · subst t
      exact False.elim ((Nat.not_even_iff_odd.mpr huJ) ht)
    have htS : t ∉ insert v S := by
      simp only [Finset.mem_insert]
      exact not_or.mpr ⟨htv,fun hh => he (hS t hh).2⟩
    have hQt := (long_preparation_original_odd_unchanged v t B O htOdd htv hB hO).1
    have hRt := starPuncture_degree_other (G := Q) u (insert v S) t htu htS
    have hJt := ordinaryMatePuncture_degree_of_avoids (G := R) N t (by
      intro e heN
      exact ⟨fun hh => he (hh ▸ (hN e heN).1),fun hh => he (hh ▸ (hN e heN).2)⟩)
    simp only [← SimpleGraph.ncard_neighborSet] at hQt hRt hJt ht he
    dsimp only [Q,R,J] at hQt hRt hJt ht
    exact False.elim (he (by rwa [hJt,hRt,hQt] at ht))
  · have hleaf := starPuncture_degree_leaf (G := Q) u (insert v S) v
      (Finset.mem_insert_self _ _) ((hau v).mpr huv)
    have hmateV := ordinaryMatePuncture_degree_of_avoids (G := R) N v hvN
    simp only [← SimpleGraph.ncard_neighborSet] at hleaf hmateV ⊢
    dsimp only [Q,R,J] at hleaf hmateV ⊢
    omega

end Gallai.TwoException
