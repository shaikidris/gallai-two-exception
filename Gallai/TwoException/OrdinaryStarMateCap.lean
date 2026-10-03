/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.OrdinaryStarMateProfile
public import Gallai.TwoException.OrdinaryPunctureCap

@[expose] public section

/-! # Global E-degree cap for simultaneous ordinary preparations -/
namespace Gallai.TwoException
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
noncomputable local instance combinedAdj (G : SimpleGraph V) (u : V)
    (B : Finset V) (M : List (V × V)) :
    DecidableRel (ordinaryMatePuncture (starPuncture G u B) M).Adj :=
  fun _ _ => Classical.propDecidable _

/-- Complete contact coverage leaves at most the protected vertex as an
even neighbour of the centre in the actual simultaneous puncture. -/
theorem ordinary_star_mates_centre_eDegree_le_one
    (h u : V) (B : Finset V) (M : List (V × V))
    (hadj : ∀ t ∈ B, G.Adj u t)
    (hleaves : ∀ t ∈ B, Even (G.degree t))
    (hdis : M.Pairwise (fun e f =>
      e.1 ≠ f.1 ∧ e.1 ≠ f.2 ∧ e.2 ≠ f.1 ∧ e.2 ≠ f.2))
    (havoid : ∀ e ∈ M, e.1 ≠ u ∧ e.2 ≠ u ∧ e.1 ∉ B ∧ e.2 ∉ B)
    (hedges : ∀ e ∈ M, G.Adj e.1 e.2 ∧ Even (G.degree e.1) ∧ Even (G.degree e.2))
    (hcontacts : ∀ t, G.Adj u t → Even (G.degree t) →
      t ∈ B ∨ (∃ e ∈ M, t = e.1 ∨ t = e.2) ∨ t = h) :
    eDegree (ordinaryMatePuncture (starPuncture G u B) M) u ≤ 1 := by
  classical
  let J := ordinaryMatePuncture (starPuncture G u B) M
  have hsub : J ≤ G := (ordinaryMatePuncture_le M).trans (fun _ _ ha => ha.1)
  have hp := ordinary_star_mates_even_preserved u B M hadj hleaves hdis havoid hedges
  have hl := ordinary_star_mates_leaves_odd u B M hadj hleaves
    (fun e he => ⟨(havoid e he).2.2.1,(havoid e he).2.2.2⟩)
  have hm := ordinary_star_mates_endpoints_odd u B M hdis havoid hedges
  have hsubset : evenNeighbors J u ⊆ {h} := by
    intro t ht
    obtain ⟨hut,htEven⟩ := (mem_evenNeighbors (G := J) u t).mp ht
    apply Finset.mem_singleton.mpr
    rcases hp t htEven with htOriginal | htu
    · rcases hcontacts t (hsub hut) htOriginal with htB | hmate | hth
      · exact False.elim ((Nat.not_even_iff_odd.mpr (hl t htB)) htEven)
      · obtain ⟨e,he,hte⟩ := hmate
        obtain ⟨ho1,ho2⟩ := hm e he
        rcases hte with hte | hte
        · rw [hte] at htEven
          exact False.elim ((Nat.not_even_iff_odd.mpr ho1) htEven)
        · rw [hte] at htEven
          exact False.elim ((Nat.not_even_iff_odd.mpr ho2) htEven)
      · exact hth
    · rw [htu] at hut
      exact False.elim (J.irrefl hut)
  exact (Finset.card_le_card hsubset).trans (by simp)

/-- Complete contact coverage by star leaves, mate endpoints and the bare
protected vertex yields a global cap, with no bound on the mate family size. -/
theorem bare_ordinary_star_mates_cap
    (h x : V) (H : BareMinimalCounterexample G h x)
    (u : V) (B : Finset V) (M : List (V × V)) (hxB : x ∈ B)
    (hadj : ∀ t ∈ B, G.Adj u t)
    (hleaves : ∀ t ∈ B, Even (G.degree t))
    (hdis : M.Pairwise (fun e f =>
      e.1 ≠ f.1 ∧ e.1 ≠ f.2 ∧ e.2 ≠ f.1 ∧ e.2 ≠ f.2))
    (havoid : ∀ e ∈ M, e.1 ≠ u ∧ e.2 ≠ u ∧ e.1 ∉ B ∧ e.2 ∉ B)
    (hedges : ∀ e ∈ M, G.Adj e.1 e.2 ∧ Even (G.degree e.1) ∧ Even (G.degree e.2))
    (hcontacts : ∀ t, G.Adj u t → Even (G.degree t) →
      t ∈ B ∨ (∃ e ∈ M, t = e.1 ∨ t = e.2) ∨ t = h) :
    ∀ t, Even ((ordinaryMatePuncture (starPuncture G u B) M).degree t) →
      eDegree (ordinaryMatePuncture (starPuncture G u B) M) t ≤ 3 := by
  classical
  let J := ordinaryMatePuncture (starPuncture G u B) M
  have hsubM : ∀ L : List (V × V), ordinaryMatePuncture (starPuncture G u B) L ≤ G := by
    intro L
    induction L with
    | nil => exact fun _ _ ha => ha.1
    | cons e L ih => exact fun _ _ ha => ih ha.1
  have hsub : J ≤ G := hsubM M
  have hp := ordinary_star_mates_even_preserved u B M hadj hleaves hdis havoid hedges
  have hl := ordinary_star_mates_leaves_odd u B M hadj hleaves
    (fun e he => ⟨(havoid e he).2.2.1, (havoid e he).2.2.2⟩)
  have hm := ordinary_star_mates_endpoints_odd u B M hdis havoid hedges
  have hxOdd : Odd (J.degree x) := hl x hxB
  have hcentre : ∀ t, J.Adj u t → Even (J.degree t) → t = h := by
    intro t hut ht
    rcases hp t ht with htOriginal | htu
    · rcases hcontacts t (hsub hut) htOriginal with htB | hmate | hth
      · have ho := hl t htB
        dsimp only [J] at ht
        rw [Nat.even_iff] at ht
        rw [Nat.odd_iff] at ho
        omega
      · obtain ⟨e, he, hte⟩ := hmate
        obtain ⟨hpOdd, hqOdd⟩ := hm e he
        dsimp only [J] at ht
        rcases hte with rfl | rfl <;>
          simp only [← SimpleGraph.ncard_neighborSet] at ht hpOdd hqOdd <;>
          rw [Nat.even_iff] at ht <;>
          rw [Nat.odd_iff] at hpOdd hqOdd <;> omega
      · exact hth
    · subst t
      exact False.elim (J.irrefl hut)
  rcases H.counterexample.1 with ⟨_, _, _, _, _, hhzero, hcap⟩
  have hc : ∀ t, Even (G.degree t) → t ≠ x → eDegree G t ≤ 3 := by
    intro t ht htx
    by_cases hth : t = h
    · subst t
      omega
    · exact hcap t ht hth htx
  exact puncture_cap_of_one_new_even_center h x u hsub hp hxOdd hhzero hc hcentre

end Gallai.TwoException
