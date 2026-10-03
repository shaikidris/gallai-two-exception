/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.OrdinaryMateProfile

@[expose] public section

/-! # Contact-star parity after simultaneous ordinary mate preparations -/
namespace Gallai.TwoException
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
noncomputable local instance starMateAdj (G : SimpleGraph V) (u : V)
    (B : Finset V) (M : List (V × V)) :
    DecidableRel (ordinaryMatePuncture (starPuncture G u B) M).Adj :=
  fun _ _ => Classical.propDecidable _
noncomputable local instance starAdj (G : SimpleGraph V) (u : V) (B : Finset V) :
    DecidableRel (starPuncture G u B).Adj := fun _ _ => Classical.propDecidable _

/-- After an even-leaf contact star and disjoint ordinary mate deletions,
only the contact centre can be newly even. The mate guards are stated in
the original graph, not assumed at each intermediate puncture. -/
theorem ordinary_star_mates_even_preserved
    (u : V) (B : Finset V) (M : List (V × V))
    (hadj : ∀ t ∈ B, G.Adj u t)
    (hleaves : ∀ t ∈ B, Even (G.degree t))
    (hdis : M.Pairwise (fun e f =>
      e.1 ≠ f.1 ∧ e.1 ≠ f.2 ∧ e.2 ≠ f.1 ∧ e.2 ≠ f.2))
    (havoid : ∀ e ∈ M, e.1 ≠ u ∧ e.2 ≠ u ∧ e.1 ∉ B ∧ e.2 ∉ B)
    (hedges : ∀ e ∈ M, G.Adj e.1 e.2 ∧ Even (G.degree e.1) ∧ Even (G.degree e.2)) :
    ∀ t, Even ((ordinaryMatePuncture (starPuncture G u B) M).degree t) →
      Even (G.degree t) ∨ t = u := by
  classical
  have hm : ∀ e ∈ M, (starPuncture G u B).Adj e.1 e.2 ∧
      Even ((starPuncture G u B).degree e.1) ∧
      Even ((starPuncture G u B).degree e.2) := by
    intro e he
    obtain ⟨hpu, hqu, hpB, hqB⟩ := havoid e he
    obtain ⟨hpq, hp, hq⟩ := hedges e he
    refine ⟨⟨hpq, ?_⟩, ?_, ?_⟩
    · intro ha
      exact hqu ((star_sup_adj_off_center u B e.1 e.2 hpu).mp ha).2
    · have hd := starPuncture_degree_other (G := G) u B e.1 hpu hpB
      simp only [← SimpleGraph.ncard_neighborSet] at hd hp ⊢
      rwa [hd]
    · have hd := starPuncture_degree_other (G := G) u B e.2 hqu hqB
      simp only [← SimpleGraph.ncard_neighborSet] at hd hq ⊢
      rwa [hd]
  intro t ht
  have hQt := ordinaryMatePuncture_even_preserved
    (G := starPuncture G u B) M hdis hm t ht
  by_cases htu : t = u
  · exact Or.inr htu
  left
  by_cases htB : t ∈ B
  · have hd := starPuncture_degree_leaf (G := G) u B t htB (hadj t htB)
    have he := hleaves t htB
    simp only [← SimpleGraph.ncard_neighborSet] at hd hQt he
    rw [Nat.even_iff] at hQt he
    omega
  · have hd := starPuncture_degree_other (G := G) u B t htu htB
    simp only [← SimpleGraph.ncard_neighborSet] at hd hQt ⊢
    rwa [hd] at hQt

/-- Every star leaf stays odd when subsequent mate deletions avoid it. -/
theorem ordinary_star_mates_leaves_odd
    (u : V) (B : Finset V) (M : List (V × V))
    (hadj : ∀ t ∈ B, G.Adj u t)
    (hleaves : ∀ t ∈ B, Even (G.degree t))
    (havoid : ∀ e ∈ M, e.1 ∉ B ∧ e.2 ∉ B) :
    ∀ t ∈ B, Odd ((ordinaryMatePuncture (starPuncture G u B) M).degree t) := by
  classical
  intro t ht
  have ha : ∀ e ∈ M, t ≠ e.1 ∧ t ≠ e.2 := by
    intro e he
    obtain ⟨hp, hq⟩ := havoid e he
    exact ⟨fun h => hp (h ▸ ht), fun h => hq (h ▸ ht)⟩
  have hd := ordinaryMatePuncture_degree_of_avoids
    (G := starPuncture G u B) M t ha
  have hs := starPuncture_degree_leaf (G := G) u B t ht (hadj t ht)
  have he := hleaves t ht
  simp only [← SimpleGraph.ncard_neighborSet] at hd hs he ⊢
  rw [hd, Nat.odd_iff]
  rw [Nat.even_iff] at he
  omega

/-- Every ordinary mate endpoint is odd in the combined puncture. -/
theorem ordinary_star_mates_endpoints_odd
    (u : V) (B : Finset V) (M : List (V × V))
    (hdis : M.Pairwise (fun e f =>
      e.1 ≠ f.1 ∧ e.1 ≠ f.2 ∧ e.2 ≠ f.1 ∧ e.2 ≠ f.2))
    (havoid : ∀ e ∈ M, e.1 ≠ u ∧ e.2 ≠ u ∧ e.1 ∉ B ∧ e.2 ∉ B)
    (hedges : ∀ e ∈ M, G.Adj e.1 e.2 ∧ Even (G.degree e.1) ∧ Even (G.degree e.2)) :
    ∀ e ∈ M,
      Odd ((ordinaryMatePuncture (starPuncture G u B) M).degree e.1) ∧
      Odd ((ordinaryMatePuncture (starPuncture G u B) M).degree e.2) := by
  classical
  apply ordinaryMatePuncture_endpoints_odd M hdis
  intro e he
  obtain ⟨hpu, hqu, hpB, hqB⟩ := havoid e he
  obtain ⟨hpq, hp, hq⟩ := hedges e he
  refine ⟨⟨hpq, ?_⟩, ?_, ?_⟩
  · intro ha
    exact hqu ((star_sup_adj_off_center u B e.1 e.2 hpu).mp ha).2
  · have hd := starPuncture_degree_other (G := G) u B e.1 hpu hpB
    simp only [← SimpleGraph.ncard_neighborSet] at hd hp ⊢
    rwa [hd]
  · have hd := starPuncture_degree_other (G := G) u B e.2 hqu hqB
    simp only [← SimpleGraph.ncard_neighborSet] at hd hq ⊢
    rwa [hd]

/-- An even-sized star preserves odd centre parity under mate deletions
that avoid the centre. -/
theorem ordinary_star_mates_centre_odd
    (u : V) (B : Finset V) (M : List (V × V))
    (hadj : ∀ t ∈ B, G.Adj u t) (huOdd : Odd (G.degree u))
    (hB : Even B.card)
    (havoid : ∀ e ∈ M, e.1 ≠ u ∧ e.2 ≠ u) :
    Odd ((ordinaryMatePuncture (starPuncture G u B) M).degree u) := by
  classical
  have huB : u ∉ B := fun hu => G.irrefl (hadj u hu)
  have hb : B ⊆ G.neighborFinset u := by
    intro t ht
    exact (G.mem_neighborFinset u t).mpr (hadj t ht)
  have hs := starPuncture_degree_center (G := G) u B huB hb
  have hm := ordinaryMatePuncture_degree_of_avoids
    (G := starPuncture G u B) M u
    (fun e he => ⟨(havoid e he).1.symm, (havoid e he).2.symm⟩)
  simp only [← SimpleGraph.ncard_neighborSet] at hs hm huOdd ⊢
  rw [hm, Nat.odd_iff]
  rw [Nat.odd_iff] at huOdd
  rw [Nat.even_iff] at hB
  omega

/-- An even-sized deletion star at an originally odd centre supplies the
positive endpoint reserve used by every regular T2 mate restoration. -/
theorem ordinary_star_mates_centre_reserve
    (u : V) (B : Finset V) (M : List (V × V))
    (hadj : ∀ t ∈ B, G.Adj u t) (huOdd : Odd (G.degree u))
    (hB : Even B.card)
    (havoid : ∀ e ∈ M, e.1 ≠ u ∧ e.2 ≠ u)
    (D : Decomposition (ordinaryMatePuncture (starPuncture G u B) M)) :
    0 < D.endpointCount u := by
  exact D.endpointCount_pos_of_odd_degree u
    (ordinary_star_mates_centre_odd u B M hadj huOdd hB havoid)

end Gallai.TwoException
