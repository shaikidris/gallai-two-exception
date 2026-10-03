/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.OrdinaryTriangleBudget

@[expose] public section

/-! # Global cap with one newly even contact centre -/
namespace Gallai.TwoException
open scoped Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G J : SimpleGraph V} [DecidableRel G.Adj] [DecidableRel J.Adj]

/-- A newly even centre whose only possible even neighbour is the bare
protected vertex preserves the global subcubic cap. The other exception
must have become odd. -/
theorem puncture_cap_of_one_new_even_center
    (h x u : V) (hsub : J ≤ G)
    (hprofile : ∀ t, Even (J.degree t) → Even (G.degree t) ∨ t = u)
    (hxOdd : Odd (J.degree x)) (hhzero : eDegree G h = 0)
    (hcap : ∀ t, Even (G.degree t) → t ≠ x → eDegree G t ≤ 3)
    (hcentre : ∀ t, J.Adj u t → Even (J.degree t) → t = h) :
    ∀ t, Even (J.degree t) → eDegree J t ≤ 3 := by
  classical
  intro t ht
  by_cases htu : t = u
  · subst t
    have hs : evenNeighbors J u ⊆ {h} := by
      intro v hv
      obtain ⟨huv, hvEven⟩ := (mem_evenNeighbors (G := J) u v).mp hv
      exact Finset.mem_singleton.mpr (hcentre v huv hvEven)
    have hc := Finset.card_le_card hs
    simp only [Finset.card_singleton] at hc
    change #(evenNeighbors J u) ≤ 3
    omega
  have htOriginal : Even (G.degree t) := (hprofile t ht).resolve_right htu
  have htx : t ≠ x := by
    intro he
    subst t
    rw [Nat.even_iff] at ht
    rw [Nat.odd_iff] at hxOdd
    omega
  by_cases hth : t = h
  · subst t
    have hempty : evenNeighbors G h = ∅ := Finset.card_eq_zero.mp hhzero
    have hs : evenNeighbors J h ⊆ {u} := by
      intro v hv
      obtain ⟨hhv, hvEven⟩ := (mem_evenNeighbors (G := J) h v).mp hv
      rcases hprofile v hvEven with hvOriginal | hvu
      · have hm := (mem_evenNeighbors (G := G) h v).mpr ⟨hsub hhv, hvOriginal⟩
        rw [hempty] at hm
        exact False.elim (Finset.notMem_empty v hm)
      · exact Finset.mem_singleton.mpr hvu
    have hc := Finset.card_le_card hs
    simp only [Finset.card_singleton] at hc
    change #(evenNeighbors J h) ≤ 3
    omega
  have hs : evenNeighbors J t ⊆ evenNeighbors G t := by
    intro v hv
    obtain ⟨htv, hvEven⟩ := (mem_evenNeighbors (G := J) t v).mp hv
    rcases hprofile v hvEven with hvOriginal | hvu
    · exact (mem_evenNeighbors (G := G) t v).mpr ⟨hsub htv, hvOriginal⟩
    · subst v
      exact False.elim (hth (hcentre t htv.symm ht))
  exact (Finset.card_le_card hs).trans (hcap t htOriginal htx)

end Gallai.TwoException
