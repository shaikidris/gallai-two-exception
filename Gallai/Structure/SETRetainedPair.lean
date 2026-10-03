/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.Structure.SETOddLeaf

@[expose] public section

/-! # Derived retained pair and centre exclusion

The odd-leaf consumer need not provide triangle labels. They are extracted
from the actual SET even-neighbour finset at its distinguished even vertex.
-/

namespace Gallai

variable {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V]
variable {H : SimpleGraph V} [DecidableRel H.Adj]
variable {G : SimpleGraph W} [DecidableRel G.Adj]

/-- An actual even SET vertex determines the other two even vertices. -/
theorem IsSET.even_pair_away (h : IsSET H) (z : V) (hz : Even (H.degree z)) :
    ∃ a b, a ≠ b ∧ a ≠ z ∧ b ≠ z ∧ Even (H.degree a) ∧ Even (H.degree b) ∧
      ∀ v, Even (H.degree v) → v = z ∨ v = a ∨ v = b := by
  obtain ⟨a, b, hab, hp⟩ := Finset.card_eq_two.mp (h.eDegree_even z hz)
  have ha : a ∈ evenNeighbors H z := by rw [hp]; simp
  have hb : b ∈ evenNeighbors H z := by rw [hp]; simp
  obtain ⟨hza, hea⟩ := (mem_evenNeighbors (G := H) z a).mp ha
  obtain ⟨hzb, heb⟩ := (mem_evenNeighbors (G := H) z b).mp hb
  refine ⟨a, b, hab, hza.ne.symm, hzb.ne.symm, hea, heb, ?_⟩
  intro v hv
  by_cases he : v = z
  · exact Or.inl he
  · right
    have hm : v ∈ evenNeighbors H z :=
      (mem_evenNeighbors (G := H) z v).mpr
        ⟨h.even_clique z v hz hv (fun hh => he hh.symm), hv⟩
    simpa only [hp, Finset.mem_insert, Finset.mem_singleton] using hm

/-- Retained-pair uniqueness with labels derived internally from the SET
graph. Only the distinguished even vertex may fail parity preservation. -/
theorem IsSET.promoted_odd_except_one_subsingleton (h : IsSET H) (f : V ↪ W)
    (hle : ∀ ⦃v w⦄, H.Adj v w → G.Adj (f v) (f w))
    (ht : ComponentsAreTriangles (evenSubgraph G)) (z : V) (hz : Even (H.degree z))
    (hkeep : ∀ v, v ≠ z → Even (H.degree v) → Even (G.degree (f v))) :
    Set.Subsingleton {v | Odd (H.degree v) ∧ Even (G.degree (f v))} := by
  obtain ⟨a, b, hab, haz, hbz, ha, hb, hcover⟩ := h.even_pair_away z hz
  exact h.promoted_odd_pair_subsingleton f hle ht z a b ha hb hab hcover
    (hkeep a haz ha) (hkeep b hbz hb)

/-- A SET graph cannot contain the designated centre if every even vertex
except the centre and one leaf keeps parity, and the centre has no surviving
originally even neighbour. This does not assume centre parity. -/
theorem IsSET.centre_contradiction (h : IsSET H) (f : V → W) (u z : V)
    (hkeep : ∀ v, v ≠ u → v ≠ z → Even (H.degree v) → Even (G.degree (f v)))
    (hcentre : ∀ v, H.Adj u v → ¬ Even (G.degree (f v))) : False := by
  obtain ⟨v, huv, hev, hvz⟩ := h.even_neighbor_ne u z
  exact hcentre v huv (hkeep v huv.ne.symm hvz hev)

end Gallai
