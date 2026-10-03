/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.Inputs.MatchingPuncture

@[expose] public section

/-! # Degree-cap transport for parity-controlled punctures -/

namespace Gallai

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G H F : SimpleGraph V}
variable [DecidableRel G.Adj] [DecidableRel H.Adj] [DecidableRel F.Adj]

omit [DecidableEq V] in
/-- A subgraph introducing no new even vertices inherits every even-degree cap. -/
theorem even_degree_cap_of_even_preserved (hle : H ≤ G)
    (hkeep : ∀ v, Even (H.degree v) → Even (G.degree v))
    (c : ℕ) (hcap : ∀ v, Even (G.degree v) → eDegree G v ≤ c) :
    ∀ v, Even (H.degree v) → eDegree H v ≤ c := by
  intro v hv
  apply (Finset.card_le_card (s := evenNeighbors H v) (t := evenNeighbors G v) ?_).trans
    (hcap v (hkeep v hv))
  intro w hw
  obtain ⟨ha, he⟩ := (mem_evenNeighbors v w).mp hw
  exact (mem_evenNeighbors v w).mpr ⟨hle ha, hkeep w he⟩

omit [DecidableEq V] in
/-- A possible new even vertex causes no cap loss when it has no even
neighbour in the subgraph. All other even vertices must be preserved. -/
theorem even_degree_cap_of_isolated_exception (hle : H ≤ G) (u : V)
    (hkeep : ∀ v, v ≠ u → Even (H.degree v) → Even (G.degree v))
    (hcentre : ∀ v, H.Adj u v → ¬ Even (H.degree v))
    (c : ℕ) (hcap : ∀ v, Even (G.degree v) → eDegree G v ≤ c) :
    ∀ v, Even (H.degree v) → eDegree H v ≤ c := by
  intro v hv
  by_cases hvu : v = u
  · subst v
    have hz : evenNeighbors H u = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro w hw
      obtain ⟨ha, he⟩ := (mem_evenNeighbors (G := H) u w).mp hw
      exact hcentre w ha he
    simp [eDegree, hz]
  · apply (Finset.card_le_card (s := evenNeighbors H v) (t := evenNeighbors G v) ?_).trans
      (hcap v (hkeep v hvu hv))
    intro w hw
    obtain ⟨ha, he⟩ := (mem_evenNeighbors (G := H) v w).mp hw
    have hwu : w ≠ u := by
      intro h
      subst w
      exact hcentre v ha.symm hv
    exact (mem_evenNeighbors (G := G) v w).mpr ⟨hle ha, hkeep w hwu he⟩

/-- If all active removed degrees are odd and their vertices were even,
deletion introduces no even vertices. This covers the three-spoke even star. -/
theorem odd_removed_degree_even_preserved (hle : F ≤ G)
    (hodd : ∀ v, 0 < F.degree v → Odd (F.degree v))
    (heven : ∀ v, 0 < F.degree v → Even (G.degree v)) :
    ∀ v, Even ((G \ F).degree v) → Even (G.degree v) := by
  intro v hv
  have hd := degree_sdiff_add_of_le hle v
  by_cases hp : 0 < F.degree v
  · have ho := hodd v hp
    have he := heven v hp
    rw [Nat.odd_iff] at ho
    rw [Nat.even_iff] at hv he
    omega
  · have hz : F.degree v = 0 := by omega
    simpa only [hz, Nat.add_zero] using hd ▸ (show Even ((G \ F).degree v + F.degree v) by
      simpa only [hz, Nat.add_zero] using hv)

/-- Explicit cap verification for odd-degree punctures on originally even vertices. -/
theorem odd_removed_degree_puncture_cap (hle : F ≤ G)
    (hodd : ∀ v, 0 < F.degree v → Odd (F.degree v))
    (heven : ∀ v, 0 < F.degree v → Even (G.degree v))
    (c : ℕ) (hcap : ∀ v, Even (G.degree v) → eDegree G v ≤ c) :
    ∀ v, Even ((G \ F).degree v) → eDegree (G \ F) v ≤ c :=
  even_degree_cap_of_even_preserved (G := G) (H := G \ F) (fun _ _ h => h.1)
    (odd_removed_degree_even_preserved hle hodd heven) c hcap

/-- Deleting a matching of even vertices preserves the even-degree cap. -/
theorem matching_puncture_cap (hle : F ≤ G) (hmatch : ∀ v, F.degree v ≤ 1)
    (heven : ∀ v, 0 < F.degree v → Even (G.degree v))
    (c : ℕ) (hcap : ∀ v, Even (G.degree v) → eDegree G v ≤ c) :
    ∀ v, Even ((G \ F).degree v) → eDegree (G \ F) v ≤ c :=
  even_degree_cap_of_even_preserved (G := G) (H := G \ F) (fun _ _ h => h.1)
    (matching_puncture_even_preserved hle hmatch heven) c hcap

end Gallai
