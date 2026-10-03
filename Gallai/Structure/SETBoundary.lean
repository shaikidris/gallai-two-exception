/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.Structure.SET

@[expose] public section

/-! # SET boundary obstruction for Fan punctures

Two odd vertices of a SET graph share an even neighbour. If its even triangle
retains parity in a supergraph of E-degree at most three, at most one old odd
vertex becomes even. This is the counting step in Theorem 13 Claim 3.
-/

namespace Gallai

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {H : SimpleGraph V} [DecidableRel H.Adj]

/-- Two odd SET vertices have a common even neighbour. -/
theorem IsSET.common_even_neighbor (h : IsSET H) (a b : V)
    (ha : Odd (H.degree a)) (hb : Odd (H.degree b)) :
    ∃ w, H.Adj a w ∧ H.Adj b w ∧ Even (H.degree w) := by
  classical
  have hs : evenNeighbors H a ∪ evenNeighbors H b ⊆
      Finset.univ.filter (fun w => Even (H.degree w)) := by
    intro w hw
    rcases Finset.mem_union.mp hw with hw | hw
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (mem_evenNeighbors a w).mp hw |>.2⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (mem_evenNeighbors b w).mp hw |>.2⟩
  have hc := (Finset.card_le_card hs).trans_eq h.card_even
  have hi : ¬ Disjoint (evenNeighbors H a) (evenNeighbors H b) := by
    intro hd
    have he := Finset.card_union_of_disjoint hd
    have h₁ := h.odd_neighbors a ha
    have h₂ := h.odd_neighbors b hb
    unfold eDegree at h₁ h₂
    omega
  obtain ⟨w, hw₁, hw₂⟩ := Finset.not_disjoint_iff.mp hi
  exact ⟨w, ((mem_evenNeighbors a w).mp hw₁).1,
    ((mem_evenNeighbors b w).mp hw₂).1, ((mem_evenNeighbors a w).mp hw₁).2⟩

/-- Preserving the even triangle under a subcubic E-degree cap permits at
most one odd-to-even boundary vertex. -/
theorem IsSET.promoted_odd_subsingleton {W : Type*} [Fintype W]
    {G : SimpleGraph W} [DecidableRel G.Adj] (h : IsSET H) (f : V ↪ W)
    (hle : ∀ ⦃a b⦄, H.Adj a b → G.Adj (f a) (f b))
    (hkeep : ∀ v, Even (H.degree v) → Even (G.degree (f v)))
    (hcap : ∀ v, Even (G.degree v) → eDegree G v ≤ 3) :
    Set.Subsingleton {v | Odd (H.degree v) ∧ Even (G.degree (f v))} := by
  classical
  intro a ha b hb
  by_contra hab
  obtain ⟨w, haw, hbw, hew⟩ := h.common_even_neighbor a b ha.1 hb.1
  have hna : a ∉ evenNeighbors H w := by
    intro hm
    exact (Nat.not_even_iff_odd.mpr ha.1) ((mem_evenNeighbors w a).mp hm).2
  have hnb : b ∉ evenNeighbors H w := by
    intro hm
    exact (Nat.not_even_iff_odd.mpr hb.1) ((mem_evenNeighbors w b).mp hm).2
  have hs : (insert a (insert b (evenNeighbors H w))).map f ⊆ evenNeighbors G (f w) := by
    intro v hv
    obtain ⟨v, hm, rfl⟩ := Finset.mem_map.mp hv
    rcases Finset.mem_insert.mp hm with rfl | hm
    · exact (mem_evenNeighbors (f w) _).mpr ⟨hle haw.symm, ha.2⟩
    rcases Finset.mem_insert.mp hm with rfl | hm
    · exact (mem_evenNeighbors (f w) _).mpr ⟨hle hbw.symm, hb.2⟩
    obtain ⟨hv, he⟩ := (mem_evenNeighbors w v).mp hm
    exact (mem_evenNeighbors (f w) (f v)).mpr ⟨hle hv, hkeep v he⟩
  have hc := Finset.card_le_card hs
  rw [Finset.card_map, Finset.card_insert_of_notMem (by simp [hab, hna]),
    Finset.card_insert_of_notMem hnb] at hc
  have ht := h.eDegree_even w hew
  have hu := hcap (f w) (hkeep w hew)
  unfold eDegree at ht hu
  omega

end Gallai
