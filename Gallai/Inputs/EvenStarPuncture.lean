/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.Inputs.MatchingPuncture

@[expose] public section

/-! # Fan star punctures with originally even leaves

The centre may have arbitrary removed degree. Off the centre, degree at most
one and original evenness derive the component parity interface.
-/

namespace Gallai

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G F : SimpleGraph V} [DecidableRel G.Adj] [DecidableRel F.Adj]

/-- Off a deleted star centre, active even endpoints become odd and no
new even vertices appear. Disjoint matching edges are allowed too. -/
theorem even_star_puncture_parity (hle : F ≤ G) (u : V)
    (hmatch : ∀ v, v ≠ u → F.degree v ≤ 1)
    (heven : ∀ v, v ≠ u → 0 < F.degree v → Even (G.degree v)) :
    (∀ v, v ≠ u → 0 < F.degree v → Odd ((G \ F).degree v)) ∧
    (∀ v, v ≠ u → Even ((G \ F).degree v) → Even (G.degree v)) := by
  have ho : ∀ v, v ≠ u → 0 < F.degree v → Odd ((G \ F).degree v) := by
    intro v hv hp
    have hd := degree_sdiff_add_of_le hle v
    have hm := hmatch v hv
    have he := heven v hv hp
    rw [Nat.even_iff] at he
    rw [Nat.odd_iff]
    omega
  refine ⟨ho, ?_⟩
  intro v hv he
  by_cases hp : 0 < F.degree v
  · exact False.elim ((Nat.not_even_iff_odd.mpr (ho v hv hp)) he)
  have hz : F.degree v = 0 := by omega
  have hd := degree_sdiff_add_of_le hle v
  simp only [hz, Nat.add_zero] at hd
  rwa [← hd]

/-- With no even neighbour in the punctured graph at the centre, an even-leaf
Fan star puncture has no SET component under guarded minimality. -/
theorem even_star_puncture_component_not_set_of_punctured_centre (hle : F ≤ G) (u : V)
    (hmatch : ∀ v, v ≠ u → F.degree v ≤ 1)
    (heven : ∀ v, v ≠ u → 0 < F.degree v → Even (G.degree v))
    (hcentre : ∀ v, (G \ F).Adj u v → ¬ Even ((G \ F).degree v))
    (hactive : ∃ a b, F.Adj a b)
    (hconn : G.Connected) (hcap : ∀ v, Even (G.degree v) → eDegree G v ≤ 3)
    (hnot : ¬ HasPathBudget G (Fintype.card V / 2)) (hset : ¬ IsSET G)
    (hmin : ∀ (U : Set V) [DecidablePred (· ∈ U)]
      (J : SimpleGraph U) [DecidableRel J.Adj],
      J.edgeFinset.card < G.edgeFinset.card → J.Connected →
      (∀ v, Even (J.degree v) → eDegree J v ≤ 3) →
      HasPathBudget J (Fintype.card U / 2) ∨ IsSET J)
    (C : (G \ F).ConnectedComponent) [DecidablePred (· ∈ C.supp)] :
    ¬ IsSET ((G \ F).induce C.supp) := by
  classical
  intro hC
  obtain ⟨ho, hk⟩ := even_star_puncture_parity hle u hmatch heven
  have hc : ∀ v ∈ C.supp, (G \ F).neighborSet v ⊆ C.supp :=
    fun _ hv _ hw => C.mem_supp_of_adj_mem_supp hv hw
  have hu : u ∉ C.supp := by
    intro hu
    have hp : 0 < (evenNeighbors ((G \ F).induce C.supp) ⟨u, hu⟩).card := by
      rcases hC.eDegree_two_or_three ⟨u, hu⟩ with h | h <;> unfold eDegree at h <;> omega
    obtain ⟨w, hw⟩ := Finset.card_pos.mp hp
    obtain ⟨ha, he⟩ := (mem_evenNeighbors (G := (G \ F).induce C.supp) ⟨u, hu⟩ w).mp hw
    rw [SimpleGraph.degree_induce_of_neighborSet_subset (hc w w.property)] at he
    exact hcentre w ha he
  have hlt : G \ F < G := by
    refine lt_iff_le_not_ge.mpr ⟨fun _ _ hh => hh.1, ?_⟩
    intro hh
    obtain ⟨a, b, hab⟩ := hactive
    exact (hh (hle hab)).2 hab
  apply preserved_triangle_puncture_not_set hlt C.supp C.nonempty_supp hc
    ?_ ?_ hconn hcap hnot hset hmin hC
  · intro v hv
    rw [SimpleGraph.degree_induce_of_neighborSet_subset (hc v v.property)] at hv
    exact hk v (fun he => hu (he ▸ v.property)) hv
  · intro v hv w hvw hn
    have hf : F.Adj v w := by
      by_contra hnf
      exact hn ⟨hvw, hnf⟩
    have hp := (F.degree_pos_iff_exists_adj v).mpr ⟨w, hf⟩
    have hvu : v ≠ u := fun he => hu (he ▸ hv)
    refine ⟨?_, heven v hvu hp⟩
    rw [SimpleGraph.degree_induce_of_neighborSet_subset (hc v hv)]
    exact ho v hvu hp

/-- Compatibility interface: excluding originally even retained neighbours
is sufficient, but stronger than the published punctured-parity condition. -/
theorem even_star_puncture_component_not_set (hle : F ≤ G) (u : V)
    (hmatch : ∀ v, v ≠ u → F.degree v ≤ 1)
    (heven : ∀ v, v ≠ u → 0 < F.degree v → Even (G.degree v))
    (hcentre : ∀ v, (G \ F).Adj u v → ¬ Even (G.degree v))
    (hactive : ∃ a b, F.Adj a b)
    (hconn : G.Connected) (hcap : ∀ v, Even (G.degree v) → eDegree G v ≤ 3)
    (hnot : ¬ HasPathBudget G (Fintype.card V / 2)) (hset : ¬ IsSET G)
    (hmin : ∀ (U : Set V) [DecidablePred (· ∈ U)]
      (J : SimpleGraph U) [DecidableRel J.Adj],
      J.edgeFinset.card < G.edgeFinset.card → J.Connected →
      (∀ v, Even (J.degree v) → eDegree J v ≤ 3) →
      HasPathBudget J (Fintype.card U / 2) ∨ IsSET J)
    (C : (G \ F).ConnectedComponent) [DecidablePred (· ∈ C.supp)] :
    ¬ IsSET ((G \ F).induce C.supp) := by
  apply even_star_puncture_component_not_set_of_punctured_centre hle u hmatch heven
    ?_ hactive hconn hcap hnot hset hmin C
  intro v hv he
  exact hcentre v hv ((even_star_puncture_parity hle u hmatch heven).2 v hv.ne.symm he)

end Gallai
