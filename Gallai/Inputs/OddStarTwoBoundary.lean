/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.Inputs.OddStarAttachment
public import Gallai.Inputs.HangingParity

@[expose] public section

/-! # Two-boundary odd-leaf punctures are not SET

The actual induced ESET and its edge complement meet only at the centre.
The attachment has degree two there, so an originally odd centre leaves an
odd remainder degree, contradicting guarded hanging parity.
-/

namespace Gallai

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G F : SimpleGraph V} [DecidableRel G.Adj] [DecidableRel F.Adj]

/-- The two-boundary case of the odd-leaf Fan puncture cannot be SET under
the source's strictly smaller-edge minimality hypothesis. -/
theorem odd_star_two_boundary_not_set_of_weak_centre (hle : F ≤ G) (u z : V)
    (hmatch : ∀ v, v ≠ u → F.degree v ≤ 1)
    (heven : ∀ v, v ≠ u → v ≠ z → 0 < F.degree v → Even (G.degree v))
    (huOdd : Odd (G.degree u)) (hz : Odd (G.degree z))
    (hdz : F.degree z = 1) (huz : F.Adj u z)
    (hcentre : ∀ v, (G \ F).Adj u v → v ≠ z → ¬ Even ((G \ F).degree v))
    (ht : ComponentsAreTriangles (evenSubgraph G))
    (C : (G \ F).ConnectedComponent) [DecidablePred (· ∈ C.supp)]
    (hzC : z ∈ C.supp) (y : V) (hyC : y ∈ C.supp) (hyz : y ≠ z)
    (hy : 0 < F.degree y) (hconn : G.Connected)
    (hcap : ∀ v, Even (G.degree v) → eDegree G v ≤ 3)
    (hnot : ¬ HasPathBudget G (Fintype.card V / 2)) (hset : ¬ IsSET G)
    (hmin : ∀ (U : Set V) [DecidablePred (· ∈ U)]
      (J : SimpleGraph U) [DecidableRel J.Adj],
      J.edgeFinset.card < G.edgeFinset.card → J.Connected →
      (∀ v, Even (J.degree v) → eDegree J v ≤ 3) →
      HasPathBudget J (Fintype.card U / 2) ∨ IsSET J) :
    ¬ IsSET ((G \ F).induce C.supp) := by
  classical
  intro hC
  have hu := (odd_star_puncture_set_interface_of_weak_centre hle u z hmatch heven hz hdz
    hcentre ht C hC).1
  obtain ⟨hE, hdeg⟩ := odd_star_puncture_attachment_data_of_weak_centre
    hle u z hmatch heven hz hdz huz
    hcentre ht C hC hzC y hyC hyz hy
  have hn := odd_star_puncture_neighborhood_subset_of_weak_centre hle u z hmatch heven hz hdz huz
    hcentre ht C hC hzC
  let S := insert u C.supp
  let T := C.suppᶜ
  let A := (G.induce S).spanningCoe
  let B := G \ A
  let : DecidableRel A.Adj := fun a b => Classical.propDecidable (A.Adj a b)
  let : DecidableRel B.Adj := fun a b => Classical.propDecidable (B.Adj a b)
  have hA : A ≤ G := G.spanningCoe_induce_le S
  have hG : A ⊔ B = G := by
    ext a b
    change (A.Adj a b ∨ G.Adj a b ∧ ¬ A.Adj a b) ↔ G.Adj a b
    constructor
    · rintro (h | h)
      · exact hA h
      · exact h.1
    · intro h
      by_cases ha : A.Adj a b
      · exact Or.inl ha
      · exact Or.inr ⟨h, ha⟩
  have haS : A.support ⊆ S := by
    intro v hv
    rw [SimpleGraph.support_spanningCoe] at hv
    obtain ⟨w, _, rfl⟩ := hv
    exact w.property
  have hbT : B.support ⊆ T := by
    rintro v ⟨w, hvw⟩ hvC
    apply hvw.2
    exact (SimpleGraph.map_adj (Function.Embedding.subtype _) _ v w).mpr
      ⟨⟨v, Set.mem_insert_of_mem u hvC⟩, ⟨w, hn v hvC hvw.1⟩, hvw.1, rfl, rfl⟩
  have he : IsESETAt (A.induce S) ⟨u, Set.mem_insert u C.supp⟩ := by
    have hh : A.induce S = G.induce S := SimpleGraph.induce_spanningCoe
    simpa only [hh] using hE
  have hp := hanging_eset_joint_parity A B S T u (Set.mem_insert u C.supp) hu
    (by ext v; simp [S, T]; tauto) (by
      ext v
      change ((v = u ∨ v ∈ C.supp) ∧ v ∉ C.supp) ↔ v = u
      constructor
      · rintro ⟨hv | hv, hnC⟩
        · exact hv
        · exact (hnC hv).elim
      · rintro rfl
        exact ⟨Or.inl rfl, hu⟩) haS hbT (by convert he using 1)
    (by simpa only [hG] using hconn) (by
      simpa only [SimpleGraph.degree, SimpleGraph.neighborFinset,
        ← Set.ncard_eq_toFinset_card', hG] using hcap)
    (by simpa only [hG] using hnot) (by simpa only [hG] using hset)
    (by simpa only [SimpleGraph.edgeFinset, ← Set.ncard_eq_toFinset_card', hG] using hmin)
  have hd : B.degree u + A.degree u = G.degree u := by
    simpa only [SimpleGraph.degree, SimpleGraph.neighborFinset,
      ← Set.ncard_eq_toFinset_card', B] using degree_sdiff_add_of_le hA u
  have hevenB := hp.2
  have hAu : A.degree u = 2 := by
    simpa only [SimpleGraph.degree, SimpleGraph.neighborFinset,
      ← Set.ncard_eq_toFinset_card', A, S] using hdeg
  rw [Nat.even_iff] at hevenB
  rw [Nat.odd_iff] at huOdd
  omega

/-- Original-parity compatibility entry point for the generalized odd-leaf argument. -/
theorem odd_star_two_boundary_not_set (hle : F ≤ G) (u z : V)
    (hmatch : ∀ v, v ≠ u → F.degree v ≤ 1)
    (heven : ∀ v, v ≠ u → v ≠ z → 0 < F.degree v → Even (G.degree v))
    (huOdd : Odd (G.degree u)) (hz : Odd (G.degree z))
    (hdz : F.degree z = 1) (huz : F.Adj u z)
    (hcentre : ∀ v, (G \ F).Adj u v → ¬ Even (G.degree v))
    (ht : ComponentsAreTriangles (evenSubgraph G))
    (C : (G \ F).ConnectedComponent) [DecidablePred (· ∈ C.supp)]
    (hzC : z ∈ C.supp) (y : V) (hyC : y ∈ C.supp) (hyz : y ≠ z)
    (hy : 0 < F.degree y) (hconn : G.Connected)
    (hcap : ∀ v, Even (G.degree v) → eDegree G v ≤ 3)
    (hnot : ¬ HasPathBudget G (Fintype.card V / 2)) (hset : ¬ IsSET G)
    (hmin : ∀ (U : Set V) [DecidablePred (· ∈ U)]
      (J : SimpleGraph U) [DecidableRel J.Adj],
      J.edgeFinset.card < G.edgeFinset.card → J.Connected →
      (∀ v, Even (J.degree v) → eDegree J v ≤ 3) →
      HasPathBudget J (Fintype.card U / 2) ∨ IsSET J) :
    ¬ IsSET ((G \ F).induce C.supp) := by
  have hc : ∀ v, (G \ F).Adj u v → v ≠ z → ¬ Even ((G \ F).degree v) := by
    intro v huv hvz hev
    exact hcentre v huv
      ((odd_star_puncture_parity hle u z hmatch heven hz hdz).2.2 v huv.ne.symm hvz hev)
  exact odd_star_two_boundary_not_set_of_weak_centre hle u z hmatch heven huOdd hz hdz huz hc ht
    C hzC y hyC hyz hy hconn hcap hnot hset hmin

end Gallai
