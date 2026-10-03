/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.Inputs.HangingParity
public import Gallai.Structure.SETBoundary
public import Gallai.Structure.PunctureBoundary

@[expose] public section

/-! # Excluding a SET component with parity-preserved triangle

This consumes Claim 1 and the actual puncture boundary. The remaining Fan
star cases can change a triangle parity and are not covered by this lemma.
-/

namespace Gallai

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G H : SimpleGraph V} [DecidableRel G.Adj] [DecidableRel H.Adj]

/-- A closed puncture part with preserved even parities and only odd-to-even
removed-edge endpoints cannot be SET in a minimal counterexample. -/
theorem preserved_triangle_puncture_not_set (hlt : H < G)
    (S : Set V) [DecidablePred (· ∈ S)] (hne : S.Nonempty)
    (hclosed : ∀ v ∈ S, H.neighborSet v ⊆ S)
    (hkeep : ∀ v : S, Even ((H.induce S).degree v) → Even (G.degree v))
    (hboundary : ∀ (v : V) (hv : v ∈ S) (w : V), G.Adj v w → ¬ H.Adj v w →
      Odd ((H.induce S).degree ⟨v, hv⟩) ∧ Even (G.degree v))
    (hconn : G.Connected) (hcap : ∀ v, Even (G.degree v) → eDegree G v ≤ 3)
    (hnot : ¬ HasPathBudget G (Fintype.card V / 2)) (hset : ¬ IsSET G)
    (hmin : ∀ (U : Set V) [DecidablePred (· ∈ U)]
      (J : SimpleGraph U) [DecidableRel J.Adj],
      J.edgeFinset.card < G.edgeFinset.card → J.Connected →
      (∀ v, Even (J.degree v) → eDegree J v ≤ 3) →
      HasPathBudget J (Fintype.card U / 2) ∨ IsSET J) :
    ¬ IsSET (H.induce S) := by
  classical
  intro hC
  obtain ⟨z, hz, w, hzw, hnzw⟩ := puncture_closed_boundary_nonempty hconn hlt S hne hclosed
  have hpz := hboundary z hz w hzw hnzw
  have hsingle := hC.promoted_odd_subsingleton (Function.Embedding.subtype _)
    (fun {_ _} hh => hlt.le hh) hkeep hcap
  have huniq : ∀ v ∈ S, ∀ w, G.Adj v w → ¬ H.Adj v w → v = z := by
    intro v hv t hvt hnvt
    exact congrArg Subtype.val (hsingle (hboundary v hv t hvt hnvt) hpz)
  let A := (H.induce S).spanningCoe
  let B := G \ A
  let T := Sᶜ ∪ {z}
  have hA : A ≤ G := (H.spanningCoe_induce_le S).trans hlt.le
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
    obtain ⟨u, _, rfl⟩ := hv
    exact u.property
  have hbT : B.support ⊆ T := puncture_closed_complement_support S {z} hclosed huniq
  have he : IsESETAt (A.induce S) ⟨z, hz⟩ := by
    have hh : A.induce S = H.induce S := SimpleGraph.induce_spanningCoe
    simpa only [hh] using hC.isESETAt ⟨z, hz⟩
  have hp := hanging_eset_joint_parity A B S T z hz (Or.inr rfl)
    (by ext v; simp [T]) (by
      ext v
      change (v ∈ S ∧ (v ∉ S ∨ v = z)) ↔ v = z
      constructor
      · rintro ⟨hv, hn | he⟩
        · exact (hn hv).elim
        · exact he
      · rintro rfl
        exact ⟨hz, Or.inr rfl⟩) haS hbT he
    (by simpa only [hG] using hconn) (by
      simpa only [SimpleGraph.degree, SimpleGraph.neighborFinset,
        ← Set.ncard_eq_toFinset_card', hG] using hcap)
    (by simpa only [hG] using hnot) (by simpa only [hG] using hset)
    (by simpa only [SimpleGraph.edgeFinset, ← Set.ncard_eq_toFinset_card', hG] using hmin)
  have ho : Odd (G.degree z) := by
    simpa only [SimpleGraph.degree, SimpleGraph.neighborFinset,
      ← Set.ncard_eq_toFinset_card', hG] using hp.1
  exact Nat.not_even_iff_odd.mpr ho hpz.2

end Gallai
