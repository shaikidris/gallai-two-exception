/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.Inputs.HangingESET
public import Gallai.Structure.OneVertexSeparation

@[expose] public section

/-! # Joint parity forced by a strictly smaller-graph induction hypothesis

This consumer implements the nontrivial-remainder part of Claim 1. It does
not supply the global induction hypothesis or discard its measure guard.
-/

namespace Gallai

universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
variable (A B : SimpleGraph V) [DecidableRel A.Adj] [DecidableRel B.Adj]

omit [DecidableEq V] in
/-- Restriction to a vertex set containing every vertex reflects the SET predicate. -/
theorem IsSET.of_induce_all (S : Set V) [DecidablePred (· ∈ S)]
    (hall : ∀ v, v ∈ S) (h : IsSET (A.induce S)) : IsSET A := by
  have hs : A.support ⊆ S := fun v _ => hall v
  have hd (v : S) := SimpleGraph.degree_induce_of_support_subset hs v
  constructor
  · have hm : (Finset.univ.filter (fun v : S => Even ((A.induce S).degree v))).map
        (Function.Embedding.subtype _) = Finset.univ.filter (fun v : V => Even (A.degree v)) := by
      ext v
      constructor
      · intro hv
        obtain ⟨w, hw, heq⟩ := Finset.mem_map.mp hv
        change w.val = v at heq
        subst v
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
          simpa only [hd w, Function.Embedding.coe_subtype] using (Finset.mem_filter.mp hw).2⟩
      · intro hv
        refine Finset.mem_map.mpr ⟨⟨v, hall v⟩, ?_, rfl⟩
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
          simpa only [hd ⟨v, hall v⟩] using (Finset.mem_filter.mp hv).2⟩
    have hcount := congrArg Finset.card hm
    simpa only [Finset.card_map, h.card_even] using hcount.symm
  · intro a b ha hb hab
    exact h.even_clique ⟨a, hall a⟩ ⟨b, hall b⟩
      (by simpa only [hd] using ha) (by simpa only [hd] using hb)
      (fun he => hab (congrArg Subtype.val he))
  · intro v hv
    have he := h.odd_neighbors ⟨v, hall v⟩ (by simpa only [hd] using hv)
    simpa only [eDegree_induce_of_support_subset A S hs] using he

/-- A singleton remainder contributes no edges; the ESET boundary then already
gives floor-or-SET on the entire graph, without invoking smaller-graph induction. -/
theorem hanging_eset_singleton_remainder (S T : Set V)
    [DecidablePred (· ∈ S)]
    (z : V) (hzS : z ∈ S) (hc : S ∪ T = Set.univ)
    (hB : B.support ⊆ T) (ht : T ⊆ {z})
    (he : IsESETAt (A.induce S) ⟨z, hzS⟩) :
    HasPathBudget (A ⊔ B) (Fintype.card V / 2) ∨ IsSET (A ⊔ B) := by
  classical
  have hall : ∀ v, v ∈ S := by
    intro v
    have hv : v ∈ S ∪ T := by rw [hc]; trivial
    rcases hv with hv | hv
    · exact hv
    · have hz : v = z := ht hv
      simpa only [hz] using hzS
  have hb : B = ⊥ := by
    ext a b
    constructor
    · intro hab
      have ha : a = z := ht (hB ⟨b, hab⟩)
      have hb : b = z := ht (hB ⟨a, hab.symm⟩)
      exact (hab.ne (ha.trans hb.symm)).elim
    · exact False.elim
  subst B
  simp only [sup_bot_eq]
  rcases he.floor_or_set with ⟨D, hD⟩ | hs
  · have ha : (A.induce S).map (Function.Embedding.subtype _) = A :=
      (A.spanningCoe_induce_eq_self S).mpr (fun v _ => hall v)
    have hc : Fintype.card S = Fintype.card V := Fintype.card_of_bijective
      (show Function.Bijective (Subtype.val : S → V) from
        ⟨Subtype.val_injective, fun v => ⟨⟨v, hall v⟩, rfl⟩⟩)
    have hm : HasPathBudget ((A.induce S).map (Function.Embedding.subtype _))
        (Fintype.card V / 2) := ⟨D.map (Function.Embedding.subtype _), by simpa [hc] using hD⟩
    exact Or.inl (by simpa only [ha] using hm)
  · exact Or.inr (hs.of_induce_all A S hall)

/-- Under bounded smaller-graph minimality, a hanging ESET with a nontrivial
remainder meets a non-floor graph at an odd whole-graph, even remainder joint. -/
theorem hanging_eset_joint_parity_of_smaller (S T : Set V)
    [DecidablePred (· ∈ S)] [DecidablePred (· ∈ T)]
    (z : V) (hzS : z ∈ S) (hzT : z ∈ T)
    (hc : S ∪ T = Set.univ) (hi : S ∩ T = {z})
    (hA : A.support ⊆ S) (hB : B.support ⊆ T)
    (he : IsESETAt (A.induce S) ⟨z, hzS⟩)
    (hconn : (A ⊔ B).Connected) (hother : ∃ v ∈ T, v ≠ z)
    (hcap : ∀ v, Even ((A ⊔ B).degree v) → eDegree (A ⊔ B) v ≤ 3)
    (hnot : ¬ HasPathBudget (A ⊔ B) (Fintype.card V / 2))
    (hmin : ∀ (U : Set V) [DecidablePred (· ∈ U)]
      (J : SimpleGraph U) [DecidableRel J.Adj],
      J.edgeFinset.card < (A ⊔ B).edgeFinset.card → J.Connected →
      (∀ v, Even (J.degree v) → eDegree J v ≤ 3) →
      HasPathBudget J (Fintype.card U / 2) ∨ IsSET J) :
    Odd ((A ⊔ B).degree z) ∧ Even (B.degree z) := by
  classical
  have hj : ∀ a b, A.Adj a b → a ∈ T → a = z := by
    intro a b hab hat
    have ha : a ∈ S ∩ T := ⟨hA ⟨b, hab⟩, hat⟩
    simpa only [hi, Set.mem_singleton_iff] using ha
  have hb : ∀ a b, B.Adj a b → a ∈ T := fun a b hab => hB ⟨b, hab⟩
  have ha : ∃ a b, A.Adj a b := by
    obtain ⟨w, hw⟩ := he.connection_adj
    exact ⟨z, w.val, hw⟩
  have reject : ¬ (Even ((A ⊔ B).degree z) ∨ Odd (B.degree z)) := by
    intro hparity
    obtain ⟨hct, hlt, hcapt⟩ := smaller_remainder_of_one_vertex_separation
      A B T z hconn hzT hb hj ha hparity 3 hcap
    have hr := hmin T (B.induce T) hlt hct hcapt
    have hp := joint_neighbor_of_one_vertex_separation A B T z hconn hzT hb hj hother
    exact hnot (hanging_eset_floor_of_alternative A B S T z hzS hzT hc hi hA hB he hp hr)
  exact ⟨Nat.not_even_iff_odd.mp (fun h => reject (Or.inl h)),
    Nat.not_odd_iff_even.mp (fun h => reject (Or.inr h))⟩

/-- Claim 1's full joint-parity conclusion under strictly smaller-edge minimality.
The singleton remainder is excluded by the ESET floor-or-SET boundary, not
by an extra nontriviality or carrier hypothesis. -/
theorem hanging_eset_joint_parity (S T : Set V)
    [DecidablePred (· ∈ S)] [DecidablePred (· ∈ T)]
    (z : V) (hzS : z ∈ S) (hzT : z ∈ T)
    (hc : S ∪ T = Set.univ) (hi : S ∩ T = {z})
    (hA : A.support ⊆ S) (hB : B.support ⊆ T)
    (he : IsESETAt (A.induce S) ⟨z, hzS⟩)
    (hconn : (A ⊔ B).Connected)
    (hcap : ∀ v, Even ((A ⊔ B).degree v) → eDegree (A ⊔ B) v ≤ 3)
    (hnot : ¬ HasPathBudget (A ⊔ B) (Fintype.card V / 2))
    (hset : ¬ IsSET (A ⊔ B))
    (hmin : ∀ (U : Set V) [DecidablePred (· ∈ U)]
      (J : SimpleGraph U) [DecidableRel J.Adj],
      J.edgeFinset.card < (A ⊔ B).edgeFinset.card → J.Connected →
      (∀ v, Even (J.degree v) → eDegree J v ≤ 3) →
      HasPathBudget J (Fintype.card U / 2) ∨ IsSET J) :
    Odd ((A ⊔ B).degree z) ∧ Even (B.degree z) := by
  classical
  have hother : ∃ v ∈ T, v ≠ z := by
    by_contra hn
    have ht : T ⊆ {z} := by
      intro v hv
      by_contra hne
      exact hn ⟨v, hv, hne⟩
    rcases hanging_eset_singleton_remainder A B S T z hzS hc hB ht he with h | h
    · exact hnot h
    · exact hset h
  exact hanging_eset_joint_parity_of_smaller A B S T z hzS hzT hc hi hA hB
    he hconn hother hcap hnot hmin

end Gallai
