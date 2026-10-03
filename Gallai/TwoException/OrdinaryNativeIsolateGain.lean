/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.OrdinaryNativeTriangleGain

@[expose] public section

/-! # Native endpoint contribution of an isolated even contact -/
namespace Gallai.TwoException
open scoped Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
noncomputable local instance isolateGainHalfAdj (G : SimpleGraph V) (u : V) (B A : Finset V) :
    DecidableRel ((starPuncture G u B) ⊔ A.sup (SimpleGraph.edge u)).Adj :=
  fun _ _ => Classical.propDecidable _

/-- An originally isolated even contact has no passing neighbour while
its spoke is pending, so a tight failure must select that contact. -/
theorem ordinary_native_isolate_gain
    (u a : V) (B A : Finset V) (hAB : A ⊆ B)
    (hadj : ∀ t ∈ B, G.Adj u t) (hleaves : ∀ t ∈ B, Even (G.degree t))
    (haB : a ∈ B) (hisolate : ∀ t, G.Adj a t → ¬ Even (G.degree t))
    (E : Decomposition ((starPuncture G u B) ⊔ A.sup (SimpleGraph.edge u)))
    (htight : ∀ w ∈ B \ A, passingNeighborCount E w = 2) :
    #({a} \ A) + 1 ≤ #({a} ∩ A) := by
  classical
  have heq := ordinary_half_star_graph u B A hAB hadj
  have hp := ordinary_half_star_even_preserved u B A hAB hadj hleaves
  have hsub : (starPuncture G u B ⊔ A.sup (SimpleGraph.edge u)) ≤ G := by
    rw [heq]
    exact fun _ _ ha => ha.1
  have haA : a ∈ A := by
    by_contra haA
    have ht := Finset.mem_sdiff.mpr ⟨haB, haA⟩
    have hu : u ∉ B \ A := fun hu => G.irrefl (hadj u (Finset.mem_sdiff.mp hu).1)
    have hmissing : ¬ (starPuncture G u B ⊔ A.sup (SimpleGraph.edge u)).Adj a u := by
      rw [heq]
      exact fun ha => starPuncture_missing G u (B \ A) hu a ht ha.symm
    have hempty : {t ∈ (starPuncture G u B ⊔ A.sup (SimpleGraph.edge u)).neighborFinset a |
        E.endpointCount t = 0} = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro t hmem
      obtain ⟨htN, htZero⟩ := Finset.mem_filter.mp hmem
      have hat := (SimpleGraph.mem_neighborFinset _ a t).mp htN
      have htEven : Even ((starPuncture G u B ⊔ A.sup (SimpleGraph.edge u)).degree t) := by
        rcases Nat.even_or_odd ((starPuncture G u B ⊔ A.sup (SimpleGraph.edge u)).degree t) with he | ho
        · exact he
        · have hpos := E.endpointCount_pos_of_odd_degree t ho
          omega
      rcases hp t htEven with he | htu
      · exact hisolate t (hsub hat) he
      · subst t
        exact hmissing hat
    have hzero : passingNeighborCount E a = 0 := by
      change #{t ∈ (starPuncture G u B ⊔ A.sup (SimpleGraph.edge u)).neighborFinset a |
        E.endpointCount t = 0} = 0
      rw [hempty]
      rfl
    have htwo := htight a ht
    omega
  simp [haA]

end Gallai.TwoException
