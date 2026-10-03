/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.BareLongE3OrdinaryRestore

@[expose] public section

/-! # Completing the ordinary side after any long-contact row -/
namespace Gallai.TwoException
open scoped Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
noncomputable local instance longOrdinaryRestoreAdj (Q : SimpleGraph V) : DecidableRel Q.Adj :=
  fun _ _ => Classical.propDecidable _

/-- The same prepared ordinary family completes once the first-side row
has exposed v. All mates and then the entire ordinary star restore without
adding paths; the prescribed vertex keeps its endpoint reserve. -/
theorem bare_long_restore_ordinary_preparation
    (h v : V) (x : evenVertices G) (H : BareMinimalCounterexample G h (x : V))
    (hvOdd : Odd (G.degree v)) (C : (evenSubgraph G).ConnectedComponent)
    (B : Finset V) (O : List (V × V))
    (hB : ∀ t ∈ B, G.Adj v t ∧ Even (G.degree t) ∧ t ≠ h ∧ t ∉ Subtype.val '' C.supp)
    (hdis : O.Pairwise (fun e f => e.1 ≠ f.1 ∧ e.1 ≠ f.2 ∧ e.2 ≠ f.1 ∧ e.2 ≠ f.2))
    (hO : ∀ e ∈ O, G.Adj e.1 e.2 ∧ Even (G.degree e.1) ∧ Even (G.degree e.2) ∧
      e.1 ∉ B ∧ e.2 ∉ B ∧ h ≠ e.1 ∧ h ≠ e.2 ∧
      e.1 ∉ Subtype.val '' C.supp ∧ e.2 ∉ Subtype.val '' C.supp)
    (hvcontacts : ∀ t, G.Adj v t → Even (G.degree t) → t ≠ h →
      t ∈ B ∨ ∃ e ∈ O, t = e.1 ∨ t = e.2)
    (hpacket : ∀ e ∈ O, ∃ (Z : (evenSubgraph G).ConnectedComponent)
      (a b c : evenVertices G), e = ((b : V),(c : V)) ∧ Z.supp = {a,b,c} ∧ (a : V) ∈ B)
    (R : OrdinaryRegularPacketData G h x v B O)
    (D : Decomposition (ordinaryMatePuncture (starPuncture G v B) O))
    (hDv : 0 < D.endpointCount v) (hDh : 2 ≤ D.endpointCount h) :
    ∃ E : Decomposition G, E.size = D.size ∧ 2 ≤ E.endpointCount h := by
  classical
  have hadj := fun t ht => (hB t ht).1
  have heven := fun t ht => (hB t ht).2.1
  have hedges : ∀ e ∈ O, G.Adj e.1 e.2 ∧ Even (G.degree e.1) ∧ Even (G.degree e.2) :=
    fun e he => ⟨(hO e he).1,(hO e he).2.1,(hO e he).2.2.1⟩
  have havoid : ∀ e ∈ O, e.1 ≠ v ∧ e.2 ≠ v ∧ e.1 ∉ B ∧ e.2 ∉ B := by
    intro e he
    have hn := Nat.not_even_iff_odd.mpr hvOdd
    exact ⟨fun hh => hn (hh ▸ (hedges e he).2.1),fun hh => hn (hh ▸ (hedges e he).2.2),
      (hO e he).2.2.2.1,(hO e he).2.2.2.2.1⟩
  obtain ⟨F,hFD,hFv,hrec,hkeep⟩ := restore_ordinary_mate_family v B hadj heven O
    hdis havoid hedges hpacket D (Or.inl hDv)
  have hFh : F.endpointCount h = D.endpointCount h :=
    hkeep h (fun e he => ⟨(hO e he).2.2.2.2.2.1,(hO e he).2.2.2.2.2.2.1⟩)
  have hpositive : ∀ t, (starPuncture G v B).Adj v t ∨ t ∈ B →
      0 < F.endpointCount t := by
    intro t ht
    by_cases htB : t ∈ B
    · have hd := starPuncture_degree_leaf (G := G) v B t htB (hadj t htB)
      have he := heven t htB
      have ho : Odd ((starPuncture G v B).degree t) := by
        simp only [← SimpleGraph.ncard_neighborSet] at hd he ⊢
        rw [Nat.even_iff] at he
        rw [Nat.odd_iff]
        omega
      exact F.endpointCount_pos_of_odd_degree t ho
    · have hvAdj : G.Adj v t := (ht.resolve_right htB).1
      by_cases htEven : Even (G.degree t)
      · by_cases hth : t = h
        · subst t; omega
        · rcases hvcontacts t hvAdj htEven hth with htB' | ⟨e,he,hends⟩
          · exact False.elim (htB htB')
          · rcases hends with rfl | rfl
            · have hr := hrec e he; omega
            · exact False.elim (R.donor_avoid e he hvAdj)
      · have hd := starPuncture_degree_other (G := G) v B t hvAdj.ne.symm htB
        have ho := Nat.not_even_iff_odd.mp htEven
        have ho' : Odd ((starPuncture G v B).degree t) := by
          simp only [← SimpleGraph.ncard_neighborSet] at hd ho ⊢
          rwa [hd]
        exact F.endpointCount_pos_of_odd_degree t ho'
  obtain ⟨E,hEF,hkeepE⟩ := bare_ordinary_regular_star_restore h x H v B O R
    hadj heven F (by omega) hrec hpositive
  have hhv : h ≠ v := fun hh => (Nat.not_even_iff_odd.mpr hvOdd)
    (hh ▸ H.counterexample.1.2.2.2.1)
  have hhB : h ∉ B := fun ht => (hB h ht).2.2.1 rfl
  refine ⟨E,hEF.trans hFD,?_⟩
  rw [hkeepE h hhv hhB,hFh]
  exact hDh

end Gallai.TwoException
