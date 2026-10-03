/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.BareLongE3Restore
public import Gallai.TwoException.OrdinarySequentialRestoration

@[expose] public section

/-! # Restoring the ordinary mates in the native E3 construction -/
namespace Gallai.TwoException
open scoped Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
noncomputable local instance longE3OrdinaryAdj (Q : SimpleGraph V) : DecidableRel Q.Adj :=
  fun _ _ => Classical.propDecidable _

/-- Restore every ordinary mate in the same preparation used by the E3
budget and first-side restoration. Only the ordinary contact star remains
deleted. Its centre is positive, every mate recipient has two endpoints,
and the prescribed vertex retains its two endpoints within the ceiling. -/
theorem bare_long_E3_ordinary_mates_endpoint
    (h u v : V) (x : evenVertices G) (H : BareMinimalCounterexample G h (x : V))
    (C : (evenSubgraph G).ConnectedComponent) (hxC : x ∈ C.supp)
    (huOdd : Odd (G.degree u)) (hvOdd : Odd (G.degree v)) (huv : G.Adj u v)
    (hsep : ∀ t ∈ Subtype.val '' C.supp, ¬ G.Adj v t)
    (S : Finset V) (hxS : (x : V) ∈ S) (hhS : h ∉ S) (hSodd : Odd #S)
    (hS : ∀ t ∈ S, G.Adj u t ∧ t ∈ Subtype.val '' C.supp)
    (hcontacts : ∀ t, G.Adj u t → Even (G.degree t) → t ∈ S) :
    ∃ B : Finset V, ∃ O : List (V × V),
      (∀ t ∈ B, G.Adj v t ∧ Even (G.degree t) ∧ t ≠ h ∧
        t ∉ Subtype.val '' C.supp) ∧
      (∀ e ∈ O, G.Adj e.1 e.2 ∧ Even (G.degree e.1) ∧ Even (G.degree e.2) ∧
        e.1 ∉ B ∧ e.2 ∉ B ∧ h ≠ e.1 ∧ h ≠ e.2 ∧
        e.1 ∉ Subtype.val '' C.supp ∧ e.2 ∉ Subtype.val '' C.supp) ∧
      (∀ t, G.Adj v t → Even (G.degree t) → t ≠ h →
        t ∈ B ∨ ∃ e ∈ O, t = e.1 ∨ t = e.2) ∧
      (∀ e ∈ O, ∃ (Z : (evenSubgraph G).ConnectedComponent)
        (a b c : evenVertices G), e = ((b : V),(c : V)) ∧
        Z.supp = {a,b,c} ∧ (a : V) ∈ B) ∧
      Nonempty (OrdinaryRegularPacketData G h x v B O) ∧
      ∃ E : Decomposition (starPuncture G v B),
        E.size ≤ (Fintype.card V + 1) / 2 ∧ 1 ≤ E.endpointCount u ∧
        1 ≤ E.endpointCount v ∧ 2 ≤ E.endpointCount h ∧
        ∀ e ∈ O, 2 ≤ E.endpointCount e.1 := by
  classical
  obtain ⟨B,O,hB,hdis,hO,hvcontacts,hpacket,hmeta,D,hsize,hDu,hDv,hDh⟩ :=
    bare_long_E3_prepared_endpoint h u v x H C hxC huOdd hvOdd huv
      hsep S hxS hhS hSodd hS hcontacts
  have hedges : ∀ e ∈ O, G.Adj e.1 e.2 ∧
      Even (G.degree e.1) ∧ Even (G.degree e.2) :=
    fun e he => ⟨(hO e he).1,(hO e he).2.1,(hO e he).2.2.1⟩
  have havoid : ∀ e ∈ O, e.1 ≠ v ∧ e.2 ≠ v ∧ e.1 ∉ B ∧ e.2 ∉ B := by
    intro e he
    have hn := Nat.not_even_iff_odd.mpr hvOdd
    exact ⟨fun hh => hn (hh ▸ (hedges e he).2.1),
      fun hh => hn (hh ▸ (hedges e he).2.2),
      (hO e he).2.2.2.1,(hO e he).2.2.2.2.1⟩
  obtain ⟨E,hsizeE,hEv,hrec,hkeep⟩ := restore_ordinary_mate_family v B
    (fun t ht => (hB t ht).1) (fun t ht => (hB t ht).2.1) O hdis
    havoid hedges hpacket D (Or.inl (by omega))
  have hEu : E.endpointCount u = D.endpointCount u := by
    apply hkeep
    intro e he
    have hn := Nat.not_even_iff_odd.mpr huOdd
    exact ⟨fun hh => hn (hh.symm ▸ (hedges e he).2.1),
      fun hh => hn (hh.symm ▸ (hedges e he).2.2)⟩
  have hEh : E.endpointCount h = D.endpointCount h := by
    apply hkeep
    intro e he
    exact ⟨(hO e he).2.2.2.2.2.1,(hO e he).2.2.2.2.2.2.1⟩
  refine ⟨B,O,hB,hO,hvcontacts,hpacket,hmeta,E,?_,?_,?_,?_,hrec⟩
  · rw [hsizeE]; exact hsize
  · rw [hEu]; exact hDu
  · rw [hEv]; exact hDv
  · rw [hEh]; exact hDh

/-- Complete E3 reconstruction: the native joint budget, both contact
sides and every prepared mate yield a decomposition of the original graph
at the ceiling, with the prescribed vertex h exposed twice. -/
theorem bare_long_E3_endpoint
    (h u v : V) (x : evenVertices G) (H : BareMinimalCounterexample G h (x : V))
    (C : (evenSubgraph G).ConnectedComponent) (hxC : x ∈ C.supp)
    (huOdd : Odd (G.degree u)) (hvOdd : Odd (G.degree v)) (huv : G.Adj u v)
    (hsep : ∀ t ∈ Subtype.val '' C.supp, ¬ G.Adj v t)
    (S : Finset V) (hxS : (x : V) ∈ S) (hhS : h ∉ S) (hSodd : Odd #S)
    (hS : ∀ t ∈ S, G.Adj u t ∧ t ∈ Subtype.val '' C.supp)
    (hcontacts : ∀ t, G.Adj u t → Even (G.degree t) → t ∈ S) :
    ∃ D : Decomposition G, D.size ≤ (Fintype.card V + 1) / 2 ∧
      2 ≤ D.endpointCount h := by
  classical
  obtain ⟨B,O,hB,hO,hvcontacts,_,⟨R⟩,D,hsize,_,hDv,hDh,hrec⟩ :=
    bare_long_E3_ordinary_mates_endpoint h u v x H C hxC huOdd hvOdd huv
      hsep S hxS hhS hSodd hS hcontacts
  have hadj := fun t ht => (hB t ht).1
  have heven := fun t ht => (hB t ht).2.1
  have hpositive : ∀ t, (starPuncture G v B).Adj v t ∨ t ∈ B →
      0 < D.endpointCount t := by
    intro t ht
    by_cases htB : t ∈ B
    · have hd := starPuncture_degree_leaf (G := G) v B t htB (hadj t htB)
      have he := heven t htB
      have ho : Odd ((starPuncture G v B).degree t) := by
        simp only [← SimpleGraph.ncard_neighborSet] at hd he ⊢
        rw [Nat.even_iff] at he
        rw [Nat.odd_iff]
        omega
      exact D.endpointCount_pos_of_odd_degree t ho
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
        exact D.endpointCount_pos_of_odd_degree t ho'
  obtain ⟨E,hED,hkeep⟩ := bare_ordinary_regular_star_restore h x H v B O R
    hadj heven D (by omega) hrec hpositive
  have hhv : h ≠ v := fun hh => (Nat.not_even_iff_odd.mpr hvOdd)
    (hh ▸ H.counterexample.1.2.2.2.1)
  have hhB : h ∉ B := fun ht => (hB h ht).2.2.1 rfl
  refine ⟨E,?_,?_⟩
  · rw [hED]; exact hsize
  · rw [hkeep h hhv hhB]; exact hDh

end Gallai.TwoException
