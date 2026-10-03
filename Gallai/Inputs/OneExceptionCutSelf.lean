/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.Inputs.OneExceptionCutEven
public import Gallai.Inputs.OneExceptionCutOdd
public import Gallai.Inputs.OneExceptionCutConnectivity

@[expose] public section

/-! # Complete even-vertex deletion claim for one-exception induction

The designated case uses strict induction in the even/even split and
floor-or-SET in the odd/odd split, including singleton-edge sides.
-/

namespace Gallai

universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

/-- A minimum counterexample remains connected after deleting its designated
vertex. Both split-degree parity cases use actual induced pieces. -/
theorem one_exception_delete_self_connected (G : SimpleGraph V)
    [DecidableRel G.Adj] (x : V) (hconn : G.Connected)
    (hxpos : 0 < G.degree x) (hxEven : Even (G.degree x))
    (hcap : ∀ v, Even (G.degree v) → v ≠ x → eDegree G v ≤ 3)
    (hnot : ¬ ∃ D : Decomposition G,
      D.size ≤ (Fintype.card V + 1) / 2 ∧ 2 ≤ D.endpointCount x)
    (hmin : ∀ (W : Type u) [Fintype W] [DecidableEq W]
      (J : SimpleGraph W) [DecidableRel J.Adj],
      J.edgeFinset.card < G.edgeFinset.card → J.Connected →
      ∀ y : W, 0 < J.degree y → Even (J.degree y) →
        (∀ v, Even (J.degree v) → v ≠ y → eDegree J v ≤ 3) →
        ∃ D : Decomposition J, D.size ≤ (Fintype.card W + 1) / 2 ∧
          2 ≤ D.endpointCount y) :
    (G.induce {v | v ≠ x}).Connected := by
  classical
  by_contra hn
  obtain ⟨a, b, ha, hb, hab⟩ := separated_vertices_of_disconnected_deletion G x
    ((G.degree_pos_iff_exists_adj x).mp hxpos) hn
  obtain ⟨S, T, hcover, hinter, haS, hbT, hg, _, _⟩ :=
    cut_vertex_pieces G hconn x a b ha hb hab
  have hx : x ∈ S ∩ T := by rw [hinter]; exact Set.mem_singleton x
  let A := (G.induce S).spanningCoe
  let B := (G.induce T).spanningCoe
  have hu : A ⊔ B = G := hg
  have hA : A.support ⊆ S := by
    rintro v ⟨w, hw⟩
    exact ((spanning_induce_adj_iff G S v w).mp hw).2.1
  have hB : B.support ⊆ T := by
    rintro v ⟨w, hw⟩
    exact ((spanning_induce_adj_iff G T v w).mp hw).2.1
  have hj (v : V) (hs : v ∈ S) (ht : v ∈ T) : v = x := by
    have h : v ∈ S ∩ T := ⟨hs, ht⟩
    simpa only [hinter, Set.mem_singleton_iff] using h
  have hm : ∀ w, (∃ a, A.Adj w a) → (∃ b, B.Adj w b) → w = x :=
    fun w ha hb => hj w (hA ha) (hB hb)
  have hdeg : (A ⊔ B).degree x = A.degree x + B.degree x := by
    have hdis : Disjoint (A.neighborFinset x) (B.neighborFinset x) := by
      apply Finset.disjoint_left.mpr
      intro w ha hb
      have ha' := (A.mem_neighborFinset x w).mp ha
      have hb' := (B.mem_neighborFinset x w).mp hb
      exact ha'.ne (hm w ⟨x, ha'.symm⟩ ⟨x, hb'.symm⟩).symm
    rw [← SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.neighborFinset_sup,
      Finset.card_union_of_disjoint hdis]
    rfl
  have hxe : Even ((A ⊔ B).degree x) := by
    simpa only [SimpleGraph.degree, SimpleGraph.neighborFinset,
      ← Set.ncard_eq_toFinset_card', hu] using hxEven
  have hce : ∀ v, Even ((A ⊔ B).degree v) → v ≠ x → eDegree (A ⊔ B) v ≤ 3 := by
    simpa only [SimpleGraph.degree, SimpleGraph.neighborFinset,
      ← Set.ncard_eq_toFinset_card', hu] using hcap
  have hc : (A ⊔ B).Connected := by rwa [hu]
  have hout : ∃ D : Decomposition (A ⊔ B),
      D.size ≤ (Fintype.card V + 1) / 2 ∧ 2 ≤ D.endpointCount x := by
    by_cases hea : Even (A.degree x)
    · have heb : Even (B.degree x) := by
        have he := hxe
        rw [Nat.even_iff, hdeg] at he
        rw [Nat.even_iff] at hea ⊢
        omega
      apply one_exception_cut_even A B S T x hx.1 hx.2 ⟨a, haS, ha⟩ ⟨b, hbT, hb⟩
        hcover hinter hA hB hc hea heb
        (by simpa only [SimpleGraph.degree, SimpleGraph.neighborFinset,
          ← Set.ncard_eq_toFinset_card'] using hxe)
        (by simpa only [SimpleGraph.degree, SimpleGraph.neighborFinset,
          ← Set.ncard_eq_toFinset_card'] using hce)
      intro W _ _ J _ hlt hcJ y hy he hcappy
      apply hmin W J ?_ hcJ y hy he hcappy
      simpa only [SimpleGraph.edgeFinset, ← Set.ncard_eq_toFinset_card', hu] using hlt
    · have hoa : Odd (A.degree x) := Nat.not_even_iff_odd.mp hea
      have hob : Odd (B.degree x) := by
        have he := hxe
        rw [Nat.even_iff, hdeg] at he
        rw [Nat.odd_iff] at hoa ⊢
        omega
      exact one_exception_cut_odd A B S T x hx.1 hx.2 hcover hinter hA hB hc hoa hob
        (by simpa only [SimpleGraph.degree, SimpleGraph.neighborFinset,
          ← Set.ncard_eq_toFinset_card'] using hxe)
        (by simpa only [SimpleGraph.degree, SimpleGraph.neighborFinset,
          ← Set.ncard_eq_toFinset_card'] using hce)
  rw [hu] at hout
  exact hnot hout

/-- Complete FHZ Claim 1 under the strict minimum-counterexample premise:
deleting any even vertex leaves a connected graph. -/
theorem one_exception_delete_even_connected (G : SimpleGraph V)
    [DecidableRel G.Adj] (x : V) (hconn : G.Connected)
    (hxpos : 0 < G.degree x) (hxEven : Even (G.degree x))
    (hcap : ∀ v, Even (G.degree v) → v ≠ x → eDegree G v ≤ 3)
    (hnot : ¬ ∃ D : Decomposition G,
      D.size ≤ (Fintype.card V + 1) / 2 ∧ 2 ≤ D.endpointCount x)
    (hmin : ∀ (W : Type u) [Fintype W] [DecidableEq W]
      (J : SimpleGraph W) [DecidableRel J.Adj],
      J.edgeFinset.card < G.edgeFinset.card → J.Connected →
      ∀ y : W, 0 < J.degree y → Even (J.degree y) →
        (∀ v, Even (J.degree v) → v ≠ y → eDegree J v ≤ 3) →
        ∃ D : Decomposition J, D.size ≤ (Fintype.card W + 1) / 2 ∧
          2 ≤ D.endpointCount y)
    (z : V) (hz : Even (G.degree z)) :
    (G.induce {v | v ≠ z}).Connected := by
  by_cases hzx : z = x
  · subst z
    exact one_exception_delete_self_connected G x hconn hxpos hxEven hcap hnot hmin
  · exact one_exception_delete_other_connected G x hconn hxpos hxEven hcap hnot hmin z hz hzx

end Gallai
