/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.BareLongPreparation
public import Gallai.TwoException.OrdinaryStarMateCap

@[expose] public section

/-! # Transport through the second endpoint's ordinary preparation -/
namespace Gallai.TwoException
open scoped Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
noncomputable local instance longTransportAdj (Q : SimpleGraph V) : DecidableRel Q.Adj :=
  fun _ _ => Classical.propDecidable _

/-- A vertex outside the preparation support retains its degree and all
incident adjacencies. This applies to the windmill and protected vertex. -/
theorem long_ordinary_preparation_unchanged
    (v w : V) (B : Finset V) (M : List (V × V))
    (hwv : w ≠ v) (hwB : w ∉ B)
    (hwM : ∀ e ∈ M, w ≠ e.1 ∧ w ≠ e.2) :
    (ordinaryMatePuncture (starPuncture G v B) M).degree w = G.degree w ∧
      ∀ t, (ordinaryMatePuncture (starPuncture G v B) M).Adj w t ↔ G.Adj w t := by
  classical
  constructor
  · have hm := ordinaryMatePuncture_degree_of_avoids (G := starPuncture G v B) M w hwM
    have hs := starPuncture_degree_other (G := G) v B w hwv hwB
    simp only [← SimpleGraph.ncard_neighborSet] at hm hs ⊢
    exact hm.trans hs
  · intro t
    rw [ordinaryMatePuncture_adj_of_avoids M w t hwM]
    change (G.Adj w t ∧ ¬ (B.sup (SimpleGraph.edge v)).Adj w t) ↔ G.Adj w t
    refine ⟨And.left,fun ht => ⟨ht,?_⟩⟩
    intro hstar
    exact hwB ((star_sup_adj_off_center v B w t hwv).mp hstar).1

/-- Original parity and actual support separation derive the unchanged
windmill, without assuming its parity in the prepared graph. -/
theorem long_ordinary_preparation_windmill_unchanged
    (v : V) (hvOdd : Odd (G.degree v))
    (C : (evenSubgraph G).ConnectedComponent) (B : Finset V) (M : List (V × V))
    (hB : ∀ t ∈ B, t ∉ Subtype.val '' C.supp)
    (hM : ∀ e ∈ M, e.1 ∉ Subtype.val '' C.supp ∧ e.2 ∉ Subtype.val '' C.supp) :
    ∀ w ∈ Subtype.val '' C.supp,
      (ordinaryMatePuncture (starPuncture G v B) M).degree w = G.degree w ∧
        ∀ t, (ordinaryMatePuncture (starPuncture G v B) M).Adj w t ↔ G.Adj w t := by
  classical
  intro w hw
  have hwC : w ∈ Subtype.val '' C.supp := hw
  obtain ⟨a,_,haw⟩ := hw
  have hwEven : Even (G.degree w) := haw ▸ a.property
  have hwv : w ≠ v := by
    intro heq
    exact (Nat.not_even_iff_odd.mpr hvOdd) (heq ▸ hwEven)
  apply long_ordinary_preparation_unchanged (G := G) v w B M hwv
  · exact fun ht => hB w ht hwC
  · intro e he
    exact ⟨fun hh => (hM e he).1 (hh ▸ hwC),
      fun hh => (hM e he).2 (hh ▸ hwC)⟩

/-- Even-ended ordinary deletions preserve an originally odd reserved
edge and the degree of its first endpoint. The second endpoint loses exactly
the selected star, followed by the reserved edge. -/
theorem long_ordinary_preparation_reserved_degree
    (u v : V) (B : Finset V) (M : List (V × V))
    (huOdd : Odd (G.degree u)) (hvOdd : Odd (G.degree v)) (huv : G.Adj u v)
    (hB : ∀ t ∈ B, G.Adj v t ∧ Even (G.degree t))
    (hM : ∀ e ∈ M, Even (G.degree e.1) ∧ Even (G.degree e.2)) :
    let Q := ordinaryMatePuncture (starPuncture G v B) M
    Q.Adj u v ∧ Q.degree u = G.degree u ∧
      (Q.deleteEdges {s(u,v)}).degree v + #B + 1 = G.degree v := by
  classical
  let Q := ordinaryMatePuncture (starPuncture G v B) M
  have hoddAway : ∀ w, Odd (G.degree w) →
      w ∉ B ∧ ∀ e ∈ M, w ≠ e.1 ∧ w ≠ e.2 := by
    intro w hw
    have hn := Nat.not_even_iff_odd.mpr hw
    constructor
    · intro ht
      exact hn (hB w ht).2
    · intro e he
      exact ⟨fun hh => hn (hh ▸ (hM e he).1),
        fun hh => hn (hh ▸ (hM e he).2)⟩
  obtain ⟨huB,huM⟩ := hoddAway u huOdd
  obtain ⟨hvB,hvM⟩ := hoddAway v hvOdd
  obtain ⟨hdu,hau⟩ := long_ordinary_preparation_unchanged (G := G) v u B M huv.ne huB huM
  have hQ : Q.Adj u v := (hau v).mpr huv
  have hdm := ordinaryMatePuncture_degree_of_avoids (G := starPuncture G v B) M v hvM
  have hds := starPuncture_degree_center (G := G) v B hvB
    (fun t ht => (G.mem_neighborFinset v t).mpr (hB t ht).1)
  have hde := degree_delete_edge_add_one_other Q u v hQ
  refine ⟨hQ,hdu,?_⟩
  simp only [← SimpleGraph.ncard_neighborSet] at hdm hds hde ⊢
  dsimp only [Q] at hdm hde ⊢
  omega

/-- The prepared second endpoint, with the reserved edge absent, has the
same parity as its selected ordinary star. This is the exact supply used
after the first-side restoration increases its endpoint count by one. -/
theorem long_ordinary_preparation_reserved_parity
    (u v : V) (B : Finset V) (M : List (V × V))
    (huOdd : Odd (G.degree u)) (hvOdd : Odd (G.degree v)) (huv : G.Adj u v)
    (hB : ∀ t ∈ B, G.Adj v t ∧ Even (G.degree t))
    (hM : ∀ e ∈ M, Even (G.degree e.1) ∧ Even (G.degree e.2)) :
    let J := (ordinaryMatePuncture (starPuncture G v B) M).deleteEdges {s(u,v)}
    (Even (J.degree v) ↔ Even #B) ∧ (Odd (J.degree v) ↔ Odd #B) := by
  classical
  have hd := (long_ordinary_preparation_reserved_degree u v B M huOdd hvOdd huv hB hM).2.2
  rw [Nat.odd_iff] at hvOdd
  constructor
  · rw [Nat.even_iff,Nat.even_iff]
    omega
  · rw [Nat.odd_iff,Nat.odd_iff]
    omega

end Gallai.TwoException
