/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.E3ProtectedBudget

@[expose] public section

/-! # Native E3 reduction with prescribed reserved endpoint -/
namespace Gallai.TwoException
open scoped Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
noncomputable local instance reductionE3StarAdj (u : V) (B : Finset V) :
    DecidableRel (starPuncture G u B).Adj := fun _ _ => Classical.propDecidable _

/-- The protected E3 branch supplies its own decomposition and endpoint
reserves, then restores the hub-inclusive contact star within budget. -/
theorem bare_windmill_E3_protected_false
    (h : V) (x : evenVertices G) (H : BareMinimalCounterexample G h (x : V))
    (u : V)
    (f : {a : evenVertices G // (evenSubgraph G).Adj x a} →
      {a : evenVertices G // (evenSubgraph G).Adj x a})
    (P : Finset {a : evenVertices G // (evenSubgraph G).Adj x a})
    (hfree : ∀ a, f a ≠ a)
    (hindex : ∀ a, ∃! r, r ∈ P ∧ (a = r ∨ a = f r))
    (he : Even #(singleContactPetals f P (windmillContacts x u)))
    (huOdd : Odd (G.degree u)) (huh : G.Adj u h) (hux : G.Adj u x)
    (hcontacts : ∀ t, G.Adj u t → Even (G.degree t) →
      t = h ∨ t = (x : V) ∨ t ∈ ambientWindmillContacts x u) : False := by
  classical
  obtain ⟨D, hDsize⟩ := bare_windmill_E3_protected_floor h x H u f P hfree hindex
    he huOdd huh hux hcontacts
  let A := ambientWindmillContacts x u
  let S := insert (x : V) A
  have hguard := bare_windmillPrivateSet_leaf_guards h x H (windmillContacts x u)
  have hstar := windmillPrivateSet_contact_guards x u (windmillContacts x u)
    (fun a ha => (Finset.mem_filter.mp ha).2)
  rcases H.counterexample.1 with ⟨_, hhx, _, hhEven, hxEven, hhzero, _⟩
  have hnil : evenNeighbors G h = ∅ := Finset.card_eq_zero.mp hhzero
  have hno : ∀ t, G.Adj h t → Even (G.degree t) → False := by
    intro t hht htEven
    have hm := (mem_evenNeighbors (G := G) h t).mpr ⟨hht, htEven⟩
    simpa [hnil] using hm
  have hhA : h ∉ A := by
    intro hs
    have hd := (hguard h hs).2
    rw [hhzero] at hd
    omega
  have huA : u ∉ A := hstar.1
  have huS : u ∉ S := by simp [S, hux.ne, huA]
  have hhS : h ∉ S := by simp [S, hhx, hhA]
  have hodd : Odd #S :=
    (windmill_contact_row_parities x f hfree P (windmillContacts x u) hindex).2.2.1 he
  have hadj : ∀ t ∈ S, G.Adj u t := by
    intro t ht
    rcases Finset.mem_insert.mp ht with rfl | ht
    · exact hux
    · exact hstar.2 t ht
  have heven : ∀ t ∈ S, Even (G.degree t) := by
    intro t ht
    rcases Finset.mem_insert.mp ht with rfl | ht
    · exact hxEven
    · exact (hguard t ht).1
  have huB : u ∉ insert h S := by simp [huh.ne, huS]
  have hBeven : Even #(insert h S) := by
    rw [Finset.card_insert_of_notMem hhS]
    rw [Nat.odd_iff] at hodd
    rw [Nat.even_iff]
    omega
  have hBAdj : ∀ t ∈ insert h S, G.Adj u t := by
    intro t ht
    rcases Finset.mem_insert.mp ht with rfl | ht
    · exact huh
    · exact hadj t ht
  have hBEven : ∀ t ∈ insert h S, Even (G.degree t) := by
    intro t ht
    rcases Finset.mem_insert.mp ht with rfl | ht
    · exact hhEven
    · exact heven t ht
  have hkeep := even_star_at_odd_center_even_preserved u (insert h S)
    huB hBAdj huOdd hBeven hBEven
  have hhOdd := contact_star_leaf_odd u h (insert h S) (by simp) huh hhEven
  have hDh : 0 < D.endpointCount h := D.endpointCount_pos_of_odd_degree h hhOdd
  have hretained : ∀ t, G.Adj u t → t ∉ S →
      Odd (G.degree t) ∨ 0 < D.endpointCount t := by
    intro t hut htS
    by_cases htEven : Even (G.degree t)
    · rcases hcontacts t hut htEven with ht | ht | ht
      · subst t
        exact Or.inr hDh
      · exact False.elim (htS (Finset.mem_insert.mpr (Or.inl ht)))
      · exact False.elim (htS (Finset.mem_insert_of_mem ht))
    · exact Or.inl (Nat.not_even_iff_odd.mp htEven)
  have hvpositive : ∀ t, (starPuncture G u (insert h S)).Adj h t →
      0 < D.endpointCount t := by
    intro t ht
    apply D.endpointCount_pos_of_odd_degree
    apply Nat.not_even_iff_odd.mp
    intro htEven
    exact hno t ht.1 (hkeep t htEven)
  obtain ⟨F, hFsize, _, hFh, _⟩ := restore_contact_E3_with_retained_reserves
    u h x S huS hhS huh.ne huOdd hodd huh hadj heven
    (Finset.mem_insert_self _ _)
    (by
      intro t ht htx
      exact (hguard t ((Finset.mem_insert.mp ht).resolve_left htx)).2.le)
    (fun t ht ha => hno t ha (heven t ht)) D hretained hvpositive
  apply H.counterexample.2
  refine ⟨F, ?_, ?_⟩
  · have hs : F.size ≤ Fintype.card V / 2 := hFsize.le.trans hDsize
    omega
  · rw [hFh]
    omega

end Gallai.TwoException
