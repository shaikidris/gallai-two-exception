/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.ContactStarAssembly
public import Gallai.TwoException.ContactE3

@[expose] public section

/-! # The native E3 auxiliary with reserved endpoint h -/
namespace Gallai.TwoException
open scoped Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
noncomputable local instance protectedE3StarAdj (u : V) (B : Finset V) :
    DecidableRel (starPuncture G u B).Adj := fun _ _ => Classical.propDecidable _

/-- E3's hub-inclusive contact star supplies a floor budget when the
reserved endpoint is h and no other even component is contacted. -/
theorem bare_windmill_E3_protected_floor
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
      t = h ∨ t = (x : V) ∨ t ∈ ambientWindmillContacts x u) :
    HasPathBudget (starPuncture G u
      (insert h (insert (x : V) (ambientWindmillContacts x u))))
      (Fintype.card V / 2) := by
  classical
  let A := ambientWindmillContacts x u
  let S := insert (x : V) A
  let B := insert h S
  have hguard := bare_windmillPrivateSet_leaf_guards h x H (windmillContacts x u)
  have hstar := windmillPrivateSet_contact_guards x u (windmillContacts x u)
    (fun a ha => (Finset.mem_filter.mp ha).2)
  rcases H.counterexample.1 with ⟨hconn, hhx, _, hhEven, hxEven, hhzero, hcapG⟩
  have hhA : h ∉ A := by
    intro ht
    have hd := (hguard h ht).2
    rw [hhzero] at hd
    omega
  have huA : u ∉ A := hstar.1
  have huxne : u ≠ (x : V) := hux.ne
  have hhS : h ∉ S := by simp [S, hhx, hhA]
  have huS : u ∉ S := by simp [S, huxne, huA]
  have huB : u ∉ B := by simp [B, huh.ne, huS]
  have hSodd : Odd #S :=
    (windmill_contact_row_parities x f hfree P (windmillContacts x u) hindex).2.2.1 he
  have hBeven : Even #B := by
    dsimp only [B]
    rw [Finset.card_insert_of_notMem hhS]
    rw [Nat.odd_iff] at hSodd
    rw [Nat.even_iff]
    omega
  have hBAdj : ∀ t ∈ B, G.Adj u t := by
    intro t ht
    rcases Finset.mem_insert.mp ht with rfl | ht
    · exact huh
    · rcases Finset.mem_insert.mp ht with rfl | ht
      · exact hux
      · exact hstar.2 t ht
  have hBEven : ∀ t ∈ B, Even (G.degree t) := by
    intro t ht
    rcases Finset.mem_insert.mp ht with rfl | ht
    · exact hhEven
    · rcases Finset.mem_insert.mp ht with rfl | ht
      · exact hxEven
      · exact (hguard t ht).1
  have hkeep := even_star_at_odd_center_even_preserved u B huB hBAdj huOdd hBeven hBEven
  have hxB : (x : V) ∈ B := Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  have hxOdd := contact_star_leaf_odd u x B hxB hux hxEven
  have hsub : starPuncture G u B ≤ G := fun _ _ ha => ha.1
  have hcap : ∀ t, Even ((starPuncture G u B).degree t) →
      eDegree (starPuncture G u B) t ≤ 3 := by
    have hmono := eDegree_le_of_subgraph_of_even_preservation hsub hkeep
    intro t ht
    have htx : t ≠ (x : V) := by
      intro heq
      subst t
      exact (Nat.not_even_iff_odd.mpr hxOdd) ht
    by_cases hth : t = h
    · subst t
      have hm := hmono h
      rw [hhzero] at hm
      omega
    · exact (hmono t).trans (hcapG t (hkeep t ht) hth htx)
  have hcentre : eDegree (starPuncture G u B) u = 0 := by
    apply contact_puncture_center_eDegree_zero u B huB le_rfl hkeep
    intro t hut htEven
    rcases hcontacts t hut htEven with heq | heq | htA
    · exact Finset.mem_insert.mpr (Or.inl heq)
    · exact Finset.mem_insert_of_mem (Finset.mem_insert.mpr (Or.inl heq))
    · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem htA)
  have hxpos : 0 < #(evenNeighbors G x) := by
    have hlarge := H.counterexample.exception_gt_three
    change 3 < #(evenNeighbors G x) at hlarge
    omega
  obtain ⟨p, hp⟩ := Finset.card_pos.mp hxpos
  obtain ⟨hxp, hpEven⟩ := (mem_evenNeighbors (G := G) x p).mp hp
  let a : {a : evenVertices G // (evenSubgraph G).Adj x a} := ⟨⟨p, hpEven⟩, hxp⟩
  have hpdeg : eDegree G p = 2 :=
    (bare_windmillPrivateSet_leaf_guards h x H {a} p
      ((mem_windmillPrivateSet x {a} p).mpr ⟨a, by simp, rfl⟩)).2
  have hpu : p ≠ u := by
    intro heq
    exact (Nat.not_even_iff_odd.mpr huOdd) (heq ▸ hpEven)
  have hxpJ : (starPuncture G u B).Adj x p := by
    refine ⟨hxp, ?_⟩
    intro ha
    exact hpu ((star_sup_adj_off_center u B x p huxne.symm).mp ha).2
  apply contact_star_floor_of_boundary_data hconn h u x B hkeep hcap hxEven hxOdd
    hcentre hhzero ?_ p hxpJ hxp.symm hpdeg
  intro t ht
  rcases Finset.mem_insert.mp ht with heq | ht
  · exact Or.inr (Or.inl heq)
  · rcases Finset.mem_insert.mp ht with heq | ht
    · exact Or.inl heq
    · obtain ⟨a, ha, rfl⟩ := (mem_windmillPrivateSet x (windmillContacts x u) t).mp ht
      exact Or.inr (Or.inr ⟨a.property.symm, (hguard _
        ((mem_windmillPrivateSet x (windmillContacts x u) _).mpr ⟨a, ha, rfl⟩)).2⟩)

end Gallai.TwoException
