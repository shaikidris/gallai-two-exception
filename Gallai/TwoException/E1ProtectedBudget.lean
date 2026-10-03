/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.ContactPunctureAssembly

@[expose] public section

/-! # Native protected-endpoint E1 puncture budget -/
namespace Gallai.TwoException
open scoped Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable local instance protectedE1StarAdj (u h : V) (S : Finset V) :
    DecidableRel (starPuncture G u (insert h S)).Adj :=
  fun _ _ => Classical.propDecidable _
noncomputable local instance protectedE1DeleteAdj (u h x q : V) (S : Finset V) :
    DecidableRel ((starPuncture G u (insert h S)).deleteEdges {s(x,q)}).Adj :=
  fun _ _ => Classical.propDecidable _

/-- In the E1 branch with reserved endpoint h and no contacts to other
even components, the actual auxiliary has a floor decomposition. Its
component budgets, parity and retained spoke are derived from native data. -/
theorem bare_windmill_E1_protected_floor
    (h : V) (x : evenVertices G) (H : BareMinimalCounterexample G h (x : V))
    (u : V)
    (f : {a : evenVertices G // (evenSubgraph G).Adj x a} →
      {a : evenVertices G // (evenSubgraph G).Adj x a})
    (P : Finset {a : evenVertices G // (evenSubgraph G).Adj x a})
    (hfree : ∀ a, f a ≠ a)
    (hindex : ∀ a, ∃! r, r ∈ P ∧ (a = r ∨ a = f r))
    (ho : Odd #(singleContactPetals f P (windmillContacts x u)))
    (p : {a : evenVertices G // (evenSubgraph G).Adj x a})
    (hp : p ∈ windmillContacts x u) (hnq : f p ∉ windmillContacts x u)
    (huOdd : Odd (G.degree u)) (huh : G.Adj u h)
    (hcontacts : ∀ t, G.Adj u t → Even (G.degree t) →
      t = h ∨ t ∈ ambientWindmillContacts x u) :
    HasPathBudget ((starPuncture G u (insert h (ambientWindmillContacts x u))).deleteEdges
      {s((x : V),(f p).val.val)}) (Fintype.card V / 2) := by
  classical
  let S := ambientWindmillContacts x u
  have hcapS := bare_windmillPrivateSet_leaf_guards h x H (windmillContacts x u)
  have hstar := windmillPrivateSet_contact_guards x u (windmillContacts x u)
    (fun a ha => (Finset.mem_filter.mp ha).2)
  rcases H.counterexample.1 with ⟨hconn, hhx, _, hhEven, hxEven, hhzero, _⟩
  have hhS : h ∉ S := by
    intro ht
    have hd := (hcapS h ht).2
    rw [hhzero] at hd
    omega
  have hxu : (x : V) ≠ u := by
    intro he
    exact (Nat.not_even_iff_odd.mpr huOdd) (he ▸ hxEven)
  have hqu : (f p).val.val ≠ u := by
    intro he
    exact (Nat.not_even_iff_odd.mpr huOdd) (he ▸ (f p).val.property)
  have hqS : (f p).val.val ∉ S := by
    intro ht
    obtain ⟨a, ha, he⟩ := (mem_windmillPrivateSet x (windmillContacts x u) _).mp ht
    have heq : a = f p := Subtype.ext (Subtype.ext he)
    exact hnq (heq ▸ ha)
  have hqdeg : eDegree G (f p).val.val = 2 :=
    (bare_windmillPrivateSet_leaf_guards h x H {f p} (f p).val.val
      ((mem_windmillPrivateSet x {f p} _).mpr ⟨f p, by simp, rfl⟩)).2
  have hqh : (f p).val.val ≠ h := by
    intro he
    rw [he, hhzero] at hqdeg
    omega
  have huS : u ∉ S := hstar.1
  have hxS : (x : V) ∉ S := hub_not_mem_windmillPrivateSet x (windmillContacts x u)
  have huB : u ∉ insert h S := by simp [huh.ne, huS]
  have hxB : (x : V) ∉ insert h S := by simp [hhx.symm, hxS]
  have hqB : (f p).val.val ∉ insert h S := by simp [hqh, hqS]
  have hSodd : Odd #S :=
    (windmill_contact_row_parities x f hfree P (windmillContacts x u) hindex).1 ho
  have hBeven : Even #(insert h S) := by
    rw [Finset.card_insert_of_notMem hhS]
    rw [Nat.odd_iff] at hSodd
    rw [Nat.even_iff]
    omega
  have hBAdj : ∀ t ∈ insert h S, G.Adj u t := by
    intro t ht
    rcases Finset.mem_insert.mp ht with rfl | ht
    · exact huh
    · exact hstar.2 t ht
  have hBEven : ∀ t ∈ insert h S, Even (G.degree t) := by
    intro t ht
    rcases Finset.mem_insert.mp ht with rfl | ht
    · exact hhEven
    · exact (hcapS t ht).1
  have hprof := contact_spoke_puncture_profile u x (f p).val.val (insert h S)
    huB hBAdj huOdd hBeven hBEven hxu hqu hxB hqB (f p).property
    hxEven (f p).val.property
  have hcap := bare_windmill_E1_protected_puncture_cap h x H u f P hfree
    hindex ho p hnq huOdd huh
  have hcentre : eDegree ((starPuncture G u (insert h S)).deleteEdges
      {s((x : V),(f p).val.val)}) u = 0 := by
    have hsub : (starPuncture G u (insert h S)).deleteEdges
        {s((x : V),(f p).val.val)} ≤ starPuncture G u (insert h S) :=
      fun _ _ ha => ha.1
    apply contact_puncture_center_eDegree_zero u (insert h S) huB
      hsub hprof.1
    intro t hut htEven
    exact Finset.mem_insert.mpr (hcontacts t hut htEven)
  have hpq : p.val.val ≠ (f p).val.val := by
    intro he
    have heq : p = f p := Subtype.ext (Subtype.ext he)
    exact hnq (heq ▸ hp)
  have hpu : p.val.val ≠ u := by
    intro he
    exact (Nat.not_even_iff_odd.mpr huOdd) (he ▸ p.val.property)
  have hxp : ((starPuncture G u (insert h S)).deleteEdges
      {s((x : V),(f p).val.val)}).Adj x p.val.val := by
    apply SimpleGraph.deleteEdges_adj.mpr
    refine ⟨⟨p.property, ?_⟩, ?_⟩
    · intro ha
      exact hpu ((star_sup_adj_off_center u (insert h S) x p.val.val hxu).mp ha).2
    · intro ha
      have he : s((x : V),p.val.val) = s((x : V),(f p).val.val) := by simpa using ha
      rcases Sym2.eq_iff.mp he with he | he
      · exact hpq he.2
      · exact (f p).property.ne (Subtype.ext he.1)
  apply contact_spoke_floor_of_boundary_data hconn h u x (f p).val.val (insert h S)
    hprof.1 hcap hxEven hprof.2.1 hcentre hhzero (f p).property hqdeg
    ?_ p.val.val hxp p.property.symm
    (bare_windmillPrivateSet_leaf_guards h x H {p} p.val.val
      ((mem_windmillPrivateSet x {p} _).mpr ⟨p, by simp, rfl⟩)).2
  intro t ht
  rcases Finset.mem_insert.mp ht with ht | ht
  · exact Or.inl ht
  · obtain ⟨a, ha, rfl⟩ := (mem_windmillPrivateSet x (windmillContacts x u) t).mp ht
    exact Or.inr ⟨a.property.symm, (hcapS _ ((mem_windmillPrivateSet x
      (windmillContacts x u) _).mpr ⟨a, ha, rfl⟩)).2⟩

end Gallai.TwoException
