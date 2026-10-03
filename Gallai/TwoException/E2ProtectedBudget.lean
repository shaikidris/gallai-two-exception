/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.ContactPunctureAssembly

@[expose] public section

/-! # Protected-endpoint E2 auxiliary budget -/
namespace Gallai.TwoException
open scoped Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
noncomputable local instance protectedE2StarAdj (u h : V) (S : Finset V) :
    DecidableRel (starPuncture G u (insert h S)).Adj :=
  fun _ _ => Classical.propDecidable _
noncomputable local instance protectedE2DeleteAdj (u h x q : V) (S : Finset V) :
    DecidableRel ((starPuncture G u (insert h S)).deleteEdges {s(x,q)}).Adj :=
  fun _ _ => Classical.propDecidable _

/-- E2 retains one double-petal contact instead of deleting its star edge.
The spoke deletion makes that contact odd, so the centre still has no even
neighbour and every auxiliary component has a floor budget. -/
theorem bare_windmill_E2_protected_floor
    (h : V) (x : evenVertices G) (H : BareMinimalCounterexample G h (x : V))
    (u : V)
    (f : {a : evenVertices G // (evenSubgraph G).Adj x a} →
      {a : evenVertices G // (evenSubgraph G).Adj x a})
    (P : Finset {a : evenVertices G // (evenSubgraph G).Adj x a})
    (hfree : ∀ a, f a ≠ a)
    (hindex : ∀ a, ∃! r, r ∈ P ∧ (a = r ∨ a = f r))
    (he : Even #(singleContactPetals f P (windmillContacts x u)))
    (p : {a : evenVertices G // (evenSubgraph G).Adj x a})
    (hp : p ∈ windmillContacts x u) (hq : f p ∈ windmillContacts x u)
    (huOdd : Odd (G.degree u)) (huh : G.Adj u h)
    (hcontacts : ∀ t, G.Adj u t → Even (G.degree t) →
      t = h ∨ t ∈ ambientWindmillContacts x u) :
    HasPathBudget ((starPuncture G u
      (insert h ((ambientWindmillContacts x u).erase (f p).val.val))).deleteEdges
      {s((x : V),(f p).val.val)}) (Fintype.card V / 2) := by
  classical
  let A := ambientWindmillContacts x u
  let S := A.erase (f p).val.val
  have hguard := bare_windmillPrivateSet_leaf_guards h x H (windmillContacts x u)
  have hstar := windmillPrivateSet_contact_guards x u (windmillContacts x u)
    (fun a ha => (Finset.mem_filter.mp ha).2)
  rcases H.counterexample.1 with ⟨hconn, hhx, _, hhEven, hxEven, hhzero, _⟩
  have hhA : h ∉ A := by
    intro ht
    have hd := (hguard h ht).2
    rw [hhzero] at hd
    omega
  have hhS : h ∉ S := fun ht => hhA (Finset.mem_of_mem_erase ht)
  have huS : u ∉ S := fun ht => hstar.1 (Finset.mem_of_mem_erase ht)
  have hxS : (x : V) ∉ S := fun ht =>
    hub_not_mem_windmillPrivateSet x (windmillContacts x u) (Finset.mem_of_mem_erase ht)
  have hqS : (f p).val.val ∉ S := Finset.notMem_erase _ _
  have hqA : (f p).val.val ∈ A :=
    (mem_windmillPrivateSet x (windmillContacts x u) _).mpr ⟨f p, hq, rfl⟩
  have hpA : p.val.val ∈ A :=
    (mem_windmillPrivateSet x (windmillContacts x u) _).mpr ⟨p, hp, rfl⟩
  have hpq : p.val.val ≠ (f p).val.val := by
    intro heq
    exact hfree p (Subtype.ext (Subtype.ext heq.symm))
  have hpS : p.val.val ∈ S := Finset.mem_erase.mpr ⟨hpq, hpA⟩
  have hodd : Odd #S :=
    (windmill_contact_row_parities x f hfree P (windmillContacts x u) hindex).2.1 he _ hqA
  have hxu : (x : V) ≠ u := by
    intro heq
    exact (Nat.not_even_iff_odd.mpr huOdd) (heq ▸ hxEven)
  have hqu : (f p).val.val ≠ u := by
    intro heq
    exact (Nat.not_even_iff_odd.mpr huOdd) (heq ▸ (f p).val.property)
  have hqdeg : eDegree G (f p).val.val = 2 := (hguard _ hqA).2
  have hqh : (f p).val.val ≠ h := by
    intro heq
    rw [heq, hhzero] at hqdeg
    omega
  have hadj : ∀ t ∈ S, G.Adj u t :=
    fun t ht => hstar.2 t (Finset.mem_of_mem_erase ht)
  have heven : ∀ t ∈ S, Even (G.degree t) :=
    fun t ht => (hguard t (Finset.mem_of_mem_erase ht)).1
  have huB : u ∉ insert h S := by simp [huh.ne, huS]
  have hxB : (x : V) ∉ insert h S := by simp [hhx.symm, hxS]
  have hqB : (f p).val.val ∉ insert h S := by simp [hqh, hqS]
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
  have hprof := contact_spoke_puncture_profile u x (f p).val.val (insert h S)
    huB hBAdj huOdd hBeven hBEven hxu hqu hxB hqB (f p).property
    hxEven (f p).val.property
  have hcap := bare_contact_spoke_puncture_cap h x H u h (f p).val.val S
    huS hhS huh.ne huOdd hhEven hodd huh hadj heven hxu hhx.symm hxS
    hqu hqh hqS (f p).property (f p).val.property
  have hcentre : eDegree ((starPuncture G u (insert h S)).deleteEdges
      {s((x : V),(f p).val.val)}) u = 0 := by
    apply eDegree_eq_zero_of_no_even_neighbor
    intro t hut htEven
    have htOrig := hprof.1 t htEven
    rcases hcontacts t hut.1.1 htOrig with ht | htA
    · subst t
      exact (starPuncture_missing G u (insert h S) huB h
        (Finset.mem_insert_self _ _)) hut.1
    · by_cases htq : t = (f p).val.val
      · subst t
        exact (Nat.not_even_iff_odd.mpr hprof.2.2) htEven
      · have htS : t ∈ S := Finset.mem_erase.mpr ⟨htq, htA⟩
        exact (starPuncture_missing G u (insert h S) huB t
          (Finset.mem_insert_of_mem htS)) hut.1
  have hpu : p.val.val ≠ u := by
    intro heq
    exact (Nat.not_even_iff_odd.mpr huOdd) (heq ▸ p.val.property)
  have hxp : ((starPuncture G u (insert h S)).deleteEdges
      {s((x : V),(f p).val.val)}).Adj x p.val.val := by
    apply SimpleGraph.deleteEdges_adj.mpr
    refine ⟨⟨p.property, ?_⟩, ?_⟩
    · intro ha
      exact hpu ((star_sup_adj_off_center u (insert h S) x p.val.val hxu).mp ha).2
    · intro ha
      have heq : s((x : V),p.val.val) = s((x : V),(f p).val.val) := by simpa using ha
      rcases Sym2.eq_iff.mp heq with heq | heq
      · exact hpq heq.2
      · exact (f p).property.ne (Subtype.ext heq.1)
  apply contact_spoke_floor_of_boundary_data hconn h u x (f p).val.val (insert h S)
    hprof.1 hcap hxEven hprof.2.1 hcentre hhzero (f p).property hqdeg
    ?_ p.val.val hxp p.property.symm (hguard _ hpA).2
  intro t ht
  rcases Finset.mem_insert.mp ht with ht | ht
  · exact Or.inl ht
  · obtain ⟨a, ha, rfl⟩ := (mem_windmillPrivateSet x (windmillContacts x u) t).mp
      (Finset.mem_of_mem_erase ht)
    exact Or.inr ⟨a.property.symm, (hguard _
      ((mem_windmillPrivateSet x (windmillContacts x u) _).mpr ⟨a, ha, rfl⟩)).2⟩

end Gallai.TwoException
