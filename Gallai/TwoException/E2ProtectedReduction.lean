/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.E2ProtectedBudget
public import Gallai.TwoException.ContactE2Reserved

@[expose] public section

/-! # The native protected-endpoint E2 reduction -/
namespace Gallai.TwoException
open scoped Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
noncomputable local instance reductionE2StarAdj (u h : V) (S : Finset V) :
    DecidableRel (starPuncture G u (insert h S)).Adj :=
  fun _ _ => Classical.propDecidable _
noncomputable local instance reductionE2DeleteAdj (u h x q : V) (S : Finset V) :
    DecidableRel ((starPuncture G u (insert h S)).deleteEdges {s(x,q)}).Adj :=
  fun _ _ => Classical.propDecidable _

/-- The double-petal protected E2 branch is reducible without a supplied
decomposition or endpoint reserve. -/
theorem bare_windmill_E2_protected_false
    (h : V) (x : evenVertices G) (H : BareMinimalCounterexample G h (x : V))
    (u : V)
    (f : {a : evenVertices G // (evenSubgraph G).Adj x a} →
      {a : evenVertices G // (evenSubgraph G).Adj x a})
    (P : Finset {a : evenVertices G // (evenSubgraph G).Adj x a})
    (hinv : Function.Involutive f) (hfree : ∀ a, f a ≠ a)
    (hindex : ∀ a, ∃! r, r ∈ P ∧ (a = r ∨ a = f r))
    (hedge : ∀ a b, (evenSubgraph G).Adj a.val b.val ↔ f a = b)
    (he : Even #(singleContactPetals f P (windmillContacts x u)))
    (p : {a : evenVertices G // (evenSubgraph G).Adj x a})
    (hp : p ∈ windmillContacts x u) (hq : f p ∈ windmillContacts x u)
    (huOdd : Odd (G.degree u)) (huh : G.Adj u h)
    (hcontacts : ∀ t, G.Adj u t → Even (G.degree t) →
      t = h ∨ t ∈ ambientWindmillContacts x u) : False := by
  classical
  obtain ⟨D, hDsize⟩ := bare_windmill_E2_protected_floor h x H u f P hfree hindex
    he p hp hq huOdd huh hcontacts
  let A := ambientWindmillContacts x u
  let S := A.erase (f p).val.val
  have hguard := bare_windmillPrivateSet_leaf_guards h x H (windmillContacts x u)
  have hstar := windmillPrivateSet_contact_guards x u (windmillContacts x u)
    (fun a ha => (Finset.mem_filter.mp ha).2)
  rcases H.counterexample.1 with ⟨_, hhx, _, hhEven, hxEven, hhzero, _⟩
  have hnil : evenNeighbors G h = ∅ := Finset.card_eq_zero.mp hhzero
  have hno : ∀ t, G.Adj h t → Even (G.degree t) → False := by
    intro t hht htEven
    have hm := (mem_evenNeighbors (G := G) h t).mpr ⟨hht, htEven⟩
    simpa [hnil] using hm
  have hvx : ¬ G.Adj h x := fun ha => hno x ha hxEven
  have hhA : h ∉ A := by
    intro hs
    obtain ⟨a, _, ha⟩ := (mem_windmillPrivateSet x (windmillContacts x u) h).mp hs
    exact hvx (ha ▸ a.property.symm)
  have hxA : (x : V) ∉ A := hub_not_mem_windmillPrivateSet x (windmillContacts x u)
  have hhS : h ∉ S := fun ht => hhA (Finset.mem_of_mem_erase ht)
  have huS : u ∉ S := fun ht => hstar.1 (Finset.mem_of_mem_erase ht)
  have hxS : (x : V) ∉ S := fun ht => hxA (Finset.mem_of_mem_erase ht)
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
  have hqh : (f p).val.val ≠ h := by
    intro heq
    exact hvx (heq ▸ (f p).property.symm)
  have hqv : ¬ G.Adj (f p).val.val h :=
    fun ha => hno _ ha.symm (f p).val.property
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
  have hhOdd := contact_spoke_puncture_leaf_odd u x (f p).val.val h (insert h S)
    (by simp) huh hhEven hhx hqh.symm
  have hDh : 0 < D.endpointCount h := D.endpointCount_pos_of_odd_degree h hhOdd
  have hux : ¬ G.Adj u x := by
    intro ha
    rcases hcontacts x ha hxEven with ht | ht
    · exact hhx ht.symm
    · exact hxA ht
  have hretained : ∀ t, G.Adj u t → t ∉ S → t ≠ (f p).val.val →
      Odd (G.degree t) ∨ 0 < D.endpointCount t := by
    intro t hut htS htq
    by_cases htEven : Even (G.degree t)
    · rcases hcontacts t hut htEven with ht | htA
      · subst t
        exact Or.inr hDh
      · exact False.elim (htS (Finset.mem_erase.mpr ⟨htq, htA⟩))
    · exact Or.inl (Nat.not_even_iff_odd.mp htEven)
  have hvpositive : ∀ t, (starPuncture G u (insert h S)).Adj h t →
      0 < D.endpointCount t := by
    intro t ht
    apply D.endpointCount_pos_of_odd_degree
    apply Nat.not_even_iff_odd.mp
    intro htEven
    exact hno t ht.1 (hprof.1 t htEven)
  obtain ⟨F, hFsize, _, hFh⟩ := restore_contact_E2_reserved_endpoint
    u h x p.val.val (f p).val.val S huS hhS huh.ne huOdd hodd huh hadj heven hpS
    (fun t ht _ => (hguard t (Finset.mem_of_mem_erase ht)).2.le)
    (fun t ht ha => hno t ha (heven t ht)) hxu hhx.symm hxS hqu hqh hqS
    (f p).property hxEven (f p).val.property hqv
    (by
      intro t ht htEven
      simpa only [hinv p] using
        bare_windmill_private_even_neighbors h x H f hedge (f p) t ht htEven)
    hvx hux D hretained hvpositive
  apply H.counterexample.2
  refine ⟨F, ?_, ?_⟩
  · have hs : F.size ≤ Fintype.card V / 2 := hFsize.le.trans hDsize
    omega
  · rw [hFh]
    omega

end Gallai.TwoException
