/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.E1ProtectedBudget
public import Gallai.TwoException.ContactE1Reserved

@[expose] public section

/-! # The protected-endpoint E1 counterexample reduction -/
namespace Gallai.TwoException
open scoped Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable local instance reductionE1StarAdj (u h : V) (S : Finset V) :
    DecidableRel (starPuncture G u (insert h S)).Adj :=
  fun _ _ => Classical.propDecidable _
noncomputable local instance reductionE1DeleteAdj (u h x q : V) (S : Finset V) :
    DecidableRel ((starPuncture G u (insert h S)).deleteEdges {s(x,q)}).Adj :=
  fun _ _ => Classical.propDecidable _

/-- E1 with reserved endpoint h and no other even-component contact is
reducible. The initial decomposition and every restoration reserve are
constructed from the original graph; none is supplied as a certificate. -/
theorem bare_windmill_E1_protected_false
    (h : V) (x : evenVertices G) (H : BareMinimalCounterexample G h (x : V))
    (u : V)
    (f : {a : evenVertices G // (evenSubgraph G).Adj x a} →
      {a : evenVertices G // (evenSubgraph G).Adj x a})
    (P : Finset {a : evenVertices G // (evenSubgraph G).Adj x a})
    (hinv : Function.Involutive f) (hfree : ∀ a, f a ≠ a)
    (hindex : ∀ a, ∃! r, r ∈ P ∧ (a = r ∨ a = f r))
    (hedge : ∀ a b, (evenSubgraph G).Adj a.val b.val ↔ f a = b)
    (ho : Odd #(singleContactPetals f P (windmillContacts x u)))
    (p : {a : evenVertices G // (evenSubgraph G).Adj x a})
    (hp : p ∈ windmillContacts x u) (hnq : f p ∉ windmillContacts x u)
    (huOdd : Odd (G.degree u)) (huh : G.Adj u h)
    (hcontacts : ∀ t, G.Adj u t → Even (G.degree t) →
      t = h ∨ t ∈ ambientWindmillContacts x u) : False := by
  classical
  obtain ⟨D, hDsize⟩ := bare_windmill_E1_protected_floor h x H u f P hfree hindex
    ho p hp hnq huOdd huh hcontacts
  let S := ambientWindmillContacts x u
  have hcap := bare_windmillPrivateSet_leaf_guards h x H (windmillContacts x u)
  have hstar := windmillPrivateSet_contact_guards x u (windmillContacts x u)
    (fun a ha => (Finset.mem_filter.mp ha).2)
  rcases H.counterexample.1 with ⟨_, hhx, _, hhEven, hxEven, hhzero, _⟩
  have hnil : evenNeighbors G h = ∅ := by
    apply Finset.card_eq_zero.mp
    exact hhzero
  have hno : ∀ t, G.Adj h t → Even (G.degree t) → False := by
    intro t hht htEven
    have hm := (mem_evenNeighbors (G := G) h t).mpr ⟨hht, htEven⟩
    simpa [hnil] using hm
  have hvx : ¬ G.Adj h x := fun ha => hno x ha hxEven
  have hhS : h ∉ S := by
    intro hs
    obtain ⟨a, _, ha⟩ := (mem_windmillPrivateSet x (windmillContacts x u) h).mp hs
    exact hvx (ha ▸ a.property.symm)
  have hxS : (x : V) ∉ S := hub_not_mem_windmillPrivateSet x (windmillContacts x u)
  have huS : u ∉ S := hstar.1
  have hpS : p.val.val ∈ S :=
    (mem_windmillPrivateSet x (windmillContacts x u) _).mpr ⟨p, hp, rfl⟩
  have hodd : Odd #S :=
    (windmill_contact_row_parities x f hfree P (windmillContacts x u) hindex).1 ho
  have hxu : (x : V) ≠ u := by
    intro he
    exact (Nat.not_even_iff_odd.mpr huOdd) (he ▸ hxEven)
  have hqu : ¬ G.Adj (f p).val.val u := by
    intro ha
    exact hnq (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha.symm⟩)
  have hqv : ¬ G.Adj (f p).val.val h :=
    fun ha => hno _ ha.symm (f p).val.property
  have hqune : (f p).val.val ≠ u := by
    intro he
    exact (Nat.not_even_iff_odd.mpr huOdd) (he ▸ (f p).val.property)
  have hqh : (f p).val.val ≠ h := by
    intro he
    exact hvx (he ▸ (f p).property.symm)
  have hqS : (f p).val.val ∉ S := by
    intro hs
    obtain ⟨a, ha, he⟩ := (mem_windmillPrivateSet x (windmillContacts x u) _).mp hs
    have heq : a = f p := Subtype.ext (Subtype.ext he)
    exact hnq (heq ▸ ha)
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
    · exact hstar.2 t ht
  have hBEven : ∀ t ∈ insert h S, Even (G.degree t) := by
    intro t ht
    rcases Finset.mem_insert.mp ht with rfl | ht
    · exact hhEven
    · exact (hcap t ht).1
  have hprof := contact_spoke_puncture_profile u x (f p).val.val (insert h S)
    huB hBAdj huOdd hBeven hBEven hxu hqune hxB hqB (f p).property
    hxEven (f p).val.property
  have hhOdd := contact_spoke_puncture_leaf_odd u x (f p).val.val h (insert h S)
    (by simp) huh hhEven hhx hqh.symm
  have hDh : 0 < D.endpointCount h := D.endpointCount_pos_of_odd_degree h hhOdd
  have hux : ¬ G.Adj u x := by
    intro ha
    rcases hcontacts x ha hxEven with he | hs
    · exact hhx he.symm
    · exact hxS hs
  have hretained : ∀ t, G.Adj u t → t ∉ S →
      Odd (G.degree t) ∨ 0 < D.endpointCount t := by
    intro t hut htS
    by_cases htEven : Even (G.degree t)
    · rcases hcontacts t hut htEven with he | hs
      · subst t
        exact Or.inr hDh
      · exact False.elim (htS hs)
    · exact Or.inl (Nat.not_even_iff_odd.mp htEven)
  have hvpositive : ∀ t, (starPuncture G u (insert h S)).Adj h t →
      0 < D.endpointCount t := by
    intro t ht
    apply D.endpointCount_pos_of_odd_degree
    apply Nat.not_even_iff_odd.mp
    intro htEven
    exact hno t ht.1 (hprof.1 t htEven)
  obtain ⟨F, hFsize, _, hFh⟩ := restore_contact_E1_reserved_endpoint
    u h x p.val.val (f p).val.val p.val.val S huS hhS huh.ne huOdd hodd huh
    hstar.2 (fun t ht => (hcap t ht).1) hpS hpS
    (fun t ht _ => (hcap t ht).2.le)
    (by
      intro t ht ha
      exact hno t ha (hcap t ht).1)
    hxu hhx.symm hxS hqu hqv hqune hqh (f p).property hxEven
    (by
      intro t ht he
      simpa only [hinv p] using
        bare_windmill_private_even_neighbors h x H f hedge (f p) t ht he)
    hvx hux D hretained hvpositive
  apply H.counterexample.2
  refine ⟨F, ?_, ?_⟩
  · have hs : F.size ≤ Fintype.card V / 2 := hFsize.le.trans hDsize
    omega
  · rw [hFh]
    omega

end Gallai.TwoException
