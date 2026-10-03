/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.E4ProtectedBudget
public import Gallai.TwoException.ContactE4Reserved

@[expose] public section

/-! # Protected E4 reduction with graph-derived endpoint reserves -/
namespace Gallai.TwoException
open scoped Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
noncomputable local instance reductionE4StarAdj (u h : V) (S : Finset V) :
    DecidableRel (starPuncture G u (insert h S)).Adj :=
  fun _ _ => Classical.propDecidable _
noncomputable local instance reductionE4DeleteAdj (u h p q : V) (S : Finset V) :
    DecidableRel ((starPuncture G u (insert h S)).deleteEdges {s(q,p)}).Adj :=
  fun _ _ => Classical.propDecidable _

/-- The protected E4 branch supplies its decomposition and every endpoint
reserve, restores the mate and contact star, and exposes h within budget. -/
theorem bare_windmill_E4_protected_false
    (h : V) (x : evenVertices G) (H : BareMinimalCounterexample G h (x : V))
    (u : V)
    (f : {a : evenVertices G // (evenSubgraph G).Adj x a} →
      {a : evenVertices G // (evenSubgraph G).Adj x a})
    (P : Finset {a : evenVertices G // (evenSubgraph G).Adj x a})
    (hfree : ∀ a, f a ≠ a)
    (hindex : ∀ a, ∃! r, r ∈ P ∧ (a = r ∨ a = f r))
    (hedge : ∀ a b, (evenSubgraph G).Adj a.val b.val ↔ f a = b)
    (ho : Odd #(singleContactPetals f P (windmillContacts x u)))
    (p : {a : evenVertices G // (evenSubgraph G).Adj x a})
    (hpA : p ∈ windmillContacts x u) (hqA : f p ∉ windmillContacts x u)
    (huOdd : Odd (G.degree u)) (huh : G.Adj u h) (hux : G.Adj u x)
    (hcontacts : ∀ t, G.Adj u t → Even (G.degree t) →
      t = h ∨ t = (x : V) ∨ t ∈ ambientWindmillContacts x u) : False := by
  classical
  obtain ⟨D, hDsize⟩ := bare_windmill_E4_protected_floor h x H u f P hfree hindex
    hedge ho p hpA hqA huOdd huh hux hcontacts
  let A := ambientWindmillContacts x u
  let S := insert (x : V) (A.erase p.val.val)
  have hguard := bare_windmillPrivateSet_leaf_guards h x H (windmillContacts x u)
  have hstar := windmillPrivateSet_contact_guards x u (windmillContacts x u)
    (fun a ha => (Finset.mem_filter.mp ha).2)
  rcases H.counterexample.1 with ⟨_, hhx, _, hhEven, hxEven, hhzero, _⟩
  have hnil : evenNeighbors G h = ∅ := Finset.card_eq_zero.mp hhzero
  have hno : ∀ t, G.Adj h t → Even (G.degree t) → False := by
    intro t ha ht
    have hm := (mem_evenNeighbors (G := G) h t).mpr ⟨ha, ht⟩
    simpa [hnil] using hm
  have hpB : p.val.val ∈ A :=
    (mem_windmillPrivateSet x (windmillContacts x u) _).mpr ⟨p, hpA, rfl⟩
  have hqB : (f p).val.val ∉ A := by
    intro ht
    obtain ⟨a, ha, heq⟩ := (mem_windmillPrivateSet x (windmillContacts x u) _).mp ht
    have hae : a = f p := Subtype.ext (Subtype.ext heq)
    exact hqA (hae ▸ ha)
  have hph : p.val.val ≠ h := fun heq => hno x (heq ▸ p.property.symm) hxEven
  have hqh : (f p).val.val ≠ h :=
    fun heq => hno x (heq ▸ (f p).property.symm) hxEven
  have hpx : p.val.val ≠ (x : V) := by
    intro heq
    exact p.property.ne (Subtype.ext heq.symm)
  have hqx : (f p).val.val ≠ (x : V) := by
    intro heq
    exact (f p).property.ne (Subtype.ext heq.symm)
  have hpu : p.val.val ≠ u := by
    intro heq
    exact (Nat.not_even_iff_odd.mpr huOdd) (heq ▸ p.val.property)
  have hqu : (f p).val.val ≠ u := by
    intro heq
    exact (Nat.not_even_iff_odd.mpr huOdd) (heq ▸ (f p).val.property)
  have hpS : p.val.val ∉ S := by simp [S, hpx]
  have hqS : (f p).val.val ∉ S := by
    simp only [S, Finset.mem_insert, not_or]
    exact ⟨hqx, fun ht => hqB (Finset.mem_of_mem_erase ht)⟩
  have hhA : h ∉ A := by
    intro ht
    have hd := (hguard h ht).2
    rw [hhzero] at hd
    omega
  have hhS : h ∉ S := by simp [S, hhx, hhA]
  have huS : u ∉ S := by
    simp only [S, Finset.mem_insert, not_or]
    exact ⟨hux.ne, fun ht => hstar.1 (Finset.mem_of_mem_erase ht)⟩
  have hodd : Odd #S :=
    (windmill_contact_row_parities x f hfree P (windmillContacts x u) hindex).2.2.2 ho _ hpB
  have hadj : ∀ t ∈ S, G.Adj u t := by
    intro t ht
    rcases Finset.mem_insert.mp ht with rfl | ht
    · exact hux
    · exact hstar.2 t (Finset.mem_of_mem_erase ht)
  have heven : ∀ t ∈ S, Even (G.degree t) := by
    intro t ht
    rcases Finset.mem_insert.mp ht with rfl | ht
    · exact hxEven
    · exact (hguard t (Finset.mem_of_mem_erase ht)).1
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
  have hprof := contact_spoke_puncture_profile u (f p).val.val p.val.val (insert h S)
    huB hBAdj huOdd hBeven hBEven hqu hpu
    (by simp [hqh, hqS]) (by simp [hph, hpS])
    ((hedge p (f p)).mpr rfl).symm (f p).val.property p.val.property
  have hhOdd := contact_spoke_puncture_leaf_odd u (f p).val.val p.val.val h (insert h S)
    (by simp) huh hhEven hqh.symm hph.symm
  have hDh : 0 < D.endpointCount h := D.endpointCount_pos_of_odd_degree h hhOdd
  have hretained : ∀ t, G.Adj u t → t ∉ S → t ≠ p.val.val →
      Odd (G.degree t) ∨ 0 < D.endpointCount t := by
    intro t hut htS htp
    by_cases htEven : Even (G.degree t)
    · rcases hcontacts t hut htEven with ht | ht | htA
      · subst t
        exact Or.inr hDh
      · exact False.elim (htS (Finset.mem_insert.mpr (Or.inl ht)))
      · exact False.elim (htS (Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨htp, htA⟩)))
    · exact Or.inl (Nat.not_even_iff_odd.mp htEven)
  have hvpositive : ∀ t, (starPuncture G u (insert h S)).Adj h t →
      0 < D.endpointCount t := by
    intro t ht
    apply D.endpointCount_pos_of_odd_degree
    apply Nat.not_even_iff_odd.mp
    intro htEven
    exact hno t ht.1 (hprof.1 t htEven)
  obtain ⟨F, hFsize, _, hFh⟩ := restore_contact_E4_reserved_endpoint
    u h x p.val.val (f p).val.val S huS hhS huh.ne huOdd hodd huh hadj heven
    (Finset.mem_insert_self _ _)
    (by
      intro t ht htx
      exact (hguard t (Finset.mem_of_mem_erase
        ((Finset.mem_insert.mp ht).resolve_left htx))).2.le)
    (fun t ht ha => hno t ha (heven t ht))
    hqu hqh hqS hpu hph hpS ((hedge p (f p)).mpr rfl).symm
    (f p).val.property p.val.property
    (fun ha => hno _ ha.symm p.val.property)
    (bare_windmill_private_even_neighbors h x H f hedge p)
    (fun ha => hno _ ha (f p).val.property)
    (fun ha => hqA (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha⟩))
    D hretained hvpositive
  apply H.counterexample.2
  refine ⟨F, ?_, ?_⟩
  · have hs : F.size ≤ Fintype.card V / 2 := hFsize.le.trans hDsize
    omega
  · rw [hFh]
    omega

end Gallai.TwoException
