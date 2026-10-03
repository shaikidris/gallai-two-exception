/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.ContactMateBudget
public import Gallai.TwoException.WindmillContactE4

@[expose] public section

/-! # Native protected E4 mate-puncture budget -/
namespace Gallai.TwoException
open scoped Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
noncomputable local instance protectedE4StarAdj (u h x p : V) (A : Finset V) :
    DecidableRel (starPuncture G u (insert h (insert x (A.erase p)))).Adj :=
  fun _ _ => Classical.propDecidable _
noncomputable local instance protectedE4DeleteAdj (u h x p q : V) (A : Finset V) :
    DecidableRel ((starPuncture G u (insert h (insert x (A.erase p)))).deleteEdges
      {s(q,p)}).Adj := fun _ _ => Classical.propDecidable _

/-- Retain a singly contacted private, delete its mate edge, and delete the
hub-inclusive contact star with reserved endpoint h. The native petal data
supplies every premise of the mate-puncture floor budget. -/
theorem bare_windmill_E4_protected_floor
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
      t = h ∨ t = (x : V) ∨ t ∈ ambientWindmillContacts x u) :
    HasPathBudget ((starPuncture G u (insert h
      (insert (x : V) ((ambientWindmillContacts x u).erase p.val.val)))).deleteEdges
      {s((f p).val.val,p.val.val)}) (Fintype.card V / 2) := by
  classical
  let A := ambientWindmillContacts x u
  let S := insert (x : V) (A.erase p.val.val)
  let B := insert h S
  have hguard := bare_windmillPrivateSet_leaf_guards h x H (windmillContacts x u)
  have hstar := windmillPrivateSet_contact_guards x u (windmillContacts x u)
    (fun a ha => (Finset.mem_filter.mp ha).2)
  rcases H.counterexample.1 with ⟨_, hhx, _, hhEven, hxEven, hhzero, _⟩
  have hpB : p.val.val ∈ A :=
    (mem_windmillPrivateSet x (windmillContacts x u) _).mpr ⟨p, hpA, rfl⟩
  have hqB : (f p).val.val ∉ A := by
    intro ht
    obtain ⟨a, ha, heq⟩ := (mem_windmillPrivateSet x (windmillContacts x u) _).mp ht
    have hae : a = f p := Subtype.ext (Subtype.ext heq)
    exact hqA (hae ▸ ha)
  have hpdeg : eDegree G p.val.val = 2 := (hguard _ hpB).2
  have hqdeg : eDegree G (f p).val.val = 2 := by
    exact (bare_windmillPrivateSet_leaf_guards h x H {f p} _
      ((mem_windmillPrivateSet x {f p} _).mpr ⟨f p, by simp, rfl⟩)).2
  have hph : p.val.val ≠ h := by
    intro heq
    rw [heq, hhzero] at hpdeg
    omega
  have hqh : (f p).val.val ≠ h := by
    intro heq
    rw [heq, hhzero] at hqdeg
    omega
  have hpxne : p.val.val ≠ (x : V) := by
    intro heq
    exact p.property.ne (Subtype.ext heq.symm)
  have hqxne : (f p).val.val ≠ (x : V) := by
    intro heq
    exact (f p).property.ne (Subtype.ext heq.symm)
  have hpu : p.val.val ≠ u := by
    intro heq
    exact (Nat.not_even_iff_odd.mpr huOdd) (heq ▸ p.val.property)
  have hqu : (f p).val.val ≠ u := by
    intro heq
    exact (Nat.not_even_iff_odd.mpr huOdd) (heq ▸ (f p).val.property)
  have hpqne : p.val.val ≠ (f p).val.val := by
    intro heq
    exact hfree p (Subtype.ext (Subtype.ext heq.symm))
  have hhA : h ∉ A := by
    intro ht
    have hd := (hguard h ht).2
    rw [hhzero] at hd
    omega
  have hhS : h ∉ S := by simp [S, hhx, hhA]
  have huS : u ∉ S := by
    simp only [S, Finset.mem_insert, not_or]
    exact ⟨hux.ne, fun ht => hstar.1 (Finset.mem_of_mem_erase ht)⟩
  have huB : u ∉ B := by simp [B, huh.ne, huS]
  have hpnotB : p.val.val ∉ B := by simp [B, S, hph, hpxne]
  have hqnotB : (f p).val.val ∉ B := by
    simp only [B, S, Finset.mem_insert, not_or]
    exact ⟨hqh, hqxne, fun ht => hqB (Finset.mem_of_mem_erase ht)⟩
  have hodd : Odd #S :=
    (windmill_contact_row_parities x f hfree P (windmillContacts x u) hindex).2.2.2 ho _ hpB
  have hBeven : Even #B := by
    dsimp only [B]
    rw [Finset.card_insert_of_notMem hhS]
    rw [Nat.odd_iff] at hodd
    rw [Nat.even_iff]
    omega
  have hBAdj : ∀ t ∈ B, G.Adj u t := by
    intro t ht
    rcases Finset.mem_insert.mp ht with rfl | ht
    · exact huh
    · rcases Finset.mem_insert.mp ht with rfl | ht
      · exact hux
      · exact hstar.2 t (Finset.mem_of_mem_erase ht)
  have hBEven : ∀ t ∈ B, Even (G.degree t) := by
    intro t ht
    rcases Finset.mem_insert.mp ht with rfl | ht
    · exact hhEven
    · rcases Finset.mem_insert.mp ht with rfl | ht
      · exact hxEven
      · exact (hguard t (Finset.mem_of_mem_erase ht)).1
  have hxp : ((starPuncture G u B).deleteEdges
      {s((f p).val.val,p.val.val)}).Adj x p.val.val := by
    apply SimpleGraph.deleteEdges_adj.mpr
    refine ⟨⟨p.property, ?_⟩, ?_⟩
    · intro ha
      exact hpu ((star_sup_adj_off_center u B x p.val.val hux.ne.symm).mp ha).2
    · intro ha
      have heq : s((x : V),p.val.val) = s((f p).val.val,p.val.val) := by simpa using ha
      rcases Sym2.eq_iff.mp heq with heq | heq
      · exact hqxne heq.1.symm
      · exact hpxne heq.1.symm
  apply bare_contact_mate_floor h x H u (f p).val.val p.val.val B huB hBAdj huOdd
    hBeven hBEven (by simp [B, S]) hqxne.symm hpxne.symm hqu hpu hqnotB hpnotB
    ((hedge p (f p)).mpr rfl).symm (f p).val.property p.val.property
    (f p).property.symm hqdeg p.property.symm hpdeg ?_ ?_ p.val.val hxp p.property.symm hpdeg
  · intro t hut htEven
    rcases hcontacts t hut htEven with ht | ht | htA
    · exact Or.inl (Finset.mem_insert.mpr (Or.inl ht))
    · exact Or.inl (Finset.mem_insert_of_mem (Finset.mem_insert.mpr (Or.inl ht)))
    · by_cases htp : t = p.val.val
      · exact Or.inr (Or.inr htp)
      · exact Or.inl (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
          (Finset.mem_erase.mpr ⟨htp, htA⟩)))
  · intro t ht
    rcases Finset.mem_insert.mp ht with ht | ht
    · exact Or.inr (Or.inl ht)
    · rcases Finset.mem_insert.mp ht with ht | ht
      · exact Or.inl ht
      · obtain ⟨a, ha, rfl⟩ := (mem_windmillPrivateSet x (windmillContacts x u) t).mp
          (Finset.mem_of_mem_erase ht)
        exact Or.inr (Or.inr ⟨a.property.symm, (hguard _
          ((mem_windmillPrivateSet x (windmillContacts x u) _).mpr ⟨a, ha, rfl⟩)).2⟩)

end Gallai.TwoException
